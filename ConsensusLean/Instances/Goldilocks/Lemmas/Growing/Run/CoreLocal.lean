module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.LocalRunCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # The node-run bundle of a Goldilocks run core

`GoldilocksRunCore.toLocalRunCore`: a Goldilocks run core (stock or shadow) gives the generic
node-run bundle `Generic.LocalRunCore` of its run, each field read on the honest prefix through
`upTo`. The client-record facts (`record_facts`, `client_record_origin_from`, `sent_origin_from`,
`signAt_wellFormed_from`), the proposal facts (`proposal_parent_held_from`,
`proposal_rows_placed_from`) and client safety (`held_atts_safe_at_from`) are re-proved here from
the core's cut law, reachability and signed runs, as copies of the stock proofs. -/

namespace Consensus.Goldilocks

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {tr : GoldilocksTrace sp ro} {ini : Fin sp.n → (goldilocksNode sp ro).State}

namespace StaticRunCore

variable {H : Set (Fin sp.n)}

/-- An honest record changes only at a signing cut, by `create_attestation`. -/
private theorem record_step (rc : StaticRunCore u frameOf proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    (tr.state y (i + 1)).record = (tr.state y i).record ∨
      ∃ C a, tr.CallAt y i (.fg (.attest C (some a))) ∧
        (tr.state y i).fg.attest (tr.state y i).record y C =
          some (a, (tr.state y (i + 1)).record) := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hlaw := rc.cutLaw y hy i c hc
    rw [tr.state_succ_of_call hc]
    rcases c with ⟨⟨B, _ | _⟩ | a' | ⟨C, _ | a'⟩⟩ | ℓ
    · exact Or.inl (by rw [((cutStepWith_block_false B).1 hlaw).2])
    · exact Or.inl ((cutStepWith_block_true B).1 hlaw).2.2.2
    · exact Or.inl ((cutStepWith_attestation a').1 hlaw).2.2
    · exact Or.inl (by rw [((cutStepWith_attest_none C).1 hlaw).2])
    · exact Or.inr ⟨C, a', hc, ((cutStepWith_attest_some C a').1 hlaw).1⟩
    · exact Or.inl ((cutStepWith_ac ℓ).1 hlaw).2.2.2
  · exact Or.inl (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

/-- The honest client record (a copy of `Healing.record_facts`). -/
theorem record_facts (rc : StaticRunCore u frameOf proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) : ∀ i,
    Healing.Client.SentOK (tr.state y i).record ∧
    (∀ b ∈ (tr.state y i).record.sent, ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b) ∧
    ∀ h r, (tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r)
  | 0 => by
    rw [Trace.state, rc.init y hy]
    refine ⟨(Healing.Client.sentOK_iff _).2 fun b hb => ?_, fun b hb => ?_, fun h r hx => ?_⟩
    · simp [Node.initWith, FG.Record.empty] at hb
    · simp [Node.initWith, FG.Record.empty] at hb
    · simp [Node.initWith, FG.Record.empty] at hx
  | i + 1 => by
    obtain ⟨ih₁, ih₂, ih₃⟩ := record_facts rc hy i
    rcases record_step rc hy i with he | ⟨C, a, hc, hca⟩
    · rw [he]
      exact ⟨ih₁, fun b hb => let ⟨k, hk, h'⟩ := ih₂ b hb; ⟨k, by omega, h'⟩,
        fun h r hx => let ⟨k, hk, h'⟩ := ih₃ h r hx; ⟨k, by omega, h'⟩⟩
    · obtain ⟨hrec, -, -, -, ht⟩ := Healing.Client.createAtt_some hca
      rw [hrec]
      have hs : tr.SignAt y i a := ⟨C, hc⟩
      refine ⟨Healing.Client.sentOK_recordAtt ih₁ fun hτ => (ht hτ).2, fun b hb => ?_,
        fun h r hx => ?_⟩
      · simp only [FG.Record.recordAtt, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · obtain ⟨k, hk, h'⟩ := ih₂ b hb
          exact ⟨k, by omega, h'⟩
        · exact ⟨i, by omega, a, hs, rfl⟩
      · simp only [FG.Record.recordAtt] at hx
        rcases hf : a.fin with _ | ⟨p₁, p₂⟩
        · rw [hf] at hx
          obtain ⟨k, hk, h'⟩ := ih₃ h r hx
          exact ⟨k, by omega, h'⟩
        · rw [hf] at hx
          dsimp only at hx
          rw [Function.update_apply] at hx
          split_ifs at hx with hh
          · cases Option.some.inj hx
            exact ⟨i, by omega, a, hs, by rw [hf, hh]⟩
          · obtain ⟨k, hk, h'⟩ := ih₃ h r hx
            exact ⟨k, by omega, h'⟩

/-- Target and timeout records have earlier signing witnesses (the first half of a copy of
`Healing.client_record_origin_from`). -/
theorem record_target_origin (rc : StaticRunCore u frameOf proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) (h r : Nat) : ∀ i,
    (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r
  | 0 => by
    rw [Trace.state, rc.init y hy]
    intro hx
    simp [Node.initWith, FG.Record.empty] at hx
  | i + 1 => by
    have ih := record_target_origin rc hy h r i
    rcases record_step rc hy i with he | ⟨C, a', hc, hca⟩
    · rw [he]
      exact fun hx => let ⟨k, hk, att, h'⟩ := ih hx; ⟨k, by omega, att, h'⟩
    · obtain ⟨hrec, -, -, -, -⟩ := Healing.Client.createAtt_some hca
      rw [hrec]
      have hs : tr.SignAt y i a' := ⟨C, hc⟩
      intro hx
      have key : (tr.state y i).record.target h = some r ∨
          r ∈ (tr.state y i).record.timeout h ∨ (a'.h = h ∧ a'.T = r) := by
        rcases hx with hx | hx
        · dsimp only [FG.Record.recordAtt] at hx
          split_ifs at hx
          · rw [Function.update_apply] at hx
            split_ifs at hx with hh
            · exact Or.inr (Or.inr ⟨hh.symm, Option.some.inj hx⟩)
            · exact Or.inl hx
          · exact Or.inl hx
        · dsimp only [FG.Record.recordAtt] at hx
          split_ifs at hx
          · rw [Function.update_apply] at hx
            split_ifs at hx with hh
            · rcases Finset.mem_insert.1 hx with rfl | hx
              · exact Or.inr (Or.inr ⟨hh.symm, rfl⟩)
              · exact Or.inr (Or.inl (by rw [hh]; exact hx))
            · exact Or.inr (Or.inl hx)
          · exact Or.inr (Or.inl hx)
      rcases key with hx | hx | ⟨h₁, h₂⟩
      · obtain ⟨k, hk, att, h'⟩ := ih (Or.inl hx)
        exact ⟨k, by omega, att, h'⟩
      · obtain ⟨k, hk, att, h'⟩ := ih (Or.inr hx)
        exact ⟨k, by omega, att, h'⟩
      · exact ⟨i, by omega, a', hs, h₁, h₂⟩

/-- An honest signature is well formed (a copy of `Healing.signAt_wellFormed_from`). -/
theorem signAt_wellFormed (rc : StaticRunCore u frameOf proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att) : att.WellFormed := by
  obtain ⟨src, hc⟩ := hs
  have hcl := ((cutStepWith_attest_some src att).1 (rc.cutLaw y hy k _ hc)).1
  have hu := rc.finalitySpec
  have hr := rc.reachable y hy k
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  rcases hsrc : (tr.state y k).fg.blocks src.root with _ | X
  · have hg : ((tr.state y k).fg.σ src.root).Th = sp.toParams.genesisRoot := by
      rw [Store.σ_of_blocks_none_with hu hr hsrc]; rfl
    rw [hg, Store.σ_genesis_with hu hr] at hcl
    exact Compose.createAtt_wellFormed le_rfl Nat.one_pos (by simp [FG.ChainState.init]) hcl
  · have hXr := Store.blocks_root_with hu hr hsrc
    have hX : X ∈ (tr.state y k).fg.tree := by
      change (tr.state y k).fg.blocks X.root = some X
      rw [hXr]; exact hsrc
    obtain ⟨⟨E, hE, hEr, -⟩, -⟩ := Store.entry_state_of_source_with hu hr X hX
    obtain ⟨c, -, -, -, hcs⟩ := Store.chain_state_of_chain_with hu hr E hE
    obtain ⟨h1, -, h3, -, -, -, -, h8, -⟩ := FG.chain_invariants sp.toParams.fg _ _ hcs
    rw [hXr] at hEr
    rw [← hEr] at hcl
    exact Compose.createAtt_wellFormed h1 h3 (fun p hp => lt_of_le_of_lt (h8 p hp).2 h3) hcl

private theorem mem_onAttestation {st : Store sp.toParams (Payload sp.n)} {a b : FG.Att sp.n}
    (h : a ∈ st.atts ∨ a = b) : a ∈ (st.onAttestation b).atts := by
  unfold _root_.Consensus.Goldilocks.Store.onAttestation
  split_ifs with hb
  · rcases h with h | rfl
    exacts [h, hb]
  · simpa using h

private theorem mem_addAtts {st : Store sp.toParams (Payload sp.n)} {a : FG.Att sp.n}
    {l : List (FG.Att sp.n)} (h : a ∈ st.atts ∨ a ∈ l) : a ∈ (st.addAtts l).atts := by
  induction l generalizing st with
  | nil => exact h.resolve_right (by simp)
  | cons b l ih =>
    change a ∈ ((st.onAttestation b).addAtts l).atts
    rcases h with h | h
    · exact ih (Or.inl (mem_onAttestation (Or.inl h)))
    · rcases List.mem_cons.1 h with rfl | h
      · exact ih (Or.inl (mem_onAttestation (Or.inr rfl)))
      · exact ih (Or.inr h)

private theorem mem_onBlockWith (hu : Store.FinalitySpec u)
    {st st' : Store sp.toParams (Payload sp.n)} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : st.onBlockWith u B = some st') {a : FG.Att sp.n}
    (h : a ∈ st.atts ∨ a ∈ B.fgPayload) : a ∈ st'.atts := by
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := Store.onBlockWith_eq_some hB
  refine mem_addAtts (h.imp_left fun h => ?_)
  rw [Store.FinalitySpec.atts hu]
  exact h

/-- The pool of an honest node only grows (a copy of `atts_mono`). -/
theorem atts_mono (rc : StaticRunCore u frameOf proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i j : Nat} (hij : i ≤ j) {a : FG.Att sp.n}
    (ha : a ∈ (tr.state y i).fg.atts) : a ∈ (tr.state y j).fg.atts := by
  induction j, hij using Nat.le_induction with
  | base => exact ha
  | succ j _ ih =>
    by_cases hc : ∃ c, tr.CallAt y j c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := rc.cutLaw y hy j c hc
      rw [tr.state_succ_of_call hc]
      rcases c with ⟨⟨B, _ | _⟩ | b | ⟨C, _ | b⟩⟩ | ℓ
      · rw [((cutStepWith_block_false B).1 hlaw).2]; exact ih
      · exact mem_onBlockWith rc.finalitySpec ((cutStepWith_block_true B).1 hlaw).2.1 (Or.inl ih)
      · rw [((cutStepWith_attestation b).1 hlaw).1]; exact mem_onAttestation (Or.inl ih)
      · rw [((cutStepWith_attest_none C).1 hlaw).2]; exact ih
      · rw [((cutStepWith_attest_some C b).1 hlaw).2.1]; exact ih
      · rw [((cutStepWith_ac ℓ).1 hlaw).2.2.1]; exact ih
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]; exact ih

/-- A processed attestation is in the pool after the cut. -/
theorem mem_atts_of_process (rc : StaticRunCore u frameOf proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {a : FG.Att sp.n} (hp : tr.ProcessAttAt y k a) :
    a ∈ (tr.state y (k + 1)).fg.atts := by
  rcases hp with hc | ⟨B, hc, ha⟩
  · rw [tr.state_succ_of_call hc, ((cutStepWith_attestation a).1 (rc.cutLaw y hy k _ hc)).1]
    exact mem_onAttestation (Or.inr rfl)
  · rw [tr.state_succ_of_call hc]
    exact mem_onBlockWith rc.finalitySpec
      ((cutStepWith_block_true B).1 (rc.cutLaw y hy k _ hc)).2.1 (Or.inr ha)

/-- The parent of an honest proposal is held at its cut (a copy of
`Healing.proposal_parent_held_from`). -/
theorem proposal_parent_held (rc : StaticRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X) :
    ∃ Pr : AC.Blk sp.n (List (FG.Att sp.n)), X.parent = some Pr.root ∧
      Pr ∈ (tr.state p kX).fg.tree := by
  obtain ⟨hacc, -, -⟩ := rc.accept_of_proposesAt hnc hp hX
  obtain ⟨pr, _, hpar, -, hsome, -⟩ := Store.onBlockWith_eq_some
    ((cutStepWith_block_true X).1 (rc.cutLaw p hp kX _ hacc)).2.1
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 hsome
  have hYr : Y.root = pr := Store.blocks_root_with rc.finalitySpec (rc.reachable p hp kX) hY
  refine ⟨Y, by rw [hpar, hYr], ?_⟩
  change (tr.state p kX).fg.blocks Y.root = some Y
  rw [hYr]
  exact hY

/-- The attestations of an honest proposal (a copy of `Healing.proposal_rows_placed_from`, read in
the node's store after the cut). -/
theorem proposal_rows_placed (rc : StaticRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X Pr : AC.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hpar : X.parent = some Pr.root) (hPr : Pr ∈ (tr.state p kX).fg.tree) :
    X ∈ (tr.state p (kX + 1)).fg.tree ∧ Pr ∈ (tr.state p (kX + 1)).fg.tree ∧
      (tr.post kX).fg.σ X.root = (tr.state p (kX + 1)).fg.σ X.root ∧
      (tr.state p kX).fg.σ Pr.root = (tr.state p (kX + 1)).fg.σ Pr.root ∧
      ∀ att, (∃ k' < kX, tr.ProcessAttAt p k' att) →
        att.h = ((tr.state p kX).fg.σ Pr.root).h → att.T = ((tr.state p kX).fg.σ Pr.root).Th →
        att ∈ X.fgPayload ∨ (tr.state p (kX + 1)).fg.OnChain Pr att := by
  classical
  have hU := rc.coherent hnc
  obtain ⟨hacc, hXt, hpost⟩ := rc.accept_of_proposesAt hnc hp hX
  have hmono := rc.tree_mono p hp (Nat.le_succ kX)
  have hPrU : Pr ∈ tr.HonestBlocks H := ⟨p, hp, kX, hPr⟩
  have hXU : X ∈ tr.HonestBlocks H := ⟨p, hp, kX + 1, hXt⟩
  obtain ⟨D, hDpar, hpay⟩ := rc.proposal_payload hp hX
  have hdroot : D.root = Pr.root := Option.some.inj (hDpar.symm.trans hpar)
  have hσPr : (tr.state p kX).fg.σ Pr.root = (tr.state p (kX + 1)).fg.σ Pr.root := by
    obtain ⟨pr, σ', -, -, -, -, -, he⟩ := Store.onBlockWith_eq_some
      ((cutStepWith_block_true X).1 (rc.cutLaw p hp kX _ hacc)).2.1
    have hne : Pr.root ≠ X.root := fun he => by
      obtain rfl : Pr = X := hU.1 hPrU hXU he
      exact lt_irrefl _ (hU.2 _ hPrU _ hPrU hpar)
    rw [tr.state_succ_of_call hacc, he, (Goldilocks.Store.addAtts_fields _ _).2.1,
      Store.FinalitySpec.σ_eq rc.finalitySpec]
    exact (Function.update_of_ne hne _ _).symm
  refine ⟨hXt, hmono hPr, by rw [hpost], hσPr, fun att ⟨k', hk', hproc⟩ hah haT => ?_⟩
  have hpool := rc.atts_mono hp (show k' + 1 ≤ kX by omega) (rc.mem_atts_of_process hp hproc)
  by_cases hon : (tr.state p kX).fg.OnChain D att
  · right
    obtain ⟨Z, hZ, hZd, haZ⟩ := hon
    have hdt := Healing.mem_of_anc_right hZd hZ
    obtain rfl : D = Pr := hU.1 ⟨p, hp, kX, hdt⟩ hPrU hdroot
    exact ⟨Z, hmono hZ, hZd.mono hmono, haZ⟩
  · left
    rw [hpay]
    refine List.mem_filter.2 ⟨hpool, decide_eq_true ⟨Or.inl ⟨?_, ?_⟩, hon⟩⟩
    · rw [hdroot, hah]
    · rw [hdroot, haT]

end StaticRunCore

namespace GoldilocksRunCore

variable {H : Time → Set (Fin sp.n)}

private theorem held_att_signed (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att sp.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hX
  rcases (rc.upTo ht).tree_accepted y hy hXt with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := rc.att_unforgeable y k a
      (rc.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (rc.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

/-- **The node-run bundle of a Goldilocks run core.** -/
theorem toLocalRunCore (rc : GoldilocksRunCore u frameOf proposer dg H tr ini) :
    Generic.LocalRunCore u proposer dg H tr ini where
  finalitySpec := rc.finalitySpec
  antitone := rc.antitone
  time_nonneg := rc.time_nonneg
  time_mono := rc.time_mono
  reachable_at := fun {y k t} ht hle hy => by
    have h := (rc.upTo ht).reachable y hy k
    rwa [Trace.upTo_state tr y hle] at h
  jmax_at := fun {y k t} ht hle hy => by
    have h := (rc.upTo ht).jmax y hy k
    rwa [Trace.upTo_state tr y hle] at h
  coherent := rc.coherent
  held_anc_at hnc := fun ht hle hy hBW hW => rc.held_anc_at hnc ht hy hle hBW hW
  tree_mono_at := fun {y k i t} ht hle hy hki => by
    have h := (rc.upTo ht).tree_mono y hy hki
    rwa [Trace.upTo_state tr y hle, Trace.upTo_state tr y fun q hq => hle q (by omega)] at h
  tree_accepted_at := fun {y i t W} ht hle hy hW => by
    have hW' : W ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hW
    rcases (rc.upTo ht).tree_accepted y hy hW' with h | ⟨k, hk, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hk, ((RunTrace.upTo_acceptAt _).mp ha).2⟩
  att_unforgeable := rc.att_unforgeable
  attest_some := fun {y k C a} hc hy => (cutStepWith_attest_some C a).1 (rc.cutLaw y k _ hc hy)
  attest_none := fun {y k C} hc hy => (cutStepWith_attest_none C).1 (rc.cutLaw y k _ hc hy)
  signAt_entry := fun {y k att} hy hs => by
    obtain ⟨src, hc⟩ := hs
    have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => rc.time_mono hq.le
    have hr := (rc.upTo (rc.time_nonneg k)).reachable y hy k
    rw [Trace.upTo_state tr y hle] at hr
    exact Store.exists_entry_of_createAtt_with rc.finalitySpec hr
      ((cutStepWith_attest_some src att).1 (rc.cutLaw y k _ hc hy)).1
  signed_before_attest := fun {y k C s} hy hc {Y} hY {a} ha haH => by
    have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => rc.time_mono hq.le
    have hc' : (tr.upTo (tr.time k)).CallAt y k (.fg (.attest C s)) :=
      (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
    have hY' : Y ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by
      rw [Trace.upTo_state tr y hle]; exact hY
    obtain ⟨j, hj, hjt⟩ := (rc.upTo (rc.time_nonneg k)).signed_before_attest y hy hc' hY' ha haH
    exact ⟨j, ((RunTrace.upTo_signAt tr).mp hj).2, hjt⟩
  client_record_origin := fun {y i t} ht hle hy h r => by
    have hs := Trace.upTo_state tr y hle
    have h₁ := (rc.upTo ht).record_target_origin hy h r i
    have h₂ := ((rc.upTo ht).record_facts hy i).2.2 h r
    rw [hs] at h₁ h₂
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨k, hk, att, hsa, he⟩ := h₁ hx
      exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩
    · obtain ⟨k, hk, att, hsa, he⟩ := h₂ hx
      exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩
  sent_origin := fun {y i t} ht hle hy {b} hb => by
    have h := ((rc.upTo ht).record_facts hy i).2.1 b
    rw [Trace.upTo_state tr y hle] at h
    obtain ⟨k, hk, att, hsa, he⟩ := h hb
    exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩
  record_sentOK := fun {y i t} ht hle hy => by
    have h := ((rc.upTo ht).record_facts hy i).1
    rw [Trace.upTo_state tr y hle] at h
    exact (Healing.Client.sentOK_iff _).1 h
  hj_mono_at := fun {y k i t} ht hle hy hki => by
    have h := (rc.upTo ht).hj_mono y hy hki
    rwa [Trace.upTo_state tr y hle, Trace.upTo_state tr y fun q hq => hle q (by omega)] at h
  held_atts_safe_at := fun {y x m i u t d} hu hytime hy ht hxtime hx hud htd a b ha hb hav hab => by
    obtain ⟨k, hk, hka⟩ := held_att_signed rc hu hytime hy ha (rc.antitone hud hav)
    obtain ⟨l, hl, hlb⟩ := held_att_signed rc ht hxtime hx hb (hab.1 ▸ rc.antitone htd hav)
    rw [← hab.1] at hlb
    have hka' : (tr.upTo d).SignAt a.val k a :=
      (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
    have hlb' : (tr.upTo d).SignAt a.val l b :=
      (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
    obtain ⟨inputs, hin, hs⟩ := (rc.upTo (hu.trans hud)).signed_run a.val hav (max k l + 1)
    exact FG.client_safety sp.toParams.fg a.val inputs hin
      a (hs k (by omega) a hka') b (hs l (by omega) b hlb') hab
  signAt_wellFormed := fun {y k att} hy hs =>
    (rc.upTo (rc.time_nonneg k)).signAt_wellFormed hy ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  accept_of_proposesAt hnc _ _ := fun {p k X} hp hX => by
    have hle1 : ∀ q < k + 1, tr.time q ≤ tr.time k := fun q hq => rc.time_mono (by omega)
    have hX' : (tr.upTo (tr.time k)).ProposesAt p k X :=
      ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
    obtain ⟨hacc, hm, hpost⟩ :=
      (rc.upTo (rc.time_nonneg k)).accept_of_proposesAt (hnc.upTo _) hp hX'
    rw [Trace.upTo_state tr p hle1] at hm hpost
    exact ⟨((RunTrace.upTo_acceptAt _).mp hacc).2, hm, hpost⟩
  proposal_parent_held hnc _ _ := fun {p k X} hp hX => by
    have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => rc.time_mono hq.le
    have hX' : (tr.upTo (tr.time k)).ProposesAt p k X :=
      ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
    have h := (rc.upTo (rc.time_nonneg k)).proposal_parent_held (hnc.upTo _) hp hX'
    rwa [Trace.upTo_state tr p hle] at h
  proposal_rows_placed hnc _ _ := fun {p kX X Pr} hp hX hpar hPr => by
    have hle : ∀ q < kX, tr.time q ≤ tr.time kX := fun q hq => rc.time_mono hq.le
    have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun q hq => rc.time_mono (by omega)
    have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
      ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
    obtain ⟨hXt, hPrt, hσX, hσPr, hplace⟩ :=
      (rc.upTo (rc.time_nonneg kX)).proposal_rows_placed (hnc.upTo _) hp hX' hpar
        (by rw [Trace.upTo_state tr p hle]; exact hPr)
    rw [Trace.upTo_state tr p hle1] at hXt hPrt hσX hσPr hplace
    rw [Trace.upTo_state tr p hle] at hσPr hplace
    refine ⟨hXt, hPrt, hσX, hσPr, fun att ⟨k', hk', hproc⟩ hah haT => ?_⟩
    exact hplace att ⟨k', hk', (RunTrace.upTo_processAttAt _).mpr
      ⟨rc.time_mono hk'.le, hproc⟩⟩ hah haT

end GoldilocksRunCore

end Consensus.Goldilocks

end
