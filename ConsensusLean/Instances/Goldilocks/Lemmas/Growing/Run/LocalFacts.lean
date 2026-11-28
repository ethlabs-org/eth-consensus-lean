module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.RecordsCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run

public section

/-! # Node-local facts retained at an honest observation horizon -/

namespace Consensus.Goldilocks.Growing.LocalRun

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
  (hrun : LocalRun proposer dg H sg tr ini)

include hrun

theorem reachable_at {y k t} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) : Store.Reachable A.genesisPayload (tr.state y k).fg := by
  have h := Compose.fg_reachable (hrun.upTo ht) hy k
  rwa [Trace.upTo_state tr y hle] at h

theorem jmax_at {y k t} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) :
    ∀ B ∈ (tr.state y k).fg.tree, ∀ X ∈ (tr.state y k).fg.tree,
      X.root = ((tr.state y k).fg.σ B.root).J → (tr.state y k).fg.Anc (tr.state y k).fg.F X →
        ((tr.state y k).fg.σ B.root).hj ≤ (tr.state y k).fg.hj :=
  (Healing.jMax_iff _).1 (Healing.jMax_of_reachable (hrun.reachable_at ht hle hy))

theorem coherent (hnc : Compose.NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) :=
  Compose.Growing.honest_blocks_coherent_local hrun hnc

theorem held_anc_at (hnc : Compose.NoCollRun dg tr) {y k t} {B C : A.Blk}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hBC : Anc (tr.HonestBlocksAt H) B C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc B C := by
  have hs := Trace.upTo_state tr y hle
  have hc : C ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, k, by rwa [hs]⟩
  have hanc := RunTrace.anc_upTo_of_right hrun hnc ht hc hBC
  rw [← hs]
  exact Healing.store_anc_of_honest_anc_from (hrun.upTo ht)
    (hnc.upTo t) hy hanc (by rwa [hs])

theorem tree_mono_at {y k i t} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (hki : k ≤ i) : (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  have h := Compose.tree_mono (hrun.upTo ht) hy hki
  rwa [Trace.upTo_state tr y hle, Trace.upTo_state tr y fun q hq => hle q (by omega)] at h

theorem attest_some {y k} {C : A.Blk} {a : FG.Att P.n}
    (hc : tr.CallAt y k (.fg (.attest C (some a)))) (hy : y ∈ H (tr.time k)) :
    (tr.state y k).fg.attest (tr.state y k).record y C = some (a, (tr.post k).record) ∧
      (tr.post k).fg = (tr.state y k).fg ∧ (tr.post k).ac = (tr.state y k).ac :=
  hrun.cutLaw y k _ hc hy

theorem attest_none {y k} {C : A.Blk} (hc : tr.CallAt y k (.fg (.attest C none)))
    (hy : y ∈ H (tr.time k)) :
    (tr.state y k).fg.attest (tr.state y k).record y C = none ∧ tr.post k = tr.state y k :=
  hrun.cutLaw y k _ hc hy

theorem signAt_entry {y k} {att : FG.Att P.n} (hy : y ∈ H (tr.time k))
    (hs : tr.SignAt y k att) :
    ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧ ((tr.state y k).fg.σ E.root).h = att.h := by
  have h := Healing.signAt_entry_from (hrun.upTo (hrun.time_nonneg k)) hy
    ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

theorem signed_before_attest {y k} {C : A.Blk} {s : Option (FG.Att P.n)}
    (hy : y ∈ H (tr.time k)) (hc : tr.CallAt y k (.fg (.attest C s)))
    {Y : A.Blk} (hY : Y ∈ (tr.state y k).fg.tree) {a : FG.Att P.n}
    (ha : a ∈ Y.fgPayload) (haH : a.val ∈ H (tr.time k)) :
    ∃ j, tr.SignAt a.val j a ∧ tr.time j < tr.time k := by
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hY' : Y ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by
    rw [Trace.upTo_state tr y hle]; exact hY
  obtain ⟨j, hj, hjt⟩ := Healing.signed_before_attest (hrun.upTo (hrun.time_nonneg k)) hy
    ((Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩) hY' ha haH
  exact ⟨j, ((RunTrace.upTo_signAt tr).mp hj).2, hjt⟩

theorem client_record_origin {y i t} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (h r : Nat) :
    ((tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r) ∧
    ((tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r)) := by
  obtain ⟨h₁, h₂⟩ := Healing.client_record_origin_from (hrun.upTo ht) hy h r i
  rw [Trace.upTo_state tr y hle] at h₁ h₂
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨k, hk, att, hsa, he⟩ := h₁ hx
    exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩
  · obtain ⟨k, hk, att, hsa, he⟩ := h₂ hx
    exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩

theorem sent_origin {y i t} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) {b : FG.Content} (hb : b ∈ (tr.state y i).record.sent) :
    ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b := by
  obtain ⟨k, hk, att, hsa, he⟩ :=
    Healing.sent_origin_from (hrun.upTo ht) hy i (by rw [Trace.upTo_state tr y hle]; exact hb)
  exact ⟨k, hk, att, ((RunTrace.upTo_signAt tr).mp hsa).2, he⟩

theorem record_sentOK {y i t} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) : ∀ b ∈ (tr.state y i).record.sent,
      (b.2.2.1 = true → b.2.1 ∈ (tr.state y i).record.timeout b.1) ∧
      (b.2.2.1 = false → (tr.state y i).record.target b.1 = some b.2.1) := by
  have h := (Healing.record_facts (hrun.upTo ht) hy i).1
  rw [Trace.upTo_state tr y hle] at h
  exact (Healing.Client.sentOK_iff _).1 h

theorem hj_mono_at {y k i t} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (hki : k ≤ i) : (tr.state y k).fg.hj ≤ (tr.state y i).fg.hj := by
  have h := Healing.hj_mono (hrun.upTo ht) hy hki
  rwa [Trace.upTo_state tr y hle, Trace.upTo_state tr y fun q hq => hle q (by omega)] at h

theorem signAt_wellFormed {y k} {att : FG.Att P.n} (hy : y ∈ H (tr.time k))
    (hs : tr.SignAt y k att) : att.WellFormed :=
  Healing.signAt_wellFormed_from (hrun.upTo (hrun.time_nonneg k)) hy
    ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)

/-- An attestation held at an honest observation was signed before the observed cut, provided
its signer is honest at the observation horizon. -/
theorem held_att_signed {y i t} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att P.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hX
  rcases Healing.tree_accepted (hrun.upTo ht) hy hXt with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := hrun.att_unforgeable y k a
      (hrun.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (hrun.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

theorem held_atts_safe_at {y x : Fin P.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hud : u ≤ d) (htd : t ≤ d) (a b : FG.Att P.n)
    (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b := by
  intro hab
  obtain ⟨k, hk, hka⟩ := held_att_signed hrun hu hytime hy ha (hrun.antitone hud hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed hrun ht hxtime hx hb
    (hab.1 ▸ hrun.antitone htd hav)
  rw [← hab.1] at hlb
  have hka' : (tr.upTo d).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
  have hlb' : (tr.upTo d).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
  obtain ⟨inputs, hin, hs⟩ :=
    Store.signed_run_of_exec (Compose.fg_exec (hrun.upTo (hu.trans hud))) hav (max k l + 1)
  exact FG.client_safety P.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab

theorem accept_of_proposesAt (hnc : Compose.NoCollRun dg tr)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    {p k} {X : A.Blk} (hp : p ∈ H (tr.time k)) (hX : tr.ProposesAt p k X) :
    tr.AcceptAt p k X ∧ X ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
  have hle1 : ∀ q < k + 1, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono (by omega)
  have hX' : (tr.upTo (tr.time k)).ProposesAt p k X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  obtain ⟨hacc, hm, hpost⟩ := Healing.accept_of_proposesAt_from (hrun.upTo (hrun.time_nonneg k))
    hroot (hnc.upTo _) hp (hq p) hX'
  rw [Trace.upTo_state tr p hle1] at hm hpost
  exact ⟨((RunTrace.upTo_acceptAt _).mp hacc).2, hm, hpost⟩

theorem proposal_parent_held (hnc : Compose.NoCollRun dg tr)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    {p k} {X : A.Blk} (hp : p ∈ H (tr.time k)) (hX : tr.ProposesAt p k X) :
    ∃ Pr : A.Blk, X.parent = some Pr.root ∧ Pr ∈ (tr.state p k).fg.tree := by
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hX' : (tr.upTo (tr.time k)).ProposesAt p k X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  have h := Healing.proposal_parent_held_from (hrun.upTo (hrun.time_nonneg k)) hroot
    (hnc.upTo _) hp (hq p) hX'
  rwa [Trace.upTo_state tr p hle] at h

theorem proposal_rows_placed (hnc : Compose.NoCollRun dg tr)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hq : ∀ y, ({ A with initial := ini y } : NodeAC P).Requirements)
    {p kX} {X Pr : A.Blk} (hp : p ∈ H (tr.time kX)) (hX : tr.ProposesAt p kX X)
    (hpar : X.parent = some Pr.root) (hPr : Pr ∈ (tr.state p kX).fg.tree) :
    X ∈ (tr.state p (kX + 1)).fg.tree ∧ Pr ∈ (tr.state p (kX + 1)).fg.tree ∧
    (tr.post kX).fg.σ X.root = (tr.state p (kX + 1)).fg.σ X.root ∧
    (tr.state p kX).fg.σ Pr.root = (tr.state p (kX + 1)).fg.σ Pr.root ∧
    ∀ att, (∃ k' < kX, tr.ProcessAttAt p k' att) →
      att.h = ((tr.state p kX).fg.σ Pr.root).h → att.T = ((tr.state p kX).fg.σ Pr.root).Th →
      att ∈ X.fgPayload ∨ (tr.state p (kX + 1)).fg.OnChain Pr att := by
  have hle : ∀ q < kX, tr.time q ≤ tr.time kX := fun q hq => hrun.time_mono hq.le
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun q hq => hrun.time_mono (by omega)
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  have hst : (tr.upTo (tr.time kX)).projFG.store p (kX + 1) = (tr.state p (kX + 1)).fg := by
    change ((tr.upTo (tr.time kX)).projFG.state p (kX + 1)).1 = _
    rw [Compose.projFG_state (hrun.upTo (hrun.time_nonneg kX)) hp, Trace.upTo_state tr p hle1]
  obtain ⟨-, hXt, hPrt, hσX, hσPr, hplace⟩ :=
    Healing.proposal_rows_placed_from (hrun.upTo (hrun.time_nonneg kX)) (fun y _ => hq y) hroot
      (hnc.upTo _) hp hX' hpar (by rw [Trace.upTo_state tr p hle]; exact hPr)
  rw [hst] at hXt hPrt hσX hσPr
  rw [Trace.upTo_state tr p hle] at hσPr hplace
  refine ⟨hXt, hPrt, hσX, hσPr, fun att ⟨k', hk', hproc⟩ hah haT => ?_⟩
  have := hplace att ⟨k', hk', (RunTrace.upTo_processAttAt _).mpr
    ⟨hrun.time_mono hk'.le, hproc⟩⟩ hah haT
  rwa [hst] at this

end Consensus.Goldilocks.Growing.LocalRun

end
