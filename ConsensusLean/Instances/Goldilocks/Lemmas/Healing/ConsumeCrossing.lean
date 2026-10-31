module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service

public section

/-! # Goldilocks Healing, HS.5: the mature crossing

`hs5-exact-helpers.md` §3.1 (the FG part of `mature_progress_consumption`): an honest proposal
`X` whose parent `Pr` has state height `h` and the entry `E` (slot `u`), with `u + δ_t ≤ X.slot`,
and whose proposer has processed a matching row of every honest validator before its proposal
cut, has state height `≥ h + 1` (`crossing_of_rows`).

* The chain argument (`crossing_step`, G1.8 (a)'s argument at one block; the store lemmas are
  `FGStore/Service`'s private ones, repeated here): every row is in `X`'s payload or on `Pr`'s
  chain; a row on the chain at height `h` was counted at its block, whose parent is at height `h`
  with the entry `E` (a row is valid against its parent's state, and an entry block is one height
  above its parent), and the bit stays while the chain keeps height `h`. So after `X`'s payload
  every honest validator is in `prog`, `|H| ≥ q`, and `ThSlot + δ_t = u + δ_t ≤ X.slot`: the
  target or timeout test raises the height.
* The run (`crossing_of_rows`): `X` is `propose_block`'s block, its payload the
  `proposal_attestations` of the proposer's store before the tick on the parent `Pr`
  (`Compose.blockCall_cases`); a processed row is in the pool (the pool only grows), and a row
  not on `Pr`'s chain is valid against `σ[Pr]` (height `h`, entry `E`), so it is in the payload.
-/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-! ## One block of the chain (FG traces) -/

section Chain

open _root_.Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- Counting attestations keeps the progress bits and sets those of the rows on the entry. -/
private theorem mem_foldl_prog_of {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ σ.prog ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) :
    v ∈ (atts.foldl FG.ChainState.processAtt σ).prog := by
  induction atts generalizing σ with
  | nil => exact h.resolve_right (by simp)
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    have key : σ.prog ⊆ (σ.processAtt a).prog ∧
        (a.h = σ.h ∧ a.T = σ.Th → a.val ∈ (σ.processAtt a).prog) := by
      unfold FG.ChainState.processAtt
      rcases hf : a.fin with _ | q <;> dsimp only <;> split_ifs <;> simp_all
    rw [List.foldl_cons]
    refine ih ?_
    rw [hh, hT]
    rcases h with h | ⟨b, hb, hbv, hbh, hbT⟩
    · exact Or.inl (key.1 h)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl (hbv ▸ key.2 ⟨hbh, hbT⟩)
      · exact Or.inr ⟨b, hb, hbv, hbh, hbT⟩

/-- One accepted block keeps the height, the entry (and its slot) and the progress bits, adds
the bits of its rows on the entry, and does not time out; or it enters the next height. -/
private theorem step_entry {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ σ'.ThSlot = σ.ThSlot ∧
      (∀ v, (v ∈ σ.prog ∨ ∃ a ∈ B.atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) → v ∈ σ'.prog) ∧
      ¬ (gp.q ≤ σ'.prog.card ∧ σ.ThSlot + gp.δt ≤ B.slot)) ∨
    (σ'.h = σ.h + 1 ∧ σ'.Th = B.root ∧ σ'.ThSlot = B.slot) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  have hP := fun v (hv : v ∈ σ.prog ∨ ∃ a ∈ B.atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) =>
    mem_foldl_prog_of (σ := { σ with s := B.slot }) hv
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hP ⊢
  dsimp only at hP ⊢
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, hto, he'⟩ <;> rw [he']
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, hP, hto⟩

/-- Along ancestry the height does not decrease; while it stays, the entry and the progress
bits stay. -/
private theorem anc_h (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A W : NodeBlock P ACP} (h : (tr.store y i).Anc A W) :
    ((tr.store y i).σ A.root).h ≤ ((tr.store y i).σ W.root).h ∧
      (((tr.store y i).σ W.root).h = ((tr.store y i).σ A.root).h →
        ((tr.store y i).σ W.root).Th = ((tr.store y i).σ A.root).Th ∧
        ((tr.store y i).σ A.root).prog ⊆ ((tr.store y i).σ W.root).prog) := by
  induction h with
  | refl => exact ⟨le_rfl, fun _ => ⟨rfl, subset_rfl⟩⟩
  | tail _ hYW ih =>
    have := ih.1
    rcases step_entry (step_σ hr hy hYW.2.1 hYW.2.2) with ⟨hh, hT, -, hp, -⟩ | ⟨hh, -, -⟩
    · refine ⟨by omega, fun he => ?_⟩
      obtain ⟨h1, h2⟩ := ih.2 (by omega)
      exact ⟨hT.trans h1, fun v hv => hp v (Or.inl (h2 hv))⟩
    · exact ⟨by omega, fun _ => by omega⟩

/-- The entry of a held block's state is a held block at the entry slot. -/
private theorem entry_slot (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {W : NodeBlock P ACP} (hW : W ∈ (tr.store y i).tree) :
    ∃ E ∈ (tr.store y i).tree, E.root = ((tr.store y i).σ W.root).Th ∧
      E.slot = ((tr.store y i).σ W.root).ThSlot := by
  have hreach := store_reachable hr hy i
  have hg := (accepted_tree P ACP acp₀ _ hreach).2.2.1
  have hA := (accepted_tree P ACP acp₀ _ hreach).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr hy]
    exact ⟨_, hg, rfl, rfl⟩
  | tail _ hYW ih =>
    rcases step_entry (step_σ hr hy hYW.2.1 hYW.2.2) with ⟨-, hT, hs, -⟩ | ⟨-, hT, hs⟩
    · obtain ⟨E, hE, h1, h2⟩ := ih
      exact ⟨E, hE, h1.trans hT.symm, h2.trans hs.symm⟩
    · exact ⟨_, hYW.2.1, hT.symm, hs.symm⟩

/-- An entry block is one height above its parent. -/
private theorem entry_parent (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {T T' : NodeBlock P ACP} (hT : ((tr.store y i).σ T.root).Th = T.root)
    (hp : ParentIn (tr.store y i).tree T' T) :
    ((tr.store y i).σ T'.root).h < ((tr.store y i).σ T.root).h := by
  have coh : Coherent (tr.store y i).tree := hr.coherent.mono (hr.tree_subset y hy i)
  rcases step_entry (step_σ hr hy hp.2.1 hp.2.2) with ⟨-, hTh, -⟩ | ⟨hh, -⟩
  · obtain ⟨E, hE, h1, hET, -⟩ :=
      (entry_state_of_source P ACP acp₀ _ (store_reachable hr hy i) T' hp.1).1
    have he : E = T := coh.1 hE hp.2.1 (h1.trans (hTh.symm.trans hT))
    rw [he] at hET
    have := (Goldilocks.Anc.slot_le coh hET).1
    have := coh.2 _ hp.1 _ hp.2.1 hp.2.2
    omega
  · omega

/-- A row of a held block is valid against its parent's state, so its height is at most the
parent's. -/
private theorem row_parent (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {X : NodeBlock P ACP} (hX : X ∈ (tr.store y i).tree) {x : FG.Att P.n}
    (hx : x ∈ X.fgPayload) :
    ∃ X', ParentIn (tr.store y i).tree X' X ∧ x.h ≤ ((tr.store y i).σ X'.root).h := by
  rcases ((accepted_tree P ACP acp₀ _ (store_reachable hr hy i)).2.2.2 X hX).cases_tail with
    rfl | ⟨X', -, hX'⟩
  · exact absurd hx (by simp [Params.genesisBlock])
  · obtain ⟨⟨-, hv⟩, -⟩ := P.fg.stateTransition_eq_some.1 (step_σ hr hy hX'.2.1 hX'.2.2)
    refine ⟨X', hX', ?_⟩
    rcases (hv x hx).2 with ⟨h, -⟩ | ⟨-, -, -, -, h⟩
    · exact h.le
    · exact h.le

/-- **The crossing at one block** (G1.8 (a)'s argument for one proposal): a held block `X` on
the parent `Pr`, whose state has the height `h` of the entry `E ⪯ Pr` and the entry `E`, with
`E.slot + δ_t ≤ X.slot`, and a set `S` of validators of weight `≥ q` each with a row for `E` at
`h` in `X`'s payload or on `Pr`'s chain: `X` has state height `≥ h + 1`. -/
theorem crossing_step (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {X Pr E : NodeBlock P ACP} (hX : X ∈ (tr.store y i).tree) (hpar : X.parent = some Pr.root)
    (hE : IsEntry P ACP (tr.store y i) E) (hEPr : (tr.store y i).Anc E Pr)
    (hPrh : ((tr.store y i).σ Pr.root).h = ((tr.store y i).σ E.root).h)
    (hslot : E.slot + P.δt ≤ X.slot) (S : Finset (Fin P.n)) (hS : P.fg.q ≤ S.card)
    (hrow : ∀ v ∈ S, ∃ a : FG.Att P.n, a.val = v ∧ a.h = ((tr.store y i).σ E.root).h ∧
      a.T = E.root ∧ (a ∈ X.fgPayload ∨ (tr.store y i).OnChain Pr a)) :
    ((tr.store y i).σ E.root).h + 1 ≤ ((tr.store y i).σ X.root).h := by
  have coh : Coherent (tr.store y i).tree := hr.coherent.mono (hr.tree_subset y hy i)
  have hPrt : Pr ∈ (tr.store y i).tree := by
    rcases hEPr.cases_tail with h | ⟨_, -, h⟩
    exacts [h ▸ hE.1, h.2.1]
  have hPrTh : ((tr.store y i).σ Pr.root).Th = E.root := ((anc_h hr hy hEPr).2 hPrh).1.trans hE.2
  obtain ⟨E', hE', hE'r, hE's⟩ := entry_slot hr hy hPrt
  rw [coh.1 hE' hE.1 (hE'r.trans hPrTh)] at hE's
  have hbits : ∀ v ∈ S, v ∈ ((tr.store y i).σ Pr.root).prog ∨ ∃ a ∈ X.fgPayload, a.val = v ∧
      a.h = ((tr.store y i).σ Pr.root).h ∧ a.T = ((tr.store y i).σ Pr.root).Th := by
    intro v hv
    obtain ⟨a, rfl, hah, haT, ha | hon⟩ := hrow v hv
    · exact Or.inr ⟨a, ha, rfl, hah.trans hPrh.symm, haT.trans hPrTh.symm⟩
    left
    obtain ⟨Z, hZt, hZPr, haZ⟩ := hon
    obtain ⟨Z', hZ'Z, hZ'h⟩ := row_parent hr hy hZt haZ
    rcases Goldilocks.Anc.total coh hZPr hEPr with hZE | hEZ
    · exfalso
      rcases (Relation.ReflTransGen.head hZ'Z hZE).cases_tail with rfl | ⟨T', hZ'T', hT'E⟩
      · have := (Goldilocks.Anc.slot_le coh hZE).1
        have := coh.2 _ hZ'Z.1 _ hZ'Z.2.1 hZ'Z.2.2
        omega
      · have := (anc_h hr hy hZ'T').1
        have := entry_parent hr hy hE.2 hT'E
        omega
    have hEZ' : (tr.store y i).Anc E Z' := by
      rcases hEZ.cases_tail with rfl | ⟨W', hEW', hW'Z⟩
      · have := entry_parent hr hy hE.2 hZ'Z
        omega
      · obtain rfl : W' = Z' :=
          coh.1 hW'Z.1 hZ'Z.1 (Option.some.inj (hW'Z.2.2.symm.trans hZ'Z.2.2))
        exact hEW'
    have h1 := anc_h hr hy hEZ'
    have h2 := (anc_h hr hy ((Relation.ReflTransGen.single hZ'Z).trans hZPr)).1
    have hZ'h' : ((tr.store y i).σ Z'.root).h = ((tr.store y i).σ E.root).h := by omega
    have hZ'T := (h1.2 hZ'h').1
    have h3 := anc_h hr hy hZPr
    rcases step_entry (step_σ hr hy hZ'Z.2.1 hZ'Z.2.2) with ⟨hh, -, -, hp, -⟩ | ⟨hh, -, -⟩
    · exact (h3.2 (by omega)).2 (hp _ (Or.inr ⟨a, haZ, rfl, by omega,
        haT.trans (hE.2.symm.trans hZ'T.symm)⟩))
    · omega
  rcases step_entry (step_σ hr hy hX hpar) with ⟨-, -, -, hp, hto⟩ | ⟨hh, -, -⟩
  · refine absurd ⟨le_trans hS (Finset.card_le_card fun v hv => hp v (hbits v hv)), ?_⟩ hto
    change ((tr.store y i).σ Pr.root).ThSlot + P.δt ≤ X.slot
    omega
  · omega

end Chain

/-! ## The run -/

section Run

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time} {proposer : Nat → Fin sp.n}

private theorem store_eq (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]

/-- The FG projection under the HS shared premises. -/
private theorem fg_run (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG := by
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  exact Compose.fg_projection _ _ dg H _ tr proposer hreq hs.genesisRoot hrun.toLocalRun hs.noColl

/-- An honest validator signs its own attestations. -/
private theorem signAt_val (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) : att.val = y := by
  obtain ⟨src, hc⟩ := hs
  have h := (hrun.cutLaw y hy k _ hc).1
  unfold _root_.Consensus.Goldilocks.Store.attest FG.Record.createAtt at h
  split at h
  · cases h
  · split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

/-- `fg_on_attestation` keeps the pool and adds its attestation. -/
private theorem mem_onAttestation {st : Store sp.toParams (Payload sp.n)} {a b : FG.Att sp.n}
    (h : a ∈ st.atts ∨ a = b) : a ∈ (st.onAttestation b).atts := by
  unfold _root_.Consensus.Goldilocks.Store.onAttestation
  split_ifs with hb
  · rcases h with h | rfl
    exacts [h, hb]
  · simpa using h

/-- `addAtts` keeps the pool and adds its attestations. -/
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

/-- An accepted block keeps the pool and adds its payload. -/
private theorem mem_onBlock {st st' : Store sp.toParams (Payload sp.n)}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : st.onBlock B = some st') {a : FG.Att sp.n}
    (h : a ∈ st.atts ∨ a ∈ B.fgPayload) : a ∈ st'.atts := by
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := Goldilocks.Store.onBlock_eq_some hB
  refine mem_addAtts (h.imp_left fun h => ?_)
  rw [(Goldilocks.Store.updateFinality_spec _ σ').2.2.1]
  exact h

/-- **The pool of an honest node only grows.** -/
private theorem atts_mono (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat}
    (hij : i ≤ j) {a : FG.Att sp.n} (ha : a ∈ (tr.state y i).fg.atts) :
    a ∈ (tr.state y j).fg.atts := by
  induction j, hij using Nat.le_induction with
  | base => exact ha
  | succ j _ ih =>
    have ha := ih
    rcases fg_step hrun.toLocalRun hy j with he | ⟨B, -, hB⟩ | ⟨b, -, he⟩
    · rwa [he]
    · exact mem_onBlock hB (Or.inl ha)
    · rw [he]
      exact mem_onAttestation (Or.inl ha)

/-- A processed attestation is in the pool after the cut. -/
private theorem mem_atts_of_process (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {a : FG.Att sp.n} (h : tr.ProcessAttAt y k a) : a ∈ (tr.state y (k + 1)).fg.atts := by
  rcases h with hc | ⟨B, hc, ha⟩
  · rw [tr.state_succ_of_call hc, (hrun.cutLaw y hy k _ hc).1]
    exact mem_onAttestation (Or.inr rfl)
  · rw [tr.state_succ_of_call hc]
    exact mem_onBlock (hrun.cutLaw y hy k _ hc).2.1 (Or.inr ha)

/-- **The mature crossing at an honest proposal** (`hs5-exact-helpers.md` §3.1): an honest
proposal `X` on the parent `Pr`, with `E ⪯ Pr` an entry of height `h` (held by an honest node),
`Pr` of state height `h`, `E.slot + δ_t ≤ X.slot`, and a matching row of every honest validator
processed by the proposer before its proposal cut: `X` has state height `≥ h + 1`. -/
theorem crossing_of_rows (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {X Pr E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hpar : X.parent = some Pr.root)
    (hEPr : Anc (tr.HonestBlocks H) E Pr) {q₀ : Fin sp.n} (hq₀ : q₀ ∈ H) {k₀ h : Nat}
    (hEt : E ∈ (tr.state q₀ k₀).fg.tree) (hETh : ((tr.state q₀ k₀).fg.σ E.root).Th = E.root)
    (hEh : ((tr.state q₀ k₀).fg.σ E.root).h = h) (hPrh : ((tr.post kX).fg.σ Pr.root).h = h)
    (hslot : E.slot + sp.toParams.δt ≤ X.slot)
    (hdel : ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ att.h = h ∧ att.T = E.root ∧
      ∃ k' < kX, tr.ProcessAttAt p k' att) :
    h + 1 ≤ ((tr.post kX).fg.σ X.root).h := by
  classical
  have hnc := hs.noColl
  have hfg := fg_run hrun hs
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hacc, hXt, hpost⟩ := accept_of_proposesAt hrun hnc hp hX
  rw [hpost] at hPrh ⊢
  have hsub : ∀ {y : Fin sp.n} (_ : y ∈ H) (i : Nat),
      (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun hy i X hX => ⟨_, hy, i, hX⟩
  have hPrU := mem_of_anc_right hEPr (hsub hq₀ _ hEt)
  have hPrX : Anc (tr.HonestBlocks H) Pr X := .single ⟨hPrU, hsub hp _ hXt, hpar⟩
  have hPrt := mem_of_honest_anc hrun hnc hp hPrX hXt
  have hEt' := mem_of_honest_anc hrun hnc hp (hEPr.trans hPrX) hXt
  have hσE := σ_eq_honest hrun hnc hp hq₀ hEt' hEt
  have hEPr' := store_anc_of_honest_anc hrun hnc hp hEPr hPrt
  have hst := store_eq hrun hp (kX + 1)
  -- the entry of `Pr`
  have hPrTh : ((tr.state p (kX + 1)).fg.σ Pr.root).Th = E.root := by
    have := ((anc_h hfg hp (i := kX + 1) (by rw [hst]; exact hEPr')).2
      (by rw [hst, hPrh, hσE, hEh])).1
    rw [hst, hσE, hETh] at this
    exact this
  -- `X` is `propose_block`'s block on `d.head`, with the pool before the tick
  rcases Compose.blockCall_cases hrun.toLocalRun hp hacc with hg |
    ⟨j, x, -, -, -, d, pay, -, hB, -, -, -, hfgj⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hX.1.2
  have hpay : X.fgPayload = (tr.state p kX).fg.proposalAttestations d.head := by
    rw [hfgj, hB]; rfl
  have hdroot : d.head.root = Pr.root := by
    have : X.parent = some d.head.root := by rw [hB]; rfl
    exact Option.some.inj (this.symm.trans hpar)
  -- `σ[Pr]` before the proposal cut
  have hσPr : (tr.state p kX).fg.σ Pr.root = (tr.state p (kX + 1)).fg.σ Pr.root := by
    obtain ⟨_, _, _, _, _, _, _, hsf, _⟩ :=
      Goldilocks.Store.onBlock_fields (hrun.cutLaw p hp kX _ hacc).2.1
    have hne : Pr.root ≠ X.root := fun he => by
      obtain rfl : Pr = X := hU.1 hPrU (hsub hp _ hXt) he
      exact lt_irrefl _ (hU.2 _ hPrU _ hPrU hpar)
    rw [tr.state_succ_of_call hacc, hsf, Function.update_of_ne hne]
  -- the rows
  have hrow : ∀ v ∈ (Finset.univ.filter (· ∈ H) : Finset (Fin sp.n)), ∃ a : FG.Att sp.n,
      a.val = v ∧ a.h = ((tr.projFG.store p (kX + 1)).σ E.root).h ∧ a.T = E.root ∧
      (a ∈ X.fgPayload ∨ (tr.projFG.store p (kX + 1)).OnChain Pr a) := by
    intro v hv
    have hvH : v ∈ H := (Finset.mem_filter.1 hv).2
    obtain ⟨k, att, hsig, hah, haT, k', hk', hproc⟩ := hdel v hvH
    refine ⟨att, signAt_val hrun hvH hsig, by rw [hst, hσE, hEh, hah], haT, ?_⟩
    have hpool := atts_mono hrun hp (show k' + 1 ≤ kX by omega) (mem_atts_of_process hrun hp hproc)
    by_cases hon : (tr.state p kX).fg.OnChain d.head att
    · right
      obtain ⟨Z, hZ, hZd, haZ⟩ := hon
      have hdt := mem_of_anc_right hZd hZ
      obtain rfl : d.head = Pr := hU.1 (hsub hp _ hdt) hPrU hdroot
      have hmono := Compose.tree_mono hrun.toLocalRun hp (Nat.le_succ kX)
      rw [hst]
      exact ⟨Z, hmono hZ, hZd.mono hmono, haZ⟩
    · left
      rw [hpay]
      refine List.mem_filter.2 ⟨hpool, decide_eq_true ⟨Or.inl ⟨?_, ?_⟩, hon⟩⟩
      · rw [hdroot, hσPr, hPrh, hah]
      · rw [hdroot, hσPr, hPrTh, haT]
  -- `|H| ≥ q`
  have hS : sp.toParams.fg.q ≤ (Finset.univ.filter (· ∈ H) : Finset (Fin sp.n)).card := by
    have he : ((Finset.univ.filter (· ∈ H) : Finset (Fin sp.n)) : Set (Fin sp.n)) = H := by
      ext; simp
    rw [← Set.ncard_coe_finset, he]
    have hHc : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h3 := hs.healthy.2.2
    have hn' : sp.n = sp.toParams.n := rfl
    change (2 * sp.toParams.n + 2) / 3 ≤ _
    omega
  have := crossing_step hfg hp (i := kX + 1) (by rw [hst]; exact hXt) hpar
    ⟨by rw [hst]; exact hEt', by rw [hst, hσE, hETh]⟩ (by rw [hst]; exact hEPr')
    (by rw [hst, hPrh, hσE, hEh]) hslot _ hS hrow
  rw [hst, hσE, hEh] at this
  exact this

end Run

end Consensus.Goldilocks.Healing

end
