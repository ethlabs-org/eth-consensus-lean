module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeCrossing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifies
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Driven
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Participants
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Proposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Safety

public section

/-! # The shadow run-facts bundles

The shadow instances of the Option B bundles, at `Store.updateFinality'` and `Node.frame'`:
`GoldilocksRun'.toStaticCore`, `Growing.GoldilocksRun'.toCore` and
`Healing.Growing.ResetPremisesUpTo'.toCore` and `Growing.GoldilocksRun'.toLocalRunCore`, every
field from the proved shadow lemmas (`driven` from `Healing.projection_driven_of_run'`). The handler
facts over `exec'` behind `report_attest`, `signed_tick`, `late_tick` and `signed_before_attest` are
private copies of the stock ones. -/

namespace Consensus.Goldilocks

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The shadow cut law is the cut law at the shadow finality update and frame. -/
theorem Node.CutStep'.with {self : Fin sp.n} {t : Time}
    {st st' : NodeState (goldilocksNode sp ro)} {c : Cut (goldilocksNode sp ro)}
    (h : Node.CutStep' self t st c st') :
    CutStepWith Store.updateFinality Node.frame self t st c st' := by
  rcases c with ⟨⟨B, _ | _⟩ | a | ⟨C, _ | a⟩⟩ | ℓ
  · have h := (Node.cutStep_block_false _ _ _ _ _).1 h
    exact (cutStepWith_block_false B).2
      ⟨by rw [← Store.onBlock_eq_onBlockWith]; exact h.1, h.2⟩
  · have h := (Node.cutStep_block_true _ _ _ _ _).1 h
    exact (cutStepWith_block_true B).2
      ⟨h.1, by rw [← Store.onBlock_eq_onBlockWith]; exact h.2.1, h.2.2⟩
  · exact (cutStepWith_attestation a).2 ((Node.cutStep_attestation _ _ _ _ _).1 h)
  · exact (cutStepWith_attest_none C).2 ((Node.cutStep_attest_none _ _ _ _ _).1 h)
  · exact (cutStepWith_attest_some C a).2 ((Node.cutStep_attest_some _ _ _ _ _ _).1 h)
  · exact (cutStepWith_ac ℓ).2 ((Node.cutStep_ac _ _ _ _ _).1 h)

variable {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}


/-! ### Handler facts over `exec'` (copies of the stock private ones) -/

private theorem proposal_no_attest'' (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro))
    (t : Time) (x : Nat) (C : AC.Blk sp.n (List (FG.Att sp.n))) (s : Option (FG.Att sp.n)) :
    Cut.fg (.attest C s) ∉ (Node.tickStep proposer dg y st t x .proposal).2 := by
  simp only [Node.tickStep_eq]
  split_ifs
  · split
    · simp [Node.acProposal_eq]
    · simp only [Node.proposeBlock_eq, Node.onBlock_eq]
      split_ifs
      · simp [Node.acProposal_eq]
      · split <;> simp [Node.acProposal_eq, Node.acCall_eq]
  · simp

private theorem signed_only_in_ticks'' (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro))
    (t : Time) (e : Node.Event (goldilocksNode sp ro)) (C : AC.Blk sp.n (List (FG.Att sp.n)))
    (a : FG.Att sp.n) (h : Cut.fg (.attest C (some a)) ∈ (Node.exec proposer dg y st t e).2) :
    ∃ x, e = .tick x true := by
  cases e with
  | tick x fgDue =>
    cases fgDue
    · exfalso
      simp only [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps,
        Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, List.nil_append,
        List.mem_append] at h
      rcases h with h | h
      · simp [Node.tickStep_eq, Node.acCall_eq] at h
      · exact proposal_no_attest'' y _ t x C _ h
    · exact ⟨x, rfl⟩
  | block B =>
    simp only [Node.exec_eq, Node.onBlock_eq, Node.acCall_eq] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp at h
  | message m => simp [Node.exec_eq, Node.onMessage_eq, Node.acCall_eq] at h
  | attestation a' => simp [Node.exec_eq, Node.onAttestation] at h
  | restart => simp [Node.exec_eq, Node.restart_eq, Node.acCall_eq] at h

/-- A tick delivers no message (the `ac_on_message` half of `exec_ac_call`). -/
private theorem tick_no_message (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro))
    (t : Time) (x : Nat) (fgDue : Bool) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hm : Cut.ac ℓ ∈ (Node.exec proposer dg y st t (.tick x fgDue)).2) (m : AC.Vote sp.n)
    (hc : ℓ.call = .message m) : False := by
  have hm' : Cut.ac ℓ ∈ (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
        .proposal).2 ++
      (Node.tickStep proposer dg y (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).1 t x .fgUpdate).2 := by
    cases fgDue
    · simp only [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps,
        Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, List.nil_append] at hm
      exact List.mem_append_left _ hm
    · simpa [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps] using hm
  simp only [List.mem_append] at hm'
  rcases hm' with (hm' | hm') | hm'
  · simp only [Node.tickStep_eq, Node.acCall_eq, List.mem_singleton, Cut.ac.injEq] at hm'
    subst hm'; cases hc
  · simp only [Node.tickStep_eq] at hm'
    split_ifs at hm'
    · split at hm'
      · simp only [Node.acProposal_eq, List.mem_singleton, Cut.ac.injEq] at hm'
        subst hm'; cases hc
      · rcases List.mem_cons.1 hm' with hm' | hm'
        · simp only [Node.acProposal_eq, Cut.ac.injEq] at hm'; subst hm'; cases hc
        · simp only [Node.proposeBlock_eq, Node.onBlock_eq] at hm'
          split_ifs at hm'
          · simp at hm'
          · split at hm'
            · simp at hm'
            · simp only [Node.acCall_eq, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
                List.not_mem_nil, or_false] at hm'
              subst hm'; cases hc
    · simp at hm'
  · simp only [Node.tickStep_eq] at hm'
    split at hm'
    · simp only [Node.acToFG_eq, List.mem_singleton, Cut.ac.injEq] at hm'; subst hm'; cases hc
    · rcases List.mem_cons.1 hm' with hm' | hm'
      · simp only [Node.acToFG_eq, Cut.ac.injEq] at hm'; subst hm'; cases hc
      · simp only [Node.attest] at hm'
        split at hm' <;> simp at hm'


/-- An attestation in the pool of an honest node was processed by it at an earlier cut (a copy of
`pool_processed`). -/
private theorem pool_processed (hrun : GoldilocksRun' proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {m : Nat} {a : FG.Att sp.n}
    (ha : a ∈ (tr.state y m).fg.atts) : ∃ k < m, tr.ProcessAttAt y k a := by
  induction m with
  | zero =>
    change a ∈ (tr.init y).fg.atts at ha
    rw [hrun.init y hy] at ha
    cases ha
  | succ m ih =>
    have lift : a ∈ (tr.state y m).fg.atts → ∃ k < m + 1, tr.ProcessAttAt y k a := fun ha =>
      let ⟨k, hk, hp⟩ := ih ha
      ⟨k, by omega, hp⟩
    rcases Coherence.fg_step hrun.toLocalRun' hy m with he | ⟨B, hA, hB⟩ | ⟨b, hb, he⟩
    · exact lift (he ▸ ha)
    · rcases (Healing.onBlock_fields hB).choose_spec.choose_spec.2.2.2.2.2.2 a ha with ha | ha
      · exact lift ha
      · exact ⟨m, by omega, Or.inr ⟨B, hA, ha⟩⟩
    · rw [he] at ha
      rcases (Store.onAttestation_fields _ b).2.2 a ha with ha | rfl
      · exact lift ha
      · exact ⟨m, by omega, Or.inl hb⟩

/-- The only block that `on_block(B')` processes is `B'`. -/
private theorem onBlock_cuts {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)} {t : Time}
    {B B' : AC.Blk sp.n (List (FG.Att sp.n))} {acc : Bool}
    (h : Cut.fg (.block B acc) ∈ (Node.onBlock y st t B').2) : B = B' := by
  rw [Node.onBlock_eq] at h
  by_cases hs : sp.toParams.slotOf t < B'.slot
  · simp [hs] at h
  · rcases ho : st.fg.onBlock B' with _ | fg' <;> simp [hs, ho, Node.acCall_eq] at h <;>
      exact h.1

/-- The only block a tick processes is the own proposal, whose attestations come from the pool
at the start of the tick (a copy of `tick_block_payload`). -/
private theorem tick_block_payload {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)}
    {t : Time} {x : Nat} {fgDue : Bool} {B : AC.Blk sp.n (List (FG.Att sp.n))} {acc : Bool}
    (h : Cut.fg (.block B acc) ∈ (Node.exec proposer dg y st t (.tick x fgDue)).2) :
    ∀ a ∈ B.fgPayload, a ∈ st.fg.atts := by
  have hprop : ∀ {st₀ : NodeState (goldilocksNode sp ro)}, st₀.fg = st.fg →
      Cut.fg (.block B acc) ∈ (Node.tickStep proposer dg y st₀ t x .proposal).2 →
      ∀ a ∈ B.fgPayload, a ∈ st.fg.atts := by
    intro st₀ hst₀ h
    simp only [Node.tickStep_eq] at h
    split_ifs at h
    · split at h
      · simp [Node.acProposal_eq] at h
      · simp only [Node.acProposal_eq, List.mem_cons, reduceCtorEq, false_or,
          Node.proposeBlock_eq] at h
        rw [onBlock_cuts h]
        intro a ha
        have := (List.mem_filter.1 ha).1
        rwa [hst₀] at this
    · simp at h
  have hst : (Node.tickStep proposer dg y st t x .acTick).1.fg = st.fg := by
    simp only [Node.tickStep_eq, Node.acCall_eq]
  cases fgDue
  case false =>
    simp only [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps,
      Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, List.nil_append,
      List.mem_append] at h
    rcases h with h | h
    · simp [Node.tickStep_eq, Node.acCall_eq] at h
    · exact hprop hst h
  simp only [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps, ↓reduceIte,
    List.foldl_cons, List.foldl_nil, List.nil_append, List.mem_append] at h
  rcases h with (h | h) | h
  · simp [Node.tickStep_eq, Node.acCall_eq] at h
  · exact hprop hst h
  · simp only [Node.tickStep_eq] at h
    split at h
    · simp [Node.acToFG_eq] at h
    · simp only [Node.acToFG_eq, List.mem_cons, reduceCtorEq, false_or, Node.attest] at h
      split at h <;> simp at h

/-- An `fg_attest` cut lies in a tick, after the earlier cuts of that tick (a copy of
`tick_of_attest`). -/
private theorem tick_of_attest (hrun : GoldilocksRun' proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest C s))) :
    ∃ j₀ ≤ k, ∃ x, tr.TickAt proposer dg y j₀ (tr.time k) ∧
      ∀ i, j₀ ≤ i → i ≤ k →
        ∃ c ∈ (Node.exec proposer dg y (tr.state y j₀) (tr.time k) (.tick x true)).2,
          tr.label i = some c := by
  obtain ⟨j₀, e, kk, hg, hk, hkk⟩ := Coherence.call_in_group hrun.toLocalRun' hy hc
  obtain ⟨x, rfl⟩ := Compose.exec_attest (proposer := proposer) (dg := dg) y _ _ e
    (List.mem_of_getElem? hkk)
  have hg' := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hg
  refine ⟨j₀, by omega, x, (RunTrace.tickAt_iff _ _ _ _ _ _).2 ⟨x, true, hg⟩,
    fun i hi hik => ?_⟩
  have hlen := (List.getElem?_eq_some_iff.1 hkk).1
  have hl := (hg'.2.1 (i - j₀) (by omega)).2.2.2.2
  rw [Nat.add_sub_cancel' hi] at hl
  exact ⟨_, List.getElem_mem _, hl⟩


/-- Only the FG update calls `ac_to_fg` (a copy of `toFG_not_mem`). -/
private theorem toFG_not_mem (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (x : Nat) {ℓ : ACLabel (goldilocksNode sp ro)} (hc : ℓ.call = .toFG)
    (h : Cut.ac ℓ ∈ (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
        .proposal).2) :
    False := by
  rcases List.mem_append.1 h with h | h
  · simp only [Node.tickStep_eq, Node.acCall_eq, List.mem_singleton, Cut.ac.injEq] at h
    rw [h] at hc
    cases hc
  · revert h
    simp only [Node.tickStep_eq]
    split_ifs
    · split
      · simp only [Node.acProposal_eq, List.mem_singleton, Cut.ac.injEq]
        rintro rfl
        cases hc
      · simp only [Node.proposeBlock_eq, Node.onBlock_eq]
        split_ifs
        · intro h
          simp only [Node.acProposal_eq, Node.acCall_eq, List.mem_cons, Cut.ac.injEq,
            List.not_mem_nil, or_false] at h
          subst h
          cases hc
        · split
          · intro h
            simp only [Node.acProposal_eq, Node.acCall_eq, List.mem_cons, Cut.ac.injEq,
              reduceCtorEq, List.not_mem_nil, or_false] at h
            subst h
            cases hc
          · intro h
            simp only [Node.acProposal_eq, Node.acCall_eq, List.mem_cons, Cut.ac.injEq,
              reduceCtorEq, List.not_mem_nil, or_false, false_or] at h
            rcases h with rfl | rfl <;> cases hc
    · simp

/-- The cut after an `ac_to_fg` cut of a handler is its `fg_attest` (a copy of `toFG_next`). -/
private theorem toFG_next (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (e : Node.Event (goldilocksNode sp ro)) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hk : (Node.exec proposer dg y st t e).2[k]? = some (.ac ℓ)) (hc : ℓ.call = .toFG) :
    ∃ st₁, Node.CutChain y t st ((Node.exec proposer dg y st t e).2.take k) st₁ ∧
      ℓ.frame = Node.frame st₁ ∧
      ∀ C, ((goldilocksNode sp ro).toFG st₁.ac (Node.frame st₁) t).2 = some C →
        ∃ s, (Node.exec proposer dg y st t e).2[k + 1]? = some (.fg (.attest C s)) := by
  cases e with
  | block B =>
    have h := List.mem_of_getElem? hk
    simp only [Node.exec_eq, Node.onBlock_eq, Node.acCall_eq] at h
    split_ifs at h
    · simp at h
    · split at h
      · simp at h
      · simp only [List.mem_cons, reduceCtorEq, Cut.ac.injEq, false_or] at h
        rcases h with h | h
        · rw [h] at hc
          cases hc
        · simp at h
  | message m =>
    have h := List.mem_of_getElem? hk
    simp only [Node.exec_eq, Node.onMessage_eq, Node.acCall_eq, List.mem_singleton,
      Cut.ac.injEq] at h
    rw [h] at hc
    cases hc
  | attestation a =>
    have h := List.mem_of_getElem? hk
    simp [Node.exec_eq, Node.onAttestation] at h
  | restart =>
    have h := List.mem_of_getElem? hk
    simp only [Node.exec_eq, Node.restart_eq, Node.acCall_eq, List.mem_singleton,
      Cut.ac.injEq] at h
    rw [h] at hc
    cases hc
  | tick x fgDue =>
    have hsign : fgDue = true := by
      cases fgDue with
      | false =>
        have hm := List.mem_of_getElem? hk
        exact (toFG_not_mem (proposer := proposer) (dg := dg) y st t x hc (List.mem_append.2
          (by simpa [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps]
            using hm))).elim
      | true => rfl
    subst fgDue
    have hcuts : (Node.exec proposer dg y st t (.tick x true)).2 =
        (Node.tickStep proposer dg y st t x .acTick).2 ++
        (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
          .proposal).2 ++
        (Node.tickStep proposer dg y
          (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
            .proposal).1 t x .fgUpdate).2 := by
      simp [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps]
    rw [hcuts] at hk ⊢
    set l := (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
        .proposal).2 with hl
    set st₁ := (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
      .proposal).1
    have hch : Node.CutChain y t st l st₁ :=
      Compose.chain_append' y (Compose.tickStep_chain' proposer dg y st t x _)
        (Compose.tickStep_chain' proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
          .proposal)
    have hn : l.length ≤ k := by
      by_contra hlt
      rw [List.getElem?_append_left (by omega)] at hk
      exact toFG_not_mem y st t x hc (List.mem_of_getElem? hk)
    rw [List.getElem?_append_right hn] at hk
    rw [List.getElem?_append_right (by omega)]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_sub_cancel_left] at hk
    rw [show l.length + m + 1 - l.length = m + 1 by omega]
    simp only [Node.tickStep_eq, Node.acToFG_eq] at hk ⊢
    have hm : m = 0 := by
      split at hk
      · rcases m with _ | m <;> simp_all
      · simp only [Node.attest] at hk
        split at hk
        · rcases m with _ | _ | m <;> simp_all
        · rcases m with _ | _ | _ | m <;> simp_all
    subst hm
    refine ⟨st₁, by rw [Nat.add_zero, List.take_left' rfl]; exact hch, ?_, fun C hC => ?_⟩
    · split at hk
      all_goals
        simp only [List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at hk
        subst hk
        rfl
    · rw [hC]
      simp only [Node.attest]
      split <;> simp

/-! ### Pending fields (placeholders with the fields' exact types) -/

private theorem hj_mono_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {i j}, i ≤ j → (tr.state y i).fg.hj ≤ (tr.state y j).fg.hj := by
  intro y hy i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    apply ih.trans
    rcases Coherence.fg_step hrun.toLocalRun' hy j with he | ⟨B, -, hB⟩ | ⟨a, -, he⟩
    · rw [he]
    · rw [Store.onBlock_eq_onBlockWith] at hB
      obtain ⟨pr, σ, -, -, -, -, -, he⟩ := Store.onBlockWith_eq_some hB
      rw [he]
      obtain ⟨atts, hatt⟩ := Store.addAtts_eq
        (Store.updateFinality { (tr.state y j).fg with
          blocks := Function.update (tr.state y j).fg.blocks B.root (some B),
          σ := Function.update (tr.state y j).fg.σ B.root σ } σ) B.fgPayload
      rw [hatt]
      have key : ∀ st₁ : Store sp.toParams (Payload sp.n), st₁.hj = (tr.state y j).fg.hj →
          (tr.state y j).fg.hj ≤ (Store.updateFinality st₁ σ).hj := by
        intro st₁ hst₁
        rcases Store.FinalitySpec.J_hj Store.finalitySpec_updateFinality' st₁ σ with
          h | ⟨-, he', -, hlex⟩
        · exact le_of_eq (hst₁.symm.trans h.2.symm)
        · rw [he', ← hst₁]
          rcases hlex with h | h
          · exact h.le
          · exact le_of_eq h.1
      exact key _ rfl
    · rw [he]
      obtain ⟨atts, he'⟩ := Store.onAttestation_eq (tr.state y j).fg a
      rw [he']

private theorem report_attest_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {k} {ℓ : ACLabel (goldilocksNode sp ro)} {C},
    tr.CallAt y k (.ac ℓ) → ℓ.call = .toFG →
    ((goldilocksNode sp ro).toFG (tr.state y k).ac ℓ.frame (tr.time k)).2 = some C →
    ∃ s, tr.CallAt y (k + 1) (.fg (.attest C s)) ∧ tr.time (k + 1) = tr.time k ∧
      (tr.state y (k + 1)).fg = (tr.state y k).fg := by
  intro y hy k ℓ C hk hc hC
  have h := hrun.toLocalRun'
  obtain ⟨j₀, e, k', hg, rfl, hk'⟩ := Coherence.call_in_group h hy hk
  obtain ⟨st₁, hch, hfr, hnext⟩ := toFG_next y _ _ e hk' hc
  have hg' := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hg
  have hlen := (List.getElem?_eq_some_iff.1 hk').1
  have hst : tr.state y (j₀ + k') = st₁ := by
    have := Compose.cutChain_run' h hy hch j₀ rfl fun m hm => by
      rw [List.length_take] at hm
      obtain ⟨hn, ht, -, -, hl⟩ := hg'.2.1 m (by omega)
      exact ⟨hn, ht, by rw [hl, List.getElem_take]⟩
    rwa [List.length_take, min_eq_left hlen.le] at this
  rw [hst, hfr] at hC
  obtain ⟨s, hs⟩ := hnext C hC
  obtain ⟨hs', hc'⟩ := List.getElem?_eq_some_iff.1 hs
  obtain ⟨hn, ht, -, -, hl⟩ := hg'.2.1 (k' + 1) hs'
  obtain ⟨-, ht₀, -, -, -⟩ := hg'.2.1 k' hlen
  refine ⟨s, ⟨by rw [← add_assoc] at hn; exact hn, ?_⟩, by rw [← add_assoc] at ht; rw [ht, ht₀],
    ?_⟩
  · rw [← add_assoc] at hl
    rw [hl, hc']
  · rw [tr.state_succ_of_call hk]
    exact ((Node.cutStep_ac _ _ _ _ _).1 (h.cutLaw y hy _ _ hk)).2.2.1

private theorem signed_tick_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {d C a}, tr.CallAt y d (.fg (.attest C (some a))) →
    ∃ j ≤ d, (∀ i, j ≤ i → i ≤ d → tr.time i = tr.time d ∧
        ∀ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y i (.ac ℓ) → ∀ m, ℓ.call ≠ .message m) ∧
      ∀ i < j, ∀ c, tr.CallAt y i c → tr.time i = tr.time d →
        ∃ ℓ : ACLabel (goldilocksNode sp ro), c = .ac ℓ ∧ ℓ.call = .restart := by
  intro y hy d C a hcd
  obtain ⟨j, ev, kk, hg, hdj, hk⟩ := Coherence.call_in_group hrun.toLocalRun' hy hcd
  obtain ⟨x, rfl⟩ := signed_only_in_ticks'' y _ _ _ C a (List.mem_of_getElem? hk)
  have hg' := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hg
  have hkk : kk < (Node.exec proposer dg y (tr.state y j) (tr.time d)
      (.tick x true)).2.length := by
    by_contra h
    rw [List.getElem?_eq_none (not_lt.mp h)] at hk
    cases hk
  refine ⟨j, by omega, fun i h1 h2 => ⟨?_, fun ℓ hc m hm => ?_⟩, fun i hi c hc ht => ?_⟩
  · have := (hg'.2.1 (i - j) (by omega)).2.1
    rwa [Nat.add_sub_cancel' h1] at this
  · have hl := (hg'.2.1 (i - j) (by omega)).2.2.2.2
    rw [Nat.add_sub_cancel' h1, hc.2] at hl
    have hmem := List.getElem_mem
      (l := (Node.exec proposer dg y (tr.state y j) (tr.time d) (.tick x true)).2)
      (n := i - j) (by omega)
    rw [← Option.some.inj hl] at hmem
    exact tick_no_message y _ _ x _ hmem m hm
  · exact Compose.before_tick' hrun.toLocalRun' hy
      ((RunTrace.tickAt_iff _ _ _ _ _ _).2 ⟨x, true, hg⟩) hc hi ht

private theorem late_tick_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {t}, 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ jt, ∃ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y jt (.ac ℓ) ∧ ℓ.call = .tick ∧
      tr.time jt = t ∧ ∀ i W, tr.AcceptAt y i W → tr.time i = t → ¬ Node.Proposes proposer y t →
        jt < i := by
  intro y hy t ht0 hpub hw
  obtain ⟨jt, hj'⟩ := hrun.tick_of_awake y hy t ht0 hpub hw
  obtain ⟨x, fgDue, hgt⟩ := (RunTrace.tickAt_iff _ _ _ _ _ _).1 hj'
  have hg := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hgt
  have hlen : 0 < (Node.exec proposer dg y (tr.state y jt) t (.tick x fgDue)).2.length := by
    cases fgDue <;> simp [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps,
      Node.tickStep_eq, Node.acCall_eq]
  obtain ⟨hn0, ht0', -, -, hl0⟩ := hg.2.1 0 hlen
  have hget : (Node.exec proposer dg y (tr.state y jt) t (.tick x fgDue)).2[0]'hlen =
      .ac ⟨.tick, Node.frame (tr.state y jt), ((goldilocksNode sp ro).step y
        (tr.state y jt).ac (Node.frame (tr.state y jt)) t .tick).2⟩ := by
    cases fgDue <;> simp [Node.exec_eq, Node.onTick_eq, Node.runSteps_eq, Node.tickSteps,
      Node.tickStep_eq, Node.acCall_eq]
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0' hl0
  refine ⟨jt, _, ⟨hn0, hl0⟩, rfl, ht0', fun i W hA hit hnp => ?_⟩
  rcases Coherence.blockCall_cases hrun.toLocalRun' hy hA with hgW |
    ⟨j, x', f', -, -, hP, -⟩
  · rw [hit] at hgW
    rcases lt_trichotomy jt i with h | rfl | h
    · exact h
    · have := hl0.symm.trans hA.2
      cases this
    · have := hrun.phase_order y hy y hy i jt t (.block W) (.tick x fgDue) hgW hgt h (.inl rfl)
      simp [Node.Event.phase] at this
  · exact absurd (hit ▸ hP) hnp

private theorem signed_before_attest_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {k C s}, tr.CallAt y k (.fg (.attest C s)) →
    ∀ {Y}, Y ∈ (tr.state y k).fg.tree → ∀ {a}, a ∈ Y.fgPayload → a.val ∈ H →
      ∃ j, tr.SignAt a.val j a ∧ tr.time j < tr.time k := by
  intro y hy k C s hc Y hY a ha haH
  have h := hrun.toLocalRun'
  rcases Coherence.tree_accepted h hy hY with rfl | ⟨i, hik, hA⟩
  · cases ha
  obtain ⟨j, hji, hj⟩ := hrun.att_unforgeable y hy i a (Or.inr ⟨Y, ⟨true, hA⟩, ha⟩) haH
  by_cases hlt : tr.time i < tr.time k
  · exact ⟨j, hj, lt_of_le_of_lt (hrun.time_mono hji.le) hlt⟩
  have hti : tr.time i = tr.time k := le_antisymm (hrun.time_mono hik.le) (not_lt.1 hlt)
  obtain ⟨j₀, hj₀k, x, ht, hl⟩ := tick_of_attest hrun hy hc
  have nfg : ∀ m < j₀, ∀ ℓ, tr.CallAt y m (.fg ℓ) → tr.time m = tr.time k → False :=
    fun m hm ℓ hcm htm => by
      obtain ⟨ℓ', he, -⟩ := Compose.before_tick' h hy ht hcm hm htm
      cases he
  rcases lt_or_ge i j₀ with hij₀ | hij₀
  · exact (nfg i hij₀ _ hA hti).elim
  obtain ⟨c, hcm, hci⟩ := hl i hij₀ hik.le
  rw [hA.2] at hci
  cases hci
  obtain ⟨m, hmj₀, hm⟩ := pool_processed hrun hy (tick_block_payload hcm a ha)
  obtain ⟨j', hj'm, hj'⟩ := hrun.att_unforgeable y hy m a
    (hm.imp_right fun ⟨B, hB, haB⟩ => ⟨B, ⟨true, hB⟩, haB⟩) haH
  have htm : tr.time m < tr.time k := by
    refine lt_of_le_of_ne (hrun.time_mono (by omega)) fun htm => ?_
    rcases hm with hm | ⟨B, hB, -⟩
    · exact nfg m hmj₀ _ hm htm
    · exact nfg m hmj₀ _ hB htm
  exact ⟨j', hj', lt_of_le_of_lt (hrun.time_mono hj'm.le) htm⟩

/-! ### The instances -/

/-- **The static core of a shadow Goldilocks run.** -/
theorem GoldilocksRun'.toStaticCore (hrun : GoldilocksRun' proposer dg H tr ini) :
    StaticRunCore Store.updateFinality Node.frame proposer dg H tr ini where
  finalitySpec := Store.finalitySpec_updateFinality'
  frameOf_F st := by rw [Node.frame_eq]; exact Store.toFrame_F _
  frameOf_tree st B := by rw [Node.frame_eq, Store.toFrame_tree]; exact Iff.rfl
  init := hrun.init
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  vstart := hrun.vstart
  root_ok := hrun.genesis_root_ok
  cutLaw y hy i c hc := (hrun.cutLaw y hy i c hc).with
  att_unforgeable := hrun.att_unforgeable
  awake_of_call := hrun.awake_of_call
  sleep_of_restart := hrun.sleep_of_restart
  sign_public y hy k a hs := by
    obtain ⟨C, hc⟩ := hs
    obtain ⟨j, -, ht⟩ := Compose.attestCall_tick' hrun.toLocalRun' hy hc
    exact hrun.tick_public y hy j _ ht
  signed_run v hv i := by
    obtain ⟨hinit, hexec⟩ := Compose.fg_exec' hrun.toLocalRun'
    obtain ⟨inputs, hin, hs⟩ := Healing.signed_run hinit hexec hv i
    exact ⟨inputs, hin, fun j hj a ha =>
      hs j hj a ⟨_, Compose.projFG_callAt.mpr ha.choose_spec⟩⟩
  reachable y hy i := (Node.fg_reachable_at hrun.toLocalRun' hy i).reachableWith
  jmax y hy i := (Healing.jMax_iff _).1 (Node.fg_reachable_at hrun.toLocalRun' hy i).jMax
  frameOK y hy i := Compose.frameOK_state' hrun.toLocalRun' hy i
  projAC_state y hy i := Compose.projAC_state' hrun.toLocalRun' hy i
  acRun hnc := Compose.goldilocks_ac_projection_from' hrun hnc
  coherent hnc := Coherence.honest_blocks_coherent hrun.toLocalRun' hnc
  tree_mono y hy _ _ hki := Coherence.tree_mono' hrun.toLocalRun' hy hki
  tree_accepted y hy _ _ hW := Coherence.tree_accepted hrun.toLocalRun' hy hW
  hj_mono := hj_mono_pending hrun
  ac_block_after y hy _ _ ha := Healing.ac_block_after' hrun.toLocalRun' hy ha
  attest_source y hy _ _ _ hc := Coherence.attest_source hrun.toLocalRun' hy hc
  report_attest := report_attest_pending hrun
  signed_tick := signed_tick_pending hrun
  late_tick := late_tick_pending hrun
  joined_at_call y hy i t hi hnr hit := Compose.joined_at_call hrun hy i hi hnr hit
  signed_before_attest := signed_before_attest_pending hrun
  accept_of_proposesAt hnc _ _ _ hp hW := Coherence.accept_of_proposesAt hrun hnc hp hW
  proposal_payload hp hW := by
    obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hW
    rcases Coherence.blockCall_cases hrun.toLocalRun' hp hc with hg |
      ⟨j, x, fgDue, -, -, -, d, pay, -, hB, -, -, -, hfgj⟩
    · rw [RunTrace.groupAt_iff] at hg
      exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
    · exact ⟨d.head, by rw [hB]; rfl, by rw [hfgj, hB]; rfl⟩
  driven := fun hnc => Healing.projection_driven_of_run' hrun hnc hrun.genesis_root_ok
  lock_origin hnc y hy i := Compose.lock_origin hrun hnc hy i
  vote_of_awake_joined hnc y hy _ hmv hw hj := Compose.vote_of_awake_joined' hrun hnc hy hmv hw hj
  awake_participant_early hnc _ _ hsync hb _ hX _ _ hu y hy hmv hw hj :=
    Compose.awake_participant_early' hrun hnc hsync hb hX hu hy hmv hw hj

/-- **The core of a shadow Goldilocks run under growing faults.** -/
theorem Growing.GoldilocksRun'.toCore {H : Time → Set (Fin sp.n)}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini) :
    GoldilocksRunCore Store.updateFinality Node.frame proposer dg H tr ini where
  finalitySpec := Store.finalitySpec_updateFinality'
  frameOf_F st := by rw [Node.frame_eq]; exact Store.toFrame_F _
  frameOf_tree st B := by rw [Node.frame_eq, Store.toFrame_tree]; exact Iff.rfl
  antitone := hrun.antitone
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  vstart := hrun.vstart
  upTo hd := (hrun.upTo hd).toStaticCore
  cutLaw y i c hc hy := (hrun.cutLaw y i c hc hy).with
  att_unforgeable := hrun.att_unforgeable
  awake_of_call := hrun.awake_of_call
  acRun hnc := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  coherent hnc := Coherence.honest_blocks_coherent_at hrun hnc
  held_anc_at hnc := fun hd hy hi h hW => Coherence.held_anc_at hrun hnc hd hy hi h hW
  F_mono_at := fun hd hy hi hki => hrun.toLocalRun'.finalized_mono_on_prefix' hd hy hki hi
  acRelayAt := fun hx hacc hy hc hanc relay => hrun.toLocalRun'.acRelayAt' hx hacc hy hc hanc relay
  acCatchAt hcatch := fun hx ha hi hy hc hj hanc =>
    hrun.toLocalRun'.acCatchAt' hcatch hx ha hi hy hc hj hanc

/-- **The node-run bundle of a shadow Goldilocks run under growing faults**
(`GoldilocksRunCore.toLocalRunCore` of `Growing.GoldilocksRun'.toCore`). -/
theorem Growing.GoldilocksRun'.toLocalRunCore {H : Time → Set (Fin sp.n)}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini) :
    Generic.LocalRunCore Store.updateFinality proposer dg H tr ini :=
  hrun.toCore.toLocalRunCore

end Consensus.Goldilocks

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {g ΔF a b hold : Time} {committee : Time → Finset (Fin sp.n)} {beta : ℚ}

/-- **The core of the shadow finite-reset premises.** -/
theorem ResetPremisesUpTo'.toCore
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b committee beta hold) :
    ResetRunCore tr H Store.updateFinality Node.frame proposer dg g ΔF a b committee beta hold
    where
  core := hp.run.toCore
  beta_le := hp.beta_le
  committee_pos := hp.committee_pos
  committeeFacts := hp.committeeFacts
  committeeFaults := hp.committeeFaults
  noColl := hp.noColl
  sync := hp.sync
  awake := hp.awake
  faults := hp.faults
  reset := hp.reset
  reset_le := hp.reset_le
  snapshot := hp.snapshot
  catchUp := hp.catchUp
  noRestart := hp.noRestart
  timeoutDelay := hp.timeoutDelay
  nonempty := hp.nonempty
  deepCover := hp.deepCover

end Consensus.Goldilocks.Healing.Growing

end
