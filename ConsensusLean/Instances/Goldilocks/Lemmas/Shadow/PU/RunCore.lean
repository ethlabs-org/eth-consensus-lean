module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Participants
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Proposal

public section

/-! # The shadow run-facts bundles

The shadow instances of the Option B bundles, at `Store.updateFinality'` and `Node.frame'`:
`GoldilocksRun'.toStaticCore`, `Growing.GoldilocksRun'.toCore` and
`Healing.Growing.ResetPremisesUpTo'.toCore`, every field from the proved shadow lemmas.

**Pending (work in progress).** The private `*_pending` theorems are placeholders with the exact
types of the fields whose shadow proofs are still being written: `report_attest`,
`signed_before_attest` (copies over `exec'`), and `driven` (lane W's
`Healing.projection_driven_of_run'`). -/

namespace Consensus.Goldilocks

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The shadow cut law is the cut law at the shadow finality update and frame. -/
theorem Node.CutStep'.with {self : Fin sp.n} {t : Time}
    {st st' : NodeState (goldilocksNode' sp ro)} {c : Cut (goldilocksNode' sp ro)}
    (h : Node.CutStep' self t st c st') :
    CutStepWith Store.updateFinality' Node.frame' self t st c st' := by
  rcases c with ⟨⟨B, _ | _⟩ | a | ⟨C, _ | a⟩⟩ | ℓ
  · have h := (Node.cutStep'_block_false _ _ _ _ _).1 h
    exact (cutStepWith_block_false B).2
      ⟨by rw [← Store.onBlock'_eq_onBlockWith]; exact h.1, h.2⟩
  · have h := (Node.cutStep'_block_true _ _ _ _ _).1 h
    exact (cutStepWith_block_true B).2
      ⟨h.1, by rw [← Store.onBlock'_eq_onBlockWith]; exact h.2.1, h.2.2⟩
  · exact (cutStepWith_attestation a).2 ((Node.cutStep'_attestation _ _ _ _ _).1 h)
  · exact (cutStepWith_attest_none C).2 ((Node.cutStep'_attest_none _ _ _ _ _).1 h)
  · exact (cutStepWith_attest_some C a).2 ((Node.cutStep'_attest_some _ _ _ _ _ _).1 h)
  · exact (cutStepWith_ac ℓ).2 ((Node.cutStep'_ac _ _ _ _ _).1 h)

variable {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}


/-! ### Handler facts over `exec'` (copies of the stock private ones) -/

private theorem proposal_no_attest'' (y : Fin sp.n) (st : NodeState (goldilocksNode' sp ro))
    (t : Time) (x : Nat) (C : AC.Blk sp.n (List (FG.Att sp.n))) (s : Option (FG.Att sp.n)) :
    Cut.fg (.attest C s) ∉ (Node.tickStep' proposer dg y st t x .proposal).2 := by
  simp only [Node.tickStep'_eq]
  split_ifs
  · split
    · simp [Node.acProposal'_eq]
    · simp only [Node.proposeBlock'_eq, Node.onBlock'_eq]
      split_ifs
      · simp [Node.acProposal'_eq]
      · split <;> simp [Node.acProposal'_eq, Node.acCall'_eq]
  · simp

private theorem signed_only_in_ticks'' (y : Fin sp.n) (st : NodeState (goldilocksNode' sp ro))
    (t : Time) (e : Node.Event (goldilocksNode' sp ro)) (C : AC.Blk sp.n (List (FG.Att sp.n)))
    (a : FG.Att sp.n) (h : Cut.fg (.attest C (some a)) ∈ (Node.exec' proposer dg y st t e).2) :
    ∃ x, e = .tick x true := by
  cases e with
  | tick x fgDue =>
    cases fgDue
    · exfalso
      simp only [Node.exec'_eq, Node.onTick'_eq, Node.runSteps'_eq, Node.tickSteps,
        Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, List.nil_append,
        List.mem_append] at h
      rcases h with h | h
      · simp [Node.tickStep'_eq, Node.acCall'_eq] at h
      · exact proposal_no_attest'' y _ t x C _ h
    · exact ⟨x, rfl⟩
  | block B =>
    simp only [Node.exec'_eq, Node.onBlock'_eq, Node.acCall'_eq] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp at h
  | message m => simp [Node.exec'_eq, Node.onMessage'_eq, Node.acCall'_eq] at h
  | attestation a' => simp [Node.exec'_eq, Node.onAttestation] at h
  | restart => simp [Node.exec'_eq, Node.restart'_eq, Node.acCall'_eq] at h

/-- A tick delivers no message (the `ac_on_message` half of `exec_ac_call`). -/
private theorem tick_no_message' (y : Fin sp.n) (st : NodeState (goldilocksNode' sp ro))
    (t : Time) (x : Nat) (fgDue : Bool) {ℓ : ACLabel (goldilocksNode' sp ro)}
    (hm : Cut.ac ℓ ∈ (Node.exec' proposer dg y st t (.tick x fgDue)).2) (m : AC.Vote sp.n)
    (hc : ℓ.call = .message m) : False := by
  have hm' : Cut.ac ℓ ∈ (Node.tickStep' proposer dg y st t x .acTick).2 ++
      (Node.tickStep' proposer dg y (Node.tickStep' proposer dg y st t x .acTick).1 t x
        .proposal).2 ++
      (Node.tickStep' proposer dg y (Node.tickStep' proposer dg y
        (Node.tickStep' proposer dg y st t x .acTick).1 t x .proposal).1 t x .fgUpdate).2 := by
    cases fgDue
    · simp only [Node.exec'_eq, Node.onTick'_eq, Node.runSteps'_eq, Node.tickSteps,
        Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, List.nil_append] at hm
      exact List.mem_append_left _ hm
    · simpa [Node.exec'_eq, Node.onTick'_eq, Node.runSteps'_eq, Node.tickSteps] using hm
  simp only [List.mem_append] at hm'
  rcases hm' with (hm' | hm') | hm'
  · simp only [Node.tickStep'_eq, Node.acCall'_eq, List.mem_singleton, Cut.ac.injEq] at hm'
    subst hm'; cases hc
  · simp only [Node.tickStep'_eq] at hm'
    split_ifs at hm'
    · split at hm'
      · simp only [Node.acProposal'_eq, List.mem_singleton, Cut.ac.injEq] at hm'
        subst hm'; cases hc
      · rcases List.mem_cons.1 hm' with hm' | hm'
        · simp only [Node.acProposal'_eq, Cut.ac.injEq] at hm'; subst hm'; cases hc
        · simp only [Node.proposeBlock'_eq, Node.onBlock'_eq] at hm'
          split_ifs at hm'
          · simp at hm'
          · split at hm'
            · simp at hm'
            · simp only [Node.acCall'_eq, List.mem_cons, reduceCtorEq, false_or, Cut.ac.injEq,
                List.not_mem_nil, or_false] at hm'
              subst hm'; cases hc
    · simp at hm'
  · simp only [Node.tickStep'_eq] at hm'
    split at hm'
    · simp only [Node.acToFG'_eq, List.mem_singleton, Cut.ac.injEq] at hm'; subst hm'; cases hc
    · rcases List.mem_cons.1 hm' with hm' | hm'
      · simp only [Node.acToFG'_eq, Cut.ac.injEq] at hm'; subst hm'; cases hc
      · simp only [Node.attest] at hm'
        split at hm' <;> simp at hm'

/-! ### Pending fields (placeholders with the fields' exact types) -/

private theorem hj_mono_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {i j}, i ≤ j → (tr.state y i).fg.hj ≤ (tr.state y j).fg.hj := by
  intro y hy i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    apply ih.trans
    rcases Coherence.fg_step' hrun.toLocalRun' hy j with he | ⟨B, -, hB⟩ | ⟨a, -, he⟩
    · rw [he]
    · rw [Store.onBlock'_eq_onBlockWith] at hB
      obtain ⟨pr, σ, -, -, -, -, -, he⟩ := Store.onBlockWith_eq_some hB
      rw [he]
      obtain ⟨atts, hatt⟩ := Store.addAtts_eq
        (Store.updateFinality' { (tr.state y j).fg with
          blocks := Function.update (tr.state y j).fg.blocks B.root (some B),
          σ := Function.update (tr.state y j).fg.σ B.root σ } σ) B.fgPayload
      rw [hatt]
      have key : ∀ st₁ : Store sp.toParams (Payload sp.n), st₁.hj = (tr.state y j).fg.hj →
          (tr.state y j).fg.hj ≤ (Store.updateFinality' st₁ σ).hj := by
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
  sorry

private theorem signed_tick_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {d C a}, tr.CallAt y d (.fg (.attest C (some a))) →
    ∃ j ≤ d, (∀ i, j ≤ i → i ≤ d → tr.time i = tr.time d ∧
        ∀ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y i (.ac ℓ) → ∀ m, ℓ.call ≠ .message m) ∧
      ∀ i < j, ∀ c, tr.CallAt y i c → tr.time i = tr.time d →
        ∃ ℓ : ACLabel (goldilocksNode sp ro), c = .ac ℓ ∧ ℓ.call = .restart := by
  intro y hy d C a hcd
  obtain ⟨j, ev, kk, hg, hdj, hk⟩ := Coherence.call_in_group' hrun.toLocalRun' hy hcd
  obtain ⟨x, rfl⟩ := signed_only_in_ticks'' y _ _ _ C a (List.mem_of_getElem? hk)
  have hg' := (RunTrace.groupAt'_iff _ _ _ _ _ _ _).1 hg
  have hkk : kk < (Node.exec' proposer dg y (tr.state y j) (tr.time d)
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
      (l := (Node.exec' proposer dg y (tr.state y j) (tr.time d) (.tick x true)).2)
      (n := i - j) (by omega)
    rw [← Option.some.inj hl] at hmem
    exact tick_no_message' y _ _ x _ hmem m hm
  · exact Compose.before_tick' hrun.toLocalRun' hy
      ((RunTrace.tickAt'_iff _ _ _ _ _ _).2 ⟨x, true, hg⟩) hc hi ht

private theorem late_tick_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {t}, 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ jt, ∃ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y jt (.ac ℓ) ∧ ℓ.call = .tick ∧
      tr.time jt = t ∧ ∀ i W, tr.AcceptAt y i W → tr.time i = t → ¬ Node.Proposes proposer y t →
        jt < i := by
  intro y hy t ht0 hpub hw
  obtain ⟨jt, hj'⟩ := hrun.tick_of_awake y hy t ht0 hpub hw
  obtain ⟨x, fgDue, hgt⟩ := (RunTrace.tickAt'_iff _ _ _ _ _ _).1 hj'
  have hg := (RunTrace.groupAt'_iff _ _ _ _ _ _ _).1 hgt
  have hlen : 0 < (Node.exec' proposer dg y (tr.state y jt) t (.tick x fgDue)).2.length := by
    cases fgDue <;> simp [Node.exec'_eq, Node.onTick'_eq, Node.runSteps'_eq, Node.tickSteps,
      Node.tickStep'_eq, Node.acCall'_eq]
  obtain ⟨hn0, ht0', -, -, hl0⟩ := hg.2.1 0 hlen
  have hget : (Node.exec' proposer dg y (tr.state y jt) t (.tick x fgDue)).2[0]'hlen =
      .ac ⟨.tick, Node.frame' (tr.state y jt), ((goldilocksNode' sp ro).step y
        (tr.state y jt).ac (Node.frame' (tr.state y jt)) t .tick).2⟩ := by
    cases fgDue <;> simp [Node.exec'_eq, Node.onTick'_eq, Node.runSteps'_eq, Node.tickSteps,
      Node.tickStep'_eq, Node.acCall'_eq]
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0' hl0
  refine ⟨jt, _, ⟨hn0, hl0⟩, rfl, ht0', fun i W hA hit hnp => ?_⟩
  rcases Coherence.blockCall_cases' hrun.toLocalRun' hy hA with hgW |
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
  sorry

private theorem driven_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    Compose.NoCollRun dg tr → AC.Driven proposer tr.projAC H := by
  sorry

/-! ### The instances -/

/-- **The static core of a shadow Goldilocks run.** -/
theorem GoldilocksRun'.toStaticCore (hrun : GoldilocksRun' proposer dg H tr ini) :
    StaticRunCore Store.updateFinality' Node.frame' proposer dg H tr ini where
  finalitySpec := Store.finalitySpec_updateFinality'
  frameOf_F st := by rw [Node.frame'_eq]; exact Store.toFrame'_F _
  frameOf_tree st B := by rw [Node.frame'_eq, Store.toFrame'_tree]; exact Iff.rfl
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
  reachable y hy i := (Node.fg_reachable_at' hrun.toLocalRun' hy i).reachableWith
  frameOK y hy i := Compose.frameOK_state' hrun.toLocalRun' hy i
  projAC_state y hy i := Compose.projAC_state' hrun.toLocalRun' hy i
  acRun hnc := Compose.goldilocks_ac_projection_from' hrun hnc
  coherent hnc := Coherence.honest_blocks_coherent' hrun.toLocalRun' hnc
  tree_mono y hy _ _ hki := Coherence.tree_mono' hrun.toLocalRun' hy hki
  tree_accepted y hy _ _ hW := Coherence.tree_accepted' hrun.toLocalRun' hy hW
  hj_mono := hj_mono_pending hrun
  ac_block_after y hy _ _ ha := Healing.ac_block_after' hrun.toLocalRun' hy ha
  attest_source y hy _ _ _ hc := Coherence.attest_source' hrun.toLocalRun' hy hc
  report_attest := report_attest_pending hrun
  signed_tick := signed_tick_pending hrun
  late_tick := late_tick_pending hrun
  joined_at_call y hy i t hi hnr hit := Compose.joined_at_call' hrun hy i hi hnr hit
  signed_before_attest := signed_before_attest_pending hrun
  accept_of_proposesAt hnc _ _ _ hp hW := Coherence.accept_of_proposesAt' hrun hnc hp hW
  proposal_payload hp hW := by
    obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hW
    rcases Coherence.blockCall_cases' hrun.toLocalRun' hp hc with hg |
      ⟨j, x, fgDue, -, -, -, d, pay, -, hB, -, -, -, hfgj⟩
    · rw [RunTrace.groupAt'_iff] at hg
      exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
    · exact ⟨d.head, by rw [hB]; rfl, by rw [hfgj, hB]; rfl⟩
  driven := driven_pending hrun
  lock_origin hnc y hy i := Compose.lock_origin' hrun hnc hy i
  vote_of_awake_joined hnc y hy _ hmv hw hj := Compose.vote_of_awake_joined' hrun hnc hy hmv hw hj
  awake_participant_early hnc _ _ hsync hb _ hX _ _ hu y hy hmv hw hj :=
    Compose.awake_participant_early' hrun hnc hsync hb hX hu hy hmv hw hj

/-- **The core of a shadow Goldilocks run under growing faults.** -/
theorem Growing.GoldilocksRun'.toCore {H : Time → Set (Fin sp.n)}
    (hrun : Growing.GoldilocksRun' proposer dg H tr ini) :
    GoldilocksRunCore Store.updateFinality' Node.frame' proposer dg H tr ini where
  finalitySpec := Store.finalitySpec_updateFinality'
  frameOf_F st := by rw [Node.frame'_eq]; exact Store.toFrame'_F _
  frameOf_tree st B := by rw [Node.frame'_eq, Store.toFrame'_tree]; exact Iff.rfl
  antitone := hrun.antitone
  time_nonneg := hrun.time_nonneg
  time_mono := hrun.time_mono
  vstart := hrun.vstart
  upTo hd := (hrun.upTo hd).toStaticCore
  cutLaw y i c hc hy := (hrun.cutLaw y i c hc hy).with
  att_unforgeable := hrun.att_unforgeable
  awake_of_call := hrun.awake_of_call
  acRun hnc := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  coherent hnc := Coherence.honest_blocks_coherent_at' hrun hnc
  held_anc_at hnc := fun hd hy hi h hW => Coherence.held_anc_at' hrun hnc hd hy hi h hW
  F_mono_at := fun hd hy hi hki => hrun.toLocalRun'.finalized_mono_on_prefix' hd hy hki hi
  acRelayAt := fun hx hacc hy hc hanc relay => hrun.toLocalRun'.acRelayAt' hx hacc hy hc hanc relay
  acCatchAt hcatch := fun hx ha hi hy hc hj hanc =>
    hrun.toLocalRun'.acCatchAt' hcatch hx ha hi hy hc hj hanc

end Consensus.Goldilocks

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace' sp ro} {H : Time → Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {g ΔF a b hold : Time} {committee : Time → Finset (Fin sp.n)} {beta : ℚ}

/-- **The core of the shadow finite-reset premises.** -/
theorem ResetPremisesUpTo'.toCore
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b committee beta hold) :
    ResetRunCore tr H Store.updateFinality' Node.frame' proposer dg g ΔF a b committee beta hold
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
