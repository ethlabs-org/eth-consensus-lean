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
types of the fields whose shadow proofs are still being written: `hj_mono`, `report_attest`,
`signed_tick`, `late_tick`, `signed_before_attest` (copies over `exec'`), and `driven` (lane W's
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

/-! ### Pending fields (placeholders with the fields' exact types) -/

private theorem hj_mono_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {i j}, i ≤ j → (tr.state y i).fg.hj ≤ (tr.state y j).fg.hj := by
  sorry

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
  sorry

private theorem late_tick_pending (hrun : GoldilocksRun' proposer dg H tr ini) :
    ∀ y ∈ H, ∀ {t}, 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ jt, ∃ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y jt (.ac ℓ) ∧ ℓ.call = .tick ∧
      tr.time jt = t ∧ ∀ i W, tr.AcceptAt y i W → tr.time i = t → ¬ Node.Proposes proposer y t →
        jt < i := by
  sorry

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
