module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FrameStatements
public import Mathlib.Tactic.IntervalCases
@[expose] public section

/-! # The FG frames of the one-validator tick run meet the premise of the frame statements

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), on the one-validator tick run of
`Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `Δ = 1`, `t_s = 4s`, a tick at every time, no
restart): `FrameSeqIn`, the premise of `FrameRetention`, `FrameNeverReturns` and
`FrameEntersOnce` (all in `Lemmas/AC/FrameClaims.lean`), holds for the validator's FG frames
given to its AC, indexed by cut (`runFrame i`, `fg_to_ac(Σ)` of its state before cut `i`),
inside the run's honest blocks (the blocks of its accepted trees).

* `runFrame_seq`: at every cut the frame stays or takes one frame step. An AC cut, a refused
  block and an `fg_attest` cut leave `Σ` unchanged; `fg_on_attestation` writes only the pool,
  which the frame does not read; an accepted block is a frame step (`Store.accept_is_frame_step`).
  So `fc_root` and `viable_heads` move only at accepted blocks, where `FrameStep` leaves them
  free.
* `runFrame_rooted` (every frame is well formed, `runFrame_ok`), `runFrame_subset` and
  `honestBlocks_coherent` (`NoColl`), bundled in `tickRun_frameSeqIn`.
* Non-vacuity (`tickRun_frameSeq_steps`): the frame before cut `34` has the tree `{genesis}`, and
  the acceptance of the own block `blk 1` at cut `34` (`t_1 = 4`) is a frame step to the tree
  `{genesis, blk 1}`.
* The frame statements on the run (`frame_statements`): retention, never returns and enters once
  for the sequence (`runFrame_retention`, `runFrame_neverReturns`, `runFrame_entersOnce`; `blk 1`
  enters at cut `34` only, `blk1_enters_once`), and, from `runFrame_ok`, the viable ancestor and
  parent closure of every frame (`runFrame_viableAncestor`, `runFrame_parentClosed`).

Limitations: with `n = 1` and `f = 0` this shows the premises consistent on a real run, not met
with faults, competing blocks or a contest; the tree only grows along one chain. -/

namespace Consensus.Goldilocks.Witness.One

open Node ChainFrame

/-- The validator's FG frame before cut `i` of the tick run: `fg_to_ac(Σ)` of its state. -/
noncomputable def runFrame (i : Nat) : N1.Frm := Node.frame ((tickRun N1 dg1).state v0 i)

theorem runFrame_eq (i : Nat) : runFrame i = ((tickRun N1 dg1).state v0 i).fg.toFrame := rfl

/-- Every FG state of the run is reachable. -/
theorem state_fg_reachable (i : Nat) :
    ((tickRun N1 dg1).state v0 i).fg.Reachable N1.genesisPayload :=
  Compose.fg_reachable tickRun_goldilocksRun.toLocalRun (Set.mem_univ v0) i

/-- Every frame of the run is well formed. -/
theorem runFrame_ok (i : Nat) : FrameOK (runFrame i) :=
  (Store.frame_realization _ _ _ _ (state_fg_reachable i)).1

/-! ## The premise -/

/-- **The frames of the run evolve by steps.** -/
theorem runFrame_seq : FrameSeq runFrame := frameSeq_iff.mpr fun i => by
  have hk := Store.accept_is_frame_step _ _ _ _ (state_fg_reachable i)
  rcases Healing.fg_step tickRun_goldilocksRun.toLocalRun (Set.mem_univ v0) i with
    he | ⟨B, -, hB⟩ | ⟨a, -, he⟩
  · exact Or.inl (by rw [runFrame_eq, runFrame_eq, he])
  · exact Or.inr ⟨B, hk.1 B _ hB⟩
  · exact Or.inl (by rw [runFrame_eq, runFrame_eq, he, hk.2 a])

/-- The first frame is rooted. -/
theorem runFrame_rooted : (runFrame 0).Rooted := (runFrame_ok 0).rooted

/-- Every frame's tree lies in the honest blocks. -/
theorem runFrame_subset (i : Nat) :
    (runFrame i).tree ⊆ (tickRun N1 dg1).HonestBlocks Set.univ :=
  fun _ hB => ⟨v0, Set.mem_univ _, i, hB.1⟩

/-- The honest blocks of the run are coherent. -/
theorem honestBlocks_coherent : Coherent ((tickRun N1 dg1).HonestBlocks Set.univ) :=
  Compose.honest_blocks_coherent tickRun_goldilocksRun.toLocalRun (dg1_noColl _)

/-- **`FrameSeqIn` on the tick run**: the validator's frames inside the honest blocks. -/
theorem tickRun_frameSeqIn :
    FrameSeqIn runFrame ((tickRun N1 dg1).HonestBlocks Set.univ) :=
  ⟨runFrame_seq, runFrame_rooted, runFrame_subset, honestBlocks_coherent⟩

/-! ## Non-vacuity -/

/-- The acceptance of `blk 1` at cut `34` (the own block of slot `1`) is a frame step. -/
theorem runFrame_step_34 : FrameStep (runFrame 34) (blk 1) (runFrame 35) := by
  have hc : (tickRun N1 dg1).CallAt v0 34 (.fg (.block (blk 1) true)) := ⟨rfl, blk_label 0⟩
  have hB := (tickRun_goldilocksRun.toLocalRun.cutLaw v0 (Set.mem_univ _) 34 _ hc).2.1
  rw [← Trace.state_succ_of_call _ hc] at hB
  exact (Store.accept_is_frame_step _ _ _ _ (state_fg_reachable 34)).1 _ _ hB

/-- The tree of a frame of the run: the chain blocks from `Σ.F` up to the state's tip. -/
theorem runFrame_tree_iff {i f : Nat} (hF : ((tickRun N1 dg1).state v0 i).fg.F = blk f)
    (B : N1.Blk) : B ∈ (runFrame i).tree ↔ ∃ m, f ≤ m ∧ m ≤ stTip i ∧ B = blk m := by
  obtain ⟨f', hf'⟩ := fgGood_frame (state_fgGood i)
  have hff : f = f' := blk_inj (hF.symm.trans hf'.F)
  subst hff
  exact hf'.tree B

/-- The frame before cut `34` has the tree `{genesis}`. -/
theorem runFrame_tree_34 : (runFrame 34).tree = {blk 0} := by
  obtain ⟨f, hf, hF⟩ := (state_fgGood 34).F
  have h1 : stTip 34 = 0 := by decide
  rw [h1, show jexp 0 = 0 by decide, Nat.le_zero] at hf
  subst hf
  ext B
  rw [runFrame_tree_iff hF, h1, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, -, hm, rfl⟩
    rw [Nat.le_zero.1 hm]
  · rintro rfl
    exact ⟨0, le_rfl, le_rfl, rfl⟩

/-- The frame before cut `35` has the tree `{genesis, blk 1}`. -/
theorem runFrame_tree_35 : (runFrame 35).tree = {blk 0, blk 1} := by
  obtain ⟨f, hf, hF⟩ := (state_fgGood 35).F
  have h1 : stTip 35 = 1 := by decide
  rw [h1, show jexp 1 = 0 by decide, Nat.le_zero] at hf
  subst hf
  ext B
  rw [runFrame_tree_iff hF, h1, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, -, hm, rfl⟩
    interval_cases m
    exacts [Or.inl rfl, Or.inr rfl]
  · rintro (rfl | rfl)
    exacts [⟨0, le_rfl, zero_le_one, rfl⟩, ⟨1, zero_le_one, le_rfl, rfl⟩]

/-- **The sequence steps**: at cut `34` the frame takes the step of `blk 1`, from the tree
`{genesis}` to the two-block tree `{genesis, blk 1}`. -/
theorem tickRun_frameSeq_steps :
    FrameStep (runFrame 34) (blk 1) (runFrame 35) ∧ (runFrame 34).tree = {blk 0} ∧
      (runFrame 35).tree = {blk 0, blk 1} ∧ blk 0 ≠ blk 1 :=
  ⟨runFrame_step_34, runFrame_tree_34, runFrame_tree_35, fun h => absurd (blk_inj h) (by decide)⟩

/-! ## The frame statements on the run -/

/-- **G0.3 (frame), retention, on the run.** -/
theorem runFrame_retention {i j : Nat} (hij : i ≤ j) {X : N1.Blk} (hX : X ∈ (runFrame i).tree)
    (hF : Anc ((tickRun N1 dg1).HonestBlocks Set.univ) (runFrame j).F X) :
    X ∈ (runFrame j).tree :=
  frameRetention_iff.mp frame_statements.retention _ _ _ _ _ tickRun_frameSeqIn i j hij X hX hF

/-- **G0.3 (frame), a block that leaves the tree never returns, on the run.** -/
theorem runFrame_neverReturns {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) {X : N1.Blk}
    (hX : X ∈ (runFrame i).tree) (hXj : X ∉ (runFrame j).tree) : X ∉ (runFrame k).tree :=
  frameNeverReturns_iff.mp frame_statements.neverReturns
    _ _ _ _ _ tickRun_frameSeqIn i j k hij hjk X hX hXj

/-- **G0.3 (frame), each block enters at most once, on the run.** -/
theorem runFrame_entersOnce {i j : Nat} {B : N1.Blk}
    (hi : FrameStep (runFrame i) B (runFrame (i + 1)))
    (hj : FrameStep (runFrame j) B (runFrame (j + 1))) : i = j :=
  frameEntersOnce_iff.mp frame_statements.entersOnce _ _ _ _ _ tickRun_frameSeqIn i j B hi hj

/-- `blk 1` enters the validator's frame at cut `34` and at no other cut. -/
theorem blk1_enters_once {j : Nat} (hj : FrameStep (runFrame j) (blk 1) (runFrame (j + 1))) :
    j = 34 :=
  (runFrame_entersOnce runFrame_step_34 hj).symm

/-- **G0.4 (frame), `viable_ancestor` exists, on the run's frames.** -/
theorem runFrame_viableAncestor (i : Nat) {B : N1.Blk} (hB : B ∈ (runFrame i).tree) :
    (runFrame i).IsViableAncestor B ((runFrame i).viableAncestor B) ∧
      ∀ A, (runFrame i).IsViableAncestor B A → A = (runFrame i).viableAncestor B :=
  viableAncestorExists_iff.mp frame_statements.viableAncestorExists _ _ _ _ _ (runFrame_ok i) hB

/-- **G0.4 (frame), parent-closed down to `Φ.F`, on the run's frames.** -/
theorem runFrame_parentClosed (i : Nat) {C : N1.Blk} (hC : C ∈ (runFrame i).tree)
    (hne : C ≠ (runFrame i).F) :
    ∃ P ∈ (runFrame i).tree, C.parent = some P.root ∧ P.slot < C.slot :=
  frameParentClosed_iff.mp frame_statements.parentClosed _ _ _ _ _ (runFrame_ok i) hC hne

end Consensus.Goldilocks.Witness.One

end
