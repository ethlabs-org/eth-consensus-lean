module
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Compose.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Growing Compose milestone contracts and axiom pins

Also the constant-honest-set control of the always rows: the static R.7 and R.8 rows over a
fixed honest set `H` (retired as statements) follow from `Regimes.Growing.always_statements` at
`H := fun _ => H`. A static `GoldilocksRun` is a growing one there (`goldilocksRun_const`, from
`Growing.LocalRun.const_iff`), and the blocks held while honest are among the honest blocks
(`honestBlocksAt_const_subset`), so compatibility inside the former gives it inside the latter.
-/

namespace Consensus.Goldilocks.Compose.Growing.Test

/-- Every run projection is proved without unfinished dependencies. -/
theorem run_contract : RunStatements := run_statements

/-- The six always rows discharge the authoritative growing contracts. -/
theorem always_contract : Regimes.Growing.AlwaysStatements := Regimes.Growing.always_statements

set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.Compose.Growing.Test.run_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_contract

/-- info: 'Consensus.Goldilocks.Compose.Growing.Test.always_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms always_contract

end Consensus.Goldilocks.Compose.Growing.Test

namespace Consensus.Goldilocks.Regimes.Growing.Test

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A Goldilocks run over the fixed honest set `H` is a growing-fault run at `fun _ => H`. -/
theorem goldilocksRun_const (h : Consensus.Goldilocks.GoldilocksRun proposer dg H tr) :
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg (fun _ => H) tr :=
  { toLocalRun := Consensus.Goldilocks.Growing.LocalRun.const_iff.2 h.toLocalRun
    genesis_root_ok := h.genesis_root_ok
    vstart := h.vstart }

/-- The blocks held while honest at the constant honest set are honest blocks. -/
theorem honestBlocksAt_const_subset : tr.HonestBlocksAt (fun _ => H) ⊆ tr.HonestBlocks H := by
  rintro B ⟨y, i, t, -, -, hy, hB⟩
  exact ⟨y, hy, i, hB⟩

/-- Compatibility inside the blocks held while honest is compatibility among the honest blocks. -/
theorem compatible_of_const {B C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Compatible (tr.HonestBlocksAt (fun _ => H)) B C) : Compatible (tr.HonestBlocks H) B C :=
  h.imp (Anc.mono honestBlocksAt_const_subset) (Anc.mono honestBlocksAt_const_subset)

/-- R.8 `nested` over a fixed honest set, from the growing row. -/
theorem outputsNested_const (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.Anc (tr.finalizedAt y i) (tr.confirmedAt y i) ∧
      (tr.state y i).fg.Anc (tr.confirmedAt y i) (tr.headAt y i) :=
  always_statements.outputsNested sp ro dg _ tr proposer (goldilocksRun_const hrun) y i hy

/-- R.8 `finalMonotone` over a fixed honest set, from the growing row. -/
theorem finalizedMonotone_const (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j) :
    (tr.state y j).fg.Anc (tr.finalizedAt y i) (tr.finalizedAt y j) :=
  always_statements.finalizedMonotone sp ro dg _ tr proposer (goldilocksRun_const hrun) y i j hij
    hy

/-- R.8 `outputValid` over a fixed honest set, from the growing row. -/
theorem outputsValid_const (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ValidOutput tr proposer dg y i (tr.finalizedAt y i) ∧
      ValidOutput tr proposer dg y i (tr.confirmedAt y i) :=
  always_statements.outputsValid sp ro dg _ tr proposer (goldilocksRun_const hrun) y i hy

/-- R.7 `finalAccountable` over a fixed honest set, from the growing row. -/
theorem finalAccountable_const (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) (i j : Nat)
    (hne : ¬ Compatible (tr.HonestBlocks H) (tr.finalizedAt y i) (tr.finalizedAt z j)) :
    ∃ X₁ ∈ (tr.state y i).fg.tree, ∃ X₂ ∈ (tr.state z j).fg.tree,
      ∃ S : Finset (Fin sp.n), 2 * sp.toParams.q - sp.n ≤ S.card ∧
        ∀ v ∈ S, ∃ a ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂,
          ∃ b ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂, a.val = v ∧ FG.slashable a b :=
  always_statements.finalAccountable sp ro dg _ tr proposer (goldilocksRun_const hrun) hnc
    y z i j hy hz fun h => hne (compatible_of_const h)

/-- R.7 `nonFraming` over a fixed honest set, from the growing row. -/
theorem nonFraming_const (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr)
    {v : Fin sp.n} (hv : v ∈ H) {k k' : Nat} {a b : FG.Att sp.n} (ha : tr.SignAt v k a)
    (hb : tr.SignAt v k' b) : ¬ FG.slashable a b :=
  always_statements.nonFraming sp ro dg _ tr proposer (goldilocksRun_const hrun) v k k' a b
    ha hb hv

/-- R.7 `finalized_safe_below_third` over a fixed honest set, from the growing row. -/
theorem finalizedSafe_const (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) (i j : Nat) :
    Compatible (tr.HonestBlocks H) (tr.finalizedAt y i) (tr.finalizedAt z j) :=
  compatible_of_const (always_statements.finalizedSafe sp ro dg _ tr proposer
    (goldilocksRun_const hrun) hnc y z i j hy hz hf)

end Consensus.Goldilocks.Regimes.Growing.Test

end
