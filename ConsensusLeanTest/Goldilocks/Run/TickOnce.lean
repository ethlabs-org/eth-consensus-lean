module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.TickOnce

@[expose] public section

/-! # One AC tick per honest node and time on runs: pin

`acTick_unique` (`Lemmas/Compose/Run/TickOnce`) is pinned by a named theorem restating its
statement in full, so a change of its hypotheses or conclusion fails here, and by its axioms. -/

namespace Consensus.Goldilocks.Compose.Test

open Node

/-- `acTick_unique`, restated: in the AC trace of a run, two AC tick calls of an honest node at
one time are one cut. -/
theorem pinAcTickUnique {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
    {tr : RunTrace A} (h : Node.LocalRun proposer dg H sg tr) :
    ∀ y ∈ H, ∀ i j (ℓ ℓ' : ACLabel A), tr.projAC.CallAt y i ℓ → tr.projAC.CallAt y j ℓ' →
      ℓ.call = .tick → ℓ'.call = .tick → tr.projAC.time i = tr.projAC.time j → i = j :=
  acTick_unique h

end Consensus.Goldilocks.Compose.Test

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned message is longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.Compose.Test.pinAcTickUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.Test.pinAcTickUnique

end
