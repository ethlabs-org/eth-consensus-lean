module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: `Carry` vote by vote, and frame-tree membership

`Carry_y` for a set of votes is `Carry_y` for each of them (`carryAt_of_each`). -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP} {g t₀ : Time} {proposer : Nat → Fin sp.n}

/-- `Carry_y` for a set of votes is `Carry_y` for each of them (the fields are per vote), at a
vote where `y` is awake and joined. -/
theorem carryAt_of_each {y : Fin sp.n} {i : Nat} {e : Em sp FGP} {s : Nat}
    {CV : Set (Vote sp.n)} (ha : tr.awake y (tr.time i)) (hj : joined sp e.readPoint (tr.time i))
    (h : ∀ v ∈ CV, CarryAt tr U y i e s {v}) : CarryAt tr U y i e s CV :=
  ⟨ha, hj, fun v hv => (h v hv).heads v rfl, fun v hv => (h v hv).holds v rfl⟩

end Consensus.Goldilocks.AC

end
