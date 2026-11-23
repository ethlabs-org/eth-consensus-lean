module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: `Carry` vote by vote, and frame-tree membership

`Carry_y` for a set of votes is `Carry_y` for each of them (`carryAt_of_each`), and a block
between `Φ.F` and a block of a well-formed frame tree is in the tree (`mem_tree_of_between`). -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {g t₀ : Time} {proposer : Nat → Fin sp.n}

/-- `Carry_y` for a set of votes is `Carry_y` for each of them (the fields are per vote), at a
vote where `y` is awake and joined. -/
theorem carryAt_of_each {y : Fin sp.n} {i : Nat} {e : Em sp FGP} {s : Nat}
    {CV : Set (Vote sp.n)} (ha : tr.awake y (tr.time i)) (hj : joined sp e.readPoint (tr.time i))
    (h : ∀ v ∈ CV, CarryAt tr U y i e s {v}) : CarryAt tr U y i e s CV :=
  ⟨ha, hj, fun v hv => (h v hv).heads v rfl, fun v hv => (h v hv).holds v rfl⟩

/-- A block between `Φ.F` and a block of a well-formed frame tree (inside a coherent `U`
containing the tree) is in the tree. -/
theorem mem_tree_of_between {Φ : Frm sp.n FGP} (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {B C : Blk sp.n FGP} (hFB : Anc U Φ.F B) (h : Anc U B C) :
    C ∈ Φ.tree → B ∈ Φ.tree := by
  induction h with
  | refl => exact id
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = Φ.F
    · subst hdF
      obtain rfl := Anc.antisymm hU (hBc.tail e) hFB
      exact hd
    obtain rfl | ⟨q, -, hq⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    have hqc : q = c := hU.1 (hΦU hq.1) e.1 (Option.some_injective _ (hq.2.2.symm.trans e.2.2))
    subst hqc
    exact ih hq.1

end Consensus.Goldilocks.AC

end
