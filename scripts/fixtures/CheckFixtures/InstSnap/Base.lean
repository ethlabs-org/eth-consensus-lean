module

@[expose] public section

/-! Fixture of check.sh step 4's drift verdict (the protected-surface snapshot). `Base` is the baseline,
`Same` a copy, `Proof` changes only a theorem's proof (to a tactic proof with an auxiliary lemma), `Body` a
definition body (same type, as a changed `tryVote`), `DefProof` the value of a definition whose proof is
abstracted into an auxiliary `_proof_1` (whose statement changes with it). `w_val`'s statement names its own
auxiliary proof, which the snapshot keeps. -/

namespace InstSnap

def dom (n : Nat) : Nat := n + 1

theorem dom_pos (n : Nat) : 0 < dom n := Nat.succ_pos _

def w : Fin 3 := ⟨2, by omega⟩

theorem w_val : (⟨4, by omega⟩ : Fin 5).val = 4 := rfl

end InstSnap
