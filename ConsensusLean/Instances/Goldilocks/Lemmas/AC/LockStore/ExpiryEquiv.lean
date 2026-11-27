module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor

public section

namespace Consensus.Goldilocks.AC.BeforeHighest

variable {sp : ACParams} {FGP : Type}

open Classical in
/-- Fast expiry before removal of the inner floor. -/
noncomputable def expiry (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) : Nat :=
  let E := {e | ∃ l ∈ liveLocks sp L Φ t, l.fast = true ∧ l.slot < s ∧ e = l.expiry}
  min (s + sp.k) (if E.Nonempty then max (s + 2) (sSup E + sp.c) else s + 2)

/-- On a capped lock set at a legal write slot, the inner floor does not change the expiry. -/
theorem expiry_eq {L : Set Lock} {Φ : Frm sp.n FGP} {t : Time} {s : Nat}
    (hcap : ∀ l ∈ L, l.expiry ≤ l.slot + sp.k) (hs : s ≤ sp.slot t) :
    expiry L Φ t s = fastExpiry sp L Φ t s := by
  have hf := le_fastExpiry sp L Φ t s hcap hs
  unfold expiry fastExpiry at *
  dsimp only at *
  split_ifs at hf ⊢
  · rw [max_eq_right (hf.trans (min_le_right _ _))]
  · rfl

end Consensus.Goldilocks.AC.BeforeHighest

end
