module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Confirmation

public section

/-! # Goldilocks SA: lock expiry facts

The write-side bounds of a new fast lock's expiry, `s + 2 ≤ fastExpiry ≤ s + k`, on every lock
set (no run invariant), and the reading of `Lock.LiveAt`. A slow lock and a slow-qualified
update's fast lock get `s + k`, so every written lock of slot `s` has an expiry in
`[s + 2, s + k]`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} (sp : SAParams)

/-- A lock is live at `t` exactly when `slot(t)` is at most its expiry. -/
theorem Lock.liveAt_iff (l : Lock) (t : Time) : l.LiveAt sp t ↔ sp.slot t ≤ l.expiry :=
  Iff.rfl

/-- A new fast lock of slot `s` lives at least through `s + 2`. -/
theorem le_fastExpiry (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    s + 2 ≤ fastExpiry sp L Φ t s := by
  have := sp.two_le_k
  unfold fastExpiry
  dsimp only
  split_ifs <;> omega

/-- A new fast lock of slot `s` lives at most through `s + k`. -/
theorem fastExpiry_le (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    fastExpiry sp L Φ t s ≤ s + sp.k := by
  unfold fastExpiry
  exact min_le_left _ _

end Consensus.Goldilocks.SA

end
