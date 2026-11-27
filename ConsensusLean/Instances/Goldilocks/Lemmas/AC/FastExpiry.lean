module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Confirmation

public section

/-! # Goldilocks AC: lock expiry facts

The write-side bounds of a new fast lock's expiry: the cap is unconditional, while the floor
needs capped stored expiries and a legal write slot. Liveness needs only capped stored expiries
and `slot(t) ≤ s + 2`. -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} (sp : ACParams)

/-- A legal fast-lock write with capped stored expiries lives through `s + 2`. -/
theorem le_fastExpiry (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat)
    (hcap : ∀ l ∈ L, l.expiry ≤ l.slot + sp.k) (hs : s ≤ sp.slot t) :
    s + 2 ≤ fastExpiry sp L Φ t s := by
  classical
  have hk := sp.two_le_k
  have hc := sp.two_le_c
  unfold fastExpiry
  dsimp only
  split_ifs with hE
  · obtain ⟨e, l, ⟨l₀, hl₀, B, hB, hroot, hlive, rfl⟩, hf, hslot, rfl⟩ := hE
    have hb : BddAbove {e | ∃ l ∈ liveLocks sp L Φ t,
        l.fast = true ∧ l.slot < s ∧ e = l.expiry} := by
      refine ⟨s + sp.k, ?_⟩
      rintro e ⟨l, ⟨l₁, hl₁, B₁, hB₁, hr₁, ht₁, rfl⟩, hf₁, hs₁, rfl⟩
      have := hcap l₁ hl₁
      dsimp only at hs₁ ⊢
      omega
    have he := le_csSup hb ⟨_, ⟨l₀, hl₀, B, hB, hroot, hlive, rfl⟩, hf, hslot, rfl⟩
    dsimp only at he
    dsimp only [Lock.LiveAt] at hlive
    exact le_min (by omega) (by omega)
  · exact le_min (by omega) le_rfl

/-- A fresh enough fast-lock write remains live, even without a legal-write-slot premise. -/
theorem slot_le_fastExpiry (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat)
    (hcap : ∀ l ∈ L, l.expiry ≤ l.slot + sp.k) (h2 : sp.slot t ≤ s + 2) :
    sp.slot t ≤ fastExpiry sp L Φ t s := by
  classical
  have hk := sp.two_le_k
  unfold fastExpiry
  dsimp only
  split_ifs with hE
  · obtain ⟨e, l, ⟨l₀, hl₀, B, hB, hroot, hlive, rfl⟩, hf, hslot, rfl⟩ := hE
    have hb : BddAbove {e | ∃ l ∈ liveLocks sp L Φ t,
        l.fast = true ∧ l.slot < s ∧ e = l.expiry} := by
      refine ⟨s + sp.k, ?_⟩
      rintro e ⟨l, ⟨l₁, hl₁, B₁, hB₁, hr₁, ht₁, rfl⟩, hf₁, hs₁, rfl⟩
      have := hcap l₁ hl₁
      dsimp only at hs₁ ⊢
      omega
    have he := le_csSup hb ⟨_, ⟨l₀, hl₀, B, hB, hroot, hlive, rfl⟩, hf, hslot, rfl⟩
    dsimp only at he
    dsimp only [Lock.LiveAt] at hlive
    exact le_min (by omega) (by omega)
  · exact le_min (by omega) h2

/-- A new fast lock of slot `s` lives at most through `s + k`. -/
theorem fastExpiry_le (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    fastExpiry sp L Φ t s ≤ s + sp.k := by
  unfold fastExpiry
  exact min_le_left _ _

end Consensus.Goldilocks.AC

end
