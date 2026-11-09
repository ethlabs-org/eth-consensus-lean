module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the start of a post-drain proposal

A proposal's walk starts at its unlocked anchor: the fork-choice root, or the viable ancestor of
a live lock after unlocking. Locks only move back, so such a lock lies below a stored lock of the
proposer; live at the proposal slot `u` after the drain, its label is at least
`cleanLabel + k + 2` (`proposal_start_root_or_clean_lock`). A frame fact: the run supplies the
well-formedness of the stored locks. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams}

/-- **The start of a post-drain proposal** is its fork-choice root, or extends to the block of a
stored lock of label at least `cleanLabel + k + 2`. -/
theorem proposal_start_root_or_clean_lock {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    (hΦ : FrameOK Φ) {A : SA.SAState sp.n} (hwf : SA.LocksWF sp A.locks) {a t : Time} {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) (ht : t = sp.ts u)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    d.start = Φ.fcRoot ∨ ∃ l ∈ A.locks, cleanLabel sp a + sp.k + 2 ≤ l.slot ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc d.start B := by
  obtain ⟨A₁, hA₁, hstart, _⟩ := Compose.acProposal_walk hd
  rw [hstart]
  rcases Compose.anchor_mem Φ A₁ t with hlock | hroot
  swap
  · exact Or.inl (Set.mem_singleton_iff.1 hroot)
  obtain ⟨hL, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hlL⟩ := hlock
  rw [hΦ.coherent.1 hL (SA.viableAncestor_anc hΦ hB).1 hlL.symm]
  rw [hA₁] at hl
  replace hlive : sp.slot t ≤ l.slot + sp.k := hlive.trans ((hwf.unlock _ _ _ _).cap hl)
  obtain ⟨l₁, hl₁, hs, _, _, B₁, hB₁, hB₁r, B', hB', hB'r, hBB₁⟩ :=
    ((SA.locks_move_back sp) _ Φ _ t hΦ).2.2 _ _ l hl
  obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
  refine Or.inr ⟨l₁, hl₁, ?_, B₁, hB₁, hB₁r, (SA.anc_viableAncestor Φ B').trans hBB₁⟩
  rw [drainTime_eq] at hR
  have h := (SA.ts_le_iff sp).mp hR
  have hslot : sp.slot t = u := by
    rw [ht]
    exact SA.slot_of_mem sp u le_rfl (by
      have hΔ := sp.toParams.hΔ
      simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ])
  rw [hslot] at hlive
  rw [cleanLabel_eq]
  clear * - hlive hs h; omega

end Consensus.Goldilocks.Healing

end
