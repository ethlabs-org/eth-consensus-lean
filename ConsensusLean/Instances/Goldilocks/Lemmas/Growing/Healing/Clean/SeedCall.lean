module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SeedRelay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # One reset seed held at every later independently honest call -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A bounded high seed is held at every later honest call above its finalized tip. -/
theorem ResetPremisesUpTo.reset_seed_held_at_call_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) :
    ∃ v r l S, HighOrigin tr H g v r l S ∧ tr.time r ≤ a ∧ tr.time r ≤ b ∧
      ∀ y c (ell : ACLabel (goldilocksNode sp ro)), y ∈ H (tr.time c) →
        tr.projAC.CallAt y c ell → a + sp.Δ ≤ tr.time c → tr.time c ≤ b →
        Anc (tr.HonestBlocksAt H) ell.frame.F S → S ∈ ell.frame.tree := by
  obtain ⟨v, r, l, S, hS, hra, _⟩ := hp.reset_seed_at
  refine ⟨v, r, l, S, hS, hra, hra.trans hp.reset_le, ?_⟩
  intro y c ell hy hcall hac hcb hF
  have hv := hp.run.antitone (le_max_right _ _) hS.1
  obtain ⟨CV, ellS, D, hcallS, hfl, hSD⟩ := hS.2.2.1
  obtain ⟨ellS', hcallS', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ellS = ellS' := Option.some.inj (hcallS.2.symm.trans hcallS'.2)
  have hSm : S ∈ ellS.frame.tree := by
    rw [hSD]
    exact (AC.viableAncestor_anc (frame_tree_subset_at hp.run hp.noColl hv hcallS).1 hD).1
  have hcut := hp.cutZ_lt_reset_at
  have hnext : AC.gbar g < sp.ts (sp.slot (AC.gbar g) + 1 : Nat) := by
    exact not_le.mp ((AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g)
      ((sp.slot (AC.gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega))
  rw [Healing.cutZ_eq] at hcut
  have hΔ := sp.toParams.hΔ
  apply hp.reset_frame_relay_at hv hy hcallS hcall hSm hcb ?_ ?_ (by linarith) hF
  · simp only [ACParams.ts] at hcut hnext
    push_cast at hcut hnext
    linarith
  · simp only [ACParams.ts] at hcut ⊢
    push_cast at hcut ⊢
    linarith

end Consensus.Goldilocks.Healing.Growing

end
