module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNext
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Compatibility with a unanimous proposal through its update deadline -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- Older origins lie below the proposal; only next-slot optimistic writes can be later. -/
theorem high_origin_compatible_before_update_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat}
    {P B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {r m : Nat} (ho : HighOrigin tr H g x r m B)
    (ht : tr.time r ≤ sp.ts u + 6 * sp.Δ) : Compatible (tr.HonestBlocksAt H) B P := by
  have hub : sp.ts u + sp.Δ ≤ b := by linarith [sp.toParams.hΔ]
  have hrb := ht.trans hTb
  by_cases ht' : tr.time r < sp.ts (u + 1 : Nat)
  · exact Or.inl (high_origins_before_next_slot_below_at hp hP hun hgu hR hub ho ht' hrb)
  obtain ⟨CV, ell, D, hcall, hfl, hB⟩ := ho.2.2.1
  have hx := hp.run.antitone (le_max_right _ _) ho.1
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hc'.2)
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  obtain ⟨hPhi, hsub⟩ : FrameOK ell.frame ∧ ell.frame.tree ⊆ tr.HonestBlocksAt H := by
    rcases hac.localRun.frameLaw x r ell hx hcall with
      ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.1
  have hBD := (AC.anc_viableAncestor ell.frame D).mono hsub
  rw [← hB] at hBD
  have hDP : Compatible (tr.HonestBlocksAt H) D P := by
    rcases hfl with ⟨ellr, C, hupd, _⟩ | hop
    · have htime : tr.time r = sp.ts m + 6 * sp.Δ := hupd.2.2.1
      have hmu : m ≤ u := by
        have hle : sp.ts m ≤ sp.ts u := by linarith
        have := (AC.ts_le_iff sp).1 hle
        omega
      by_cases heq : m = u
      · subst m
        exact Or.inl (hp.same_slot_source_below_unanimous_at hx
          (Or.inl ⟨CV, Or.inl ⟨ellr, C, hupd, by assumption⟩⟩) hrb
          (hp.cutZ_le_ts_of_highOrigin_at ho) hP hun)
      have hm : m < u := by omega
      have hbefore : tr.time r < sp.ts (u + 1 : Nat) := by
        simp only [ACParams.ts] at htime ⊢
        push_cast at htime ⊢
        have hmu : (m : Time) + 1 ≤ u := by exact_mod_cast hm
        have h4 : (0 : Time) ≤ 4 * sp.Δ := by linarith [sp.toParams.hΔ]
        linarith [sp.toParams.hΔ, mul_le_mul_of_nonneg_left hmu h4]
      exact False.elim (ht' hbefore)
    · have hs : sp.slot (tr.time r) = m := hop.choose_spec.choose_spec.2.1
      have hdeadline : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
        AC.slot_of_mem sp (u + 1)
          (by simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
          (by simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
      have hm := AC.slot_mono sp (hp.run.time_nonneg r) ht
      rw [hs, hdeadline] at hm
      have hml : u + 1 ≤ m := by
        have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r)
          ((u + 1 : Nat) : Int)).1 (not_lt.mp ht')
        omega
      have heq : m = u + 1 := by omega
      exact unanimous_next_optimistic_compatible_at hp hP hslot hu hun hgu hR hub
        hx (heq ▸ hop) hrb
  rcases hDP with h | h
  · exact Or.inl (hBD.trans h)
  · exact AC.anc_total (Compose.Growing.honest_blocks_coherent hp.run hp.noColl) hBD h

/-- A finalized cache after the reset is below a bounded origin compatible with the proposal. -/
theorem finalized_compatible_before_update_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (ha : a ≤ tr.time k)
    (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F P := by
  rcases ProposalImpl.finalized_below_high_origin_or_covered_at hp hy ha (ht.trans hTb) with
    ⟨x, r, m, B, ho, hrk, _, hFB⟩ | hcov
  swap
  · obtain ⟨hc, C, s, hC, hsk, hFC⟩ := coveredUpTo_iff.1 hcov
    have hdeadline : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
      AC.slot_of_mem sp (u + 1)
        (by simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
        (by simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
    have hsu := hsk.trans (AC.slot_mono sp (hp.run.time_nonneg k) ht)
    rw [hdeadline] at hsu
    rcases healed_member_compatible_before_update_at hp hc hP hslot hu hun hgu hR hTb
        C s hC hsu with hCP | hPC
    · exact Or.inl (hFC.trans hCP)
    · exact AC.anc_total (Compose.Growing.honest_blocks_coherent hp.run hp.noColl) hFC hPC
  rcases high_origin_compatible_before_update_at hp hP hslot hu hun hgu hR hTb ho
      (hrk.trans ht) with h | h
  · exact Or.inl (hFB.trans h)
  · exact AC.anc_total (Compose.Growing.honest_blocks_coherent hp.run hp.noColl) hFB h

end Consensus.Goldilocks.Healing.Growing

end
