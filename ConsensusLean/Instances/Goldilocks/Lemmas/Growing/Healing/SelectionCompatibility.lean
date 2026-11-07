module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNext
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources

public section

/-! # Compatibility with a unanimous proposal through its update deadline -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Older origins lie below the proposal; only next-slot optimistic writes can be later. -/
theorem high_origin_compatible_before_update_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat}
    {P B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {r m : Nat} (ho : HighOrigin tr H g x r m B)
    (ht : tr.time r ≤ sp.ts u + 6 * sp.Δ) : Compatible (tr.HonestBlocksAt H) B P := by
  have hub : sp.ts u + sp.Δ ≤ b := by linarith [sp.toParams.hΔ]
  have hrb := ht.trans hTb
  by_cases ht' : tr.time r < sp.ts (u + 1 : Nat)
  · exact Or.inl (high_origins_before_next_slot_below_at hp hc hP hun hgu hR hub ho ht' hrb)
  obtain ⟨CV, ell, D, hcall, hfl, hB⟩ := ho.2.2.1
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hc'.2)
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  obtain ⟨hPhi, hsub⟩ : FrameOK ell.frame ∧ ell.frame.tree ⊆ tr.HonestBlocksAt H := by
    rcases hac.localRun.frameLaw x r ell ho.1 hcall with
      ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.1
  have hBD := (SA.anc_viableAncestor ell.frame D).mono hsub
  rw [← hB] at hBD
  have hDP : Compatible (tr.HonestBlocksAt H) D P := by
    rcases hfl with ⟨ellr, C, hupd, _⟩ | hop
    · have htime : tr.time r = sp.ts m + 6 * sp.Δ := hupd.2.2.1
      have hmu : m ≤ u := by
        have hle : sp.ts m ≤ sp.ts u := by linarith
        have := (SA.ts_le_iff sp).1 hle
        omega
      by_cases heq : m = u
      · subst m
        exact Or.inl (hp.same_slot_source_below_unanimous_at hc ho.1
          (Or.inl ⟨CV, Or.inl ⟨ellr, C, hupd, by assumption⟩⟩) hrb
          (hp.cutZ_le_ts_of_highOrigin_at ho hrb) hP hun)
      have hm : m < u := by omega
      have hbefore : tr.time r < sp.ts (u + 1 : Nat) := by
        simp only [SAParams.ts] at htime ⊢
        push_cast at htime ⊢
        nlinarith [sp.toParams.hΔ]
      exact False.elim (ht' hbefore)
    · have hs : sp.slot (tr.time r) = m := hop.choose_spec.choose_spec.2.1
      have hdeadline : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
        SA.slot_of_mem sp (u + 1)
          (by simp only [SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
          (by simp only [SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
      have hm := SA.slot_mono sp (hp.run.time_nonneg r) ht
      rw [hs, hdeadline] at hm
      have hml : u + 1 ≤ m := by
        have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r)
          ((u + 1 : Nat) : Int)).1 (not_lt.mp ht')
        omega
      have heq : m = u + 1 := by omega
      exact unanimous_next_optimistic_compatible_at hp hc hP hslot hu hun hgu hR hub
        ho.1 (heq ▸ hop) hrb
  rcases hDP with h | h
  · exact Or.inl (hBD.trans h)
  · exact SA.anc_total (Compose.Growing.honest_blocks_coherent hp.run hp.noColl) hBD h

/-- A finalized cache after the reset is below a bounded origin compatible with the proposal. -/
theorem finalized_compatible_before_update_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (ha : a ≤ tr.time k)
    (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F P := by
  obtain ⟨x, r, m, B, ho, hrk, _, hFB⟩ :=
    ProposalImpl.finalized_below_high_origin_at hp hy ha (ht.trans hTb)
  rcases high_origin_compatible_before_update_at hp hc hP hslot hu hun hgu hR hTb ho
      (hrk.trans ht) with h | h
  · exact Or.inl (hFB.trans h)
  · exact SA.anc_total (Compose.Growing.honest_blocks_coherent hp.run hp.noColl) hFB h

end Consensus.Goldilocks.Healing.Growing

end
