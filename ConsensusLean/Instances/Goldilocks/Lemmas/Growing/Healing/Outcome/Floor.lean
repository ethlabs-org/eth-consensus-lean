module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Contest
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RowOrder
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The voter's height floor is bounded by its old-origin upper bound -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An older fast-lock label written by the late-vote deadline was written before the slot. -/
theorem fastLock_time_lt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} {r m u : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hfl : SA.FastLockAt tr.projAC x r m D CV)
    (hmu : m < u) (htr : tr.time r ≤ sp.ts u + sp.Δ) : tr.time r < sp.ts u := by
  rcases hfl with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hsl, _⟩
  · change tr.time r = sp.ts m + 6 * sp.Δ at ht
    have htwo : (m : Int) + 2 ≤ u := by
      have := Compose.ts_add_two_le (ht ▸ htr)
      exact_mod_cast this
    have hDelta := sp.toParams.hΔ
    rw [ht]
    simp only [SAParams.ts] at htr ⊢
    nlinarith only [htwo, hDelta]
  · change sp.slot (tr.time r) = m at hsl
    by_contra h
    have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg r) u).mp (not_lt.mp h)
    omega

end Outcome

namespace ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A bounded old-origin upper bound reaches the actual voter's height floor. A high contest is
ruled out by `no_high_contest_at`, whose origins are compared by
`ResetPremisesUpTo.origins_compatible_at`. -/
theorem reset_vote_floor_above_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {j u : Nat} (hy : y ∈ H (tr.time j)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O B) :
    (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  have ht := hp.run.time_nonneg j
  have hj : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hp.run.time_mono hq.le
  have hreach := fg_reachable_at hp.run ht hj hy
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
  have hBh := Outcome.high_of_anc_at hp.run hp.noColl ho₀ ht hj hy hB
    (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb)
  have hnc := Outcome.no_high_contest_at hp hy hjb
  by_contra hle
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state y j).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state y j).fg.headHeightFloor = (tr.state y j).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ := Healing.entry_at_height hreach hC
    (h := (tr.state y j).fg.hmax - 1) (by omega) (by omega)
  have hq : (H (tr.time j))ᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults (tr.time j) ht hjb
    have hn := sp.toParams.hn
    change 3 * (H (tr.time j))ᶜ.ncard ≤ sp.toParams.n - 1 at h3
    change (H (tr.time j))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  obtain ⟨W, hW, att, ha, v, hv, d, hdj, hs, _, r, hrd, l, O, ho, hEO⟩ :=
    Outcome.left_entry_origin_at (g := g) hp.run hp.noColl ht hj hy hq hE hET
      (by omega) hEC (by omega)
  have hlu : l < u := hes ▸ Outcome.row_origin_label_lt_at hp.run hp.noColl
    hy hv hc hW ha hs hdj hrd ho
  obtain ⟨CV, ellw, D, _, hf, _⟩ := ho.2.2.1
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc.1⟩
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j)) _ proposer
    (hp.run.upTo ht) (hp.noColl.upTo _)).localRun
  have hrt := Outcome.fastLock_time_lt_at hp.run hf hlu
    ((hp.run.time_mono (show r ≤ j by omega)).trans
      (hes ▸ (Compose.cast_head_fcRoot hr hy ⟨hc', hc.2⟩).2))
  have hEB := hEO.trans (hBold v r l O ho hrt
    ((hp.run.time_mono (show r ≤ j by omega)).trans hjb))
  have hh := Healing.h_le_of_store_anc hreach
    (store_anc_of_honest_anc_at hp.run hp.noColl ht hj hy hEB hB)
  omega

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end
