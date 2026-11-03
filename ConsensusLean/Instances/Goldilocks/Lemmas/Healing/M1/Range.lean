module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset

public section

/-! # M1′ A1 and the frame range: `H_z ≤ h_max ≤ H_z + 1` before the advance

pre_advance_finality §26 Step A (F1) and §23 (the lower bound after `c_z + Δ`).

* `hmax_le_of_noAdvance` (F1): if no honest node signs at a height `> H_z` at a time `< T`,
  every honest `h_max` at a cut before `T` is `≤ H_z + 1`. A block of state height `≥ H_z + 2`
  carries an honest row of height `H_z + 1` (G0.2 (f), `f < q`), signed before the block was
  accepted. Only `f < q` is used, not `Healthy(g)`.
* `HZ_le_hmax`: every honest `h_max` is `≥ H_z` at a cut `m` after a call of the node at or after
  `max(c_z, g) + Δ` and after `ḡ + κ`. `H_z` is the `h_max` of an honest holder at the snapshot
  cut after `c_z`, and `frameKey_lag_le` carries its key (so its `h_max`) to the node.
* `exists_frameWindow_of_noAdvance`: `exists_frameWindow_of_service` with the range premise
  discharged by the two lemmas above. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **F1 (A-item 5).** Before the height advance (no honest signature of height `> H_z` at a
time `< T`), every honest `h_max` at a cut before `T` is at most `H_z + 1`. -/
theorem hmax_le_of_noAdvance (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q) {g T : Time}
    (hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} (hiT : tr.time i < T) :
    (tr.state y i).fg.hmax ≤ HZ tr H g + 1 := by
  have hR := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨-, -, -, -, -, ⟨X, hX, hXh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  by_contra hlt
  obtain ⟨Y, hYX, a, ha, haH, hah⟩ :=
    Store.exists_honest_att_of_lt hR hq hX (HZ tr H g + 1) (by omega) (by omega)
  have hY : Y ∈ (tr.state y i).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  rcases tree_accepted hrun.toLocalRun hy hY with rfl | ⟨k, hki, hA⟩
  · cases ha
  obtain ⟨j, hjk, hj⟩ :=
    hrun.toLocalRun.att_unforgeable y hy k a (Or.inr ⟨Y, ⟨true, hA⟩, ha⟩) haH
  have hjT : tr.time j < T := lt_of_le_of_lt (hrun.time_mono (by omega)) hiT
  have := hna _ haH j a hj hjT
  omega

/-- `H_z` is the `h_max` of some honest node at the snapshot cut after `c_z`. -/
theorem exists_HZ_holder (hH : H.Nonempty) {g : Time} {j : Nat}
    (hj : FirstCutAfter tr j (cutZ sp.toParams g)) :
    ∃ x ∈ H, (tr.state x j).fg.hmax = HZ tr H g := by
  obtain ⟨y, hy⟩ := hH
  have hne : {h | ∃ y ∈ H, ∃ j, FirstCutAfter tr j (cutZ sp.toParams g) ∧
      (tr.state y j).fg.hmax = h}.Nonempty := ⟨_, y, hy, j, hj, rfl⟩
  obtain ⟨x, hx, j', hj', he⟩ := Nat.sSup_mem hne
    (((Set.finite_range fun z => (tr.state z j).fg.hmax).subset (by
      rintro _ ⟨z, -, j', hj', rfl⟩
      obtain rfl := hj'.unique hj
      exact ⟨z, rfl⟩)).bddAbove)
  obtain rfl := hj'.unique hj
  exact ⟨x, hx, he⟩

/-- **The range lower bound.** Every honest `h_max` is at least `H_z` at a cut `m` after a call
of the node at or after the relay deadline `max(c_z, g) + Δ`, and at or after `ḡ + κ`. The
premises are those of `frameKey_lag_le`, a snapshot cut after `c_z`, and an honest node. -/
theorem HZ_le_hmax (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {g ΔF b κ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : H.Nonempty) (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    {z : Fin sp.n} (hz : z ∈ H) {m : Nat}
    (hcall : ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    HZ tr H g ≤ (tr.state z m).fg.hmax := by
  obtain ⟨j, hj⟩ := hsnap
  obtain ⟨x, hx, hxe⟩ := exists_HZ_holder hH hj
  have := frameKey_lag_le hrun hnc hf hsvc hcatch hx hz (i := j) hj.1 hcall hcm
  have h1 := frameKey_bounds (tr.state x j).fg
  have h2 := frameKey_bounds (tr.state z m).fg
  omega

/-- **The range `H_z ≤ h_max ≤ H_z + 1` on `[lo, T)`**, from F1 and the lower bound. -/
theorem hmax_range (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF b κ T lo : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : H.Nonempty) (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    (hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g)
    (hlo : gbar g + κ ≤ lo)
    (hcallZ : ∀ z ∈ H, ∀ m, lo ≤ tr.time m → tr.time m < T → ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j) :
    ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ tr H g ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ tr H g + 1 :=
  fun _ hy _ hi hiT =>
    ⟨HZ_le_hmax hrun hnc hf hsvc hcatch hH hsnap hy (hcallZ _ hy _ hi hiT) (hlo.trans hi),
      hmax_le_of_noAdvance hrun hq hna hy hiT⟩

/-- **A FrameWindow before the advance.** `exists_frameWindow_of_service` with the range premise
discharged by `hmax_range`. -/
theorem exists_frameWindow_of_noAdvance (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF b κ : Time} (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : H.Nonempty) (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    {lo len lam T : Time} (hlen : 0 ≤ len) (hlam : 0 ≤ lam)
    (hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g)
    (hlo : gbar g + κ ≤ lo)
    (hcallZ : ∀ z ∈ H, ∀ m, lo ≤ tr.time m → tr.time m < T → ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hcall : ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + 6 * (len + lam) < T) :
    ∃ a, lo + lam ≤ a ∧ a + len ≤ lo + 6 * (len + lam) ∧
      ∃ floor contest kindJ J,
        FrameWindow (tr := tr) (H := H) a (a + len) floor contest kindJ J :=
  exists_frameWindow_of_service hrun hnc hf hsvc hcatch hlen hlam hlo
    (hmax_range hrun hnc hf hq hsvc hcatch hH hsnap hna hlo hcallZ) hcall hT

/-- **A FrameWindowF before the advance (5 windows).** `exists_frameWindowF5_of_service` with
the range premise discharged by `hmax_range`. -/
theorem exists_frameWindowF5_of_noAdvance (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF b κ : Time} (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : H.Nonempty) (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    {lo len lam T : Time} (hlen : 0 ≤ len) (hlam : 0 ≤ lam)
    (hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g)
    (hlo : gbar g + κ ≤ lo)
    (hcallZ : ∀ z ∈ H, ∀ m, lo ≤ tr.time m → tr.time m < T → ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hcall : ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + 5 * (len + lam) < T) :
    ∃ a, lo + lam ≤ a ∧ a + len ≤ lo + 5 * (len + lam) ∧
      ∃ floor kindJ J, FrameWindowF (tr := tr) (H := H) a (a + len) floor kindJ J :=
  exists_frameWindowF5_of_service hrun hnc hf hsvc hcatch hlen hlam hlo
    (hmax_range hrun hnc hf hq hsvc hcatch hH hsnap hna hlo hcallZ) hcall hT

end Consensus.Goldilocks.Healing

end
