module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache

public section

/-! # The frame-key lag

If an honest `x` has key `v` at cut `i`, an honest `z` has key
`≥ v` at every cut `m` after a call of `z` at or after the relay deadline of `i`
(`frameKey_lag`). Each trigger block (the `h_max` carrier, the `J` carrier, the contest
witness) is held by `x`, so it was accepted by an honest node: `ResetService.relay` delivers
it when `x` accepted it at a time `≥ g`, `CatchRun g κ` when earlier. In both cases the target
precondition `Σ.F_z ⪯ B` holds because `σ[B].h ≥ h_max(z)` (`F_anc_of_hmax_le`).

No time bound against `T`, no NoAdvance and no `h_max ≥ HZ` premise is necessary. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

theorem accept_mem' (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (h : tr.AcceptAt y k B) :
    B ∈ (tr.state y (k + 1)).fg.tree := by
  rw [tr.state_succ_of_call h, (Store.tree_grows _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hy k)).1 B _ (hrun.toLocalRun.cutLaw y hy k _ h).2.1]
  exact Set.mem_insert _ _

/-- A block held by an honest `x` at `i`, of height at least `h_max(z)` at `m`, is held by `z`
at `m`: by relay (accepted at `≥ g`) or by catch-up (accepted before `g`). The relay deadline is
read from any bound `τ` on the times of the cuts before `i`. -/
theorem held_of_relay_le (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {g ΔF b κ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H) {i m : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state x i).fg.tree)
    (hh : (tr.state z m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h) {τ : Time}
    (hτ : ∀ k < i, tr.time k ≤ τ)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max τ g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    B ∈ (tr.state z m).fg.tree := by
  have hF : ∀ j ≤ m, Anc (tr.HonestBlocks H) (tr.state z j).fg.F B := fun j hj =>
    F_anc_of_hmax_le hrun hnc hf hz hx hB
      ((hmax_mono hrun.toLocalRun hz hj).trans hh)
  have hlift : ∀ k', k' + 1 ≤ m → tr.AcceptAt z k' B → B ∈ (tr.state z m).fg.tree :=
    fun k' hk' ha => Compose.tree_mono hrun.toLocalRun hz hk' (accept_mem' hrun hz ha)
  rcases tree_accepted hrun.toLocalRun hx hB with he | ⟨k, hk, hacc⟩
  · rw [he]
    exact Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hz m)
  have hki : tr.time k ≤ τ := hτ k hk
  by_cases hg : g ≤ tr.time k
  · obtain ⟨j, hjm, hcj, hdl⟩ := hcall
    have hdl' : tr.deadline z j (max (tr.time k) g) sp.Δ ≤ tr.time j :=
      (tr.deadline_mono z j (max_le_max hki le_rfl) sp.Δ).trans hdl
    obtain ⟨k', hk'j, ha, -⟩ :=
      hsvc.relay x hx k B hacc hg z hz j hcj hdl' (hF j hjm.le)
    exact hlift k' (by omega) ha
  · have hlt : tr.time k < gbar g := lt_of_lt_of_le (not_le.1 hg) (le_max_left _ _)
    obtain ⟨j₀, hfirst, hj₀⟩ := exists_firstCutFrom_le hcm
    obtain ⟨k', hk', ha⟩ := hcatch x hx k B hacc hlt z hz j₀ hfirst (hF j₀ hj₀)
    exact hlift k' (by omega) ha

/-- A store-level `G1.2`: `Σ.F` of an honest store is below every honest-held block of state
height `> h_j`. -/
theorem F_anc_of_hj_lt (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H)
    {m i : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBt : B ∈ (tr.state x i).fg.tree)
    (hlt : (tr.state y m).fg.hj < ((tr.state x i).fg.σ B.root).h) :
    Anc (tr.HonestBlocks H) (tr.state y m).fg.F B :=
  (Store.F_anc_of_hj_lt_of_safe (Compose.fg_reachable hrun.toLocalRun hy m)
    (Compose.fg_reachable hrun.toLocalRun hx i) (Compose.honest_blocks_coherent hrun.toLocalRun hnc)
    (fun _ h => ⟨y, hy, m, h⟩) (fun _ h => ⟨x, hx, i, h⟩) hf (held_atts_safe_run hrun hnc hy hx m i)
    hBt hlt).mono fun _ h => ⟨x, hx, i, h⟩

/-- **The frame-key lag.** Premises: relay (`ResetService`), catch-up
(`CatchRun g κ`), a call of `z` before `m` at or after the relay deadline of `i`, and
`ḡ + κ ≤ time m`. The relay deadline is read from any bound `τ` on the times of the cuts before
`i` (`frameKey_lag` takes `τ = time i`). -/
theorem frameKey_lag_le (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {g ΔF b κ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H) {i m : Nat} {τ : Time}
    (hτ : ∀ k < i, tr.time k ≤ τ)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max τ g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    frameKey (tr.state x i).fg ≤ frameKey (tr.state z m).fg := by
  have hRx := Compose.fg_reachable hrun.toLocalRun hx i
  have hRz := Compose.fg_reachable hrun.toLocalRun hz m
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨-, hJx, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, ⟨Bh, hBh, hBhh⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hRx
  obtain ⟨-, -, -, -, hgez, -, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hRz
  have hbx := frameKey_bounds (tr.state x i).fg
  have hbz := frameKey_bounds (tr.state z m).fg
  by_cases hlt : (tr.state x i).fg.hmax < (tr.state z m).fg.hmax
  · omega
  have hle : (tr.state z m).fg.hmax ≤ (tr.state x i).fg.hmax := not_lt.1 hlt
  have hheld : ∀ {B : SA.Blk sp.n (List (FG.Att sp.n))}, B ∈ (tr.state x i).fg.tree →
      (tr.state x i).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h → B ∈ (tr.state z m).fg.tree :=
    fun hB hh => held_of_relay_le hrun hnc hf hsvc hcatch hx hz hB (hle.trans hh) hτ hcall hcm
  -- the `h_max` carrier
  have hBhz := hheld hBh hBhh.ge
  have heq : (tr.state z m).fg.hmax = (tr.state x i).fg.hmax := by
    have := hgez Bh hBhz
    rw [σ_eq_honest hrun hnc hz hx hBhz hBh] at this
    omega
  -- the `J` carrier
  have hjz := hj_lt_hmax hrun hz m
  have hjx := hj_lt_hmax hrun hx i
  have hb : (tr.state x i).fg.hmax = (tr.state x i).fg.hj + 1 →
      (tr.state z m).fg.hmax = (tr.state z m).fg.hj + 1 := by
    intro hbx'
    have hBjh := Store.hj_lt_h hRx hBj
    have hBjz := hheld hBj (by omega)
    obtain ⟨E, hE, hEr, hEB, -⟩ := Store.J_entry_of_reachable hRx hBj
    obtain rfl : E = (tr.state x i).fg.J :=
      hU.1 ⟨x, hx, i, hE⟩ ⟨x, hx, i, hJx⟩ (hEr.trans hBjJ)
    have hJz : (tr.state x i).fg.J ∈ (tr.state z m).fg.tree :=
      mem_of_honest_anc hrun hnc hz (hEB.mono fun X hX => ⟨x, hx, i, hX⟩) hBjz
    have hJh := Store.J_height_le hRx hBj hJx hBjJ.symm
    by_contra hn
    have hzlt : (tr.state z m).fg.hj < (tr.state x i).fg.hj := by omega
    have hFJ := store_anc_of_honest_anc hrun hnc hz
      (F_anc_of_hj_lt hrun hnc hf hz hx (m := m) (i := i) hJx
        (by rw [hBjhj] at hJh; omega)) hJz
    have hσ := σ_eq_honest hrun hnc hz hx hBjz hBj
    have := (jMax_iff _).1 (jMax_of_reachable hRz) Bj hBjz _ hJz (by rw [hσ, hBjJ]) hFJ
    rw [hσ] at this
    omega
  -- the contest witness
  have hC : (tr.state x i).fg.Contest → (tr.state z m).fg.Contest := by
    rintro ⟨hbx', W, hW, -, hWh, hJW⟩
    have hbz' := hb hbx'
    have hWz := hheld hW hWh.ge
    have hσ := σ_eq_honest hrun hnc hz hx hWz hW
    have hJ := J_eq_of_hj_eq_run hrun hnc hf hz hx (i := m) (m := i) (by omega)
    refine ⟨hbz', W, hWz, ?_, by rw [hσ]; omega, ?_⟩
    · exact store_anc_of_honest_anc hrun hnc hz
        (F_anc_of_hmax_le hrun hnc hf hz hz hWz (by rw [hσ]; omega)) hWz
    · intro hJW'
      rw [hJ] at hJW'
      exact hJW (store_anc_of_honest_anc hrun hnc hx
        (hJW'.mono fun X hX => ⟨z, hz, m, hX⟩) hW)
  rw [frameKey_def, frameKey_def]
  split_ifs <;> first | omega | tauto

/-- **The frame-key lag** with the relay deadline read from `time i`. -/
theorem frameKey_lag (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {g ΔF b κ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H) {i m : Nat}
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    frameKey (tr.state x i).fg ≤ frameKey (tr.state z m).fg :=
  frameKey_lag_le hrun hnc hf hsvc hcatch hx hz (fun _ hk => hrun.time_mono hk.le) hcall hcm

/-- **The merged-key lag** with the relay deadline read from `time i`. -/
theorem frameKey'_lag (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {g ΔF b κ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H) {i m : Nat}
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) :
    frameKey' (tr.state x i).fg ≤ frameKey' (tr.state z m).fg :=
  (frameKey'_def _).symm ▸ (frameKey'_def _).symm ▸ keyMerge_mono
    (frameKey_lag hrun hnc hf hsvc hcatch hx hz hcall hcm)

end Consensus.Goldilocks.Healing

end
