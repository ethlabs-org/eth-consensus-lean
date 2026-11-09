module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.B2
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Deadline
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle

public section

/-! # Relay from independently honest held-state observations

The source is observed at a time bounding its preceding events; it need not remain honest
at the receiver's observation. Relay debts survive compromise of the sender.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Relay and catch-up carry a held block to a receiver whose height has not passed it. -/
theorem held_of_relay_le_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ τ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} {i m : Nat} (hτ0 : 0 ≤ τ) (hx : x ∈ H τ)
    (hz : z ∈ H (tr.time m))
    (hf : (H (max τ (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state x i).fg.tree)
    (hh : (tr.state z m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h)
    (hτ : ∀ k < i, tr.time k ≤ τ)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max τ g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : B ∈ (tr.state z m).fg.tree := by
  have hm0 := hrun.time_nonneg m
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => hrun.time_mono hk.le
  have hs : ∀ j ≤ m, (tr.upTo (tr.time m)).state z j = tr.state z j :=
    fun j hj => Trace.upTo_state tr z (fun k hk => hrun.time_mono (by omega))
  have hr := (hrun.upTo hm0).toLocalRun
  have hF : ∀ j ≤ m, Anc (tr.HonestBlocksAt H) (tr.state z j).fg.F B := by
    intro j hj
    have hheight := Healing.hmax_mono hr hz hj
    dsimp only at hheight
    rw [hs j hj, hs m le_rfl] at hheight
    apply F_anc_of_hmax_le_at hrun hnc hm0
      (fun k hk => hrun.time_mono (by omega)) hz hτ0 hτ hx
      (by rwa [max_comm]) hB (hheight.trans hh)
  have hlift : ∀ k, k + 1 ≤ m → tr.AcceptAt z k B → B ∈ (tr.state z m).fg.tree := by
    intro k hkm ha
    have ha' : (tr.upTo (tr.time m)).AcceptAt z k B :=
      (RunTrace.upTo_acceptAt tr).mpr ⟨hrun.time_mono (by omega), ha⟩
    have hmem := Healing.accept_mem' (hrun.upTo hm0) hz ha'
    have := Compose.tree_mono hr hz hkm hmem
    rwa [hs m le_rfl] at this
  have hB' : B ∈ ((tr.upTo τ).state x i).fg.tree := by
    rwa [Trace.upTo_state tr x hτ]
  rcases Healing.tree_accepted (hrun.upTo hτ0).toLocalRun hx hB' with he | ⟨k, hk, ha⟩
  · rw [he]
    exact Store.genesis_mem (fg_reachable_at hrun hm0 hm hz)
  have ha := ((RunTrace.upTo_acceptAt tr).mp ha).2
  have hxk := hrun.antitone (hτ k hk) hx
  by_cases hg : g ≤ tr.time k
  · obtain ⟨j, hjm, hcj, hdl⟩ := hcall
    have hdl' := (tr.deadline_mono z j (max_le_max (hτ k hk) le_rfl) sp.Δ).trans hdl
    obtain ⟨k', hk'j, ha', -⟩ := hsvc.relay x k B hxk ha hg z j
      (hrun.antitone (hrun.time_mono hjm.le) hz) hcj hdl' (hF j hjm.le)
    exact hlift k' (by omega) ha'
  · obtain ⟨j₀, hfirst, hj₀⟩ := Healing.exists_firstCutFrom_le hcm
    obtain ⟨k', hk', ha'⟩ := hcatch x k B hxk ha
      (lt_of_lt_of_le (not_le.mp hg) (le_max_left _ _)) z j₀
      (hrun.antitone hcm hz) hfirst (hF j₀ hj₀)
    exact hlift k' (by omega) ha'

/-- The snapshot height is attained by a member of its own honest cohort. -/
theorem exists_HZ_holder_at {g : Time} (hH : (H (cutZ sp.toParams g)).Nonempty) {j : Nat}
    (hj : FirstCutAfter tr j (cutZ sp.toParams g)) :
    ∃ x ∈ H (cutZ sp.toParams g), (tr.state x j).fg.hmax = HZ tr H g := by
  obtain ⟨y, hy⟩ := hH
  have hne : {h | ∃ y ∈ H (cutZ sp.toParams g), ∃ j,
      FirstCutAfter tr j (cutZ sp.toParams g) ∧ (tr.state y j).fg.hmax = h}.Nonempty :=
    ⟨_, y, hy, j, hj, rfl⟩
  obtain ⟨x, hx, j', hj', he⟩ := Nat.sSup_mem hne
    (((Set.finite_range fun z => (tr.state z j).fg.hmax).subset (by
      rintro _ ⟨z, -, j', hj', rfl⟩
      obtain rfl := hj'.unique hj
      exact ⟨z, rfl⟩)).bddAbove)
  obtain rfl := hj'.unique hj
  exact ⟨x, hx, he⟩

/-- After its relay obligation is paid, a receiver has at least the snapshot height. -/
theorem HZ_le_hmax_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : (H (cutZ sp.toParams g)).Nonempty)
    (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hf : (H (max (cutZ sp.toParams g) (tr.time m)))ᶜ.ncard <
      2 * sp.toParams.fg.q - sp.n)
    (hcall : ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : HZ tr H g ≤ (tr.state z m).fg.hmax := by
  obtain ⟨j, hj⟩ := hsnap
  obtain ⟨x, hx, hxe⟩ := exists_HZ_holder_at hH hj
  have hc0 : 0 ≤ cutZ sp.toParams g := by
    rw [Healing.cutZ_eq]
    simp only [SA.SAParams.ts]
    exact mul_nonneg (SA.four_delta_pos sp).le (by positivity)
  have hRx := fg_reachable_at hrun hc0 hj.1 hx
  have hm : ∀ k < m, tr.time k ≤ tr.time m := fun k hk => hrun.time_mono hk.le
  have hRz := fg_reachable_at hrun (hrun.time_nonneg m) hm hz
  obtain ⟨-, -, -, -, -, ⟨B, hB, hBh⟩, -⟩ := Store.cache_invariants _ _ _ _ hRx
  by_cases hle : HZ tr H g ≤ (tr.state z m).fg.hmax
  · exact hle
  have hBz := held_of_relay_le_at hrun hnc hsvc hcatch hc0 hx hz hf hB
    (by omega) hj.1 hcall hcm
  have he := σ_eq_honest_at hrun hnc hc0 hj.1 hx (hrun.time_nonneg m) hm hz hB hBz
  have hh := (Store.cache_invariants _ _ _ _ hRz).2.2.2.2.1 B hBz
  rw [← he] at hh
  omega

end Consensus.Goldilocks.Healing.Growing

end
