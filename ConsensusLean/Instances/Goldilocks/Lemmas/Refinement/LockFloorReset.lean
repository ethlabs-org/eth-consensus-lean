module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorSegmentsGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Cover

public section

/-! # Goldilocks: the lock floor over unanimous segments under the reset (N7)

consensus-lean#135, plan N7 (workbench `notes/fg-liveness/r14-end-to-end/n6-cover.md` §4.3).
`Healing.lock_floor_unanimous_le` with the reset premises: `HealthyBase` from
`healthy_base_of_reset_catch`; `hnext` from `unanimous_next_vote_viable` and
`unanimous_next_votes_extend_healthy`; the `FrameKeepsOrRoot` part of `hcut` from the N6 cover
(`frameKeeps_or_root_of_bracket`); the frame membership of `hcut` and `hN` from N2
(`frame_mem_of_tree`). This module is in `Lemmas.Refinement` because `Lemmas.Healing` may not
import `unanimous_next_vote_viable`.

Explicit inputs: the unanimous slot sequence (with `htick` for the fresh floors), the bracket of
`B₀`, `F ⪯ B₀` at every cut up to the stop cut `i M` (`C(x, j)`), the base of segment 0, and, at
each exact-spacing segment, the old-origin bound `hold` of `unanimous_next_vote_viable`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

private theorem seg_bounds {M : Nat} {i : Nat → Nat} (hi : ∀ m < M, i m ≤ i (m + 1)) :
    ∀ m ≤ M, i 0 ≤ i m ∧ i m ≤ i M := by
  have hlo : ∀ m ≤ M, i 0 ≤ i m := by
    intro m
    induction m with
    | zero => exact fun _ => le_rfl
    | succ m ih => exact fun h => (ih (by omega)).trans (hi m (by omega))
  have hhi : ∀ d, d ≤ M → i (M - d) ≤ i M := by
    intro d
    induction d with
    | zero => exact fun _ => le_rfl
    | succ d ih =>
      intro h
      have h1 := hi (M - (d + 1)) (by omega)
      have h2 : M - (d + 1) + 1 = M - d := by omega
      rw [h2] at h1
      exact h1.trans (ih (by omega))
  intro m hm
  refine ⟨hlo m hm, ?_⟩
  have := hhi (M - m) (by omega)
  rwa [Nat.sub_sub_self hm] at this

/-- **The lock floor over unanimous segments under the reset (N7).** `lock_floor_unanimous_le`
with `ResetPremises` and `CatchRun`. Bracket of `B₀` (`Br`): `B₀` is held at an honest `z` at
height `≥ H_z + 1` and lies below the block `O₀` of a high origin. `C(x, j)`: every honest `x`
holds `B₀` at `i 0`, and `F ⪯ B₀` at each cut of `[i 0, i M]`. At each segment `m` of exact
spacing `p (m+1) = p m + k` (`hexact`): slot `p (m+1)` is unanimous for the honest block
`Ps (m+1) ⪰ B₀` of that slot, after `ḡ + 4Δ` and after the drain at `t_{p (m+1) + 1}`, and the
high origins before `t_{p (m+1)}` are below `Ps (m+1)` (`hold`). The conclusion is that of
`lock_floor_unanimous_le`. -/
theorem lock_floor_unanimous_le_reset (hp : Healing.ResetPremises tr H proposer dg g ΔF a)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    {z : Fin sp.n} {mz : Nat} (hz : z ∈ H) (hBz : B₀ ∈ (tr.state z mz).fg.tree)
    (hBh : Healing.HZ tr H g + 1 ≤ ((tr.state z mz).fg.σ B₀.root).h)
    {v₀ : Fin sp.n} {r₀ l₀ : Nat} {O₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho₀ : Healing.HighOrigin tr H g v₀ r₀ l₀ O₀) (hB₀O : Anc (tr.HonestBlocks H) B₀ O₀)
    (M : Nat) (hM : 0 < M) (i : Nat → Nat)
    (hi : ∀ m < M, i m ≤ i (m + 1)) (p : Nat → Nat) (Ps : Nat → SA.Blk sp.n (List (FG.Att sp.n)))
    (hsp : ∀ m < M, p (m + 1) ≤ p m + sp.k)
    (htime : ∀ m < M, ∀ c < i (m + 1), tr.time c ≤ sp.ts (p (m + 1)) + 6 * sp.Δ)
    (hbase0 : ∀ x ∈ H, Compose.FloorAt tr x (i 0) B₀ (p 0))
    (hp4 : ∀ m, m + 1 < M → SA.gbar g + 4 * sp.Δ ≤ sp.ts (p (m + 1)))
    (hun : ∀ m, m + 1 < M → Healing.Unanimous tr H (p (m + 1)) (Ps (m + 1)))
    (hPg : ∀ m, m + 1 < M → (Ps (m + 1)).root ≠ sp.genesisRoot)
    (htick : ∀ m, m + 1 < M → ∀ x ∈ H, ∃ k, ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.projAC.CallAt x k ℓ ∧ ℓ.call = .tick ∧ tr.time k = sp.ts (p (m + 1)) + 6 * sp.Δ ∧
      i m ≤ k + 1 ∧ k + 1 ≤ i (m + 1) ∧ Ps (m + 1) ∈ ℓ.frame.tree ∧
      ℓ.frame.viableAncestor (Ps (m + 1)) = Ps (m + 1) ∧
      (∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state x k).locks ℓ.frame (tr.time k),
        Compatible (tr.HonestBlocks H) L (Ps (m + 1))) ∧ ℓ.frame.Anc B₀ (Ps (m + 1)))
    (hB0 : ∀ x ∈ H, B₀ ∈ (tr.state x (i 0)).fg.tree)
    (hF : ∀ x ∈ H, ∀ j, i 0 ≤ j → j ≤ i M → (tr.state x j).fg.Anc (tr.state x j).fg.F B₀)
    (hexact : ∀ m < M, p (m + 1) = p m + sp.k →
      Ps (m + 1) ∈ tr.HonestBlocks H ∧ (Ps (m + 1)).slot = p (m + 1) ∧
      Healing.Unanimous tr H (p (m + 1)) (Ps (m + 1)) ∧
      SA.gbar g + 4 * sp.Δ ≤ sp.ts (p (m + 1)) ∧
      Healing.drainTime sp a ≤ sp.ts (p (m + 1) + 1 : Nat) ∧
      Anc (tr.HonestBlocks H) B₀ (Ps (m + 1)) ∧
      ∀ x r b B, Healing.HighOrigin tr H g x r b B → tr.time r < sp.ts (p (m + 1)) →
        Anc (tr.HonestBlocks H) B (Ps (m + 1)))
    (hearly : Compose.EarlyVotes H tr (i 0) B₀) :
    (∀ m < M, ∀ x ∈ H, Compose.FloorAt tr x (i m) B₀ (p m)) ∧
    ∀ j, i 0 ≤ j → j < i M → ∀ x ∈ H, ∃ m < M, i m ≤ j ∧ j < i (m + 1) ∧
      (sp.slot (tr.time j) ≤ p m + sp.k → Compose.FloorAt tr x j B₀ (p m)) ∧
      Compose.UnlockKeeps tr x j B₀ := by
  have hS := Healing.healthy_base_of_reset_catch hp hc
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.healthy.2.2
    have := Fin.pos z
    have hn : sp.n = sp.toParams.n := rfl
    omega
  have hb := seg_bounds hi
  have hmem : ∀ x ∈ H, ∀ j, i 0 ≤ j → j ≤ i M → B₀ ∈ (tr.state x j).fg.toFrame.tree :=
    fun x hx j h0 hM' => Compose.frame_mem_of_tree hp.run hx h0 (hB0 x hx) (hF x hx j h0 hM')
  refine Healing.lock_floor_unanimous_le hp.run hp.noColl hf hS M hM i hi p Ps hsp htime hbase0
    hp4 hun hPg htick (fun m hm x hx j hj hjN => ?_) (fun m hm x hx => ?_)
    (fun m hm hk y hy j e hv hs => ?_) hearly
  · have hB := hmem x hx j ((hb m hm.le).1.trans hj)
      (hjN.le.trans (hb (m + 1) hm).2)
    exact ⟨hB, Healing.frameKeeps_or_root_of_bracket hp hx j hB hz hBz hBh ho₀ hB₀O⟩
  · exact hmem x hx _ ((hb m hm.le).1.trans (hi m hm)) (hb (m + 1) hm).2
  · obtain ⟨hP, hslot, hu, hgu, hR, hBP, hold⟩ := hexact m hm hk
    have hk2 := sp.two_le_k
    have hviab : ∀ y ∈ H, ∀ j ℓ e, SA.CastAt tr.projAC y j ℓ e → e.msg.slot = p (m + 1) + 1 →
        Anc (tr.HonestBlocks H) ℓ.frame.F (Ps (m + 1)) ∧
          SA.ViableAtVote ℓ e (p (m + 1) + 1) (Ps (m + 1)) := by
      intro y hy j ℓ e hcast hs
      obtain ⟨hFP, hPt⟩ := unanimous_next_vote_viable hp hc hP hslot (by omega) hu hgu hR hold
        hy hcast hs
      exact ⟨hFP, Or.inl hPt⟩
    obtain ⟨Hd, hHd, he, hPH⟩ :=
      Healing.unanimous_next_votes_extend_healthy hS hP hu hgu hviab y hy j e hv hs
    exact ⟨Hd, hHd, he, hBP.trans hPH⟩

end Consensus.Goldilocks.Refinement

end
