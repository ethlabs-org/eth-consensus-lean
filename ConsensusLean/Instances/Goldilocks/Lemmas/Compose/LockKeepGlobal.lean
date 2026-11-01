module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepVote
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointKeep

public section

/-! # Goldilocks: honest locks on `B` kept by every honest node over an interval

consensus-lean#135 (WI-16), r14 s1 L1.2: the induction over time that discharges the read-point
premise of `lock_keep_interval_cases_locked`. Each honest node `x` holds a lock `lk x` on `B` at
cut `i₀`. At every cut `j ∈ [i₀, N)` of every honest node, the lock does not expire and the frame
regime keeps `B` (`FrameKeeps`); these stay premises. The votes that `unlock` reads at cut `j` are
of slot `slot(t_j) − 1`, so their honest casts are at earlier cuts (`cast_lt_of_slot`). A cast at a
cut `k ≥ i₀` reads `B` as a live lock block (`SA.mem_readPoint_liveLockBlocks_of_keep`, by the
induction hypothesis at `k`); a cast before `i₀` is the premise `hearly`. Strong induction on the
global cut index (`lock_keep_global`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The frame-regime cases of `viableAncestor_eq_self_run` at node `y`, cut `j`, block `B`. -/
abbrev FrameKeeps (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (j : Nat)
    (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ((tr.state y j).fg.Contest ∧ ∃ Y ∈ (tr.state y j).fg.tree,
    (tr.state y j).fg.Anc (tr.state y j).fg.F Y ∧
    (tr.state y j).fg.hmax ≤ ((tr.state y j).fg.σ Y.root).h ∧
    (tr.state y j).fg.toFrame.Anc B Y) ∨
  ((tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 ∧ ¬ (tr.state y j).fg.Contest ∧
    (tr.state y j).fg.Anc (tr.state y j).fg.F (tr.state y j).fg.J ∧
    (tr.state y j).fg.Anc (tr.state y j).fg.J B ∧ ∃ Y ∈ (tr.state y j).fg.tree,
    (tr.state y j).fg.Anc (tr.state y j).fg.J Y ∧ (tr.state y j).fg.IsViable Y ∧
    (tr.state y j).fg.toFrame.Anc B Y) ∨
  ((tr.state y j).fg.hmax ≠ (tr.state y j).fg.hj + 1 ∧
    ∃ Y ∈ (tr.state y j).fg.toFrame.viableHeads, (tr.state y j).fg.toFrame.Anc B Y)

/-- The unlock premise of `lock_keep_run_view` at node `y`, cut `j`: `unlock` at the view of the
AC call at `j` does not move `B` (for the slot-`(slot(t_j) − 1)` votes). -/
abbrev UnlockKeeps (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (j : Nat)
    (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ ℓ, tr.CallAt y j (.ac ℓ) → SA.unlockTarget sp (Node.frame (tr.state y j))
    (SA.unlockView (ro := ro) (tr.state y j).ac (Node.frame (tr.state y j)) (tr.time j) ℓ.call)
    ((sp.slot (tr.time j) : Int) - 1) B = B

/-- **`unlock` keeps `B` against honest votes that read a lock above it.** At an AC cut `j` of
an honest `y`, with `2|Hᶜ| < n`, if every held honest vote of slot `slot(t_j) − 1` satisfies
`ReadsLockAbove`, the unlock target of `B` at the call's view is `B`. -/
theorem unlockKeeps_of_reads (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y j).fg.toFrame.tree) (hf : 2 * Hᶜ.ncard < sp.n)
    (hread : ∀ x ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac
      (Node.frame (tr.state y j)), x.val ∈ H →
      (x.slot : Int) = (sp.slot (tr.time j) : Int) - 1 → ReadsLockAbove tr x B) :
    UnlockKeeps tr y j B := by
  intro ℓ hcall
  obtain ⟨hfr, hst, -, -⟩ := hrun.cutLaw y hy j _ hcall
  rw [hfr] at hst
  have hA' : ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y (tr.state y j).ac
      (Node.frame (tr.state y j)) (tr.time j) ℓ.call).1 = (tr.state y (j + 1)).ac := by
    rw [tr.state_succ_of_call hcall, hst]
  have hpool : ∀ m τ, ∀ v ∈ (tr.state y m).ac.pool τ, v.slot = τ := fun m τ v hv => by
    rw [← projAC_state hrun.toLocalRun hy] at hv
    exact (state_pool_cap hrun hy m τ).1 v hv
  have hpay : ∀ C ∈ (Node.frame (tr.state y j)).tree, SA.validPayload C := by
    have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
    rw [← hfr]
    exact SA.frame_validPayload sp hr hy (projAC_callAt.2 hcall)
  exact SA.unlockTarget_unlockView_held_of_honest_slot y ℓ.call hA'
    (frameOK_state hrun.toLocalRun hy j) _ hB (hpool j) (hpool (j + 1)) hpay
    (fun x hx x' hx' hxH hval hs => heldVotes_honest_unique hrun hnc hy hcall hx hx' hxH hval hs)
    (fun x hx hxH hs => heldVote_compatible_of_cast hrun hnc hy hcall hB hx hxH
      (hread x hx hxH hs)) hf

/-- An honest cast of a vote of slot `slot(t_j) − 1` is at a cut before `j`. -/
theorem cast_lt_of_slot (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k j : Nat}
    {ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} {e}
    (hc : SA.CastAt tr.projAC x k ℓ' e)
    (hs : (e.msg.slot : Int) = (sp.slot (tr.time j) : Int) - 1) : k < j := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hsk : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hr hx hc).2.1
  by_contra hkj
  have := SA.slot_mono sp (hrun.time_nonneg j) (hrun.time_mono (Nat.le_of_not_lt hkj))
  omega

/-- **Every honest node keeps its lock on `B` over `[i₀, N]`.** Premises: `2|Hᶜ| < n`; at
`i₀` each honest `x` holds `lk x` with block `B`; at every cut `j ∈ [i₀, N)` of every honest
`x`, `lk x` does not expire, `B` is in the frame's tree and a frame regime keeps it; every honest
cast before `i₀` of a slot at least `slot(t_{i₀}) − 1` reads a live lock block or `fc_root`
above `B`. Conclusion: at every cut `j ∈ [i₀, N]` each honest `x` holds `lk x`, and for `j < N`
`unlock` at `x`'s call at `j` does not move `B`. -/
theorem lock_keep_global (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ N : Nat}
    (lk : Fin sp.n → SA.Lock) (hbase : ∀ x ∈ H, lk x ∈ (tr.state x i₀).ac.locks)
    (hBr : ∀ x ∈ H, B.root = (lk x).block)
    (hcut : ∀ x ∈ H, ∀ j, i₀ ≤ j → j < N → sp.slot (tr.time j) ≤ (lk x).slot + sp.k ∧
      B ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeeps tr x j B)
    (hearly : ∀ x ∈ H, ∀ k < i₀, sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 →
      ∀ (ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) e,
      SA.CastAt tr.projAC x k ℓ' e →
      ∃ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k) ∪ {ℓ'.frame.fcRoot},
        ℓ'.frame.Anc B C) :
    ∀ j, i₀ ≤ j → j ≤ N → ∀ x ∈ H,
      lk x ∈ (tr.state x j).ac.locks ∧ (j < N → UnlockKeeps tr x j B) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hij hjN y hy
  -- the lock at `j`
  have hlock : lk y ∈ (tr.state y j).ac.locks := by
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact hbase y hy
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨hl, hu⟩ := ih j' (by omega) (by omega) (by omega) y hy
      obtain ⟨hk, hB, hc⟩ := hcut y hy j' (by omega) (by omega)
      exact lock_keep_run_view hrun hy j' hl hk hB (hBr y hy)
        (viableAncestor_eq_self_run hrun hy j' hB hc) fun ℓ hℓ => Or.inr (hu (by omega) ℓ hℓ)
  refine ⟨hlock, fun hjN' => ?_⟩
  obtain ⟨-, hB, -⟩ := hcut y hy j hij hjN'
  refine unlockKeeps_of_reads hrun hnc hy hB hf fun x _ hxH hs => ?_
  refine readsLockAbove_of_live hrun hnc hxH fun k ℓ' e hc hm => ?_
  subst hm
  have hkj : k < j := cast_lt_of_slot hrun hnc hxH hc hs
  have hsk : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hr hxH hc).2.1
  by_cases hki : k < i₀
  · refine hearly _ hxH k hki ?_ ℓ' e hc
    have := SA.slot_mono sp (hrun.time_nonneg i₀) (hrun.time_mono hij)
    omega
  obtain ⟨hl, hu⟩ := ih k hkj (by omega) (by omega) _ hxH
  obtain ⟨hk, hBk, hcK⟩ := hcut _ hxH k (by omega) (by omega)
  have hcall : tr.CallAt e.msg.val k (.ac ℓ') := projAC_callAt.1 hc.1
  have hfr : ℓ'.frame = Node.frame (tr.state e.msg.val k) :=
    (hrun.cutLaw _ hxH k _ hcall).1
  have hva : ℓ'.frame.viableAncestor B = B := by
    rw [hfr]
    exact viableAncestor_eq_self_run hrun hxH k hBk hcK
  have hu' := hu (by omega) ℓ' hcall
  rw [← hfr] at hu'
  replace hBk : B ∈ ℓ'.frame.tree := by
    rw [hfr]
    exact hBk
  rw [← projAC_state hrun.toLocalRun hxH] at hl hu'
  exact ⟨B, Or.inl (SA.mem_readPoint_liveLockBlocks_of_keep hr hxH hc hl hk hBk (hBr _ hxH) hva
    (Or.inr hu')), Relation.ReflTransGen.refl⟩

end Consensus.Goldilocks.Compose

end
