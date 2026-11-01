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

/-- **Locks on `B` from slot `s₀ − 1` on: no early-read premise.** As `lock_keep_global` from
`i₀`, with `hearly` replaced by premises on the cuts `k ≤ i₀` with
`slot(t_{i₀}) ≤ slot(t_k) + 1`: each honest `x` holds `lk x` there and, for `k < N`, the
per-cut premises of `hcut` hold; the lock is of slot at least `slot(t_{i₀}) − 1`
(`hlslot`), so `unlock` at the casts before `i₀` (of slot `≤ slot(t_{i₀})`) cannot drop it. -/
theorem lock_keep_global_slot (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ N : Nat}
    (lk : Fin sp.n → SA.Lock) (hBr : ∀ x ∈ H, B.root = (lk x).block)
    (hlslot : ∀ x ∈ H, sp.slot (tr.time i₀) ≤ (lk x).slot + 1)
    (hhold : ∀ x ∈ H, ∀ k ≤ i₀, sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 →
      lk x ∈ (tr.state x k).ac.locks)
    (hcut : ∀ x ∈ H, ∀ j, sp.slot (tr.time i₀) ≤ sp.slot (tr.time j) + 1 → j < N →
      sp.slot (tr.time j) ≤ (lk x).slot + sp.k ∧
      B ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeeps tr x j B) :
    ∀ j, i₀ ≤ j → j ≤ N → ∀ x ∈ H,
      lk x ∈ (tr.state x j).ac.locks ∧ (j < N → UnlockKeeps tr x j B) := by
  intro j hij hjN
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hmono : ∀ {a b}, a ≤ b → sp.slot (tr.time a) ≤ sp.slot (tr.time b) := fun h =>
    SA.slot_mono sp (hrun.time_nonneg _) (hrun.time_mono h)
  refine lock_keep_global hrun hnc hf lk (fun x hx => hhold x hx i₀ le_rfl (by omega)) hBr
    (fun x hx j hj hjN => hcut x hx j (by have := hmono hj; omega) hjN) ?_ j hij hjN
  intro x hx k hki hsk ℓ' e hc
  have hsk' := hmono hki.le
  obtain ⟨hk, hBk, hcK⟩ := hcut x hx k hsk (by omega)
  have hl := hhold x hx k hki.le hsk
  have hcall : tr.CallAt x k (.ac ℓ') := projAC_callAt.1 hc.1
  have hfr : ℓ'.frame = Node.frame (tr.state x k) := (hrun.cutLaw _ hx k _ hcall).1
  have hva : ℓ'.frame.viableAncestor B = B := by
    rw [hfr]
    exact viableAncestor_eq_self_run hrun hx k hBk hcK
  replace hBk : B ∈ ℓ'.frame.tree := by
    rw [hfr]
    exact hBk
  rw [← projAC_state hrun.toLocalRun hx] at hl
  have hls := hlslot x hx
  have htk : (tr.projAC).time k = tr.time k := rfl
  exact ⟨B, Or.inl (SA.mem_readPoint_liveLockBlocks_of_keep hr hx hc hl hk hBk (hBr x hx) hva
    (Or.inl (by rw [htk]; omega))), Relation.ReflTransGen.refl⟩

/-- **Chained locks over segments.** Segments `m < M` cover the cut intervals `[i m, i (m+1)]`;
in segment `m` every honest `x` holds the fresh lock `lk m x` on the common block `Bs m`, with the
premises of `lock_keep_global_slot` for `i₀ := i m`, `N := i (m+1)`. The no-expiry part of
`hcut` (`slot(t_j) ≤ (lk m x).slot + k` for `j < i (m+1)`, with `(lk m x).slot + 1 ≥
slot(t_{i m})` by `hlslot`) is the segment condition: segment `m` can only cover slots up to
`(lk m x).slot + k`. One block per segment is needed: `unlock` keeps a lock against the honest
votes that read a live lock *above its own block*, so locks of different nodes on incomparable
blocks are not kept. Conclusion: at every cut `j ∈ [i 0, i M]` each honest `x` holds the lock
`lk m x` on `Bs m` of some segment `m` with `i m ≤ j ≤ i (m+1)`. -/
theorem lock_keep_chain (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) (M : Nat) (hM : 0 < M) (i : Nat → Nat)
    (Bs : Nat → SA.Blk sp.n (List (FG.Att sp.n))) (lk : Nat → Fin sp.n → SA.Lock)
    (hBr : ∀ m < M, ∀ x ∈ H, (Bs m).root = (lk m x).block)
    (hlslot : ∀ m < M, ∀ x ∈ H, sp.slot (tr.time (i m)) ≤ (lk m x).slot + 1)
    (hhold : ∀ m < M, ∀ x ∈ H, ∀ k ≤ i m, sp.slot (tr.time (i m)) ≤ sp.slot (tr.time k) + 1 →
      lk m x ∈ (tr.state x k).ac.locks)
    (hcut : ∀ m < M, ∀ x ∈ H, ∀ j, sp.slot (tr.time (i m)) ≤ sp.slot (tr.time j) + 1 →
      j < i (m + 1) → sp.slot (tr.time j) ≤ (lk m x).slot + sp.k ∧
      Bs m ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeeps tr x j (Bs m)) :
    ∀ j, i 0 ≤ j → j ≤ i M → ∀ x ∈ H, ∃ m < M, i m ≤ j ∧ j ≤ i (m + 1) ∧
      lk m x ∈ (tr.state x j).ac.locks ∧ (Bs m).root = (lk m x).block := by
  intro j h0 hjM x hx
  have hex : ∃ m, j ≤ i (m + 1) := ⟨M - 1, by rw [Nat.sub_add_cancel hM]; exact hjM⟩
  classical
  let m := Nat.find hex
  have hm : j ≤ i (m + 1) := Nat.find_spec hex
  have hmM : m < M := by
    have := Nat.find_min' hex (m := M - 1) (by rw [Nat.sub_add_cancel hM]; exact hjM)
    omega
  have hlo : i m ≤ j := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h]; exact h0
    · have := Nat.find_min hex (m := m - 1) (by omega)
      rw [Nat.sub_add_cancel h] at this
      omega
  exact ⟨m, hmM, hlo, hm, (lock_keep_global_slot hrun hnc hf (lk m) (hBr m hmM) (hlslot m hmM)
    (hhold m hmM) (hcut m hmM) j hlo hm x hx).1, hBr m hmM x hx⟩

/-- **The common block `B` is a read live lock block of every honest cast in the segment.** Under
the premises of `lock_keep_global_slot`, an honest cast at cut `k` of a vote of slot
`slot(t_j) − 1` for `j ∈ [i₀, N)` is at a cut `k < j` with `slot(t_{i₀}) ≤ slot(t_k) + 1`, its
frame is the node's frame at `k`, and `B` is a live lock block of its read point. -/
theorem cast_reads_common (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ N : Nat}
    (lk : Fin sp.n → SA.Lock) (hBr : ∀ x ∈ H, B.root = (lk x).block)
    (hlslot : ∀ x ∈ H, sp.slot (tr.time i₀) ≤ (lk x).slot + 1)
    (hhold : ∀ x ∈ H, ∀ k ≤ i₀, sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 →
      lk x ∈ (tr.state x k).ac.locks)
    (hcut : ∀ x ∈ H, ∀ j, sp.slot (tr.time i₀) ≤ sp.slot (tr.time j) + 1 → j < N →
      sp.slot (tr.time j) ≤ (lk x).slot + sp.k ∧
      B ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeeps tr x j B)
    {j : Nat} (hij : i₀ ≤ j) (hjN : j < N) {x : Fin sp.n} (hxH : x ∈ H) {k : Nat}
    {ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} {e}
    (hc : SA.CastAt tr.projAC x k ℓ' e)
    (hs : (e.msg.slot : Int) = (sp.slot (tr.time j) : Int) - 1) :
    k < j ∧ sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 ∧
      ℓ'.frame = Node.frame (tr.state x k) ∧
      B ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hmono : ∀ {a b}, a ≤ b → sp.slot (tr.time a) ≤ sp.slot (tr.time b) := fun h =>
    SA.slot_mono sp (hrun.time_nonneg _) (hrun.time_mono h)
  have hkj : k < j := cast_lt_of_slot hrun hnc hxH hc hs
  have hsk : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hr hxH hc).2.1
  have hsl : sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 := by
    have := hmono hij
    omega
  obtain ⟨hk, hBk, hcK⟩ := hcut x hxH k hsl (by omega)
  have hcall : tr.CallAt x k (.ac ℓ') := projAC_callAt.1 hc.1
  have hfr : ℓ'.frame = Node.frame (tr.state x k) := (hrun.cutLaw _ hxH k _ hcall).1
  have hva : ℓ'.frame.viableAncestor B = B := by
    rw [hfr]
    exact viableAncestor_eq_self_run hrun hxH k hBk hcK
  have hBk' : B ∈ ℓ'.frame.tree := by
    rw [hfr]
    exact hBk
  refine ⟨hkj, hsl, hfr, ?_⟩
  by_cases hki : k < i₀
  · have hl := hhold x hxH k hki.le hsl
    rw [← projAC_state hrun.toLocalRun hxH] at hl
    have hls := hlslot x hxH
    have hsk' := hmono hki.le
    have htk : (tr.projAC).time k = tr.time k := rfl
    exact SA.mem_readPoint_liveLockBlocks_of_keep hr hxH hc hl hk hBk' (hBr x hxH) hva
      (Or.inl (by rw [htk]; omega))
  · obtain ⟨hl, hu⟩ := lock_keep_global_slot hrun hnc hf lk hBr hlslot hhold hcut k
      (by omega) (by omega) x hxH
    have hu' := hu (by omega) ℓ' hcall
    rw [← hfr] at hu'
    rw [← projAC_state hrun.toLocalRun hxH] at hl hu'
    exact SA.mem_readPoint_liveLockBlocks_of_keep hr hxH hc hl hk hBk' (hBr x hxH) hva
      (Or.inr hu')

/-- **Locks on blocks below a common lock block are kept.** Premises of `lock_keep_global_slot`
for the common block `B` (every honest `x` holds `lk x` on `B`), and, for each honest `y`, a
further lock `lkD y` on a block `D y` held at `i₀`, with: at every cut `j ∈ [i₀, N)` of `y`,
`lkD y` does not expire, `D y` is in the frame's tree and a frame regime keeps it; and
`D y ⪯ B` in the frame of every honest node at every cut `k < N` with
`slot(t_{i₀}) ≤ slot(t_k) + 1` (the casting frames of the votes `unlock` reads). Conclusion: at
every cut `j ∈ [i₀, N]` each honest `y` holds `lkD y`, and for `j < N` `unlock` does not move
`D y`. The locks of one chain are kept when every honest node also locks its top `B`: a vote
that reads `C ⪰ B ⪰ D y` has heads compatible with `D y`. Without the common top the keep step
fails: an honest vote that reads only `C ≺ D y` may have a head on a branch off `C` that
conflicts with `D y`, and a majority of such votes moves `D y` back (`unlock`). -/
theorem lock_keep_below (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ N : Nat}
    (lk : Fin sp.n → SA.Lock) (hBr : ∀ x ∈ H, B.root = (lk x).block)
    (hlslot : ∀ x ∈ H, sp.slot (tr.time i₀) ≤ (lk x).slot + 1)
    (hhold : ∀ x ∈ H, ∀ k ≤ i₀, sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 →
      lk x ∈ (tr.state x k).ac.locks)
    (hcut : ∀ x ∈ H, ∀ j, sp.slot (tr.time i₀) ≤ sp.slot (tr.time j) + 1 → j < N →
      sp.slot (tr.time j) ≤ (lk x).slot + sp.k ∧
      B ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeeps tr x j B)
    (D : Fin sp.n → SA.Blk sp.n (List (FG.Att sp.n))) (lkD : Fin sp.n → SA.Lock)
    (hDr : ∀ y ∈ H, (D y).root = (lkD y).block)
    (hbaseD : ∀ y ∈ H, lkD y ∈ (tr.state y i₀).ac.locks)
    (hcutD : ∀ y ∈ H, ∀ j, i₀ ≤ j → j < N → sp.slot (tr.time j) ≤ (lkD y).slot + sp.k ∧
      D y ∈ (tr.state y j).fg.toFrame.tree ∧ FrameKeeps tr y j (D y))
    (hDB : ∀ y ∈ H, ∀ z ∈ H, ∀ k, sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 → k < N →
      (Node.frame (tr.state z k)).Anc (D y) B) :
    ∀ j, i₀ ≤ j → j ≤ N → ∀ y ∈ H,
      lkD y ∈ (tr.state y j).ac.locks ∧ (j < N → UnlockKeeps tr y j (D y)) := by
  have hkeep : ∀ j, i₀ ≤ j → j < N → ∀ y ∈ H, UnlockKeeps tr y j (D y) := by
    intro j hij hjN y hy
    obtain ⟨-, hD, -⟩ := hcutD y hy j hij hjN
    refine unlockKeeps_of_reads hrun hnc hy hD hf fun x _ hxH hs => ?_
    refine readsLockAbove_of_live hrun hnc hxH fun k ℓ' e hc hm => ?_
    subst hm
    obtain ⟨hkj, hsl, hfr, hBl⟩ :=
      cast_reads_common hrun hnc hf lk hBr hlslot hhold hcut hij hjN hxH hc hs
    refine ⟨B, Or.inl hBl, ?_⟩
    rw [hfr]
    exact hDB y hy _ hxH k hsl (by omega)
  intro j hij hjN
  induction j, hij using Nat.le_induction with
  | base => exact fun y hy => ⟨hbaseD y hy, fun h => hkeep i₀ le_rfl h y hy⟩
  | succ j hij ih =>
    intro y hy
    obtain ⟨hl, -⟩ := ih (by omega) y hy
    obtain ⟨hk, hD, hc⟩ := hcutD y hy j hij (by omega)
    refine ⟨lock_keep_run_view hrun hy j hl hk hD (hDr y hy)
      (viableAncestor_eq_self_run hrun hy j hD hc)
      fun ℓ hℓ => Or.inr (hkeep j hij (by omega) y hy ℓ hℓ), fun h => ?_⟩
    exact hkeep (j + 1) (by omega) h y hy

end Consensus.Goldilocks.Compose

end
