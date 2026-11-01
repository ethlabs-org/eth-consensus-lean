module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockFloorStep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees

public section

/-! # Goldilocks: every honest node keeps a lock above `B₀` over an interval

consensus-lean#135 (WI-16), the floor form of `lock_keep_global`. The invariant is "each honest
`x` holds a lock of slot `js x` on a block `⪰ B₀` of its frame's tree" (`FloorAt`). The lock may
move (`live_locks` to its viable ancestor, `unlock` to its unlock target); it stays `⪰ B₀` when
`B₀` is its own viable ancestor and `unlock` keeps `B₀` (`SA.exists_step_locks_floor`). The
moved lock keeps its slot, so the no-expiry premise `slot(t_j) ≤ js x + k` bounds the interval.
The frame changes between cuts: the honest tree only grows, so a block `⪰ B₀` stays in the
frame's tree and `⪰ B₀` when `B₀` stays in the tree (`floor_frame_transport`). The vote
condition of `unlockKeeps_of_reads` for `B₀` holds because each honest cast reads its own floor
lock, a live lock block `⪰ B₀` (`SA.exists_readPoint_liveLockBlocks_floor`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The floor at node `y`, cut `i`: a lock of slot `j` on a block `⪰ B₀` of the frame's tree. -/
abbrev FloorAt (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat)
    (B₀ : SA.Blk sp.n (List (FG.Att sp.n))) (j : Nat) : Prop :=
  ∃ l ∈ (tr.state y i).ac.locks, l.slot = j ∧ ∃ B ∈ (tr.state y i).fg.toFrame.tree,
    B.root = l.block ∧ (tr.state y i).fg.toFrame.Anc B₀ B

/-- **A block above `B₀` stays above `B₀` in a later frame** that still holds `B₀`. -/
theorem floor_frame_transport (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {i i' : Nat} (hii' : i ≤ i') {B₀ B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB0 : B₀ ∈ (tr.state y i').fg.toFrame.tree) (hB : B ∈ (tr.state y i).fg.toFrame.tree)
    (h : (tr.state y i).fg.toFrame.Anc B₀ B) :
    B ∈ (tr.state y i').fg.toFrame.tree ∧ (tr.state y i').fg.toFrame.Anc B₀ B := by
  have hsub := tree_mono hrun.toLocalRun hy hii'
  have h1 : Anc (tr.state y i').fg.tree B₀ B := (h.mono fun X hX => hX.1).mono hsub
  exact ⟨⟨hsub hB.1, hB0.2.trans h1⟩, Anc.restrict hB0.2 h1⟩

/-- **The floor over one cut.** At an honest `y`, cut `i`: the floor, no expiry, `B₀` in the
trees at `i` and `i + 1` and its own viable ancestor at `i`, and `unlock` at the AC call's view
keeping `B₀` (or `slot(t_i) − 1 ≤ j`) give the floor at `i + 1`. -/
theorem floor_run_view (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat} (hfl : FloorAt tr y i B₀ j)
    (hk : sp.slot (tr.time i) ≤ j + sp.k) (hB0 : B₀ ∈ (tr.state y i).fg.toFrame.tree)
    (hB0' : B₀ ∈ (tr.state y (i + 1)).fg.toFrame.tree)
    (hva0 : (tr.state y i).fg.toFrame.viableAncestor B₀ = B₀)
    (hu : ∀ ℓ, tr.CallAt y i (.ac ℓ) → (sp.slot (tr.time i) : Int) - 1 ≤ j ∨
      SA.unlockTarget sp (Node.frame (tr.state y i))
        (SA.unlockView (ro := ro) (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)
          ℓ.call) ((sp.slot (tr.time i) : Int) - 1) B₀ = B₀) :
    FloorAt tr y (i + 1) B₀ j := by
  have hold : ∃ l ∈ (tr.state y (i + 1)).ac.locks, l.slot = j ∧
      ∃ B ∈ (tr.state y i).fg.toFrame.tree, B.root = l.block ∧
        (tr.state y i).fg.toFrame.Anc B₀ B := by
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := hrun.cutLaw y hy i c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        obtain ⟨hfr, hstep, -, -⟩ := hlaw
        rw [hfr] at hstep
        have := SA.exists_step_locks_floor (ro := ro) y ℓ.call
          (frameOK_state hrun.toLocalRun hy i) (hrun.time_nonneg i) hB0 hva0 hk (hu ℓ hc) hfl
        rw [hstep] at this
        exact this
      | fg ℓ =>
        cases ℓ with
        | block C acc =>
          cases acc with
          | true => rw [hlaw.2.2.1]; exact hfl
          | false => rw [hlaw.2]; exact hfl
        | attestation a => rw [hlaw.2.1]; exact hfl
        | attest C s =>
          cases s with
          | none => rw [hlaw.2]; exact hfl
          | some a => rw [hlaw.2.2]; exact hfl
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact hfl
  obtain ⟨l, hl, hj, B, hB, hBr, hB0B⟩ := hold
  obtain ⟨hB', hB0B'⟩ := floor_frame_transport hrun hy (Nat.le_succ i) hB0' hB hB0B
  exact ⟨l, hl, hj, B, hB', hBr, hB0B'⟩

/-- **Every honest node keeps a lock above `B₀` over `[i₀, N]`.** Premises: `2|Hᶜ| < n`; at
`i₀` each honest `x` has the floor for `B₀` with slot `js x`; at every cut `j ∈ [i₀, N)` of
every honest `x`, `slot(t_j) ≤ js x + k`, `B₀` is in the frame's tree and a frame regime keeps
it (`FrameKeeps`); `B₀` is in the frame's tree at `N`; every honest cast before `i₀` of a slot at
least `slot(t_{i₀}) − 1` reads a live lock block or `fc_root` above `B₀`. Conclusion: at every
cut `j ∈ [i₀, N]` each honest `x` has the floor, and for `j < N` `unlock` at `x`'s call at `j`
keeps `B₀`. -/
theorem lock_floor_global (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ N : Nat}
    (js : Fin sp.n → Nat) (hbase : ∀ x ∈ H, FloorAt tr x i₀ B₀ (js x))
    (hcut : ∀ x ∈ H, ∀ j, i₀ ≤ j → j < N → sp.slot (tr.time j) ≤ js x + sp.k ∧
      B₀ ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeeps tr x j B₀)
    (hN : ∀ x ∈ H, B₀ ∈ (tr.state x N).fg.toFrame.tree)
    (hearly : ∀ x ∈ H, ∀ k < i₀, sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 →
      ∀ (ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) e,
      SA.CastAt tr.projAC x k ℓ' e →
      ∃ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k) ∪ {ℓ'.frame.fcRoot},
        ℓ'.frame.Anc B₀ C) :
    ∀ j, i₀ ≤ j → j ≤ N → ∀ x ∈ H,
      FloorAt tr x j B₀ (js x) ∧ (j < N → UnlockKeeps tr x j B₀) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hij hjN y hy
  -- the floor at `j`
  have hfl : FloorAt tr y j B₀ (js y) := by
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact hbase y hy
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨hl, hu⟩ := ih j' (by omega) (by omega) (by omega) y hy
      obtain ⟨hk, hB, hc⟩ := hcut y hy j' (by omega) (by omega)
      have hB' : B₀ ∈ (tr.state y (j' + 1)).fg.toFrame.tree := by
        rcases Nat.eq_or_lt_of_le hjN with h | h
        · rw [h]
          exact hN y hy
        · exact (hcut y hy (j' + 1) (by omega) h).2.1
      exact floor_run_view hrun hy j' hl hk hB hB'
        (viableAncestor_eq_self_run hrun hy j' hB hc) fun ℓ hℓ => Or.inr (hu (by omega) ℓ hℓ)
  refine ⟨hfl, fun hjN' => ?_⟩
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
  have hva : ℓ'.frame.viableAncestor B₀ = B₀ := by
    rw [hfr]
    exact viableAncestor_eq_self_run hrun hxH k hBk hcK
  have hu' := hu (by omega) ℓ' hcall
  rw [← hfr] at hu'
  replace hBk : B₀ ∈ ℓ'.frame.tree := by
    rw [hfr]
    exact hBk
  have hl' : ∃ l ∈ (tr.projAC.state e.msg.val k).locks, l.slot = js e.msg.val ∧
      ∃ B ∈ ℓ'.frame.tree, B.root = l.block ∧ ℓ'.frame.Anc B₀ B := by
    rw [hfr, projAC_state hrun.toLocalRun hxH]
    exact hl
  rw [← projAC_state hrun.toLocalRun hxH] at hu'
  obtain ⟨C, hC, hB0C⟩ := SA.exists_readPoint_liveLockBlocks_floor hr hxH hc hBk hva hk
    (Or.inr hu') hl'
  exact ⟨C, Or.inl hC, hB0C⟩

/-- **The floor from slot `s₀ − 1` on: no early-read premise.** As `lock_floor_global` from
`i₀`, with `hearly` replaced by premises on the cuts `k ≤ i₀` with
`slot(t_{i₀}) ≤ slot(t_k) + 1`: each honest `x` has the floor there and, for `k < N`, the
per-cut premises of `hcut` hold; the floor slot is at least `slot(t_{i₀}) − 1` (`hlslot`), so
`unlock` at the casts before `i₀` (of slot `≤ slot(t_{i₀})`) does not move the floor lock. The
no-expiry part of `hcut` stays explicit: the moved lock keeps its slot `js x`, so the interval
covers slots up to `js x + k` only. -/
theorem lock_floor_global_slot (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ N : Nat}
    (js : Fin sp.n → Nat) (hlslot : ∀ x ∈ H, sp.slot (tr.time i₀) ≤ js x + 1)
    (hhold : ∀ x ∈ H, ∀ k ≤ i₀, sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 →
      FloorAt tr x k B₀ (js x))
    (hcut : ∀ x ∈ H, ∀ j, sp.slot (tr.time i₀) ≤ sp.slot (tr.time j) + 1 → j < N →
      sp.slot (tr.time j) ≤ js x + sp.k ∧
      B₀ ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeeps tr x j B₀)
    (hN : ∀ x ∈ H, B₀ ∈ (tr.state x N).fg.toFrame.tree) :
    ∀ j, i₀ ≤ j → j ≤ N → ∀ x ∈ H,
      FloorAt tr x j B₀ (js x) ∧ (j < N → UnlockKeeps tr x j B₀) := by
  intro j hij hjN
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hmono : ∀ {a b}, a ≤ b → sp.slot (tr.time a) ≤ sp.slot (tr.time b) := fun h =>
    SA.slot_mono sp (hrun.time_nonneg _) (hrun.time_mono h)
  refine lock_floor_global hrun hnc hf js (fun x hx => hhold x hx i₀ le_rfl (by omega))
    (fun x hx j hj hjN => hcut x hx j (by have := hmono hj; omega) hjN) hN ?_ j hij hjN
  intro x hx k hki hsk ℓ' e hc
  obtain ⟨hk, hBk, hcK⟩ := hcut x hx k hsk (by omega)
  have hl := hhold x hx k hki.le hsk
  have hcall : tr.CallAt x k (.ac ℓ') := projAC_callAt.1 hc.1
  have hfr : ℓ'.frame = Node.frame (tr.state x k) := (hrun.cutLaw _ hx k _ hcall).1
  have hva : ℓ'.frame.viableAncestor B₀ = B₀ := by
    rw [hfr]
    exact viableAncestor_eq_self_run hrun hx k hBk hcK
  replace hBk : B₀ ∈ ℓ'.frame.tree := by
    rw [hfr]
    exact hBk
  have hl' : ∃ l ∈ (tr.projAC.state x k).locks, l.slot = js x ∧
      ∃ B ∈ ℓ'.frame.tree, B.root = l.block ∧ ℓ'.frame.Anc B₀ B := by
    rw [hfr, projAC_state hrun.toLocalRun hx]
    exact hl
  have hls := hlslot x hx
  have hsk' := hmono hki.le
  have htk : (tr.projAC).time k = tr.time k := rfl
  obtain ⟨C, hC, hB0C⟩ := SA.exists_readPoint_liveLockBlocks_floor hr hx hc hBk hva hk
    (Or.inl (by rw [htk]; omega)) hl'
  exact ⟨C, Or.inl hC, hB0C⟩

/-- The early-read premise of `lock_floor_global` from cut `i₀`: every honest cast before `i₀`
of a slot at least `slot(t_{i₀}) − 1` reads a live lock block or `fc_root` above `B₀`. -/
abbrev EarlyReads (H : Set (Fin sp.n)) (tr : GoldilocksTrace sp ro) (i₀ : Nat)
    (B₀ : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ x ∈ H, ∀ k < i₀, sp.slot (tr.time i₀) ≤ sp.slot (tr.time k) + 1 →
    ∀ (ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) e,
    SA.CastAt tr.projAC x k ℓ' e →
    ∃ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k) ∪ {ℓ'.frame.fcRoot},
      ℓ'.frame.Anc B₀ C

/-- **The early reads move forward.** If the early reads hold from `i₀`, and at every cut
`k ∈ [i₀, i₁)` each honest `x` has the floor for `B₀` with some slot `j'`, no expiry
(`slot(t_k) ≤ j' + k`), `B₀` in the frame's tree, a frame regime keeping it and `unlock` keeping
it, then the early reads hold from `i₁ ≥ i₀`. A cast before `i₀` is the old premise; a cast in
`[i₀, i₁)` reads its own floor lock (`SA.exists_readPoint_liveLockBlocks_floor`). -/
theorem floor_early_step (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ i₁ : Nat} (h01 : i₀ ≤ i₁)
    (hearly : EarlyReads H tr i₀ B₀)
    (hmid : ∀ x ∈ H, ∀ k, i₀ ≤ k → k < i₁ → ∃ j', FloorAt tr x k B₀ j' ∧
      sp.slot (tr.time k) ≤ j' + sp.k ∧ B₀ ∈ (tr.state x k).fg.toFrame.tree ∧
      FrameKeeps tr x k B₀ ∧ UnlockKeeps tr x k B₀) :
    EarlyReads H tr i₁ B₀ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro x hx k hk hsk ℓ' e hc
  by_cases hki : k < i₀
  · refine hearly x hx k hki ?_ ℓ' e hc
    have := SA.slot_mono sp (hrun.time_nonneg i₀) (hrun.time_mono h01)
    omega
  obtain ⟨j', hl, hkk, hBk, hcK, hu⟩ := hmid x hx k (by omega) hk
  have hcall : tr.CallAt x k (.ac ℓ') := projAC_callAt.1 hc.1
  have hfr : ℓ'.frame = Node.frame (tr.state x k) := (hrun.cutLaw _ hx k _ hcall).1
  have hva : ℓ'.frame.viableAncestor B₀ = B₀ := by
    rw [hfr]
    exact viableAncestor_eq_self_run hrun hx k hBk hcK
  have hu' := hu ℓ' hcall
  rw [← hfr] at hu'
  replace hBk : B₀ ∈ ℓ'.frame.tree := by
    rw [hfr]
    exact hBk
  have hl' : ∃ l ∈ (tr.projAC.state x k).locks, l.slot = j' ∧
      ∃ B ∈ ℓ'.frame.tree, B.root = l.block ∧ ℓ'.frame.Anc B₀ B := by
    rw [hfr, projAC_state hrun.toLocalRun hx]
    exact hl
  rw [← projAC_state hrun.toLocalRun hx] at hu'
  obtain ⟨C, hC, hB0C⟩ := SA.exists_readPoint_liveLockBlocks_floor hr hx hc hBk hva hkk
    (Or.inr hu') hl'
  exact ⟨C, Or.inl hC, hB0C⟩

/-- **The floor over chained segments.** Segments `m < M` cover the cut intervals
`[i m, i (m+1)]` (`i` nondecreasing). Premises: `2|Hᶜ| < n`; at the first cut `i m` of each
segment each honest `x` has a fresh floor for `B₀` with slot `js m x` (`hbase`); at every cut
`j ∈ [i m, i (m+1))` of every honest `x`, `slot(t_j) ≤ js m x + k`, `B₀` is in the frame's tree
and a frame regime keeps it; `B₀` is in the frame's tree at each `i (m+1)`; the early reads hold
from `i 0` only. The early reads of segment `m + 1` come from the floor of segment `m`
(`floor_early_step`), so no slot bound on the fresh lock is needed. Conclusion: at every cut
`j ∈ [i 0, i M]` each honest `x` has the floor for `B₀` with slot `js m x` of a segment `m` with
`i m ≤ j ≤ i (m+1)`, and `unlock` keeps `B₀` for `j < i (m+1)`. -/
theorem lock_floor_chain (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (M : Nat) (hM : 0 < M)
    (i : Nat → Nat) (hi : ∀ m < M, i m ≤ i (m + 1)) (js : Nat → Fin sp.n → Nat)
    (hbase : ∀ m < M, ∀ x ∈ H, FloorAt tr x (i m) B₀ (js m x))
    (hcut : ∀ m < M, ∀ x ∈ H, ∀ j, i m ≤ j → j < i (m + 1) →
      sp.slot (tr.time j) ≤ js m x + sp.k ∧ B₀ ∈ (tr.state x j).fg.toFrame.tree ∧
      FrameKeeps tr x j B₀)
    (hN : ∀ m < M, ∀ x ∈ H, B₀ ∈ (tr.state x (i (m + 1))).fg.toFrame.tree)
    (hearly : EarlyReads H tr (i 0) B₀) :
    ∀ j, i 0 ≤ j → j ≤ i M → ∀ x ∈ H, ∃ m < M, i m ≤ j ∧ j ≤ i (m + 1) ∧
      FloorAt tr x j B₀ (js m x) ∧ (j < i (m + 1) → UnlockKeeps tr x j B₀) := by
  have hseg : ∀ m < M, EarlyReads H tr (i m) B₀ → ∀ j, i m ≤ j → j ≤ i (m + 1) → ∀ x ∈ H,
      FloorAt tr x j B₀ (js m x) ∧ (j < i (m + 1) → UnlockKeeps tr x j B₀) :=
    fun m hm he => lock_floor_global (i₀ := i m) (N := i (m + 1)) hrun hnc hf (js m)
      (hbase m hm) (hcut m hm) (hN m hm) he
  have hall : ∀ m < M, EarlyReads H tr (i m) B₀ := by
    intro m
    induction m with
    | zero => exact fun _ => hearly
    | succ m ih =>
      intro hm
      have he := ih (by omega)
      refine floor_early_step hrun hnc (hi m (by omega)) he fun x hx k hk hkN => ?_
      obtain ⟨hl, hu⟩ := hseg m (by omega) he k hk hkN.le x hx
      obtain ⟨hkk, hB, hc⟩ := hcut m (by omega) x hx k hk hkN
      exact ⟨js m x, hl, hkk, hB, hc, hu hkN⟩
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
  exact ⟨m, hmM, hlo, hm, hseg m hmM (hall m hmM) j hlo hm x hx⟩

end Consensus.Goldilocks.Compose

end
