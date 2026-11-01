module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal

public section

/-! # Goldilocks: the lock floor over segments with carried fresh floors and early votes

consensus-lean#135, item N4 (Compose part). `lock_floor_chain` asks for the fresh floor of each
segment at its first cut `i m`, for every honest node at once. A fresh floor is written at a
node's own update tick, which is a different cut for each node. Here the fresh floor of segment
`m + 1` may start at any cut `a ∈ [i m, i (m+1)]` of the node; it is carried to `i (m+1)` over
the cuts of segment `m`, where segment `m`'s floor gives `UnlockKeeps` (`floor_carry`).

Item N5: the early-read premise at `i 0` is weakened to `EarlyVotes`: an early honest vote
either read a lock above `B₀` or has a head compatible with `B₀`. `unlock` needs only the
compatible heads (`SA.unlockTarget_unlockView_held_of_honest_slot`), so a unanimous slot on a
block `⪰ B₀` gives the premise (`earlyVotes_of_compat`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **`unlock` keeps `B` against honest votes that read a lock above it or have compatible
heads.** As `unlockKeeps_of_reads`, with each held honest vote of slot `slot(t_j) − 1` either
reading a lock above `B` or having only heads (in the frame's tree) compatible with `B`. -/
theorem unlockKeeps_of_reads_or_compat (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.toFrame.tree)
    (hf : 2 * Hᶜ.ncard < sp.n)
    (hread : ∀ x ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac
      (Node.frame (tr.state y j)), x.val ∈ H →
      (x.slot : Int) = (sp.slot (tr.time j) : Int) - 1 → ReadsLockAbove tr x B ∨
        ∀ Hd ∈ (Node.frame (tr.state y j)).tree, Hd.root = x.head →
          Compatible (Node.frame (tr.state y j)).tree Hd B) :
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
  refine SA.unlockTarget_unlockView_held_of_honest_slot y ℓ.call hA'
    (frameOK_state hrun.toLocalRun hy j) _ hB (hpool j) (hpool (j + 1)) hpay
    (fun x hx x' hx' hxH hval hs => heldVotes_honest_unique hrun hnc hy hcall hx hx' hxH hval hs)
    (fun x hx hxH hs => ?_) hf
  rcases hread x hx hxH hs with h | h
  · exact heldVote_compatible_of_cast hrun hnc hy hcall hB hx hxH h
  · exact h

/-- The early-vote premise from cut `i₀` (N5): every honest vote cast before `i₀` of a slot at
least `slot(t_{i₀}) − 1` read a live lock block or `fc_root` above `B₀` at each of its casts,
or its head is compatible with `B₀` in the frame of every honest node at every cut from `i₀`. -/
abbrev EarlyVotes (H : Set (Fin sp.n)) (tr : GoldilocksTrace sp ro) (i₀ : Nat)
    (B₀ : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ x ∈ H, ∀ k < i₀, ∀ e, SA.VoteAt tr.projAC x k e →
    sp.slot (tr.time i₀) ≤ e.msg.slot + 1 →
    (∀ ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro), SA.CastAt tr.projAC x k ℓ' e →
      ∃ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k) ∪ {ℓ'.frame.fcRoot},
        ℓ'.frame.Anc B₀ C) ∨
    ∀ y ∈ H, ∀ j, i₀ ≤ j → ∀ Hd ∈ (Node.frame (tr.state y j)).tree, Hd.root = e.msg.head →
      Compatible (Node.frame (tr.state y j)).tree Hd B₀

/-- The early reads give the early votes. -/
theorem earlyVotes_of_reads (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ : Nat} (hearly : EarlyReads H tr i₀ B₀) :
    EarlyVotes H tr i₀ B₀ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro x hx k hk e _ hs
  refine Or.inl fun ℓ' hc => hearly x hx k hk ?_ ℓ' e hc
  have hsk : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hr hx hc).2.1
  omega

/-- **Honest votes compatible with `B₀` give the early votes** (N5, the form of
lean-plan-next §4): every honest vote before `i₀` of a slot at least `slot(t_{i₀}) − 1` has its
head compatible with `B₀` in every honest frame from `i₀` on. -/
theorem earlyVotes_of_compat {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ : Nat}
    (hvotes0 : ∀ x ∈ H, ∀ k < i₀, ∀ e, SA.VoteAt tr.projAC x k e →
      sp.slot (tr.time i₀) ≤ e.msg.slot + 1 →
      ∀ y ∈ H, ∀ j, i₀ ≤ j → ∀ Hd ∈ (Node.frame (tr.state y j)).tree, Hd.root = e.msg.head →
        Compatible (Node.frame (tr.state y j)).tree Hd B₀) :
    EarlyVotes H tr i₀ B₀ :=
  fun x hx k hk e hv hs => Or.inr (hvotes0 x hx k hk e hv hs)

/-- **The early votes move forward** (`floor_early_step` for `EarlyVotes`). -/
theorem floor_early_step_votes (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ i₁ : Nat} (h01 : i₀ ≤ i₁)
    (hearly : EarlyVotes H tr i₀ B₀)
    (hmid : ∀ x ∈ H, ∀ k, i₀ ≤ k → k < i₁ → ∃ j', FloorAt tr x k B₀ j' ∧
      sp.slot (tr.time k) ≤ j' + sp.k ∧ B₀ ∈ (tr.state x k).fg.toFrame.tree ∧
      FrameKeeps tr x k B₀ ∧ UnlockKeeps tr x k B₀) :
    EarlyVotes H tr i₁ B₀ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro x hx k hk e hv hs
  by_cases hki : k < i₀
  · have := SA.slot_mono sp (hrun.time_nonneg i₀) (hrun.time_mono h01)
    rcases hearly x hx k hki e hv (by omega) with h | h
    · exact Or.inl h
    · exact Or.inr fun y hy j hj => h y hy j (by omega)
  refine Or.inl fun ℓ' hc => ?_
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

/-- **The floor over `[i₀, N]` from the early votes** (N5): `lock_floor_global` with
`EarlyReads` replaced by `EarlyVotes`. -/
theorem lock_floor_global_votes (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ N : Nat}
    (js : Fin sp.n → Nat) (hbase : ∀ x ∈ H, FloorAt tr x i₀ B₀ (js x))
    (hcut : ∀ x ∈ H, ∀ j, i₀ ≤ j → j < N → sp.slot (tr.time j) ≤ js x + sp.k ∧
      B₀ ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeeps tr x j B₀)
    (hN : ∀ x ∈ H, B₀ ∈ (tr.state x N).fg.toFrame.tree)
    (hearly : EarlyVotes H tr i₀ B₀) :
    ∀ j, i₀ ≤ j → j ≤ N → ∀ x ∈ H,
      FloorAt tr x j B₀ (js x) ∧ (j < N → UnlockKeeps tr x j B₀) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hij hjN y hy
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
  refine unlockKeeps_of_reads_or_compat hrun hnc hy hB hf fun v _ hvH hs => ?_
  classical
  by_cases hE : ∃ k < i₀, ∃ e, SA.VoteAt tr.projAC v.val k e ∧ e.msg = v ∧
      ∀ y' ∈ H, ∀ j', i₀ ≤ j' → ∀ Hd ∈ (Node.frame (tr.state y' j')).tree,
        Hd.root = e.msg.head → Compatible (Node.frame (tr.state y' j')).tree Hd B₀
  · obtain ⟨k, -, e, -, hm, h⟩ := hE
    refine Or.inr fun Hd hHd hr' => h y hy j hij Hd hHd ?_
    rw [hm]
    exact hr'
  refine Or.inl (readsLockAbove_of_live hrun hnc hvH fun k ℓ' e hc hm => ?_)
  subst hm
  have hkj : k < j := cast_lt_of_slot hrun hnc hvH hc hs
  have hsk : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hr hvH hc).2.1
  by_cases hki : k < i₀
  · have := SA.slot_mono sp (hrun.time_nonneg i₀) (hrun.time_mono hij)
    rcases hearly _ hvH k hki e ⟨ℓ', hc.1, hc.2⟩ (by omega) with h | h
    · exact h ℓ' hc
    · exact absurd ⟨k, hki, e, ⟨ℓ', hc.1, hc.2⟩, rfl, h⟩ hE
  obtain ⟨hl, hu⟩ := ih k hkj (by omega) (by omega) _ hvH
  obtain ⟨hk, hBk, hcK⟩ := hcut _ hvH k (by omega) (by omega)
  have hcall : tr.CallAt e.msg.val k (.ac ℓ') := projAC_callAt.1 hc.1
  have hfr : ℓ'.frame = Node.frame (tr.state e.msg.val k) :=
    (hrun.cutLaw _ hvH k _ hcall).1
  have hva : ℓ'.frame.viableAncestor B₀ = B₀ := by
    rw [hfr]
    exact viableAncestor_eq_self_run hrun hvH k hBk hcK
  have hu' := hu (by omega) ℓ' hcall
  rw [← hfr] at hu'
  replace hBk : B₀ ∈ ℓ'.frame.tree := by
    rw [hfr]
    exact hBk
  have hl' : ∃ l ∈ (tr.projAC.state e.msg.val k).locks, l.slot = js e.msg.val ∧
      ∃ B ∈ ℓ'.frame.tree, B.root = l.block ∧ ℓ'.frame.Anc B₀ B := by
    rw [hfr, projAC_state hrun.toLocalRun hvH]
    exact hl
  rw [← projAC_state hrun.toLocalRun hvH] at hu'
  obtain ⟨C, hC, hB0C⟩ := SA.exists_readPoint_liveLockBlocks_floor hr hvH hc hBk hva hk
    (Or.inr hu') hl'
  exact ⟨C, Or.inl hC, hB0C⟩

/-- **The floor is carried over an interval.** At an honest `y`, the floor of slot `j` at cut
`a`; at every cut `c ∈ [a, b)` no expiry, `B₀` in the frame's tree, a frame regime keeping it
and `unlock` keeping it; `B₀` in the frame's tree at `b`. Then the floor holds at `b`. -/
theorem floor_carry (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {j a b : Nat} (hab : a ≤ b)
    (hfl : FloorAt tr y a B₀ j)
    (hmid : ∀ c, a ≤ c → c < b → sp.slot (tr.time c) ≤ j + sp.k ∧
      B₀ ∈ (tr.state y c).fg.toFrame.tree ∧ FrameKeeps tr y c B₀ ∧ UnlockKeeps tr y c B₀)
    (hb : B₀ ∈ (tr.state y b).fg.toFrame.tree) : FloorAt tr y b B₀ j := by
  have key : ∀ d, a + d ≤ b → FloorAt tr y (a + d) B₀ j := by
    intro d
    induction d with
    | zero => intro _; exact hfl
    | succ d ih =>
      intro hd
      obtain ⟨hk, hB, hc, hu⟩ := hmid (a + d) (by omega) (by omega)
      have hB' : B₀ ∈ (tr.state y (a + d + 1)).fg.toFrame.tree := by
        rcases Nat.lt_or_ge (a + d + 1) b with h | h
        · exact (hmid _ (by omega) h).2.1
        · have he : a + d + 1 = b := by omega
          rw [he]
          exact hb
      exact floor_run_view hrun hy (a + d) (ih (by omega)) hk hB hB'
        (viableAncestor_eq_self_run hrun hy _ hB hc) fun ℓ hℓ => Or.inr (hu ℓ hℓ)
  have h := key (b - a) (by omega)
  rwa [Nat.add_sub_cancel' hab] at h

/-- **The floor over chained segments, fresh floors at any cut of the previous segment.** As
`lock_floor_chain` (with `EarlyVotes` at `i 0`), with `hbase` for `m ≥ 1` replaced by
`hfresh`: each honest `x` has the floor of slot `js (m+1) x` at some cut
`a ∈ [i m, i (m+1)]`, with no expiry on `[a, i (m+1))`.
Segment `m`'s floor gives `UnlockKeeps` there, so the fresh floor reaches `i (m+1)`. -/
theorem lock_floor_chain_carry (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (M : Nat) (hM : 0 < M)
    (i : Nat → Nat) (hi : ∀ m < M, i m ≤ i (m + 1)) (js : Nat → Fin sp.n → Nat)
    (hbase0 : ∀ x ∈ H, FloorAt tr x (i 0) B₀ (js 0 x))
    (hfresh : ∀ m, m + 1 < M → ∀ x ∈ H, ∃ a, i m ≤ a ∧ a ≤ i (m + 1) ∧
      FloorAt tr x a B₀ (js (m + 1) x) ∧
      ∀ c, a ≤ c → c < i (m + 1) → sp.slot (tr.time c) ≤ js (m + 1) x + sp.k)
    (hcut : ∀ m < M, ∀ x ∈ H, ∀ j, i m ≤ j → j < i (m + 1) →
      sp.slot (tr.time j) ≤ js m x + sp.k ∧ B₀ ∈ (tr.state x j).fg.toFrame.tree ∧
      FrameKeeps tr x j B₀)
    (hN : ∀ m < M, ∀ x ∈ H, B₀ ∈ (tr.state x (i (m + 1))).fg.toFrame.tree)
    (hearly : EarlyVotes H tr (i 0) B₀) :
    ∀ j, i 0 ≤ j → j ≤ i M → ∀ x ∈ H, ∃ m < M, i m ≤ j ∧ j ≤ i (m + 1) ∧
      FloorAt tr x j B₀ (js m x) ∧ (j < i (m + 1) → UnlockKeeps tr x j B₀) := by
  have hseg : ∀ m < M, (∀ x ∈ H, FloorAt tr x (i m) B₀ (js m x)) →
      EarlyVotes H tr (i m) B₀ → ∀ j, i m ≤ j → j ≤ i (m + 1) → ∀ x ∈ H,
      FloorAt tr x j B₀ (js m x) ∧ (j < i (m + 1) → UnlockKeeps tr x j B₀) :=
    fun m hm hb he => lock_floor_global_votes (i₀ := i m) (N := i (m + 1)) hrun hnc hf (js m) hb
      (hcut m hm) (hN m hm) he
  have hall : ∀ m < M,
      (∀ x ∈ H, FloorAt tr x (i m) B₀ (js m x)) ∧ EarlyVotes H tr (i m) B₀ := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨hbase0, hearly⟩
    | succ m ih =>
      intro hm
      obtain ⟨hb, he⟩ := ih (by omega)
      have hs := hseg m (by omega) hb he
      refine ⟨fun x hx => ?_,
        floor_early_step_votes hrun hnc (hi m (by omega)) he fun x hx k hk hkN => ?_⟩
      · obtain ⟨a, hma, hai, hfl, hk⟩ := hfresh m hm x hx
        refine floor_carry hrun hx hai hfl (fun c hac hc => ?_) (hN m (by omega) x hx)
        obtain ⟨-, hB, hcK⟩ := hcut m (by omega) x hx c (by omega) hc
        exact ⟨hk c hac hc, hB, hcK, (hs c (by omega) hc.le x hx).2 hc⟩
      · obtain ⟨hl, hu⟩ := hs k hk hkN.le x hx
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
  obtain ⟨hb, he⟩ := hall m hmM
  exact ⟨m, hmM, hlo, hm, hseg m hmM hb he j hlo hm x hx⟩

end Consensus.Goldilocks.Compose

end
