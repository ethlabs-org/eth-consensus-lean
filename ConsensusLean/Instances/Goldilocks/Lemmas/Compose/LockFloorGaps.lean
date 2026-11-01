module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorSegments
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.FrameKeepsCover

public section

/-! # Goldilocks: the lock floor over segments with expiry gaps

consensus-lean#137. `lock_floor_chain_carry` asks that the floor lock of segment `m` stays live
over the whole segment. When a floor lock expires before the fresh floor of the next segment is
written, there is a gap of cuts without a floor. In a gap, `unlock` keeps `B₀` when each honest
vote cast in a gap extends `B₀` (`hgap`): such a vote satisfies the compatible-head alternative
of `unlockKeeps_of_reads_or_compat`. Every other honest vote reads its caster's live floor lock.
The conclusion: the floor wherever its lock is live, and `UnlockKeeps` of `B₀` at every cut. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The early votes from cut `i₀` with a third alternative: the vote extends `B₀` in the honest
blocks. -/
abbrev EarlyVotesExt (H : Set (Fin sp.n)) (tr : GoldilocksTrace sp ro) (i₀ : Nat)
    (B₀ : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ x ∈ H, ∀ k < i₀, ∀ e, SA.VoteAt tr.projAC x k e →
    sp.slot (tr.time i₀) ≤ e.msg.slot + 1 →
    (∀ ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro), SA.CastAt tr.projAC x k ℓ' e →
      ∃ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k) ∪ {ℓ'.frame.fcRoot},
        ℓ'.frame.Anc B₀ C) ∨
    SA.VoteExtends (tr.HonestBlocks H) e.msg B₀ ∨
    ∀ y ∈ H, ∀ j, i₀ ≤ j → ∀ Hd ∈ (Node.frame (tr.state y j)).tree, Hd.root = e.msg.head →
      Compatible (Node.frame (tr.state y j)).tree Hd B₀

/-- `EarlyVotes` gives `EarlyVotesExt`. -/
theorem earlyVotesExt_of_earlyVotes {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ : Nat}
    (h : EarlyVotes H tr i₀ B₀) : EarlyVotesExt H tr i₀ B₀ :=
  fun x hx k hk e hv hs => (h x hx k hk e hv hs).imp_right Or.inr

/-- **A vote that extends `B₀` has heads compatible with `B₀`** in an honest frame that holds
`B₀`. -/
theorem compat_of_voteExtends (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B₀ ∈ (tr.state y j).fg.toFrame.tree) {v : SA.Vote sp.n}
    (h : SA.VoteExtends (tr.HonestBlocks H) v B₀) :
    ∀ Hd ∈ (Node.frame (tr.state y j)).tree, Hd.root = v.head →
      Compatible (Node.frame (tr.state y j)).tree Hd B₀ := by
  have hU := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hΦU : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocks H :=
    fun _ hX => ⟨y, hy, j, hX.1⟩
  intro Hd hHd hr
  obtain ⟨Hd', hHd', hr', hBH⟩ := h
  obtain rfl : Hd = Hd' := hU.1 (hΦU hHd) hHd' (hr.trans hr'.symm)
  exact Or.inr (SA.anc_tree_of_anc_U hU (frameOK_state hrun.toLocalRun hy j) hΦU hB hBH hHd)

/-- **The floor over `[i₀, N]` with an expiry gap.** As `lock_floor_global_votes`, without the
no-expiry premise: the floor of slot `js x` holds at each cut `j` with `slot(t_j) ≤ js x + k`,
and `unlock` keeps `B₀` at every cut of `[i₀, N)`. A vote cast by `x` at a cut of `[i₀, N)` after
its floor lock expired extends `B₀` (`hgap`). -/
theorem lock_floor_global_gaps (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ N : Nat}
    (js : Fin sp.n → Nat) (hbase : ∀ x ∈ H, FloorAt tr x i₀ B₀ (js x))
    (hcut : ∀ x ∈ H, ∀ j, i₀ ≤ j → j < N →
      B₀ ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeepsOrRoot tr x j B₀)
    (hN : ∀ x ∈ H, B₀ ∈ (tr.state x N).fg.toFrame.tree)
    (hgap : ∀ x ∈ H, ∀ k, i₀ ≤ k → k < N → js x + sp.k < sp.slot (tr.time k) →
      ∀ e, SA.VoteAt tr.projAC x k e → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    (hearly : EarlyVotesExt H tr i₀ B₀) :
    ∀ j, i₀ ≤ j → j ≤ N → ∀ x ∈ H,
      (sp.slot (tr.time j) ≤ js x + sp.k → FloorAt tr x j B₀ (js x)) ∧
      (j < N → UnlockKeeps tr x j B₀) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hij hjN y hy
  refine ⟨fun hsl => ?_, fun hjN' => ?_⟩
  · rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact hbase y hy
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hk : sp.slot (tr.time j') ≤ js y + sp.k := by
      have := SA.slot_mono sp (hrun.time_nonneg j') (hrun.time_mono (Nat.le_add_right j' 1))
      omega
    obtain ⟨hl, hu⟩ := ih j' (by omega) (by omega) (by omega) y hy
    obtain ⟨hB, hc⟩ := hcut y hy j' (by omega) (by omega)
    have hB' : B₀ ∈ (tr.state y (j' + 1)).fg.toFrame.tree := by
      rcases Nat.eq_or_lt_of_le hjN with h | h
      · rw [h]
        exact hN y hy
      · exact (hcut y hy (j' + 1) (by omega) h).1
    exact floor_run_view hrun hy j' (hl hk) hk hB hB'
      (viableAncestor_eq_self_of_keeps_or_root hrun hy j' hB hc)
      fun ℓ hℓ => Or.inr (hu (by omega) ℓ hℓ)
  obtain ⟨hB, -⟩ := hcut y hy j hij hjN'
  refine unlockKeeps_of_reads_or_compat hrun hnc hy hB hf fun v _ hvH hs => ?_
  classical
  by_cases hX : ∃ k e, SA.VoteAt tr.projAC v.val k e ∧ e.msg = v ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg B₀
  · obtain ⟨k, e, -, hm, h⟩ := hX
    exact Or.inr (compat_of_voteExtends hrun hnc hy hB (hm ▸ h))
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
    rcases hearly _ hvH k hki e ⟨ℓ', hc.1, hc.2⟩ (by omega) with h | h | h
    · exact h ℓ' hc
    · exact absurd ⟨k, e, ⟨ℓ', hc.1, hc.2⟩, rfl, h⟩ hX
    · exact absurd ⟨k, hki, e, ⟨ℓ', hc.1, hc.2⟩, rfl, h⟩ hE
  by_cases hkk : sp.slot (tr.time k) ≤ js e.msg.val + sp.k
  swap
  · exact absurd ⟨k, e, ⟨ℓ', hc.1, hc.2⟩, rfl,
      hgap _ hvH k (by omega) (by omega) (by omega) e ⟨ℓ', hc.1, hc.2⟩⟩ hX
  obtain ⟨hl, hu⟩ := ih k hkj (by omega) (by omega) _ hvH
  obtain ⟨hBk, hcK⟩ := hcut _ hvH k (by omega) (by omega)
  have hcall : tr.CallAt e.msg.val k (.ac ℓ') := projAC_callAt.1 hc.1
  have hfr : ℓ'.frame = Node.frame (tr.state e.msg.val k) :=
    (hrun.cutLaw _ hvH k _ hcall).1
  have hva : ℓ'.frame.viableAncestor B₀ = B₀ := by
    rw [hfr]
    exact viableAncestor_eq_self_of_keeps_or_root hrun hvH k hBk hcK
  have hu' := hu (by omega) ℓ' hcall
  rw [← hfr] at hu'
  replace hBk : B₀ ∈ ℓ'.frame.tree := by
    rw [hfr]
    exact hBk
  have hl' : ∃ l ∈ (tr.projAC.state e.msg.val k).locks, l.slot = js e.msg.val ∧
      ∃ B ∈ ℓ'.frame.tree, B.root = l.block ∧ ℓ'.frame.Anc B₀ B := by
    rw [hfr, projAC_state hrun.toLocalRun hvH]
    exact hl hkk
  rw [← projAC_state hrun.toLocalRun hvH] at hu'
  obtain ⟨C, hC, hB0C⟩ := SA.exists_readPoint_liveLockBlocks_floor hr hvH hc hBk hva hkk
    (Or.inr hu') hl'
  exact ⟨C, Or.inl hC, hB0C⟩

/-- **The early votes move forward over a segment with an expiry gap.** At each cut of
`[i₀, i₁)` an honest `x` has a live floor (with `unlock` keeping `B₀`), or its votes there
extend `B₀`. -/
theorem floor_early_step_gaps (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {i₀ i₁ : Nat} (h01 : i₀ ≤ i₁)
    (hearly : EarlyVotesExt H tr i₀ B₀)
    (hmid : ∀ x ∈ H, ∀ k, i₀ ≤ k → k < i₁ → (∃ j', FloorAt tr x k B₀ j' ∧
      sp.slot (tr.time k) ≤ j' + sp.k ∧ B₀ ∈ (tr.state x k).fg.toFrame.tree ∧
      FrameKeepsOrRoot tr x k B₀ ∧ UnlockKeeps tr x k B₀) ∨
      ∀ e, SA.VoteAt tr.projAC x k e → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀) :
    EarlyVotesExt H tr i₁ B₀ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro x hx k hk e hv hs
  by_cases hki : k < i₀
  · have := SA.slot_mono sp (hrun.time_nonneg i₀) (hrun.time_mono h01)
    rcases hearly x hx k hki e hv (by omega) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr fun y hy j hj => h y hy j (by omega))
  rcases hmid x hx k (by omega) hk with ⟨j', hl, hkk, hBk, hcK, hu⟩ | h
  swap
  · exact Or.inr (Or.inl (h e hv))
  refine Or.inl fun ℓ' hc => ?_
  have hcall : tr.CallAt x k (.ac ℓ') := projAC_callAt.1 hc.1
  have hfr : ℓ'.frame = Node.frame (tr.state x k) := (hrun.cutLaw _ hx k _ hcall).1
  have hva : ℓ'.frame.viableAncestor B₀ = B₀ := by
    rw [hfr]
    exact viableAncestor_eq_self_of_keeps_or_root hrun hx k hBk hcK
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

/-- `floor_carry` with `FrameKeepsOrRoot` (the R0 case added) at the cuts of `[a, b)`. -/
theorem floor_carry_root (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} {j a b : Nat} (hab : a ≤ b)
    (hfl : FloorAt tr y a B₀ j)
    (hmid : ∀ c, a ≤ c → c < b → sp.slot (tr.time c) ≤ j + sp.k ∧
      B₀ ∈ (tr.state y c).fg.toFrame.tree ∧ FrameKeepsOrRoot tr y c B₀ ∧ UnlockKeeps tr y c B₀)
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
        (viableAncestor_eq_self_of_keeps_or_root hrun hy _ hB hc) fun ℓ hℓ => Or.inr (hu ℓ hℓ)
  have h := key (b - a) (by omega)
  rwa [Nat.add_sub_cancel' hab] at h

/-- **The floor over chained segments with expiry gaps.** As `lock_floor_chain_carry` without
the no-expiry premise on the segments: a vote cast by `x` in segment `m` after the lock of slot
`js m x` expired extends `B₀` (`hgap`). Conclusion: the floor of slot `js m x` at the first cut
of each segment; at every cut `j ∈ [i 0, i M)`, in its segment `m`, the floor of slot `js m x`
while its lock is live, and `unlock` keeps `B₀`. -/
theorem lock_floor_chain_gaps (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (M : Nat) (hM : 0 < M)
    (i : Nat → Nat) (hi : ∀ m < M, i m ≤ i (m + 1)) (js : Nat → Fin sp.n → Nat)
    (hbase0 : ∀ x ∈ H, FloorAt tr x (i 0) B₀ (js 0 x))
    (hfresh : ∀ m, m + 1 < M → ∀ x ∈ H, ∃ a, i m ≤ a ∧ a ≤ i (m + 1) ∧
      FloorAt tr x a B₀ (js (m + 1) x) ∧
      ∀ c, a ≤ c → c < i (m + 1) → sp.slot (tr.time c) ≤ js (m + 1) x + sp.k)
    (hcut : ∀ m < M, ∀ x ∈ H, ∀ j, i m ≤ j → j < i (m + 1) →
      B₀ ∈ (tr.state x j).fg.toFrame.tree ∧ FrameKeepsOrRoot tr x j B₀)
    (hN : ∀ m < M, ∀ x ∈ H, B₀ ∈ (tr.state x (i (m + 1))).fg.toFrame.tree)
    (hgap : ∀ m < M, ∀ x ∈ H, ∀ k, i m ≤ k → k < i (m + 1) →
      js m x + sp.k < sp.slot (tr.time k) →
      ∀ e, SA.VoteAt tr.projAC x k e → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    (hearly : EarlyVotesExt H tr (i 0) B₀) :
    (∀ m < M, ∀ x ∈ H, FloorAt tr x (i m) B₀ (js m x)) ∧
    ∀ j, i 0 ≤ j → j < i M → ∀ x ∈ H, ∃ m < M, i m ≤ j ∧ j < i (m + 1) ∧
      (sp.slot (tr.time j) ≤ js m x + sp.k → FloorAt tr x j B₀ (js m x)) ∧
      UnlockKeeps tr x j B₀ := by
  have hseg : ∀ m < M, (∀ x ∈ H, FloorAt tr x (i m) B₀ (js m x)) →
      EarlyVotesExt H tr (i m) B₀ → ∀ j, i m ≤ j → j ≤ i (m + 1) → ∀ x ∈ H,
      (sp.slot (tr.time j) ≤ js m x + sp.k → FloorAt tr x j B₀ (js m x)) ∧
      (j < i (m + 1) → UnlockKeeps tr x j B₀) :=
    fun m hm hb he => lock_floor_global_gaps (i₀ := i m) (N := i (m + 1)) hrun hnc hf (js m) hb
      (hcut m hm) (hN m hm) (hgap m hm) he
  have hall : ∀ m < M,
      (∀ x ∈ H, FloorAt tr x (i m) B₀ (js m x)) ∧ EarlyVotesExt H tr (i m) B₀ := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨hbase0, hearly⟩
    | succ m ih =>
      intro hm
      obtain ⟨hb, he⟩ := ih (by omega)
      have hs := hseg m (by omega) hb he
      refine ⟨fun x hx => ?_,
        floor_early_step_gaps hrun hnc (hi m (by omega)) he fun x hx k hk hkN => ?_⟩
      · obtain ⟨a, hma, hai, hfl, hk⟩ := hfresh m hm x hx
        refine floor_carry_root hrun hx hai hfl (fun c hac hc => ?_) (hN m (by omega) x hx)
        obtain ⟨hB, hcK⟩ := hcut m (by omega) x hx c (by omega) hc
        exact ⟨hk c hac hc, hB, hcK, (hs c (by omega) hc.le x hx).2 hc⟩
      · by_cases hkk : sp.slot (tr.time k) ≤ js m x + sp.k
        · obtain ⟨hl, hu⟩ := hs k hk hkN.le x hx
          obtain ⟨hB, hc⟩ := hcut m (by omega) x hx k hk hkN
          exact Or.inl ⟨js m x, hl hkk, hkk, hB, hc, hu hkN⟩
        · exact Or.inr (hgap m (by omega) x hx k hk hkN (by omega))
  refine ⟨fun m hm => (hall m hm).1, fun j h0 hjM x hx => ?_⟩
  have hex : ∃ m, j < i (m + 1) := ⟨M - 1, by rw [Nat.sub_add_cancel hM]; exact hjM⟩
  classical
  let m := Nat.find hex
  have hm : j < i (m + 1) := Nat.find_spec hex
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
  have h := hseg m hmM hb he j hlo hm.le x hx
  exact ⟨m, hmM, hlo, hm, h.1, h.2 hm⟩

end Consensus.Goldilocks.Compose

end
