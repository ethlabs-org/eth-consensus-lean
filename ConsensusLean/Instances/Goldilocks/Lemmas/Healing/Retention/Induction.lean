module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Cut
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot

public section

/-! # Goldilocks Healing, HR.4: the vote step, the induction and the assembly -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### The vote step -/

/-- The label of a high origin starts at or after `g` (`t_j ≥ c_z > ḡ ≥ g`). -/
theorem le_ts_of_highOrigin (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) : g ≤ sp.ts j := by
  have h₁ := cutZ_le_ts_of_highOrigin hp ho
  have h₂ := lt_cutZ sp g
  have h₃ := le_gbar g
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  linarith

/-- **The caches at a vote** (as C1.1's `state_caches`): at a cut at or after `t_{j+1}`, the
caches of an honest node's state are those after its last call, by `CacheInv` (the origin is
active there) when that call is at or after `a`, by HBoot (`boot_caches`) when it is before `a`,
and by activation (`activation_caches`) when there is no call since `t_{j+1}`. -/
theorem vote_state_caches (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) (hk : sp.ts (j + 1 : Nat) ≤ tr.time k) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.state y k).fg.hj →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B) := by
  classical
  have hex : ∃ k', sp.ts (j + 1 : Nat) ≤ tr.time k' := ⟨k, hk⟩
  have hk₁ : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hfirst : tr.FirstCutFrom (Nat.find hex) (sp.ts (j + 1 : Nat)) :=
    ⟨Nat.find_spec hex, fun k' hk' => not_le.mp (Nat.find_min hex hk')⟩
  have hboot : ∀ k₀, (∀ k' < k₀, tr.time k' < a) →
      Compatible (tr.HonestBlocks H) (tr.state y k₀).fg.F B ∧
        (HZ tr H g + 1 ≤ (tr.state y k₀).fg.hj →
          Compatible (tr.HonestBlocks H) (tr.state y k₀).fg.J B) := fun k₀ hk₀ => by
    obtain ⟨hj, hF⟩ := boot_caches hp hy hk₀
    exact ⟨hF x i j B ho, fun h => absurd (h.trans hj) (Nat.not_succ_le_self _)⟩
  rcases Compose.state_of_le (tr := tr) (y := y) hk₁ with h | ⟨k', hk', hk'k, hc, h⟩
  · rw [h]
    by_cases hta : sp.ts (j + 1 : Nat) ≤ a
    · exact hboot _ fun k' hk' => lt_of_lt_of_le (hfirst.2 k' hk') hta
    · exact activation_caches hp ho hy hfirst (not_le.mp hta)
        fun k' hk' => ih k' (lt_of_lt_of_le hk' hk₁)
  · rw [h]
    have hact : sp.ts (j + 1 : Nat) ≤ tr.time k' := hfirst.1.trans (hp.run.time_mono hk')
    by_cases hak : a ≤ tr.time k'
    · exact (cacheInv_iff.1 (ih k' hk'k).2) y hy hc hak x i j B ho (Or.inr hact)
    · obtain ⟨c, hc'⟩ := hc
      rw [← Trace.state_succ_of_call _ hc']
      exact hboot _ fun k'' hk'' =>
        lt_of_le_of_lt (hp.run.time_mono (Nat.lt_succ_iff.mp hk'')) (not_le.mp hak)

/-- **The fork-choice root at a vote is compatible with the origin**: it is `Σ.F` (compatible,
`vote_state_caches`), a high `Σ.J` (compatible, `vote_state_caches`), or a low `Σ.J`, which is
compatible by (K2) (`low_root_compatible`, or `B ⪯ fc_root`). -/
theorem vote_root_compatible (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot)
    (hK2 : (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hts' : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr (by rw [(SA.castAt_spec hr hy hc).2.1])
  have hts : sp.ts (j + 1 : Nat) ≤ tr.time k :=
    ((SA.ts_le_iff sp).mpr (by exact_mod_cast hj : ((j + 1 : Nat) : Int) ≤ e.msg.slot)).trans hts'
  have hcache := vote_state_caches hp k ih ho hy hts
  have hroot_eq : ℓ.frame.fcRoot = (tr.state y k).fg.fcRoot := by
    rw [Compose.frame_of_projAC hp.run hy hc.1]; rfl
  rw [hroot_eq] at hK2 ⊢
  by_cases hroot : (tr.state y k).fg.hmax = (tr.state y k).fg.hj + 1 ∧ ¬ (tr.state y k).fg.Contest
  · rw [Store.fcRoot, ite_eq_left hroot] at hK2 ⊢
    by_cases hlow : (tr.state y k).fg.hj ≤ HZ tr H g
    · rcases hK2 with ⟨D, hD, hBD, -⟩ | hBJ
      · exact low_root_compatible hp ho hy hc hj hroot hlow hD hBD
      · exact Or.inr hBJ
    · exact hcache.2 (by omega)
  · rw [Store.fcRoot, ite_eq_right hroot]
    exact hcache.1

/-- **C1.1 (i) at a vote, from a compatible root** (C1.1's `vote_viable`, with the compatibility
of `fc_root` with `B` as the premise instead of both caches): with (K2), `B` is in the viable voter
block tree or at or below `fc_root`. -/
theorem vote_viable_of_root (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ℓ e)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hcomp : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B)
    (hK2 : (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hfr := Compose.frame_of_projAC hrun hy hc.1
  rcases hK2 with ⟨D, hD, hBD, hvD⟩ | h
  · rcases hcomp with hfB | hBf
    · have hDt : D ∈ ℓ.frame.tree := hD.1
      have hFB := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
      have hBt := SA.frame_mem_of_between sp hU hΦ hΦU hDt hBD hFB
      have hΦBD := SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBD hDt
      have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
      refine Or.inl ⟨SA.voterBlockTree_anc hr hy hc D hD B hΦBD, hΦfB, D, hD, ?_, hΦBD⟩
      have hfD := hΦfB.trans hΦBD
      rw [hfr] at hDt hfD ⊢
      exact ⟨hDt.1, hDt.2, Anc.mono (fun X hX => hX.1) hfD, hvD⟩
    · exact Or.inr hBf
  · exact Or.inr h

/-- **C1.1 (ii) at a vote, height-scoped** (C1.1's `vote_extends` for a high origin, every slot
`> j` instead of the window `(j, m]`, and the premises one by one instead of `PersistPremises`,
whose `Clean` need not hold): when (i) holds at an honest vote of a slot `σ > j` and every honest
vote of a slot `> j` at an earlier cut extends `B`, the vote extends `B`: below `fc_root` by
requirement 1, otherwise by A1.2 for `σ = j + 1` (its stored-block form) and by A1.3 after. -/
theorem high_vote_extends (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hx : x ∈ H) (hfl : Compose.StoredFastLockAt tr x i j B CV) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hs : j < e.msg.slot)
    (hsync : tr.SyncRun H ΔF (sp.ts j) (sp.ts e.msg.slot + sp.Δ))
    (hcarry : e.msg.slot = j + 1 → ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV)
    (hcarryLater : ∀ m', e.msg.slot = m' + 1 → j < m' →
      ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m'))
    (hhalf : ∀ m', e.msg.slot = m' + 1 → j < m' →
      sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j' e', SA.VoteAt tr.projAC x' j' e' ∧ e'.msg.slot = m'}.ncard)
    (hfault : tr.FaultBound H (tr.time k))
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hprior : ∀ z ∈ H, ∀ j' < k, ∀ e', SA.VoteAt tr.projAC z j' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, hle⟩ := Compose.cast_head_fcRoot hr hy hc
  obtain ⟨-, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  by_cases hBf : Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot
  · exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  have hv := hviab.resolve_right hBf
  have h0 := hr.time_nonneg k
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr
    proposer ΔF (sp.ts j) (sp.ts e.msg.slot + sp.Δ) hrun.toLocalRun hsync
  have hfault' : SA.FaultBound tr.projAC H (tr.time k) := by
    unfold SA.FaultBound
    rw [← (Compose.joined_projection sp ro dg H tr proposer hrun y hy (tr.time k)).2.2]
    exact hfault
  have hearlier : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) k e.msg.slot B :=
    fun z hz j' hj' e' hv' hsl => hprior z hz j' hj' e' hv' (hsl ▸ hs)
  by_cases h1 : e.msg.slot = j + 1
  · obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := hfl
    have hΦwU : ℓw.frame.tree ⊆ tr.HonestBlocks H := by
      rcases hr.frameLaw x hx i ℓw hcw with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
    refine SA.first_transfer_stored sp hrun' hx hflD
      (hBD ▸ Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)) hy hc h1
      (Compose.syncAC_mono hsync0 le_rfl hle) (hcarry h1 hBf) hfault' ?_ ?_
    · rw [← h1]; exact Or.inl hv
    · rw [← h1]; exact hearlier
  · obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm' : j < m' := by omega
    refine SA.next_transfer sp _ ro H _ tr.projAC proposer hrun' m' y k B ℓ e hy hc hm' ?_
      (hhalf m' hm' hsm') (hcarryLater m' hm' hsm' hBf) hfault'
      (Compose.syncAC_mono hsync0 ((SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hsm'.le)) hle) ?_ ?_
    · intro z hz j' e' hv' hsl
      have hjk : j' < k := by
        by_contra hjk
        obtain ⟨ℓ', hc', he'⟩ := hv'
        have h₁ := (SA.castAt_spec hr hz ⟨hc', he'⟩).2.1
        have h₂ := SA.slot_mono sp h0 (hr.time_mono (not_lt.mp hjk))
        have h₃ := (SA.castAt_spec hr hy hc).2.1
        omega
      exact hprior z hz j' hjk e' hv' (by omega)
    · rw [← hm']; exact Or.inl hv
    · rw [← hm']; exact hearlier

/-- **The vote step** (§13 "Closing the first-violating-event induction"; §11 item 2 for the
votes through the ticks at `a_z`): (R3) at the honest votes of cut `k`, from the invariant at every
earlier cut: (K2) by R5 (`vote_height_lead`) and the root's compatibility
(`vote_root_compatible`) give (i) (`vote_viable_of_root`); (i), `Carry` (`first_carry`,
`later_carry`), the half committee and `f < h_t` after `c_z` (`Healthy(g)`) and the earlier votes
give (ii) (`high_vote_extends`). -/
theorem retention_vote_step (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') : VoteInv tr H g k := by
  refine voteInv_iff.2 fun x i j B ho y hy ℓ e hc hj => ?_
  obtain ⟨CV, hfl⟩ := ho.2.2.1
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hts : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr (by rw [(SA.castAt_spec hr hy hc).2.1])
  have hlate : ∀ m : Nat, j ≤ m → cutZ sp.toParams g ≤ sp.ts m := fun m hm =>
    (cutZ_le_ts_of_highOrigin hp ho).trans ((SA.ts_le_iff sp).mpr (by exact_mod_cast hm))
  have hK2 := vote_height_lead hp k ih ho hy hc hj
  have hvi := vote_viable_of_root hp.run hp.noColl hy hc
    (vote_root_compatible hp k ih ho hy hc hj hK2) hK2
  refine ⟨high_vote_extends hp.run hp.noColl ho.1 hfl hy hc hj
    (syncRun_of_gst hp.healthy.1 (le_ts_of_highOrigin hp ho))
    (fun h1 hroot => first_carry hp k ih ho hfl hy hc h1 hroot)
    (fun m' hm' hjm hroot => later_carry hp k ih ho hy hc hm' hjm hroot)
    (fun m' _ hjm => half_committee hp (hlate m' hjm.le))
    (fault_bound_late hp ((hlate _ hj.le).trans hts)) hvi
    (fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ h₁ =>
      ((voteInv_iff.1 (ih k' hk').1) x i j B ho z hz ℓ' e' ⟨hc', he'⟩ h₁).1), hvi⟩

/-! ### The join and the assembly -/

/-- **The join**: the invariant holds at every cut (strong induction on the cut index, F.5
(run)). -/
theorem retention_inv (hp : ResetPremises tr H proposer dg g ΔF a) :
    ∀ k, VoteInv tr H g k ∧ CacheInv tr H g a k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    exact ⟨retention_vote_step hp k ih, retention_cut_step hp k ih (retention_vote_step hp k ih)⟩

/-- **Two high origins are comparable** (§11 item 3, §13 "Activation uses earlier labels"), from
(R3) at the votes up to the later write: for labels `j < j'`, the later lock is supported by an
honest slot-`j'` vote (half of the committee, or three quarters, against `f < n/2`), which extends
`B` (`fastLock_compatible_of_votes`); for `j = j'`, two fast locks of one slot are compatible
(`fastLock_same_slot`, TSQ, with `Sync` from `GST(g)` since `t_j ≥ c_z`). The stored blocks are
ancestors of the selected ones. -/
theorem origins_compatible (hp : ResetPremises tr H proposer dg g ΔF a) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (ho' : HighOrigin tr H g x' i' j' B') (hjj : j ≤ j') (hv : ∀ k ≤ i', VoteInv tr H g k) :
    Compatible (tr.HonestBlocks H) B B' := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.healthy.2.2
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  have hsel : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
      {CV₀ : Set (SA.Vote sp.n)}, x₀ ∈ H → Compose.StoredFastLockAt tr x₀ i₀ j₀ B₀ CV₀ →
      ∃ D, SA.FastLockAt tr.projAC x₀ i₀ j₀ D CV₀ ∧ Anc (tr.HonestBlocks H) B₀ D := by
    rintro x₀ i₀ j₀ B₀ CV₀ hx₀ ⟨ℓ, D, hc, hfl, rfl⟩
    have hΦU : ℓ.frame.tree ⊆ tr.HonestBlocks H := by
      rcases hr.frameLaw x₀ hx₀ i₀ ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨k, ℓ', -, -, -, h⟩ <;>
        exact h.1.2
    exact ⟨D, hfl, Anc.mono hΦU (SA.anc_viableAncestor ℓ.frame D)⟩
  obtain ⟨CV, hst⟩ := ho.2.2.1
  obtain ⟨CV', hst'⟩ := ho'.2.2.1
  obtain ⟨D, hfl, hBD⟩ := hsel ho.1 hst
  obtain ⟨D', hfl', hBD'⟩ := hsel ho'.1 hst'
  rcases hjj.lt_or_eq with hlt | rfl
  · have hD'B : Compatible (tr.HonestBlocks H) D' B :=
      SA.fastLock_compatible_of_votes hrun' ho'.1 (Nat.lt_succ_self i') hfl' hf
        fun z hz k hk e hve hsl => by
          obtain ⟨ℓ, hc, he⟩ := hve
          exact (voteInv_iff.1 (hv k (Nat.lt_succ_iff.mp hk)) x i j B ho z hz ℓ e ⟨hc, he⟩
            (by omega)).1
    by_contra hn
    exact SA.not_compatible_of_anc hU hBD' hn hD'B.symm
  · have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
      tr proposer ΔF (sp.ts j) (sp.ts (j + 1 : Nat) + sp.Δ) hp.run.toLocalRun
      (syncRun_of_gst hp.healthy.1 (le_ts_of_highOrigin hp ho))
    rcases SA.fastLock_same_slot hrun' ho.1 hfl ho'.1 hfl' hsync hf with h | h
    · exact SA.anc_total hU (hBD.trans h) hBD'
    · exact SA.anc_total hU hBD (hBD'.trans h)

/-- **HR.4, height-scoped retention** (HBoot §11, JointRet §13, high records §16): (R1)'s
comparability from the votes (`origins_compatible`), (R1)'s rows (`high_rows`), (R2) and (R3) from
the invariant (`retention_inv`), (R4) from (R1) (`high_records`). -/
theorem height_scoped_retention : HeightScopedRetention := by
  intro sp ro proposer dg H tr g ΔF hrun hh hnc a ha
  have hp : ResetPremises tr H proposer dg g ΔF a := ⟨hrun, hh, hnc, ha⟩
  have hinv := retention_inv hp
  have hcomp : ∀ x i j B x' i' j' B', HighOrigin tr H g x i j B →
      HighOrigin tr H g x' i' j' B' → Compatible (tr.HonestBlocks H) B B' := by
    intro x i j B x' i' j' B' ho ho'
    rcases le_total j j' with h | h
    · exact origins_compatible hp ho ho' h fun k _ => (hinv k).1
    · exact (origins_compatible hp ho' ho h fun k _ => (hinv k).1).symm
  have hrows := high_rows hp
  exact ⟨hcomp, hrows,
    fun y hy k hc hk x i j B ho hik =>
      (cacheInv_iff.1 (hinv k).2) y hy hc hk x i j B ho (Or.inl hik),
    fun x i j B ho y hy k ℓ e hc hj => (voteInv_iff.1 (hinv k).1) x i j B ho y hy ℓ e hc hj,
    high_records hp hcomp hrows⟩

end Consensus.Goldilocks.Healing

end
