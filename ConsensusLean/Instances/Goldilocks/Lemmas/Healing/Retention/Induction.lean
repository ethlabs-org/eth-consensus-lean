module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Cut
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HR.4: the vote step, the induction and the assembly -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### The vote step -/

/-- At a bounded observation after activation, earlier bounded vote extension
already supplies both cache comparisons; cache hypotheses need not be assumed separately. -/
theorem ResetPremisesUpTo.vote_state_caches {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {k : Nat}
    (hvote : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
      ∀ z ∈ H, ∀ c < k, tr.time c ≤ b → ∀ e, SA.VoteAt tr.projAC z c e →
        j₀ < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    (hkb : tr.time k ≤ b) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (hib : tr.time i ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    (hk : sp.ts (j + 1 : Nat) ≤ tr.time k) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.state y k).fg.hj →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B) := by
  classical
  have hex : ∃ k', sp.ts (j + 1 : Nat) ≤ tr.time k' := ⟨k, hk⟩
  have hk₁ : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hfirst : tr.FirstCutFrom (Nat.find hex) (sp.ts (j + 1 : Nat)) :=
    ⟨Nat.find_spec hex, fun k' hk' => not_le.mp (Nat.find_min hex hk')⟩
  rcases Compose.state_of_le (tr := tr) (y := y) hk₁ with h | ⟨k', hk', hk'k, hc, h⟩
  · rw [h]
    exact hp.activation_caches ho hy hfirst hib ((hp.run.time_mono hk₁).trans hkb)
      (fun ho₀ hi₀ z hz c hc => hvote ho₀ hi₀ z hz c (lt_of_lt_of_le hc hk₁))
  · rw [h]
    exact hp.retention_cut_step
      (fun ho₀ hi₀ z hz c hc => hvote ho₀ hi₀ z hz c (lt_of_le_of_lt hc hk'k))
      ((hp.run.time_mono hk'k.le).trans hkb) hy hc ho hib
      (Or.inr (hfirst.1.trans (hp.run.time_mono hk')))

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
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B) :=
  (hp.toUpTo tr H (le_max_left a (max (tr.time k) (tr.time i)))).vote_state_caches
    (fun ho₀ _ z hz c hc _ e ⟨ℓ, hcl, he⟩ hsl =>
      ((voteInv_iff.1 (ih c hc).1) _ _ _ _ ho₀ z hz ℓ e ⟨hcl, he⟩ hsl).1)
    ((le_max_left _ _).trans (le_max_right _ _)) ho
    ((le_max_right _ _).trans (le_max_right _ _)) hy hk

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
theorem high_vote_extends_of_syncAC
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hx : x ∈ H) (hfl : Compose.StoredFastLockAt tr x i j B CV) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hs : j < e.msg.slot)
    (hsync0 : SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H)
      (sp.ts j) (tr.time k) tr.projAC)
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
      hsync0 (hcarry h1 hBf) hfault' ?_ ?_
    · rw [← h1]; exact Or.inl hv
    · rw [← h1]; exact hearlier
  · obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm' : j < m' := by omega
    refine SA.next_transfer sp _ ro H _ tr.projAC proposer hrun' m' y k B ℓ e hy hc hm' ?_
      (hhalf m' hm' hsm') (hcarryLater m' hm' hsm' hBf) hfault' ?_ ?_
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

/-- Node synchrony specialization of high-origin vote transfer. -/
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
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr
    proposer ΔF (sp.ts j) (sp.ts e.msg.slot + sp.Δ) hrun.toLocalRun hsync
  exact high_vote_extends_of_syncAC hrun hnc hx hfl hy hc hs
    (Compose.syncAC_mono hsync0 le_rfl (Compose.cast_head_fcRoot hr hy hc).2)
    hcarry hcarryLater hhalf hfault hviab hprior

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

/-- Vote extension with frozen viability or global root coverage at a bounded cut.
Global coverage deliberately allows targets below the frame's finalized root. -/
def RawVoteAt (P : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop) (Q : Time)
    (k : Nat) : Prop :=
  ∀ B j, P B j → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
    j < e.msg.slot → tr.time k ≤ Q → SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
      (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)

theorem rawVoteAt_iff (P : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop)
    (Q : Time) (k : Nat) : RawVoteAt (tr := tr) (H := H) P Q k ↔
    ∀ B j, P B j → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
      j < e.msg.slot → tr.time k ≤ Q → SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
        (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
          Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) := by rfl

/-- Activated raw targets compare with high origins at strictly earlier cuts. -/
def RawCompareAt (P : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop) (g : Time)
    (k : Nat) : Prop :=
  ∀ B j, P B j → sp.ts (j + 1 : Nat) ≤ tr.time k →
    ∀ x r l O, r < k → HighOrigin tr H g x r l O → Compatible (tr.HonestBlocks H) B O

theorem rawCompareAt_iff (P : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop)
    (g : Time) (k : Nat) : RawCompareAt (tr := tr) (H := H) P g k ↔
    ∀ B j, P B j → sp.ts (j + 1 : Nat) ≤ tr.time k →
      ∀ x r l O, r < k → HighOrigin tr H g x r l O →
        Compatible (tr.HonestBlocks H) B O := by rfl

/-- Bounded decreasing-cut assembly. Service, participant counts, cache geometry,
floor extraction and the local transfer steps are caller obligations, never obtained
from a globally assumed activation invariant. -/
theorem raw_vote_activation_before_core (hp : ResetPremises tr H proposer dg g ΔF a)
    (P : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop) (Q : Time)
    (hcompare : ∀ k, tr.time k ≤ Q →
      (∀ q < k, RawVoteAt (tr := tr) (H := H) P Q q) →
      RawCompareAt (tr := tr) (H := H) P g k)
    (hroot : ∀ k, RawCompareAt (tr := tr) (H := H) P g k →
      ∀ B j, P B j → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
        j < e.msg.slot → tr.time k ≤ Q → Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B)
    (hlow : ∀ k B j, P B j → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
      j < e.msg.slot → tr.time k ≤ Q → Anc (tr.HonestBlocks H) ℓ.frame.F B →
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ B.root).h →
      B ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)
    (hhigh : ∀ k, (∀ q < k, RawVoteAt (tr := tr) (H := H) P Q q) →
      RawCompareAt (tr := tr) (H := H) P g k →
      ∀ B j, P B j → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
        j < e.msg.slot → tr.time k ≤ Q → Anc (tr.HonestBlocks H) ℓ.frame.F B →
        ((tr.state y k).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor →
        ∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
          Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D)
    (htransfer : ∀ k, (∀ q < k, RawVoteAt (tr := tr) (H := H) P Q q) →
      ∀ B j, P B j → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
        j < e.msg.slot → tr.time k ≤ Q → SA.ViableAtVote ℓ e e.msg.slot B →
        SA.VoteExtends (tr.HonestBlocks H) e.msg B) :
    ∀ k, tr.time k ≤ Q → RawCompareAt (tr := tr) (H := H) P g k ∧
      RawVoteAt (tr := tr) (H := H) P Q k := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hprior : ∀ q < k, RawVoteAt (tr := tr) (H := H) P Q q := by
      intro q hq
      exact (ih q hq ((hr.time_mono hq.le).trans hk)).2
    have hcomp := hcompare k hk hprior
    refine ⟨hcomp, (rawVoteAt_iff P Q k).mpr ?_⟩
    intro B j hP y hy ℓ e hc hj htime
    have hroot' := hroot k hcomp B j hP y hy ℓ e hc hj htime
    obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
    by_cases hcovered : Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot
    · obtain ⟨⟨Hd, hHd, hHdr, hpath⟩, _⟩ := Compose.cast_head_fcRoot hr hy hc
      exact ⟨⟨Hd, hΦU hHd, hHdr, hcovered.trans (Anc.mono hΦU hpath)⟩, Or.inr hcovered⟩
    have hfcB := hroot'.resolve_right hcovered
    have hFB := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfcB
    have hK2 : ∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D := by
      by_cases hf : (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ B.root).h
      · exact ⟨B, hlow k B j hP y hy ℓ e hc hj htime hFB hf, .refl, hf⟩
      · exact hhigh k hprior hcomp B j hP y hy ℓ e hc hj htime hFB (not_le.mp hf)
    have hvi := (vote_viable_of_root hp.run hp.noColl hy hc hroot' (Or.inl hK2)).resolve_right
      hcovered
    exact ⟨htransfer k hprior B j hP y hy ℓ e hc hj htime (Or.inl hvi), Or.inl hvi⟩

/-- All high origins, including writes pending at the observing cut. -/
def HistoricalTargets (B : SA.Blk sp.n (List (FG.Att sp.n))) (j : Nat) : Prop :=
  ∃ x i, HighOrigin tr H g x i j B

theorem historicalTargets_iff (B : SA.Blk sp.n (List (FG.Att sp.n))) (j : Nat) :
    HistoricalTargets (tr := tr) (H := H) (g := g) B j ↔
      ∃ x i, HighOrigin tr H g x i j B := by rfl

/-- Bounded activation for all high origins. `cutZ` starts the service window; `a` remains
the actual reset time. No cache invariant, Catch, or global activation theorem is used. -/
theorem historical_activation_cutZ_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (Q : Time)
    (hsync : SyncACWindowBefore H (tr.HonestBlocks H) (cutZ sp.toParams g) Q tr.projAC) :
    ∀ k, tr.time k ≤ Q →
      RawCompareAt (tr := tr) (H := H) (HistoricalTargets (tr := tr) (H := H) (g := g)) g k ∧
      RawVoteAt (tr := tr) (H := H) (HistoricalTargets (tr := tr) (H := H) (g := g)) Q k := by
  let P := HistoricalTargets (tr := tr) (H := H) (g := g)
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have htime : ∀ {y k ell e j}, y ∈ H → SA.CastAt tr.projAC y k ell e → j < e.msg.slot →
      sp.ts (j + 1 : Nat) ≤ tr.time k := by
    intro y k ell e j hy hc hj
    have ht := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) e.msg.slot).mpr
      (by rw [(SA.castAt_spec hr hy hc).2.1])
    exact ((SA.ts_le_iff sp).mpr (by omega)).trans ht
  have hprior : ∀ k, tr.time k ≤ Q → (∀ q < k, RawVoteAt (tr := tr) (H := H) P Q q) →
      ∀ x i j B, HighOrigin tr H g x i j B → ∀ z ∈ H, ∀ q < k, ∀ e,
        SA.VoteAt tr.projAC z q e → j < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
    rintro k hk hv x i j B ho z hz q hq e ⟨ell, hc, he⟩ hj
    exact ((rawVoteAt_iff P Q q).mp (hv q hq) B j
      ((historicalTargets_iff B j).mpr ⟨x, i, ho⟩) z hz ell e ⟨hc, he⟩ hj
      ((hp.run.time_mono hq.le).trans hk)).1
  refine raw_vote_activation_before_core hp P Q ?_ ?_ ?_ ?_ ?_
  · intro k hk hv
    apply (rawCompareAt_iff P g k).mpr
    intro B j hB ht v r l O h rO
    obtain ⟨x, i, ho⟩ := (historicalTargets_iff B j).mp hB
    exact activated_origin_compatible_before hp (hprior k hk hv) ho ht rO h
  · intro k hcomp B j hB y hy ell e hc hj hk
    obtain ⟨x, i, ho⟩ := (historicalTargets_iff B j).mp hB
    by_cases hlow : (tr.state y k).fg.hj ≤ HZ tr H g
    · exact high_origin_low_J_root_before hp hsync ho hy hc hj hk hlow
    · exact high_J_root_of_origins_before hp ho hy hc (by omega)
        ((rawCompareAt_iff P g k).mp hcomp B j hB (htime hy hc hj))
  · intro k B j hB y hy ell e hc hj hk hF _
    obtain ⟨x, i, ho⟩ := (historicalTargets_iff B j).mp hB
    obtain ⟨CV, hst⟩ := ho.2.2.1
    obtain ⟨_, C, hfl, hBC⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
    obtain ⟨v, _, D, hDU, _, hBD, hacc⟩ := raw_writer_relay_source hr ho.1 (Or.inr hfl) hBC
    rcases hacc with hg | ⟨q, hq, hqt⟩
    · obtain ⟨z, hz, m, hDm⟩ := hDU
      exact False.elim ((cutZ_lt_of_anc hp ho hz hDm hBD).2 hg)
    · have hstart := (cutZ_lt_of_anc hp ho ho.1 (acceptAt_mem hp ho.1 hq) hBD).1.le
      have hD := relay_mem_voterBlockTree_window_after hr hsync ho.1 hy hq hstart hqt hc
        (by omega) hk (hF.trans hBD)
      obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
      have hBt := SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hD.1 hBD hF
      exact SA.voterBlockTree_anc hr hy hc D hD B
        (SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hBt hBD hD.1)
  · intro k hv hcomp B j hB y hy ell e hc hj hk hF hf
    obtain ⟨x, i, ho⟩ := (historicalTargets_iff B j).mp hB
    have hhist : HistoricalVoteExtensionBefore (tr := tr) (H := H) (g := g) k :=
      (historicalVoteExtensionBefore_iff k).mpr fun x i j B ho _ => hprior k hk hv x i j B ho
    obtain ⟨v, r, l, O, E, _, hO, hl, hE, hEO, hBO, hfloor⟩ :=
      high_floor_source_before hp ho hy hc hj
        (fun _ _ _ _ hr ho _ _ _ _ hr' ho' =>
          historical_origins_compatible_before hp hhist ho hr ho' hr')
        ((rawCompareAt_iff P g k).mp hcomp B j hB (htime hy hc hj)) hF
        ((high_origin_height_at_vote hp ho hy hc hj hF).trans_lt hf)
    exact raw_target_frozen_witness hp hO hy hc hl hF hBO hE hEO hfloor
  · intro k hv B j hB y hy ell e hc hj hk hvi
    obtain ⟨x, i, ho⟩ := (historicalTargets_iff B j).mp hB
    obtain ⟨CV, hfl⟩ := ho.2.2.1
    obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
    have hvi' : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot :=
      hvi.imp id (Anc.mono hPhiU)
    have hF : ¬ Anc (tr.HonestBlocks H) B ell.frame.fcRoot →
        Anc (tr.HonestBlocks H) ell.frame.F B := by
      intro hn
      have hb := hvi'.resolve_right hn
      exact (Anc.mono hPhiU hPhi.F_anc_fcRoot).trans (Anc.mono hPhiU hb.2.1)
    have hlate : ∀ m : Nat, j ≤ m → cutZ sp.toParams g ≤ sp.ts m := fun m hm =>
      (cutZ_le_ts_of_highOrigin hp ho).trans ((SA.ts_le_iff sp).mpr (by exact_mod_cast hm))
    have hts : sp.ts e.msg.slot ≤ tr.time k :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr (by rw [(SA.castAt_spec hr hy hc).2.1])
    exact high_vote_extends hp.run hp.noColl ho.1 hfl hy hc hj
      (syncRun_of_gst hp.healthy.1 (le_ts_of_highOrigin hp ho))
      (fun hs hn => first_carry_of_finalized_anc hp k ho hfl hy hc hs (hF hn))
      (fun m hm hjm hn => later_carry_of_finalized_anc hp k ho hy hc hm hjm (hF hn)
        (fun z hz q hq e' he hs => hprior k hk hv x i j B ho z hz q hq e' he (by omega)))
      (fun m _ hjm => half_committee hp (hlate m hjm.le))
      (fault_bound_late hp ((hlate _ hj.le).trans hts)) hvi' (hprior k hk hv x i j B ho)

/-- Node-level GST supplies cutZ-windowed service. A recipient deadline bounded by `Q`
bounds the source time too; no nonempty-window assumption is required. -/
theorem reset_sync_window_before (hp : ResetPremises tr H proposer dg g ΔF a) (Q : Time) :
    SyncACWindowBefore H (tr.HonestBlocks H) (cutZ sp.toParams g) Q tr.projAC := by
  have hg : g ≤ cutZ sp.toParams g := by
    have := le_gbar g
    have := lt_cutZ sp g
    have := sp.toParams.hΔ
    linarith
  have hs := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (cutZ sp.toParams g) Q hp.run.toLocalRun
    (syncRun_of_gst hp.healthy.1 hg)
  have hsource : ∀ y j (t : Time), t ≤ tr.projAC.deadline y j t := by
    intro y j t
    unfold ACTrace.deadline
    have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
    cases tr.projAC.lastWake y j with
    | bot => change t ≤ t + sp.Δ; linarith
    | coe w =>
      change t ≤ max t w + sp.Δ
      have := le_max_left t w
      linarith
  constructor
  · intro x hx i m hm hi y hy j ell hc hQ hd
    exact hs.1 x hx i m hm hi ((hsource y j _).trans hQ) y hy j ell hc hd
  · intro x hx i B hB hi y hy j ell hc hQ hd hF
    exact hs.2 x hx i B hB hi ((hsource y j _).trans hQ) y hy j ell hc hd hF

/-- Historical activation under the existing node reset premises. This does not supply
the engine-to-node Healthy/GST transport required to establish those premises. -/
theorem historical_activation_before (hp : ResetPremises tr H proposer dg g ΔF a) (Q : Time) :
    ∀ k, tr.time k ≤ Q →
      RawCompareAt (tr := tr) (H := H) (HistoricalTargets (tr := tr) (H := H) (g := g)) g k ∧
      RawVoteAt (tr := tr) (H := H) (HistoricalTargets (tr := tr) (H := H) (g := g)) Q k :=
  historical_activation_cutZ_before hp Q (reset_sync_window_before hp Q)

/-- Finite domain reduction with the earlier-origin comparisons left explicit.
The seed need only be comparable with the target, not cover it. -/
theorem ResetPremisesUpTo.held_target_vote_domain_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hS : HighOrigin tr H g v q m S) (hm : m < e.msg.slot)
    (hBS : Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocks H) B O)
    (hseedCompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocks H) S O)
    (hpair : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
      Compatible (tr.HonestBlocks H) O O') :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hroot : Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · exact hp.low_root_of_seed_before hx hBx hy hS hcast hm hlow hBS hheld
    · exact hp.high_J_root_of_held_at_call_before hx hBx hy hcast.1 (by omega) hcompare
  by_cases hcovered : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
  · exact Or.inl hcovered
  have hkeep : ∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W := by
    obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcast.1
    have hFB := (Anc.mono hPhiU hPhi.F_anc_fcRoot).trans (hroot.resolve_right hcovered)
    have hBt := hheld hFB
    have hBy := hp.frame_tree_subset hy hcast.1 hBt.1
    have hreach := Compose.fg_reachable hp.run.toLocalRun hy i
    by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
    · exact ⟨B, hBt, .refl, hfloor⟩
    have hBfloor := lt_of_not_ge hfloor
    obtain ⟨-, -, -, -, -, -, -, -, -, hSsrc⟩ := hp.highOrigin_mem hS
    by_cases hSf : (tr.state y i).fg.headHeightFloor ≤ ((tr.state v q).fg.σ S.root).h
    · have hBS' : Anc (tr.HonestBlocks H) B S := by
        rcases hBS with h | h
        · exact h
        · have hSy := hp.mem_tree_of_anc hy h hBy
          have hh := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hy h hBy)
          rw [← hp.σ_eq_run hS.1 hy hSsrc hSy] at hh
          omega
      have hSy := hp.high_origin_held_at_vote hS hy hcast hm (hFB.trans hBS')
      have hSf' : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ S.root).h := by
        rw [← hp.σ_eq_run hS.1 hy hSsrc hSy]
        exact hSf
      exact hp.raw_target_frozen_witness hS hy hcast hm hFB hBS' hSy .refl hSf'
    · obtain ⟨z, d, n, O, E, hd, ho, hn, hE, hEO, _, hEf⟩ :=
        hp.high_floor_source_core hS hy hcast hm hpair hseedCompare (lt_of_not_ge hSf)
      have hBO : Anc (tr.HonestBlocks H) B O := by
        rcases hcompare z d n O hd ho with h | h
        · exact h
        · have hh := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hy (hEO.trans h) hBy)
          omega
      exact hp.raw_target_frozen_witness ho hy hcast hn hFB hBO hE hEO hEf
  exact (vote_viable_of_root hp.run hp.noColl hy hcast hroot (Or.inl hkeep)).symm

/-- High origins written within the finite horizon retain every later-label honest
vote through that horizon. The origin write need not precede the receiving vote. -/
theorem ResetPremisesUpTo.high_origin_votes_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y k ell e → j < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hg : ∀ {x i j B}, HighOrigin tr H g x i j B → g ≤ sp.ts j := by
    intro x i j B ho
    have := hp.cutZ_le_ts_of_highOrigin ho
    have := lt_cutZ sp g
    have := le_gbar g
    have := sp.toParams.hΔ
    linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkb x i j B ho hib y hy ell e hc hj
    have prior : ∀ {x₀ i₀ j₀ B₀}, HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
        ∀ z ∈ H, ∀ c < k, tr.time c ≤ b → ∀ e', SA.VoteAt tr.projAC z c e' →
          j₀ < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B₀ := by
      rintro x₀ i₀ j₀ B₀ ho₀ hi₀ z hz c hck hcb e' ⟨ell', hc'⟩ hj'
      exact ih c hck hcb x₀ i₀ j₀ B₀ ho₀ hi₀ z hz ell' e' hc' hj'
    have hts : sp.ts e.msg.slot ≤ tr.time k :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr
        (by rw [(SA.castAt_spec hr hy hc).2.1])
    have hact : sp.ts (j + 1 : Nat) ≤ tr.time k :=
      ((SA.ts_le_iff sp).mpr (by omega)).trans hts
    have compare : ∀ z d n O, d < k → HighOrigin tr H g z d n O →
        Compatible (tr.HonestBlocks H) B O := by
      intro z d n O hd hO
      exact hp.origins_compatible_before prior ho (hg ho)
        (Or.inr fun c hct => not_le.mp fun hkc =>
          (not_lt_of_ge (hact.trans (hp.run.time_mono hkc))) hct)
        hO hd hib ((hp.run.time_mono hd.le).trans hkb)
    have pair : ∀ z d n O, d < k → HighOrigin tr H g z d n O →
        ∀ z' d' n' O', d' < k → HighOrigin tr H g z' d' n' O' →
        Compatible (tr.HonestBlocks H) O O' := by
      intro z d n O hd hO z' d' n' O' hd' hO'
      exact hp.origins_compatible_before prior hO (hg hO) (Or.inl hd) hO' hd'
        ((hp.run.time_mono hd.le).trans hkb) ((hp.run.time_mono hd'.le).trans hkb)
    obtain ⟨CV, hfl⟩ := ho.2.2.1
    obtain ⟨hBx, C, hraw, hBC⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hfl
    have held : Anc (tr.HonestBlocks H) ell.frame.F B →
        B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
      intro hFB
      obtain ⟨v, _, D, hDU, _, hBD, hacc⟩ := raw_writer_relay_source hr ho.1 (Or.inr hraw) hBC
      rcases hacc with hgen | ⟨q, hq, hqt⟩
      · obtain ⟨z, hz, d, hD⟩ := hDU
        exact False.elim ((hp.cutZ_lt_of_anc ho hz hD hBD).2 hgen)
      · have hqg : g ≤ tr.projAC.time q := by
          have := (hp.cutZ_lt_of_anc ho ho.1 (hp.acceptAt_mem ho.1 hq) hBD).1
          have := lt_cutZ sp g
          have := le_gbar g
          have := sp.toParams.hΔ
          change g ≤ tr.time q
          linarith
        have hDt := relay_mem_voterBlockTree hr (hp.sync.syncAC hp.run le_rfl)
          ho.1 hq hqg hqt le_rfl hy hc hj (hFB.trans hBD)
        obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
        have hBt := SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt.1 hBD hFB
        exact SA.voterBlockTree_anc hr hy hc D hDt B
          (SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hBt hBD hDt.1)
    have hvi := hp.held_target_vote_domain_before ho.1 hy hBx hc held ho hj
      (Or.inl .refl) compare compare pair
    have hF : ¬ Anc (tr.HonestBlocks H) B ell.frame.fcRoot →
        Anc (tr.HonestBlocks H) ell.frame.F B := by
      intro hn
      obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
      exact (hPhi.rooted.2 B (hvi.resolve_left hn).1.1).mono hPhiU
    apply high_vote_extends_of_syncAC hp.run hp.noColl ho.1 hfl hy hc hj
      (hp.sync.syncAC hp.run (hg ho))
      (fun hs hn => hp.first_carry_of_finalized_anc k ho hfl hy hc hs (hF hn))
      (fun m hm hjm hn => hp.later_carry_of_finalized_anc k ho hy hc hm hjm (hF hn)
        (fun z hz q hq e' hv hs => prior ho hib z hz q hq
          ((hp.run.time_mono hq.le).trans hkb) e' hv (by omega)))
      ?_ (fault_bound_late_before hp
        ((hp.cutZ_le_ts_of_highOrigin ho).trans
          (((SA.ts_le_iff sp).mpr (show (j : Int) ≤ e.msg.slot by omega)).trans hts)) hkb)
      hvi.symm ?_
    · intro m hm hjm
      apply hp.half_committee
        ((hp.cutZ_le_ts_of_highOrigin ho).trans ((SA.ts_le_iff sp).mpr (by omega)))
      have hnext : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      rw [hm, hnext] at hts
      have := sp.toParams.hΔ
      linarith
    · intro z hz q hq e' hv hs
      exact prior ho hib z hz q hq ((hp.run.time_mono hq.le).trans hkb) e' hv hs

/-- Any two actual high-origin writes within the horizon are compatible. -/
theorem ResetPremisesUpTo.origins_compatible {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x z : Fin sp.n} {i j r l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocks H) B O := by
  have hgj : g ≤ sp.ts j := by
    have := hp.cutZ_le_ts_of_highOrigin ho
    have := lt_cutZ sp g
    have := le_gbar g
    have := sp.toParams.hΔ
    linarith
  apply hp.origins_compatible_before (k := max i r + 1) ?_ ho hgj
    (Or.inl (by omega)) hO (by omega) hib hrb
  rintro x₀ i₀ j₀ B₀ ho₀ hi₀ y hy c _ hcb e ⟨ell, hc⟩ hj
  exact hp.high_origin_votes_before c hcb x₀ i₀ j₀ B₀ ho₀ hi₀ y hy ell e hc hj

set_option linter.unusedVariables false in
/-- **Two high origins are comparable** (§11 item 3, §13 "Activation uses earlier labels"), from
(R3) at the votes up to the later write: for labels `j < j'`, the later lock is supported by an
honest slot-`j'` vote (half of the committee, or three quarters, against `f < n/2`), which extends
`B` (`fastLock_compatible_of_votes`); for `j = j'`, two fast locks of one slot are compatible
(`fastLock_same_slot`, TSQ, with `Sync` from `GST(g)` since `t_j ≥ c_z`). The stored blocks are
ancestors of the selected ones. -/
theorem origins_compatible (hp : ResetPremises tr H proposer dg g ΔF a) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (ho' : HighOrigin tr H g x' i' j' B') (hjj : j ≤ j') (hv : ∀ k ≤ i', VoteInv tr H g k) :
    Compatible (tr.HonestBlocks H) B B' :=
  (hp.toUpTo tr H (le_max_left a (max (tr.time i) (tr.time i')))).origins_compatible ho
    ((le_max_left _ _).trans (le_max_right _ _)) ho' ((le_max_right _ _).trans (le_max_right _ _))

/-- **HR.4, height-scoped retention** (HBoot §11, JointRet §13, high records §16): (R1)'s
comparability from the votes (`origins_compatible`), (R1)'s attestations (`high_rows`), (R2) and
(R3) from the invariant (`retention_inv`), (R4) from (R1) (`high_records`). -/
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

/-- An actual bounded honest supporter compares its target with an older bounded origin. -/
theorem ResetPremisesUpTo.target_compatible_older_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x z : Fin sp.n} {r m q l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    {e : SA.Em sp (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hrb : tr.time r ≤ b)
    (hz : z ∈ H) (hv : SA.VoteAt tr.projAC z q e) (hqb : tr.time q ≤ b)
    (hs : e.msg.slot = l) (hml : m < l)
    (hB : SA.VoteExtends (tr.HonestBlocks H) e.msg B) :
    Compatible (tr.HonestBlocks H) B O := by
  obtain ⟨ell, hc⟩ := hv
  obtain ⟨HO, hHO, hOr, hOO⟩ :=
    hp.high_origin_votes_before q hqb x r m O ho hrb z hz ell e hc (by omega)
  obtain ⟨HB, hHB, hBr, hBB⟩ := hB
  obtain rfl : HO = HB := hp.honest_coherent.1 hHO hHB (hOr.trans hBr.symm)
  exact SA.anc_total hp.honest_coherent hBB hOO

/-- Conditional §75 domain reduction. The explicit producer hypotheses are the open
joint-induction boundary, not consequences asserted of reset premises. Frozen target
membership must be produced before its receiver height is read. -/
theorem held_target_vote_domain_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {r i : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hseed : ∃ v r₀ m S, HighOrigin tr H g v r₀ m S ∧ m < e.msg.slot ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v r₀ m O, r₀ < i → HighOrigin tr H g v r₀ m O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hroot : Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · obtain ⟨v, q, m, S, hS, hm, hBS⟩ := hseed
      exact low_root_of_seed_before hp hx hBx hy hS hcast hm hlow hBS hheld
    · exact high_J_root_of_held_before hp hx hBx hy hcast (by omega) hcompare
  refine ⟨hroot, ?_⟩
  by_cases hcovered : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
  · exact Or.inr hcovered
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcast.1
  have hFB := (Anc.mono hPhiU hPhi.F_anc_fcRoot).trans (hroot.resolve_right hcovered)
  have hBt := hheld hFB
  have hBy := frame_tree_subset hp hy hcast.1 hBt.1
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy i
  by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
  · exact Or.inl ⟨B, hBt, .refl, hfloor⟩
  have hBfloor := lt_of_not_ge hfloor
  obtain ⟨v, r₀, m, S, hS, hm, hBS⟩ := hseed
  obtain ⟨-, -, -, -, -, -, -, -, -, hSsrc⟩ := highOrigin_mem hp hS
  have orient : ∀ {z q n O E}, HighOrigin tr H g z q n O →
      E ∈ (tr.state y i).fg.tree → Anc (tr.HonestBlocks H) E O →
      (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ E.root).h →
      Compatible (tr.HonestBlocks H) B O → Anc (tr.HonestBlocks H) B O := by
    intro z q n O E _ hE hEO hEf hcomp
    rcases hcomp with h | h
    · exact h
    · have hEB := hEO.trans h
      have hh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy hEB hBy)
      omega
  by_cases hSf : (tr.state y i).fg.headHeightFloor ≤ ((tr.state v r₀).fg.σ S.root).h
  · have hBS' : Anc (tr.HonestBlocks H) B S := by
      rcases hBS with h | h
      · exact h
      · have hSy := mem_tree_of_anc hp hy h hBy
        have hh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy h hBy)
        rw [← σ_eq_run hp hS.1 hy hSsrc hSy] at hh
        omega
    have hSy := high_origin_held_at_vote hp hS hy hcast hm (hFB.trans hBS')
    have hSf' : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ S.root).h := by
      rw [← σ_eq_run hp hS.1 hy hSsrc hSy]
      exact hSf
    exact Or.inl (raw_target_frozen_witness hp hS hy hcast hm hFB hBS' hSy .refl hSf')
  · have hist : HistoricalVoteExtensionBefore (tr := tr) (H := H) (g := g) i := by
      apply (historicalVoteExtensionBefore_iff i).mpr
      intro z q n O ho _ w hw c _ e' hv hn
      obtain ⟨ell', hc', he'⟩ := hv
      exact ((rawVoteAt_iff _ _ _).mp
        (historical_activation_before hp (tr.time c) c le_rfl).2 O n
        ((historicalTargets_iff O n).mpr ⟨z, q, ho⟩) w hw ell' e' ⟨hc', he'⟩ hn le_rfl).1
    have hact : sp.ts (m + 1 : Nat) ≤ tr.time i := by
      have ht := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) e.msg.slot).mpr
        (by rw [(SA.castAt_spec hr hy hcast).2.1])
      exact ((SA.ts_le_iff sp).mpr (by omega)).trans ht
    have hScmp := (rawCompareAt_iff _ _ _).mp
      (historical_activation_before hp (tr.time i) i le_rfl).1 S m
      ((historicalTargets_iff S m).mpr ⟨v, r₀, hS⟩) hact
    obtain ⟨z, q, n, O, E, hq, ho, hn, hE, hEO, _, hEf⟩ :=
      high_floor_source_core hp hS hy hcast hm
        (fun _ _ _ _ hq ho _ _ _ _ hq' ho' =>
          historical_origins_compatible_before hp hist ho hq ho' hq')
        hScmp (lt_of_not_ge hSf)
    exact Or.inl (raw_target_frozen_witness hp ho hy hcast hn hFB
      (orient ho hE hEO hEf (hcompare z q n O hq ho)) hE hEO hEf)

/-- Slow-target specialization; the domain core needs actual heldness, not a slow tag. -/
theorem slow_target_vote_domain_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ)) (Q : Time)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {r l i : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsl : SA.SlowLockAt tr.projAC x r l B)
    (_hjoined : SA.JoinedAt tr.projAC x (tr.time r))
    (_hclean : sp.ts (sp.slot a + 3 : Nat) ≤ sp.ts ((l : Int) - sp.k + 1))
    (_hrQ : tr.time r ≤ Q)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (_hl : l < e.msg.slot) (_hiQ : tr.time i ≤ Q)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hseed : ∃ v r₀ m S, HighOrigin tr H g v r₀ m S ∧ m < e.msg.slot ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v r₀ m O, r₀ < i → HighOrigin tr H g v r₀ m O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot) := by
  obtain ⟨ellX, C, hupd, _, hdeep⟩ := hsl
  exact held_target_vote_domain_before hp hx hy
    (frame_tree_subset hp hx hupd.1 (SA.deepest_mem hdeep).1.1.1) hcast hheld hseed hcompare

/-- A later controlling high source compares with a prospective target from strictly
earlier head support. The target need not be a high origin or have been written yet. -/
theorem ResetPremisesUpTo.target_compatible_later_origin_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {r m i l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hri : r < i) (hlm : l < m)
    (hsupport : ∀ z ∈ H, ∀ q < i, ∀ e, SA.VoteAt tr.projAC z q e →
      l < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B) :
    Compatible (tr.HonestBlocks H) B O := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.faults
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  obtain ⟨CV, hst⟩ := ho.2.2.1
  obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
  have hcomp := SA.fastLock_compatible_of_votes hrun ho.1 hri hfl hf
    (fun z hz q hq e hv hs => hsupport z hz q hq e hv (by omega))
  rcases hcomp with hDB | hBD
  · exact Or.inr (hOD.trans hDB)
  · exact SA.anc_total hrun.localRun.coherent hBD hOD

/-- Whole-run specialization of the prior-support comparison. -/
theorem target_compatible_later_origin_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} {r m i l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hri : r < i) (hlm : l < m)
    (hsupport : ∀ z ∈ H, ∀ q < i, ∀ e, SA.VoteAt tr.projAC z q e →
      l < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B) :
    Compatible (tr.HonestBlocks H) B O :=
  (hp.toUpTo tr H (le_refl a)).target_compatible_later_origin_before ho hri hlm hsupport

/-- An actual honest target supporter compares the target with every strictly older
high origin. The participant-count adapter is responsible for supplying this vote. -/
theorem target_compatible_older_origin
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x z : Fin sp.n} {r m q l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    {e : SA.Em sp (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hz : z ∈ H) (hv : SA.VoteAt tr.projAC z q e)
    (hs : e.msg.slot = l) (hml : m < l)
    (hB : SA.VoteExtends (tr.HonestBlocks H) e.msg B) :
    Compatible (tr.HonestBlocks H) B O :=
  (hp.toUpTo tr H (le_max_left a (max (tr.time r) (tr.time q)))).target_compatible_older_origin
    ho ((le_max_left _ _).trans (le_max_right _ _)) hz hv
    ((le_max_right _ _).trans (le_max_right _ _)) hs hml hB

/-- §76 join: the remaining inputs are actual frozen service, an honest counted
supporter, a seed witness, same-label comparison, and prospective prior-cut support. -/
theorem slow_target_vote_domain_of_support_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (Q : Time)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {r l i : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsl : SA.SlowLockAt tr.projAC x r l B)
    (hjoined : SA.JoinedAt tr.projAC x (tr.time r))
    (hclean : sp.ts (sp.slot a + 3 : Nat) ≤ sp.ts ((l : Int) - sp.k + 1))
    (hrQ : tr.time r ≤ Q)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hl : l < e.msg.slot) (hiQ : tr.time i ≤ Q)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ m < l)
    (hcounted : ∃ z ∈ H, ∃ q e', SA.VoteAt tr.projAC z q e' ∧ e'.msg.slot = l ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hsame : ∀ v q O, q < i → HighOrigin tr H g v q l O →
      Compatible (tr.HonestBlocks H) B O)
    (hsupport : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
      l < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot) := by
  obtain ⟨z, hz, q, e', hv, hs, hB⟩ := hcounted
  refine slow_target_vote_domain_before hp hcatch Q hx hy hsl hjoined hclean hrQ
    hc hl hiQ hheld ?_ ?_
  · obtain ⟨v, r₀, m, S, hS, hm⟩ := hseed
    exact ⟨v, r₀, m, S, hS, by omega,
      target_compatible_older_origin hp hS hz hv hs hm hB⟩
  · intro v r₀ m O hri ho
    rcases lt_trichotomy m l with hm | rfl | hm
    · exact target_compatible_older_origin hp ho hz hv hs hm hB
    · exact hsame v r₀ O hri ho
    · exact target_compatible_later_origin_before hp ho hri hm hsupport

end Consensus.Goldilocks.Healing

end
