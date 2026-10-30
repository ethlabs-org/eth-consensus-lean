module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry

public section

/-! # Goldilocks Healing, HS.2: the settled setting and the common local facts

`hs234-exact-interface.md` §1 (the context `Γ`: `GoldilocksRun`, `HSShared`, `Catch(2Δ)`,
`Prop⁺(G_p)`, `SettledIn … w i₀ m c`) and §2 (the common local facts of HS.2–HS.4).

* The settled time facts (proved): `w + 4Δ ≤ t_a` (`slotA_spec`), a clean label `j`
  (`t_j ≥ w + 4Δ`) is after `ḡ` and after the cut `c_z` (`gbar_le_of_clean`,
  `cutZ_le_of_clean`), and from `Healthy(g)` alone, after `c_z`, `f < h_t`
  (`faultBound_of_healthy`) and the honest votes are half of the committee
  (`half_committee_of_healthy`); HR.4's `fault_bound_late` and `half_committee` restated over
  `HSShared` instead of `ResetPremises`.
* §2.1, exact `Carry` (proved from frozen viability): the root split `Σ.F ⪯ B` at a vote whose
  `fc_root` is not above a frozen-viable `B`; then the counted votes of a clean fast origin
  (`clean_fast_carry`), of a clean slow origin's result (`clean_slow_carry`) and of the preceding
  honest batch (`honest_batch_carry`) are carried by H.2's `carryAt_of_writer_catch`: a head the
  writer accepted after `ḡ` relays under `Sync` from `ḡ`, one accepted before `ḡ` was caught up
  by `ḡ + 2Δ` (`Catch(2Δ)`, `Σ.F` monotone).
* §2's open contracts: the frozen viability of a clean origin at a later in-phase vote
  (`clean_fast_viable`, `clean_slow_viable`, §2.1 "aligned witnesses") and the raw-result
  comparisons RR/RO (`raw_results_compatible`, `raw_result_optimistic_compatible`, §2.2). The
  viability contracts take the earlier in-phase honest votes of a later slot as extending the
  origin's block (the simultaneous event induction of §3 supplies it), which only weakens them.

The pre-`ḡ` acceptance relay of `GSTRun` is not used: `Sync` windows start at `ḡ`
(`syncRun_of_gst`), and pre-`ḡ` acceptances go through `Catch(2Δ)`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-! ### Settled time facts -/

/-- `w + 4Δ ≤ t_a`: the slot `a = slotA w` is a member of the set it is the least of. -/
theorem slotA_spec (sp : SAParams) (w : Time) : w + 4 * sp.Δ ≤ sp.ts (slotA sp w) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hne : {s : Nat | w + 4 * sp.Δ ≤ sp.ts s}.Nonempty := by
    refine ⟨(w + 4 * sp.Δ).toNat, ?_⟩
    change w + 4 * sp.Δ ≤ 4 * sp.Δ * (((w + 4 * sp.Δ).toNat : Nat) : Int)
    have h1 := Int.self_le_toNat (w + 4 * sp.Δ)
    have h2 : (0 : Int) ≤ ((w + 4 * sp.Δ).toNat : Int) := Int.natCast_nonneg _
    have h3 : (1 : Int) ≤ 4 * sp.Δ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h3 h2]
  exact Nat.sInf_mem hne

/-- A settled time is at least `ḡ + 8Δ`. -/
theorem gbar_add_le_of_settled (hw : SettledIn tr H g w i₀ m c) : gbar g + 8 * sp.Δ ≤ w :=
  (le_max_right _ _).trans hw.1.late

/-- A clean label starts after `ḡ`. -/
theorem gbar_le_of_clean (hw : SettledIn tr H g w i₀ m c) {j : Int}
    (hj : w + 4 * sp.Δ ≤ sp.ts j) : gbar g ≤ sp.ts j := by
  have := gbar_add_le_of_settled hw
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  linarith

/-- A clean label starts after the cut `c_z ≤ ḡ + 12Δ`. -/
theorem cutZ_le_of_clean (hw : SettledIn tr H g w i₀ m c) {j : Int}
    (hj : w + 4 * sp.Δ ≤ sp.ts j) : cutZ sp.toParams g ≤ sp.ts j := by
  have := gbar_add_le_of_settled hw
  have := cutZ_le sp g
  linarith

/-- A cut at a time `≥ w` is at or after the settled cut `i₀`. -/
theorem le_of_settled (hw : SettledIn tr H g w i₀ m c) {k : Nat} (hk : w ≤ tr.time k) :
    i₀ ≤ k := by
  by_contra h
  have := hw.2.1.2 k (not_le.1 h)
  linarith

/-- The phase holds on every shorter interval. -/
theorem PhaseOn.mono_right {k k' : Nat} (h : PhaseOn tr.projFG H i₀ k m c) (hk : k' ≤ k) :
    PhaseOn tr.projFG H i₀ k' m c :=
  fun k'' h₁ h₂ => h k'' h₁ (h₂.trans hk)

/-! ### `Healthy(g)` after the cut `c_z` (HR.4's facts over `HSShared`) -/

/-- An honest restart is at or before `t_{slot(ḡ)+1}` (`Healthy(g)`; HR.4's `restart_le`). -/
theorem restart_le_of_healthy (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hk : tr.RestartAt y k) :
    tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  by_contra hlt
  obtain ⟨u, -, -, hu, hprev⟩ := hrun.sleep_of_restart y hy k hk
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (SA.ts_le_iff_le_slot sp (gbar_nonneg g) ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr
      (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu (hs.healthy.2.1 y hy u hgu)
  · obtain ⟨j, _x, hne, hcs, -⟩ := hrun.tick_of_awake y hy _ ((gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [SAParams.ts]; ring⟩
      (hs.healthy.2.1 y hy _ hp₀)
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    have hjk : j < k := by
      by_contra h
      have := hrun.time_mono (not_lt.mp h)
      exact hlt (ht ▸ this)
    have := hprev j hjk ⟨_, hn, hl⟩
    exact hgu (by linarith)

/-- **`f < h_t` after the cut** (`Healthy(g)`; HR.4's `fault_bound_late`). -/
theorem faultBound_of_healthy (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    {t : Time} (ht : cutZ sp.toParams g ≤ t) : tr.FaultBound H t := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ t := (gbar_nonneg g).trans hgt
  have hs3 : sp.slot (gbar g) + 3 ≤ sp.slot t := by
    have h := (SA.ts_le_iff_le_slot sp ht0 ((sp.slot (gbar g) + 3 : Nat) : Int)).mp
      ((cutZ_eq sp g) ▸ ht)
    exact_mod_cast h
  have hsub : H ⊆ {y | y ∈ H ∧ tr.awake y t ∧ tr.JoinedAt y t} := by
    refine fun y hy => ⟨hy, hs.healthy.2.1 y hy t hgt, fun k hk _ => ?_⟩
    change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
    have he : sp.toParams.slotTime (sp.slot t - 1) = sp.ts ((sp.slot t - 1 : Nat) : Int) :=
      sp.slotTime_eq _
    refine ⟨by omega, (restart_le_of_healthy hrun hs hy hk).trans ?_⟩
    rw [he]
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hle : H.ncard ≤ tr.honestAwakeJoined H t := Set.ncard_le_ncard hsub
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hs.healthy.2.2
  have hn' : sp.n = sp.toParams.n := rfl
  have hpos := sp.toParams.hn
  unfold RunTrace.FaultBound
  omega

/-- **Half of the committee votes** in a slot `s'` with `t_{s'} ≥ c_z` (`Healthy(g)`; HR.4's
`half_committee`). -/
theorem half_committee_of_healthy (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    {s' : Nat} (hs' : cutZ sp.toParams g ≤ sp.ts s') :
    sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ sp.ts s' + sp.Δ := by have := lt_cutZ sp g; linarith
  have hsl : sp.slot (sp.ts s' + sp.Δ) = s' :=
    SA.slot_of_mem sp s' (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  have hs3 : sp.slot (gbar g) + 3 ≤ s' := by
    have h := (SA.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hs')
    exact_mod_cast h
  have hsub : H ⊆ {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'} := by
    intro y hy
    have hj : tr.JoinedAt y (sp.ts s' + sp.Δ) := fun k hk _ => by
      change 0 < sp.slot (sp.ts s' + sp.Δ) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts s' + sp.Δ) - 1)
      have he : sp.toParams.slotTime (sp.slot (sp.ts s' + sp.Δ) - 1) =
          sp.ts ((sp.slot (sp.ts s' + sp.Δ) - 1 : Nat) : Int) := sp.slotTime_eq _
      refine ⟨by omega, (restart_le_of_healthy hrun hs hy hk).trans ?_⟩
      rw [he]
      exact (SA.ts_le_iff sp).mpr (by omega)
    obtain ⟨k, e, hv, hes, -⟩ :=
      Compose.vote_of_awake_joined hrun hs.noColl hy (hs.healthy.2.1 y hy _ hgt) hj
    exact ⟨hy, k, e, hv, hes⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hs.healthy.2.2
  have hn' : sp.n = sp.toParams.n := rfl
  omega

/-! ### `Carry` from a writer: the root split and the pre-`ḡ` catch-up -/

/-- **The receiver-root split** (`hs234-exact-interface.md` §2.1): at an honest vote whose
`fc_root` is not above `B`, frozen viability of `B` puts `B` in the frame tree, so `Σ.F ⪯ B`. -/
private theorem frame_F_anc_of_viable (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    Anc (tr.HonestBlocks H) ℓ.frame.F B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hv.1
  exact (hΦ.rooted.2 B (hviab.resolve_right hroot).1.1).mono hΦU

/-- **A head accepted before `ḡ`**, read at a vote whose `Σ.F` it extends, at a time
`≥ ḡ + 2Δ`: `Catch(2Δ)` (with `Σ.F` monotone) gives its acceptance by the voter before
`ḡ + 2Δ`, at or before the vote. -/
private theorem accept_of_catch (hrun : GoldilocksRun dg H tr) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {kw : Nat} {Hv : SA.Blk sp.n (List (FG.Att sp.n))}
    (hkw : tr.projAC.AcceptAt x kw Hv) (hlt : tr.time kw < gbar g) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y k ℓ)
    (hk : gbar g + 2 * sp.Δ ≤ tr.time k) (hF : Anc (tr.HonestBlocks H) ℓ.frame.F Hv) :
    ∃ k' ≤ k, tr.projAC.AcceptAt y k' Hv ∧ tr.time k' < gbar g + 2 * sp.Δ := by
  classical
  obtain ⟨kw', rfl, hacc, ht⟩ := fg_accept_before hrun.toLocalRun hx hkw
  have hex : ∃ j, gbar g + 2 * sp.Δ ≤ tr.time j := ⟨k, hk⟩
  have hj₀ : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun j hj => not_le.1 (Nat.find_min hex hj)⟩
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hFk : ℓ.frame.F = (tr.state y k).fg.F := by
    rw [Compose.frame_of_projAC hrun hy hcall]; rfl
  obtain ⟨k', hk', hacc'⟩ := hc x hx kw' Hv hacc (ht ▸ hlt) y hy _ hj₀
    ((run_F_mono hrun.toLocalRun hy hle).trans (hFk ▸ hF))
  obtain ⟨hacc'', ht', -⟩ := ac_block_after hrun.toLocalRun hy hacc'
  exact ⟨k' + 1, by omega, hacc'', by rw [ht']; exact hj₀.2 k' hk'⟩

section Writer

variable {FGP : Type} {ro' : ReplayOrder sp FGP} {U : Set (SA.Blk sp.n FGP)}
  {T : SA.SATrace sp FGP ro'}

private theorem etime_lt {t t' : Time} : SA.ETime.of t < SA.ETime.of t' ↔ t < t' := by
  simp [SA.ETime.of]

private theorem etime_le {t t' : Time} : SA.ETime.of t ≤ SA.ETime.of t' ↔ t ≤ t' := by
  simp [SA.ETime.of]

/-- **A stamp is not earlier than the acceptance** (main's Sleepy `stamp_ge_of_accept`). -/
private theorem stamp_ge_of_accept (hr : ACLocalRun (SA.goldilocksSA sp FGP ro') H U T)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {B : SA.Blk sp.n FGP} (hk : T.AcceptAt y k B)
    (hB : B.root ≠ sp.genesisRoot) :
    ∀ c, k + 1 ≤ c → SA.ETime.of (T.time k) ≤ (T.state y c).blockStamp B.root := by
  have hpost : ∀ c (ℓ : ACLabel (SA.goldilocksSA sp FGP ro')), T.CallAt y c ℓ → k ≤ c →
      (ℓ.call = .block B ∨ SA.ETime.of (T.time k) ≤ (T.state y c).blockStamp B.root) →
      SA.ETime.of (T.time k) ≤ (T.post c).blockStamp B.root := by
    intro c ℓ hc hkc hpre
    have hΦ : FrameOK ℓ.frame := by
      rcases hr.frameLaw y hy c ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hp : T.post c =
        ((SA.goldilocksSA sp FGP ro').step y (T.state y c) ℓ.frame (T.time c) ℓ.call).1 := by
      rw [he]
    have htk : SA.ETime.of (T.time k) ≤ SA.ETime.of (T.time c) := etime_le.2 (hr.time_mono hkc)
    obtain ⟨hblk, -, hoth⟩ :=
      SA.step_blockStamp_eq ro' y (T.state y c) hΦ (hr.time_nonneg c) ℓ.call
    rw [hp]
    generalize ℓ.call = cl at hpre hblk hoth ⊢
    cases cl with
    | block B' =>
      rw [hblk B' rfl, Function.update_apply]
      split_ifs with h
      · exact htk
      · rcases hpre with hpre | hpre
        · cases hpre
          exact absurd rfl h
        · exact hpre
    | restart =>
      change _ ≤ (SA.acRestart sp ro' y (T.state y c) ℓ.frame (T.time c)).1.blockStamp B.root
      rcases ((SA.restart_state sp) FGP ro' y (T.state y c) ℓ.frame (T.time c) hΦ
        (hr.time_nonneg c)).2.2.2.2.2.2.2.2.2.2 B.root with h | ⟨h, -⟩
      · rw [h]; simp [SA.SAState.initial, hB]
      · rw [h]; exact htk
    | tick => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | message m => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | proposal => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
    | toFG => rw [hoth (fun _ => by simp) (by simp)]; exact hpre.resolve_left (by simp)
  intro c hc
  induction c, hc using Nat.le_induction with
  | base =>
    obtain ⟨ℓ, hcl, hcall⟩ := hk
    rw [Trace.state_succ_of_call T hcl]
    exact hpost k ℓ hcl le_rfl (Or.inl hcall)
  | succ c hkc ih =>
    by_cases hn : ∃ ℓ, T.CallAt y c ℓ
    · obtain ⟨ℓ, hcl⟩ := hn
      rw [Trace.state_succ_of_call T hcl]
      exact hpost c ℓ hcl (by omega) (Or.inr ih)
    · rw [Trace.state_succ_of_not T fun ℓ hcl => hn ⟨ℓ, hcl⟩]
      exact ih

/-- **What a result's writer did with its counted votes** (main's Sleepy `result_writer`, private
there): each was admitted (or sent) by the
writer at a time in `[t_s, t_s + 2Δ)` (its stamp, below the resolution time), and its head extends
the result and is genesis or was accepted by the writer before `t_s + 2Δ` (the head's stamp). -/
private theorem result_writer (hr : ACLocalRun (SA.goldilocksSA sp FGP ro') H U T)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {C : SA.Blk sp.n FGP} {CV : Set (SA.Vote sp.n)}
    (hR : SA.ResultAt T X i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit X k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, T.AcceptAt X k Hv ∧ T.time k < sp.ts s + 2 * sp.Δ) := by
  obtain ⟨ℓX, ⟨hcX, htick, -, -⟩, -, rfl⟩ := hR
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hΦXU : ℓX.frame.tree ⊆ U := by
    rcases hr.frameLaw X hX i₀ ℓX hcX with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
  rintro v ⟨hvp, -, hvres, R, hR, hRr, hCR⟩
  have hvs : v.slot = s := SA.state_pool_slot sp hr hX i₀ s v hvp
  -- the stamps of the vote and of its head are before `t_s + 2Δ`
  obtain ⟨hvst, hbst⟩ : (T.state X i₀).voteStamp v < SA.ETime.of (sp.ts s + 2 * sp.Δ) ∧
      (T.state X i₀).blockStamp v.head < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
    unfold SA.resolutionTime at hvres
    split at hvres
    · exact absurd hvres (by simp [SA.ETime.of])
    · split_ifs at hvres
      · exact absurd hvres (by simp [SA.ETime.of])
      · exact max_lt_iff.1 hvres
  refine ⟨hvs, ?_, R, hΦXU hR, hRr, Anc.mono hΦXU hCR, ?_⟩
  · rcases SA.pool_origin hr hX i₀ v (by rw [hvs]; exact hvp) with
      ⟨k, -, hsend, hst, hsl⟩ | ⟨k, -, ℓk, hck, -, hst, B, hB, hvB⟩
    · rw [hst, etime_lt] at hvst
      exact ⟨k, hsend, (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by rw [← hvs]; exact_mod_cast hsl), hvst⟩
    · -- a restart's vote is of a block of slot at most `slot(t_k) ≤ s`, so of slot below `s`
      exfalso
      rw [hst, etime_lt] at hvst
      have hBv := (SA.frame_validPayload sp hr hX hck B hB).1 v hvB
      have hBs := SA.frame_slot_le sp hr hX hck B hB
      have : ¬ ((s + 1 : Nat) : Int) ≤ sp.slot (T.time k) := fun h => by
        have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 h
        rw [hts] at this; linarith
      omega
  · rcases Compose.frame_anc_accepted hr hX i₀ ℓX hcX R hR R Relation.ReflTransGen.refl with
      hg | ⟨k, hk, hacc⟩
    · exact Or.inl hg
    · refine Or.inr ⟨k, hacc, not_le.1 fun hge => ?_⟩
      have hki : k < i₀ := by
        refine lt_of_le_of_ne hk ?_
        rintro rfl
        obtain ⟨ℓ', hc', hcall⟩ := hacc
        rw [Option.some.inj (hc'.2.symm.trans hcX.2), htick] at hcall
        cases hcall
      rw [← hRr] at hbst
      have h := (stamp_ge_of_accept hr hX hacc (SA.accept_ne_genesis sp hr hX hacc) i₀ hki).trans_lt
        hbst
      rw [etime_lt] at h
      linarith

end Writer

/-! ### §2.1: aligned witnesses and exact `Carry` (open contracts) -/

/-- **Frozen viability of a clean fast origin** (`hs234-exact-interface.md` §2.1 "aligned
witnesses", §3 first helper): under `Γ`, let `x` write at cut `i` in the phase a fast lock of a
clean label `j` (`t_j ≥ w + 4Δ`) with stored block `B`. At an in-phase honest vote of a slot
`> j`, before which every in-phase honest vote of a slot `> j` extends `B`, `B` is in the
viable voter block tree or at or below `fc_root`: a counted honest head extending the selection
has an effectively allowed witness held at its vote; HS.1 retains it, and relay places it in the
frozen domain before `t_j + 3Δ`. -/
theorem clean_fast_viable (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hi : PhaseOn tr.projFG H i₀ i m c) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (hjs : j < e.msg.slot) (hk : PhaseOn tr.projFG H i₀ k m c)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

/-- **Frozen viability of a clean slow origin** (`hs234-exact-interface.md` §2.1, §3 slow
helper): as `clean_fast_viable`, for a slow lock of label `j` with `t_{j−k+1} ≥ w + 4Δ` and
stored block `B` (an honest supporter of the slow selection supplies the retained frozen
witness). -/
theorem clean_slow_viable (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) (hi : PhaseOn tr.projFG H i₀ i m c)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (hjs : j < e.msg.slot) (hk : PhaseOn tr.projFG H i₀ k m c)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

/-- **`Carry` of a clean fast origin's counted votes** (`hs234-exact-interface.md` §2.1
"all-head Carry"): at an in-phase honest slot-`(j+1)` vote whose `fc_root` is not above `B`,
`Carry_y(j, CV)`: an honest counted head has an allowed descendant `D` with `F ⪯ D` (HS.1), so
`F ⪯ B` (else `B ⪯ F ⪯ fc_root`), and every counted head, Byzantine ones included, extends `B`;
the counted heads are resolved at the writer before `t_j + 2Δ` and relay (post-`ḡ`) or were caught
up at `w` before `t_j + 3Δ`; raw votes and the two-vote cap give the held votes. -/
theorem clean_fast_carry (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hi : PhaseOn tr.projFG H i₀ i m c) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (he : e.msg.slot = j + 1)
    (hk : PhaseOn tr.projFG H i₀ k m c)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hFB := frame_F_anc_of_viable hrun hs hy hv
    (clean_fast_viable hrun hs hc hp hw hx ho hj hi hy hv (by omega) hk hprior) hroot
  have hgj := gbar_le_of_clean hw hj
  have htk : sp.ts (j + 1 : Nat) ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [← he, (SA.castAt_spec hr hy hv).2.1])
  have hts : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨ℓw, D, hcw, hflD, rfl⟩ := ho
  have hBD : Anc (tr.HonestBlocks H) (ℓw.frame.viableAncestor D) D :=
    Anc.mono (SA.frameIn_of_callAt hr hx hcw).2 (SA.anc_viableAncestor _ D)
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr ΔF (gbar g) (sp.ts j + 2 * sp.Δ) hrun.toLocalRun (syncRun_of_gst hs.healthy.1 (le_gbar g))
  refine SA.carryAt_of_writer_catch hr hsync hgj le_rfl hx hy hv he fun v hvv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hDHv, h₃⟩ := fastLock_writer hr hx hflD v hvv
  have hFHv := hFB.trans (hBD.trans hDHv)
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, ?_⟩
  rcases h₃ with hgen | ⟨kw, hkw, hkwt⟩
  · exact Or.inl hgen
  by_cases hkg : gbar g ≤ tr.time kw
  · exact Or.inr (Or.inl ⟨kw, hkw, hkg, hkwt⟩)
  · obtain ⟨k', hk', hacc, hk't⟩ :=
      accept_of_catch hrun hc hx hkw (not_le.1 hkg) hy hv.1 (by linarith) hFHv
    exact Or.inr (Or.inr ⟨k', hk', hacc, by change tr.time k' < _; linarith⟩)

/-- **`Carry` of a clean slow origin's result votes** (`hs234-exact-interface.md` §2.1, §3 slow
helper): as `clean_fast_carry`, for the counted votes `CV` of every regular result `C` of the
writer's update (every counted head extends `C ⪰ S ⪰ B`, `S` the raw slow selection). -/
theorem clean_slow_carry (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) (hi : PhaseOn tr.projFG H i₀ i m c)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = j + 1) (hk : PhaseOn tr.projFG H i₀ k m c)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x i j C CV) (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hFB := frame_F_anc_of_viable hrun hs hy hv
    (clean_slow_viable hrun hs hc hp hw hx ho hj hi hy hv (by omega) hk hprior) hroot
  have hj' : w + 4 * sp.Δ ≤ sp.ts j :=
    hj.trans ((SA.ts_le_iff sp).2 (by have := sp.two_le_k; omega))
  have hgj := gbar_le_of_clean hw hj'
  have htk : sp.ts (j + 1 : Nat) ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [← he, (SA.castAt_spec hr hy hv).2.1])
  have hts : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- the stored block is below the slow selection, on the result's path
  have hBC : Anc (tr.HonestBlocks H) B C := by
    obtain ⟨ℓw, D, hcw, ⟨ℓs, C', ⟨hcs, -⟩, hC', -, hD, -⟩, rfl⟩ := ho
    obtain ⟨ℓr, ⟨hcr, -⟩, hCr, -⟩ := hC
    obtain rfl : ℓs = ℓw := Option.some.inj (hcs.2.symm.trans hcw.2)
    obtain rfl : ℓr = ℓs := Option.some.inj (hcr.2.symm.trans hcs.2)
    obtain rfl : C' = C := Option.some.inj (hC'.symm.trans hCr)
    have hΦU := (SA.frameIn_of_callAt hr hx hcw).2
    exact Anc.mono hΦU ((SA.anc_viableAncestor _ D).trans (SA.deepest_mem hD).1.1.2.2)
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr ΔF (gbar g) (sp.ts j + 2 * sp.Δ) hrun.toLocalRun (syncRun_of_gst hs.healthy.1 (le_gbar g))
  refine SA.carryAt_of_writer_catch hr hsync hgj le_rfl hx hy hv he fun v hvv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hCHv, h₃⟩ := result_writer hr hx hC v hvv
  have hFHv := hFB.trans (hBC.trans hCHv)
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, ?_⟩
  rcases h₃ with hgen | ⟨kw, hkw, hkwt⟩
  · exact Or.inl hgen
  by_cases hkg : gbar g ≤ tr.time kw
  · exact Or.inr (Or.inl ⟨kw, hkw, hkg, hkwt⟩)
  · obtain ⟨k', hk', hacc, hk't⟩ :=
      accept_of_catch hrun hc hx hkw (not_le.1 hkg) hy hv.1 (by linarith) hFHv
    exact Or.inr (Or.inr ⟨k', hk', hacc, by change tr.time k' < _; linarith⟩)

/-- **`Carry` of the preceding honest batch** (`hs234-exact-interface.md` §2.1 "all-head Carry",
§3 "the preceding common honest batch"): under `Γ`, if every honest vote of a clean slot `m'`
extends `B`, then at an in-phase honest slot-`(m'+1)` vote at which `B` is frozen-viable and not
at or below `fc_root`, `Carry_y(m', S_{m'})` holds for the honest slot-`m'` votes: `Σ.F ⪯ B` (the
root split), so every honest head is above `Σ.F`; each was accepted by its voter before its vote,
and relays (post-`ḡ`) or was caught up by `ḡ + 2Δ` (`Catch(2Δ)`). -/
theorem honest_batch_carry (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {m' : Nat} (hm' : w + 4 * sp.Δ ≤ sp.ts m')
    (hall : ∀ z ∈ H, ∀ k' e', SA.VoteAt tr.projAC z k' e' → e'.msg.slot = m' →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = m' + 1)
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m') := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl).localRun
  have hU := hr.coherent
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hF := frame_F_anc_of_viable hrun hs hy hv hviab hroot
  have hgm := gbar_le_of_clean hw hm'
  have htk : sp.ts (m' + 1 : Nat) ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [← he, (SA.castAt_spec hr hy hv).2.1])
  have hts : sp.ts (m' + 1 : Nat) = sp.ts m' + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr ΔF (gbar g) (sp.ts m' + 2 * sp.Δ) hrun.toLocalRun (syncRun_of_gst hs.healthy.1 (le_gbar g))
  have hone : ∀ v ∈ Compose.honestVotes tr H m',
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' {v} := by
    rintro v ⟨z, hz, k', e', ⟨ℓk, hck, he'⟩, rfl, hvs⟩
    change e'.msg.slot = m' at hvs
    have hk' := (SA.castAt_spec hr hz ⟨hck, he'⟩).2.1
    obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hall z hz k' e' ⟨ℓk, hck, he'⟩ hvs
    obtain ⟨⟨Hd, hHd, hHdr, -⟩, hkt⟩ := Compose.cast_head_fcRoot hr hz ⟨hck, he'⟩
    obtain rfl : Hd = Hv :=
      hU.1 ((SA.frameIn_of_callAt hr hz hck).2 hHd) hHv (hHdr.trans hHvr.symm)
    rw [hvs] at hkt
    change tr.time k' ≤ _ at hkt
    have hFHd := hF.trans hBHv
    refine SA.carryAt_of_writer_catch hr hsync hgm le_rfl hz hy hv he ?_
    rintro v rfl
    refine ⟨hvs, ⟨k', ⟨ℓk, hck, Or.inl ⟨e', he', rfl⟩⟩,
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg k') m').2 (by omega), by
        change tr.time k' < _; linarith⟩, Hd, hHv, hHvr, hFHd, ?_⟩
    rcases Compose.frame_anc_accepted hr hz k' ℓk hck Hd hHd Hd .refl with hg | ⟨k'', hk'', hacc⟩
    · exact Or.inl hg
    have hk''t : tr.time k'' < sp.ts m' + 2 * sp.Δ := by
      have := hr.time_mono hk''
      change tr.time k'' ≤ tr.time k' at this
      linarith
    by_cases hkg : gbar g ≤ tr.time k''
    · exact Or.inr (Or.inl ⟨k'', hacc, hkg, hk''t⟩)
    · obtain ⟨k₂, hk₂, hacc₂, hk₂t⟩ :=
        accept_of_catch hrun hc hz hacc (not_le.1 hkg) hy hv.1 (by linarith) hFHd
      exact Or.inr (Or.inr ⟨k₂, hk₂, hacc₂, by change tr.time k₂ < _; linarith⟩)
  exact ⟨hr.awake_of_call y hy k ℓ hv.1, (SA.castAt_spec hr hy hv).2.2.1,
    fun v hv' => (hone v hv').heads v rfl, fun v hv' => (hone v hv').holds v rfl⟩

/-! ### §2.2: raw-result comparisons (open contracts) -/

/-- **RR** (`hs234-exact-interface.md` §2.2; continuation §36): two raw regular results of one
clean label `j`, saved by honest writers in the settled phase (vetoed or not), are compatible:
transported supporters of one target are participants on the other side, and the two
strict-majority inequalities contradict disjoint support. -/
theorem raw_results_compatible (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x x' : Fin sp.n} (hx : x ∈ H) (hx' : x' ∈ H)
    {i i' j : Nat} {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {CV CV' : Set (SA.Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x i j C CV) (hC' : SA.ResultAt tr.projAC x' i' j C' CV')
    (hj : w + 4 * sp.Δ ≤ sp.ts j) (hi : PhaseOn tr.projFG H i₀ i m c)
    (hi' : PhaseOn tr.projFG H i₀ i' m c) :
    Compatible (tr.HonestBlocks H) C C' := by
  sorry

/-- **RO** (`hs234-exact-interface.md` §2.2; continuation §36): a raw regular result and an
optimistic lock of one clean label `j`, by honest writers in the settled phase, are compatible
(equivocation counts towards the optimistic threshold but cannot support a conflicting regular
majority). -/
theorem raw_result_optimistic_compatible (hrun : GoldilocksRun dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x x' : Fin sp.n} (hx : x ∈ H) (hx' : x' ∈ H)
    {i i' j : Nat} {C O : SA.Blk sp.n (List (FG.Att sp.n))} {CV OV : Set (SA.Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x i j C CV) (hO : SA.OptimisticLockAt tr.projAC x' i' j O OV)
    (hj : w + 4 * sp.Δ ≤ sp.ts j) (hi : PhaseOn tr.projFG H i₀ i m c)
    (hi' : PhaseOn tr.projFG H i₀ i' m c) :
    Compatible (tr.HonestBlocks H) C O := by
  sorry

end Consensus.Goldilocks.Healing

end
