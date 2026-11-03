module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo

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
* §2.1, aligned witnesses (`viable_of_clean_vote`): an honest vote of a clean slot `j` that
  extends `B` makes `B` frozen-viable (or at or below `fc_root`) at every in-phase honest vote of
  a later slot. Its head lies in its voter's full viable tree (`fc_root` is there, by the phase's
  frontier block; `getAnchor_viable`), below a viable, hence effectively allowed
  (`viableHeads_iff`), head `W`; `W` relays (post-`ḡ`) or was caught up (`Catch(2Δ)`) into the
  later voter block tree, and HS.1 retains its ancestors. Hence `clean_fast_viable` (an honest
  counted vote, `fastLock_honest_vote`) and `clean_slow_viable` (an honest supporter of the
  result, `result_extended`); no induction hypothesis is needed.
* §2.1, exact `Carry`: the root split `Σ.F ⪯ B` at a vote whose `fc_root` is not above a
  frozen-viable `B`; then the counted votes of a clean fast origin (`clean_fast_carry`), of a
  clean slow origin's result (`clean_slow_carry`) and of the preceding honest batch
  (`honest_batch_carry`) are carried by H.2's `carryAt_of_writer_catch`.
* §2.2, RR/RO: H.1's
  `HealthyBase` comparisons over the AC projection (`healthyBase_of_hs`).

Everything here is proved.

The pre-`ḡ` acceptance relay of `GSTRun` is not used: `Sync` windows start at `ḡ`
(`syncRun_of_gst`), and pre-`ḡ` acceptances go through `Catch(2Δ)`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
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
theorem restart_le_of_healthy (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
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
theorem faultBound_of_healthy (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
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
theorem half_committee_of_healthy (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF)
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
private theorem frame_F_anc_of_viable (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    Anc (tr.HonestBlocks H) ℓ.frame.F B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hs.noColl).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hv.1
  exact (hΦ.rooted.2 B (hviab.resolve_right hroot).1.1).mono hΦU

/-- **A head accepted before `ḡ`**, read at a vote whose `Σ.F` it extends, at a time
`≥ ḡ + 2Δ`: `Catch(2Δ)` (with `Σ.F` monotone) gives its acceptance by the voter before
`ḡ + 2Δ`, at or before the vote. -/
private theorem accept_of_catch (hrun : GoldilocksRun proposer dg H tr)
    (hc : CatchRun tr H g (2 * sp.Δ))
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

/-! ### §2.1: aligned witnesses -/

/-- The AC projection under the HS premises is a healthy driven AC trace (H.1's `HealthyBase`). -/
theorem healthyBase_of_hs (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g :=
  ⟨Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hs.noColl,
    projection_driven hrun hs.noColl hs.genesisRoot hs.healthy,
    projection_healthy hrun hs.noColl hs.healthy,
    projection_catch hrun hs.noColl hs.healthy hc⟩

/-- A walk that starts in `S` and steps inside `T ⊆ S` stays in `S`. -/
private theorem ghost_mem {FGP : Type} {S T : Set (SA.Blk sp.n FGP)} (hTS : T ⊆ S)
    {sc : SA.Blk sp.n FGP → Nat} {el : SA.Blk sp.n FGP → Prop} :
    ∀ (f : Nat) {a : SA.Blk sp.n FGP}, a ∈ S → SA.ghost sp T sc el f a ∈ S
  | 0, _, ha => ha
  | f + 1, _, ha => by
    rw [SA.ghost]
    split
    · rename_i h
      exact ghost_mem hTS f (hTS h.choose_spec.1.1)
    · exact ha

/-- **An honest vote's head is in the full viable tree** when `fc_root` is
(`hs234-exact-interface.md` §2.1): the anchor is in the full viable tree (`getAnchor_viable`), and
every step of the walk is in the viable vote domain, a subset of the full one. -/
private theorem head_viable {FGP : Type} {ro' : ReplayOrder sp FGP} {U : Set (SA.Blk sp.n FGP)}
    {T : SA.SATrace sp FGP ro'} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro') H U T)
    {z : Fin sp.n} (hz : z ∈ H) {kz : Nat} {ℓz : ACLabel (SA.goldilocksSA sp FGP ro')}
    {e' : SA.Em sp FGP} (hc : SA.CastAt T z kz ℓz e')
    (hfc : ℓz.frame.fcRoot ∈ ℓz.frame.viableTree ℓz.frame.tree) :
    ∃ Hd ∈ ℓz.frame.viableTree ℓz.frame.tree, Hd.root = e'.msg.head := by
  have hΦ := (SA.frameIn_of_callAt hr hz hc.1).1
  obtain ⟨-, -, -, hhead⟩ := SA.castAt_spec hr hz hc
  refine ⟨_, ?_, hhead.symm⟩
  have hsub : ℓz.frame.viableTree (SA.voteDomain sp e'.readPoint ℓz.frame e'.msg.slot) ⊆
      ℓz.frame.viableTree ℓz.frame.tree :=
    SA.viableTree_voteDomain_subset_tree
  exact ghost_mem hsub _ (getAnchor_viable hΦ e'.readPoint (T.time kz) hfc)

/-- **`fc_root` is in the full viable tree** at an honest call in the settled phase: the
frontier block of the phase's evidence is allowed, so a viable head (`viableHeads_iff`, HS.1
(a)). -/
private theorem fcRoot_viable (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) {z : Fin sp.n} (hz : z ∈ H) {kz : Nat}
    {ℓz : ACLabel (goldilocksNode sp ro)} (hcz : tr.projAC.CallAt z kz ℓz)
    (hph : PhaseAt tr.projFG H kz m c) (hev : HoldsEvidence (tr.state z kz).fg m c) :
    ℓz.frame.fcRoot ∈ ℓz.frame.viableTree ℓz.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hs.noColl).localRun
  have hΦ := (SA.frameIn_of_callAt hr hz hcz).1
  obtain ⟨Bm, hBm, hBmh⟩ : ∃ B ∈ (tr.state z kz).fg.tree, ((tr.state z kz).fg.σ B.root).h = m := by
    cases c with
    | gap => exact hev
    | top J => exact hev.1
    | contest J => exact hev.1
  have hBe : EffAllowed (tr.state z kz).fg m c Bm := by
    refine ⟨hBm, ?_, fun J hJ => ?_⟩
    · cases c <;> (simp only [phaseFloor]; omega)
    · subst hJ
      by_contra hn
      exact hph.2.2 ⟨_, hz, Bm, by rw [projFG_store_eq hrun hz]; exact hBm,
        by rw [projFG_store_eq hrun hz]; exact hBmh, by rw [projFG_store_eq hrun hz]; exact hn⟩
  have hBv : Bm ∈ ℓz.frame.viableHeads := by
    rw [Compose.frame_of_projAC hrun hz hcz]
    exact (viableHeads_iff hrun hs hc hz hph hev hBm).2 ⟨store_anc_of_honest_anc hrun hs.noColl hz
      (viable_witness_retention_of hrun hs (fun k' h1 h2 => (le_antisymm h2 h1).symm ▸ hph) hz
        hBe hz le_rfl le_rfl).1 hBm, hBe⟩
  exact ⟨hΦ.fcRoot_mem, .refl, Bm, hΦ.viableHeads_subset hBv, hBv,
    hΦ.fcRoot_anc_viableHeads Bm hBv⟩

/-- The only ancestor of a block without parent is itself. -/
private theorem eq_of_anc_parent_none {FGP : Type} {U : Set (SA.Blk sp.n FGP)}
    {X G : SA.Blk sp.n FGP} (h : Anc U X G) (hG : G.parent = none) : X = G := by
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with rfl | ⟨Q, -, hQ⟩
  · rfl
  · exact absurd (hQ.2.2.symm.trans hG) (Option.some_ne_none _)

/-- **A block accepted before the freeze is in the voter block tree** of an honest vote: its
stamp at the state before the vote's call is its acceptance time (`blockStamp_lt_of_acceptedBefore`;
the vote's call does not accept it again), and the read point keeps that state's stamps. -/
private theorem mem_voterBlockTree_of_accept {FGP : Type} {ro' : ReplayOrder sp FGP}
    {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro'}
    (hr : ACLocalRun (SA.goldilocksSA sp FGP ro') H U T) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro')} {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e)
    {W : SA.Blk sp.n FGP} (hWt : W ∈ ℓ.frame.tree) {k' : Nat} (hacc : T.AcceptAt y k' W)
    (hkt : T.time k' < SA.freeze sp e.msg.slot) :
    W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  obtain ⟨-, hys, hyj, -⟩ := SA.castAt_spec hr hy hc
  have hti : sp.ts e.msg.slot ≤ T.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [hys])
  have hm : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [SAParams.ts]; ring
  have hfz : SA.freeze sp e.msg.slot ≤ T.time i := by unfold SA.freeze; linarith
  have hrsy : ∀ k ≤ i, T.RestartAt y k → T.time k < SA.freeze sp e.msg.slot := by
    have hj' : SA.joined sp (T.post i) (T.time i) := by
      unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hyj
    intro k hk hrk
    have := ((SA.joined_awake sp) FGP ro' H U T hr y hy i ℓ hc.1 hj').2 k hk hrk
    rw [← hys] at this
    unfold SA.freeze
    linarith
  have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hWt (Or.inr ⟨k', hacc, hkt⟩)
    hrsy (Or.inl hfz)
  -- the vote's call does not accept `W`
  have hne : ∀ B, ℓ.call = .block B → W.root ≠ B.root := by
    intro B₀ hcall hB
    have hB₀ := (SA.accept_new sp hr hy ⟨ℓ, hc.1, hcall⟩).1 ℓ hc.1
    obtain rfl : B₀ = W := hU.1 (hΦU hB₀) (hΦU hWt) hB.symm
    obtain rfl := SA.accept_unique sp hr hy hacc ⟨ℓ, hc.1, hcall⟩
    linarith
  have he := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at he
  have hpost : (T.post i).blockStamp W.root = (T.state y i).blockStamp W.root := by
    obtain ⟨hblk, -, hoth⟩ := SA.step_blockStamp_eq ro' y (T.state y i) hΦ (hr.time_nonneg i)
      ℓ.call
    have hp : T.post i =
        ((SA.goldilocksSA sp FGP ro').step y (T.state y i) ℓ.frame (T.time i) ℓ.call).1 := by
      rw [he]
    rw [hp]
    by_cases hb : ∃ B, ℓ.call = .block B
    · obtain ⟨B, hB⟩ := hb
      rw [hblk B hB, Function.update_of_ne (hne B hB)]
    · simp only [not_exists] at hb
      have hrs : ℓ.call ≠ .restart := by
        intro hrs
        have he' : e ∈ ((SA.goldilocksSA sp FGP ro').step y (T.state y i) ℓ.frame (T.time i)
            ℓ.call).2 := by rw [he]; exact hc.2
        rw [hrs] at he'
        change e ∈ (SA.acRestart sp ro' y (T.state y i) ℓ.frame (T.time i)).2 at he'
        rw [((SA.restart_state sp) FGP ro' y (T.state y i) ℓ.frame (T.time i) hΦ
          (hr.time_nonneg i)).1] at he'
        simp at he'
      rw [hoth hb hrs]
  exact ⟨hWt, Or.inl (by rw [SA.readPoint_blockStamp_eq hr hy hc, hpost]; exact hbs)⟩

/-- **The aligned witness of a clean vote** (`hs234-exact-interface.md` §2.1): under `Γ`
(without `Prop⁺`), let an honest vote of a clean slot `j` (`t_j ≥ w + 4Δ`, cut `kz`) extend `B`,
and let the phase hold from `i₀` through a cut `k` after `t_j + Δ`. Then `i₀ ≤ kz < k`, the vote
is cast by `t_j + Δ`, and `B` is below a block `W` effectively allowed at the vote (its head is in
its voter's full viable tree: `fc_root` is there, by the phase's frontier block,
`getAnchor_viable`, and the walk steps in the viable vote domain; so it is below a viable head,
allowed by `viableHeads_iff`) that is genesis or that the voter accepted before `t_j + 2Δ`. -/
theorem clean_vote_witness (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {z : Fin sp.n}
    (hz : z ∈ H) {kz : Nat} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hvz : SA.VoteAt tr.projAC z kz e') {j : Nat} (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hes : e'.msg.slot = j) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hext : SA.VoteExtends (tr.HonestBlocks H) e'.msg B) {k : Nat}
    (hk : PhaseOn tr.projFG H i₀ k m c) (hkt : sp.ts j + sp.Δ < tr.time k) :
    i₀ ≤ kz ∧ kz < k ∧ tr.time kz ≤ sp.ts j + sp.Δ ∧
      ∃ W, Anc (tr.HonestBlocks H) B W ∧ EffAllowed (tr.state z kz).fg m c W ∧
        (W.root = sp.genesisRoot ∨
          ∃ kw ≤ kz, tr.projAC.AcceptAt z kw W ∧ tr.time kw < sp.ts j + 2 * sp.Δ) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hs.noColl).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓz, hcz, hez⟩ := hvz
  have hvz : SA.CastAt tr.projAC z kz ℓz e' := ⟨hcz, hez⟩
  obtain ⟨-, hΦzU⟩ := SA.frameIn_of_callAt hr hz hcz
  have hsz := (SA.castAt_spec hr hz hvz).2.1
  have htz : sp.ts j ≤ tr.time kz :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg kz) _).2 (by rw [← hes, hsz])
  have htz' : tr.time kz ≤ sp.ts j + sp.Δ := by
    have := (Compose.cast_head_fcRoot hr hz hvz).2
    rw [hes] at this
    exact this
  have hkzk : kz < k := by
    by_contra h
    have := hr.time_mono (not_lt.1 h)
    change tr.time k ≤ tr.time kz at this
    linarith
  have hi₀z : i₀ ≤ kz := le_of_settled hw (by linarith)
  have hphz := hk kz hi₀z hkzk.le
  have hev : HoldsEvidence (tr.state z kz).fg m c := by
    have h := hw.1.evidence i₀ hw.2.1 m c hw.2.2 z hz
    rw [projFG_store_eq hrun hz] at h
    exact holdsEvidence_mono hrun hs.noColl hz hi₀z h
  obtain ⟨Hd, ⟨hHdt, -, W, hWt, hWv, hHdW⟩, hHdr⟩ :=
    head_viable hr hz hvz (fcRoot_viable hrun hs hc hz hcz hphz hev)
  obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hext
  obtain rfl : Hd = Hv := hU.1 (hΦzU hHdt) hHv (hHdr.trans hHvr.symm)
  have hWst : W ∈ (tr.state z kz).fg.tree := mem_tree_of_frame hrun hz hcz hWt
  have hWE : EffAllowed (tr.state z kz).fg m c W := by
    rw [Compose.frame_of_projAC hrun hz hcz] at hWv
    exact ((viableHeads_iff hrun hs hc hz hphz hev hWst).1 hWv).2
  refine ⟨hi₀z, hkzk, htz', W, hBHv.trans (Anc.mono hΦzU hHdW), hWE, ?_⟩
  rcases Compose.frame_anc_accepted hr hz kz ℓz hcz W hWt W .refl with hg | ⟨kw, hkw, hacc⟩
  · exact Or.inl hg
  · refine Or.inr ⟨kw, hkw, hacc, ?_⟩
    have := hr.time_mono hkw
    change tr.time kw ≤ tr.time kz at this
    linarith

/-- **§2.1, aligned witnesses at a vote** (`hs234-exact-interface.md` §2.1): under `Γ` (without
`Prop⁺`), let an honest vote of a clean slot `j` extend `B`. At every in-phase honest vote of a
later slot, `B` is in the viable voter block tree or at or below `fc_root`: the witness `W` of
`clean_vote_witness` relays (post-`ḡ`) or was caught up by `ḡ + 2Δ` (`Catch(2Δ)`) to the later
voter before its freeze, above its `Σ.F` (HS.1 (a)), so it is in the later voter block tree, and
HS.1 (d) retains every ancestor of `W`. A genesis witness makes `B` the genesis, at or below
`fc_root`. -/
theorem viable_of_clean_vote (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {z : Fin sp.n}
    (hz : z ∈ H) {kz : Nat} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hvz : SA.VoteAt tr.projAC z kz e') {j : Nat} (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hes : e'.msg.slot = j) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hext : SA.VoteExtends (tr.HonestBlocks H) e'.msg B) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (hjs : j < e.msg.slot)
    (hk : PhaseOn tr.projFG H i₀ k m c) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hs.noColl).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hv.1
  have hty : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [(SA.castAt_spec hr hy hv).2.1])
  have hjσ : sp.ts j + 4 * sp.Δ ≤ sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ := by
    have := (SA.ts_le_iff sp).2 (show (j : Int) ≤ (e.msg.slot : Int) - 1 by omega)
    linarith
  have hσ : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [SAParams.ts]; ring
  obtain ⟨hi₀z, hkzk, -, W, hBW, hWE, hWo⟩ :=
    clean_vote_witness hrun hs hc hw hz hvz hj hes hext hk (by linarith)
  have hon : PhaseOn tr.projFG H kz k m c := fun k' h1 h2 => hk k' (hi₀z.trans h1) h2
  have hret := viable_witness_retention_of hrun hs hon hz hWE hy hkzk.le le_rfl
  have hFW : Anc (tr.HonestBlocks H) ℓ.frame.F W := by
    rw [Compose.frame_of_projAC hrun hy hv.1]
    exact hret.1
  have hWU : W ∈ tr.HonestBlocks H := ⟨z, hz, kz, hWE.1⟩
  rcases hWo with hg | ⟨kw, hkw, hacc, hkwt⟩
  · -- a genesis witness: `B` and `Σ.F` are the genesis
    right
    obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy k ℓ hv.1
    obtain rfl : W = G := hU.1 hWU hGU (hg.trans hGr.symm)
    rw [eq_of_anc_parent_none hBW hGp, ← eq_of_anc_parent_none hFW hGp]
    exact hΦ.F_anc_fcRoot.mono hΦU
  -- `W` is in the later voter block tree: relayed after `ḡ`, caught up before
  have hWv' : W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
    by_cases hkg : gbar g ≤ tr.time kw
    · have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H
        (fun v => v.val) tr proposer ΔF (gbar g) (sp.ts j + 2 * sp.Δ) hrun.toLocalRun
        (syncRun_of_gst hs.healthy.1 (le_gbar g))
      exact relay_mem_voterBlockTree hr hsync hz hacc hkg hkwt le_rfl hy hv (by omega) hFW
    · have hw8 := gbar_add_le_of_settled hw
      obtain ⟨k', hk', hacc', hk't⟩ :=
        accept_of_catch hrun hc hz hacc (not_le.1 hkg) hy hv.1 (by linarith) hFW
      refine mem_voterBlockTree_of_accept hr hy hv
        (SA.mem_tree_of_acceptAt sp hr hy hacc' hk' hv.1 hFW) hacc' ?_
      unfold SA.freeze
      change tr.time k' < _
      linarith
  rw [Compose.frame_of_projAC hrun hy hv.1] at hWv' ⊢
  exact (hret.2.2 ℓ e hv (by rw [Compose.frame_of_projAC hrun hy hv.1]; exact hWv') B hBW).imp
    (fun h => by rwa [← Compose.frame_of_projAC hrun hy hv.1]) fun h => by
      rwa [← Compose.frame_of_projAC hrun hy hv.1]

/-- **§2.1, aligned witnesses in a frame** (`hs234-exact-interface.md` §2.1, the proposal
boundary of §2.2): under `Γ` (without `Prop⁺`), let an honest vote of a clean slot `j` extend
`B`. At every in-phase cut of an honest node at a time `≥ t_j + 3Δ`, every ancestor of `B` is at
or below its `fc_root` or in the viable tree of its frame: the witness `W` of
`clean_vote_witness` is held there (genesis, or relayed by `t_j + 3Δ` above its `Σ.F` (HS.1 (a)),
or caught up, `relay_held`), and HS.1 (c) retains its ancestors. -/
theorem clean_vote_frame (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {z : Fin sp.n}
    (hz : z ∈ H) {kz : Nat} {e' : SA.Em sp (List (FG.Att sp.n))}
    (hvz : SA.VoteAt tr.projAC z kz e') {j : Nat} (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hes : e'.msg.slot = j) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hext : SA.VoteExtends (tr.HonestBlocks H) e'.msg B) {q : Fin sp.n} (hq : q ∈ H) {kq : Nat}
    (hkq : PhaseOn tr.projFG H i₀ kq m c) (hkt : sp.ts j + 3 * sp.Δ ≤ tr.time kq) :
    ∀ X, Anc (tr.HonestBlocks H) X B →
      Anc (tr.HonestBlocks H) X (Node.frame (tr.state q kq)).fcRoot ∨
        X ∈ (Node.frame (tr.state q kq)).viableTree (Node.frame (tr.state q kq)).tree := by
  classical
  have hl := hrun.toLocalRun
  have hU := Compose.honest_blocks_coherent hl hs.noColl
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hw8 := gbar_add_le_of_settled hw
  obtain ⟨hi₀z, hkzk, htz, W, hBW, hWE, hWo⟩ :=
    clean_vote_witness hrun hs hc hw hz hvz hj hes hext hkq (by linarith)
  have hon : PhaseOn tr.projFG H kz kq m c := fun k' h1 h2 => hkq k' (hi₀z.trans h1) h2
  have hret := viable_witness_retention_of hrun hs hon hz hWE hq hkzk.le le_rfl
  have hWq : W ∈ (tr.state q kq).fg.tree := by
    rcases hWo with hg | ⟨kw, -, hacc, hkwt⟩
    · have hG := Store.genesis_mem (Compose.fg_reachable hl hq kq)
      obtain rfl : W = _ := hU.1 ⟨z, hz, kz, hWE.1⟩ ⟨q, hq, kq, hG⟩ hg
      exact hG
    obtain ⟨kw', rfl, haccr, htw⟩ := fg_accept_before hl hz hacc
    have hex : ∃ a, tr.time kq ≤ tr.time a := ⟨kq, le_rfl⟩
    have hj₁ : tr.FirstCutFrom (Nat.find hex) (tr.time kq) :=
      ⟨Nat.find_spec hex, fun a ha => not_le.1 (Nat.find_min hex ha)⟩
    have hle : Nat.find hex ≤ kq := Nat.find_min' hex le_rfl
    have hz₁ : kz ≤ Nat.find hex := by
      by_contra hn
      have := hl.time_mono (not_le.1 hn).le
      linarith [hj₁.1]
    have hF := (viable_witness_retention_of hrun hs hon hz hWE hq hz₁ hle).1
    exact Compose.tree_mono hl hq hle (relay_held hl hs.healthy hs.noRestart hc hz hq haccr
      (by linarith) (by rw [htw]; linarith) hj₁ hF)
  exact fun X hXB => (hret.2.1 hWq).2.2 X (hXB.trans hBW)

/-- **Frozen viability of a clean fast origin** (`hs234-exact-interface.md` §2.1 "aligned
witnesses", §3 first helper): under `Γ` (without `Prop⁺`), let `x` write a fast lock of a clean
label `j` (`t_j ≥ w + 4Δ`) with stored block `B`. At every in-phase honest vote of a slot `> j`,
`B` is in the viable voter block tree or at or below `fc_root`: an honest counted vote extends the
selection `D ⪰ B` (`fastLock_honest_vote`; `viable_of_clean_vote`). -/
theorem clean_fast_viable (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (hjs : j < e.msg.slot) (hk : PhaseOn tr.projFG H i₀ k m c) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hS := healthyBase_of_hs hrun hs hc
  obtain ⟨ℓw, D, hcw, hfl, rfl⟩ := ho
  have hBD : Anc (tr.HonestBlocks H) (ℓw.frame.viableAncestor D) D :=
    Anc.mono (SA.frameIn_of_callAt hS.run.localRun hx hcw).2 (SA.anc_viableAncestor _ D)
  obtain ⟨z, hz, kz, e', hvz, hes, Hd, hHd, hHdr, hDHd⟩ :=
    SA.fastLock_honest_vote hS.run hS.two_faulty_lt hx hfl
  exact viable_of_clean_vote hrun hs hc hw hz hvz hj hes ⟨Hd, hHd, hHdr, hBD.trans hDHd⟩ hy hv
    hjs hk

/-- **Frozen viability of a clean slow origin** (`hs234-exact-interface.md` §2.1, §3 slow
helper): as `clean_fast_viable`, for a slow lock of label `j` with `t_{j−k+1} ≥ w + 4Δ` and
stored block `B`: an honest slot-`j` vote extends the update's result `C ⪰ D ⪰ B`
(`result_extended`; `viable_of_clean_vote`). -/
theorem clean_slow_viable (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : StoredSlowLockAt tr x i j B) (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (hjs : j < e.msg.slot) (hk : PhaseOn tr.projFG H i₀ k m c) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

/-! ### §2.1: exact `Carry` -/

/-- **`Carry` of a clean fast origin's counted votes** (`hs234-exact-interface.md` §2.1
"all-head Carry"): at an in-phase honest slot-`(j+1)` vote whose `fc_root` is not above `B`,
`Carry_y(j, CV)`: an honest counted head has an allowed descendant `D` with `F ⪯ D` (HS.1), so
`F ⪯ B` (else `B ⪯ F ⪯ fc_root`), and every counted head, Byzantine ones included, extends `B`;
the counted heads are resolved at the writer before `t_j + 2Δ` and relay (post-`ḡ`) or were caught
up at `w` before `t_j + 3Δ`; raw votes and the two-vote cap give the held votes. -/
theorem clean_fast_carry (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = j + 1) (hk : PhaseOn tr.projFG H i₀ k m c)
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hs.noColl).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hFB := frame_F_anc_of_viable hrun hs hy hv
    (clean_fast_viable hrun hs hc hw hx ho hj hy hv (by omega) hk) hroot
  have hgj := gbar_le_of_clean hw hj
  have htk : sp.ts (j + 1 : Nat) ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [← he, (SA.castAt_spec hr hy hv).2.1])
  have hts : sp.ts (j + 1 : Nat) = sp.ts j + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨ℓw, D, hcw, hflD, rfl⟩ := ho
  have hBD : Anc (tr.HonestBlocks H) (ℓw.frame.viableAncestor D) D :=
    Anc.mono (SA.frameIn_of_callAt hr hx hcw).2 (SA.anc_viableAncestor _ D)
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (gbar g) (sp.ts j + 2 * sp.Δ) hrun.toLocalRun
    (syncRun_of_gst hs.healthy.1 (le_gbar g))
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
theorem clean_slow_carry (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : StoredSlowLockAt tr x i j B) (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = j + 1) (hk : PhaseOn tr.projFG H i₀ k m c)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x i j C CV) (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  sorry

/-- **`Carry` of the preceding honest batch** (`hs234-exact-interface.md` §2.1 "all-head Carry",
§3 "the preceding common honest batch"): under `Γ`, if every honest vote of a clean slot `m'`
extends `B`, then at an in-phase honest slot-`(m'+1)` vote at which `B` is frozen-viable and not
at or below `fc_root`, `Carry_y(m', S_{m'})` holds for the honest slot-`m'` votes: `Σ.F ⪯ B` (the
root split), so every honest head is above `Σ.F`; each was accepted by its voter before its vote,
and relays (post-`ḡ`) or was caught up by `ḡ + 2Δ` (`Catch(2Δ)`). -/
theorem honest_batch_carry (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
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
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hs.noColl).localRun
  have hU := hr.coherent
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hF := frame_F_anc_of_viable hrun hs hy hv hviab hroot
  have hgm := gbar_le_of_clean hw hm'
  have htk : sp.ts (m' + 1 : Nat) ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [← he, (SA.castAt_spec hr hy hv).2.1])
  have hts : sp.ts (m' + 1 : Nat) = sp.ts m' + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (gbar g) (sp.ts m' + 2 * sp.Δ) hrun.toLocalRun
    (syncRun_of_gst hs.healthy.1 (le_gbar g))
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

/-! ### §2.2: raw-result comparisons -/

end Consensus.Goldilocks.Healing

end
