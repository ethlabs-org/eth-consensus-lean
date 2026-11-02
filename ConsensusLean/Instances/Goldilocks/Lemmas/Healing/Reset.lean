module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Phase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries

public section

/-! # Goldilocks Healing: pieces of HR.3, reset existence

The whole-run reset-existence route (HS.5's `producer`, the count `reset_count` and HR.3
`reset_existence`) was retired (#136); the proved pieces remain. HR.3 (a): `c_z > ḡ + 8Δ`
(`lt_cutZ`), so HS.0 (`Settle(Δ)`, `settle`) applies at every `u ≥ c_z`. A phase change persists
to later cuts (`PhaseChanged.mono`). The reset is unique (`IsReset.eq`: `IsReset` is a least time).

`settle` is HS.0 (claims §"Healing: phase service"; phase-service.md §§1–8, the author's paper
results with Astra's review applied).

`settle` is proved from the facts of `Settle` (`phase-service.md` §8.3): unless the phase changes,
the phase at `u + Δ` is the one after `u`; its witnesses of state height `m` were accepted by `u`
and extend every honest `Σ.F` at `u + Δ` (strict-height G1.2), so they reach every honest node by
`Catch(2Δ)` or acceptance relay; joining and the catch-up at `u + Δ` follow from no restart after
`ḡ` and `Catch(2Δ)`.

Interfaces: none here (`settle` uses the chain-level G1.2 of `Settle`, open there
only because its proof in `FGChain/Accountable` is private). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **HS.0, bounded settling** (`Settle(Δ)`, with `κ = 2Δ`): from `u ≥ ḡ + 8Δ`, by `u + Δ`
the effective phase after all events at `u` has changed or the run is settled at `u + Δ`. -/
theorem settle {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {g ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (u : Time)
    (hu : gbar g + 8 * sp.Δ ≤ u) (j j' : Nat) (hj : FirstCutAfter tr j u)
    (hj' : tr.FirstCutFrom j' (u + sp.Δ)) :
    PhaseChanged tr.projFG H j j' ∨ SettledAt tr H g (2 * sp.Δ) (u + sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  have hfg := Compose.fg_projection _ _ dg H _ tr proposer hreq hs.genesisRoot
    hrun.toLocalRun hs.noColl
  have hq : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
    change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    have := sp.toParams.hn
    have := hs.healthy.2.2
    omega
  have hst : ∀ z ∈ H, ∀ i, tr.projFG.store z i = (tr.state z i).fg := fun z hz i => by
    simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hz i]
  have hw : gbar g + 2 * sp.Δ ≤ u + sp.Δ := by linarith
  by_cases hch : PhaseChanged tr.projFG H j j'
  · exact Or.inl hch
  simp only [PhaseChanged, not_forall, not_not] at hch
  obtain ⟨m, c, hc₁, hc₂⟩ := hch
  refine Or.inr ⟨max_le (by linarith) (by linarith), joined_late hs.noRestart (by linarith),
    fun j₀ hj₀ m' c' hc₀ y hy => ?_, catchRun_at hc hrun.toLocalRun hw⟩
  obtain rfl : j₀ = j' := le_antisymm
    (not_lt.1 fun h => absurd (hj₀.2 _ h) (not_lt.2 hj'.1))
    (not_lt.1 fun h => absurd (hj'.2 _ h) (not_lt.2 hj₀.1))
  obtain ⟨rfl, rfl⟩ := phaseAt_eq hfg hq hc₂ hc₀
  -- every honest block of height `m` held after `u` is held by `y` at `u + Δ`
  refine holdsEvidence_of_relay hfg hy hc₁ fun x hx B hB hBh => ?_
  have hFB := finalized_anc hfg hq hy hx hB (hBh ▸ hc₂.frontierAt.2 y hy)
  rw [hst x hx] at hB hFB
  rw [hst y hy] at hFB ⊢
  rcases Compose.tree_cases hrun.toLocalRun hx hB with rfl | ⟨k₀, hk₀, hacc⟩
  · exact (Store.accepted_tree _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hy j₀)).2.2.1
  · exact relay_held hrun.toLocalRun hs.healthy hs.noRestart hc hx hy hacc hw
      (by linarith [hj.1 k₀ hk₀]) hj' (Anc.mono (fun X hX => ⟨x, hx, j, hX⟩) hFB)

/-! ## Cuts of a run and its FG projection -/

section Cuts

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}

private theorem after_le_from {j j' : Nat} {t t' : Time} (h : FirstCutAfter tr j t)
    (h' : tr.FirstCutFrom j' t') (htt : t < t') : j ≤ j' := by
  by_contra hlt
  have := h.1 j' (not_le.1 hlt)
  have := h'.1
  linarith

private theorem from_le_after {j j' : Nat} {t t' : Time} (h : tr.FirstCutFrom j t)
    (h' : FirstCutAfter tr j' t') (htt : t ≤ t') : j ≤ j' := by
  by_contra hlt
  have := h.2 j' (not_le.1 hlt)
  have := h'.2
  linarith

private theorem after_le_after {j j' : Nat} {t t' : Time} (h : FirstCutAfter tr j t)
    (h' : FirstCutAfter tr j' t') (htt : t ≤ t') : j ≤ j' := by
  by_contra hlt
  have := h.1 j' (not_le.1 hlt)
  have := h'.2
  linarith

/-- In a run where an honest node is awake from `t₀` on, every time has a first cut after it
and a first cut from it (`awake_in_horizon`). -/
private theorem exists_cuts {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
    {proposer : Nat → Fin P.n} {sg : A.Msg → Fin P.n}
    (hrun : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    {t₀ : Time} (hawake : ∀ t, t₀ ≤ t → tr.awake y t) (t : Time) :
    (∃ j, FirstCutAfter tr j t) ∧ ∃ j, tr.FirstCutFrom j t := by
  classical
  obtain ⟨i, -, hi⟩ := hrun.awake_in_horizon y hy _ (hawake (max t₀ (t + 1)) (le_max_left _ _))
  have hti : t + 1 ≤ tr.time i := (le_max_right _ _).trans hi
  have hlt : ∃ i, t < tr.time i := ⟨i, by linarith⟩
  have hle : ∃ i, t ≤ tr.time i := ⟨i, by linarith⟩
  exact ⟨⟨Nat.find hlt, fun k hk => not_lt.1 (Nat.find_min hlt hk), Nat.find_spec hlt⟩,
    Nat.find hle, Nat.find_spec hle, fun k hk => not_le.1 (Nat.find_min hle hk)⟩

private theorem projFG_store {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
    {proposer : Nat → Fin P.n} {sg : A.Msg → Fin P.n}
    (hrun : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    (i : Nat) : tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun hy i]

end Cuts

/-! ## The effective phase as a potential -/

section Potential

variable {P : Params} {ACP : Type} {tr : FGTrace P ACP} {H : Set (Fin P.n)}

private theorem store_hmax_mono {acp₀ : ACP} {U : Set (NodeBlock P ACP)}
    (hr : FGLocalRun acp₀ H U tr)
    {y : Fin P.n} (hy : y ∈ H) {k m : Nat} (hkm : k ≤ m) :
    (tr.store y k).hmax ≤ (tr.store y m).hmax := by
  obtain ⟨-, -, -, -, -, ⟨B, hB, hBh⟩, -⟩ :=
    Store.cache_invariants P ACP acp₀ _ (Store.store_reachable hr hy k)
  obtain ⟨hB', hσ⟩ := Store.held_mono hr hy hkm hB
  have := (Store.cache_invariants P ACP acp₀ _ (Store.store_reachable hr hy m)).2.2.2.2.1 B hB'
  rwa [hσ, hBh] at this

private theorem PhaseAt.frontier {i m : Nat} {c : PhaseCase (NodeBlock P ACP)}
    (h : PhaseAt tr H i m c) : FrontierAt tr H i m := by
  cases c <;> exact h.1

private theorem exists_phase (hH : H.Nonempty) (i : Nat) :
    ∃ p : Nat × PhaseCase (NodeBlock P ACP), PhaseAt tr H i p.1 p.2 := by
  classical
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image H.toFinset (fun y => (tr.store y i).hmax)
    (Set.toFinset_nonempty.2 hH)
  have hf : FrontierAt tr H i (tr.store y i).hmax :=
    ⟨⟨y, Set.mem_toFinset.1 hy, rfl⟩, fun z hz => hmax z (Set.mem_toFinset.2 hz)⟩
  by_cases hJ : ∃ J, JustifiedAt tr H i ((tr.store y i).hmax - 1) J
  · obtain ⟨J, hJ⟩ := hJ
    by_cases hC : ContestAt tr H i (tr.store y i).hmax J
    · exact ⟨(_, .contest J), hf, hJ, hC⟩
    · exact ⟨(_, .top J), hf, hJ, hC⟩
  · exact ⟨(_, .gap), hf, fun J hj => hJ ⟨J, hj⟩⟩

private theorem PhaseCase.eq_of_rank {β : Type} {c c' : PhaseCase β} (hr : c.rank = c'.rank)
    (hJ : ∀ J, c.topJ = some J → c'.topJ = some J) : c = c' := by
  cases c <;> cases c' <;> simp_all [PhaseCase.rank, PhaseCase.topJ]

private theorem PhaseCase.rank_le {β : Type} (c : PhaseCase β) : c.rank ≤ 2 := by
  cases c <;> simp [PhaseCase.rank]

/-- HR.2 (b): at a fixed frontier the case moves only forward, with one `J`. -/
private def Forward (tr : FGTrace P ACP) (H : Set (Fin P.n)) : Prop :=
  ∀ m i j c c', i ≤ j → PhaseAt tr H i m c → PhaseAt tr H j m c' →
    c.rank ≤ c'.rank ∧ ∀ J, c.topJ = some J → c'.topJ = some J

/-- The potential `3m + rank` of the effective phase does not fall (the frontier does not fall,
and at a fixed frontier the case moves forward). -/
private theorem pot_le (hb : Forward tr H)
    (hmono : ∀ y ∈ H, ∀ i j, i ≤ j → (tr.store y i).hmax ≤ (tr.store y j).hmax)
    {i j m m' : Nat} {c c' : PhaseCase (NodeBlock P ACP)} (hij : i ≤ j)
    (h : PhaseAt tr H i m c) (h' : PhaseAt tr H j m' c') : 3 * m + c.rank ≤ 3 * m' + c'.rank := by
  obtain ⟨y, hy, rfl⟩ := h.frontier.1
  have hm := (hmono y hy i j hij).trans (h'.frontier.2 y hy)
  have := c.rank_le
  rcases hm.lt_or_eq with hlt | heq
  · omega
  · subst heq
    have := (hb _ i j c c' hij h h').1
    omega

/-- A phase change raises the potential. -/
private theorem pot_lt (hb : Forward tr H)
    (hmono : ∀ y ∈ H, ∀ i j, i ≤ j → (tr.store y i).hmax ≤ (tr.store y j).hmax)
    {i j m m' : Nat} {c c' : PhaseCase (NodeBlock P ACP)} (hij : i ≤ j)
    (hch : PhaseChanged tr H i j) (h : PhaseAt tr H i m c) (h' : PhaseAt tr H j m' c') :
    3 * m + c.rank < 3 * m' + c'.rank := by
  obtain ⟨y, hy, rfl⟩ := h.frontier.1
  have hm := (hmono y hy i j hij).trans (h'.frontier.2 y hy)
  have := c.rank_le
  rcases hm.lt_or_eq with hlt | heq
  · omega
  · subst heq
    obtain ⟨h1, h2⟩ := hb _ i j c c' hij h h'
    rcases h1.lt_or_eq with hlt | heq
    · omega
    · exact absurd (PhaseCase.eq_of_rank heq h2 ▸ h') (hch _ c h)

/-- A phase change from `i` to `j₁` persists to every later cut `j₂` (the potential `3m + rank`
rises from `i` to `j₁` and does not fall after: HR.2 (b) and the growth of the honest
`Σ.h_max`). -/
theorem PhaseChanged.mono {acp₀ : ACP} {U : Set (NodeBlock P ACP)} (hr : FGLocalRun acp₀ H U tr)
    (hf : Hᶜ.ncard < 2 * P.fg.q - P.n) {i j₁ j₂ : Nat} (hij : i ≤ j₁) (hj : j₁ ≤ j₂)
    (h : PhaseChanged tr H i j₁) : PhaseChanged tr H i j₂ := by
  intro m c hi hi₂
  obtain ⟨-, hb, -⟩ := phase_count P ACP acp₀ H U tr hr hf
  have hmono : ∀ y ∈ H, ∀ i j, i ≤ j → (tr.store y i).hmax ≤ (tr.store y j).hmax :=
    fun y hy i j hij => store_hmax_mono hr hy hij
  obtain ⟨y, hy, -⟩ := hi.frontier.1
  obtain ⟨p, hp⟩ := exists_phase (tr := tr) ⟨y, hy⟩ j₁
  have := pot_lt hb hmono hij h hi hp
  have := pot_le hb hmono hj hp hi₂
  omega

end Potential

/-! ## HS.5 and the reset count -/

/-- What every HS proof here starts from: the FG projection is an FG trace (C0.5 (c)), with
`f < 2q − n` (from `3f ≤ n − 1`), some honest validator, and `0 ≤ D_HS ≤ A_HS` (`Δ_F ≥ Δ > 0`,
and `G_p ≥ 0` from `Prop⁺(G_p)` at `ḡ`). -/
private theorem hs_setup {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {g ΔF Gp : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF) (hp : PropPlus tr H proposer g Gp) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG ∧
      Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n ∧ H.Nonempty ∧
      0 ≤ D_HS sp Gp ∧ D_HS sp Gp ≤ A_HS sp ΔF Gp := by
  obtain ⟨hgst, -, hf⟩ := hs.healthy
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  have hn := sp.toParams.hn
  refine ⟨Compose.fg_projection _ _ dg H _ tr proposer hreq hs.genesisRoot
    hrun.toLocalRun hs.noColl,
    by change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n; omega, ?_, ?_⟩
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hf
    omega
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨s, -, -, -, h1, h2, -⟩ := hp (gbar g) le_rfl
  have hF : 0 ≤ ΔF := hgst.deltaF.le
  have hk : (0 : Time) ≤ sp.k := Int.natCast_nonneg _
  have hδ : (0 : Time) ≤ sp.toParams.δt := Int.natCast_nonneg _
  have hD : 0 ≤ D_HS sp Gp := by
    simp only [D_HS]
    nlinarith [mul_nonneg (by linarith : (0 : Time) ≤ 8 * sp.k + 48) hΔ.le]
  refine ⟨hD, ?_⟩
  simp only [A_HS, C_HS]
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : Time) ≤ 4) hΔ.le) hδ]

/-- The reset is unique. -/
theorem IsReset.eq {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Set (Fin P.n)} {g a a' : Time}
    (h : IsReset tr H g a) (h' : IsReset tr H g a') : a = a' := by
  obtain ⟨y, hy, k, att, hk, hh, hka⟩ := h.1
  obtain ⟨y', hy', k', att', hk', hh', hka'⟩ := h'.1
  exact le_antisymm ((h.2 y' hy' k' att' hk' hh').trans hka'.le)
    ((h'.2 y hy k att hk hh).trans hka.le)

end Consensus.Goldilocks.Healing

end
