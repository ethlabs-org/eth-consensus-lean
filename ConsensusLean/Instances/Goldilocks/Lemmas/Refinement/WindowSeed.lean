module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowParentsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowUnanimous
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowAnchorStep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposalWindowUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifiesSigned
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks Refinement: the seed height of the route-A window (#136)

consensus-lean#136, workbench `window_start_h0.md` §1–§3 (r3). One honest **seed** proposal `Q`
at a slot `u` after the drain, and an honest proposal `P₀` at a slot `s₀ ≥ u + δt` by the horizon
`b`: `HZ + 2 ≤ σ[P₀].h` in every honest store that holds `P₀`. Hence H0 (`HZ + 1 ≤ h₀`) and
`h₀ ≥ HZ + 2` at the first anchor. Every proposer of a slot in `(u, s₀)` can be faulty.

Proof (card §1.3): H0 at `Q` (`reset_seed_before_slot`, `operational_unanimous`,
`old_origin_below_unanimous`); `Q ⪯ Pr = parent(P₀)` (C4). If `σ[Pr].h ≥ HZ + 2`, by
monotonicity. Otherwise `σ[Q].h = σ[Pr].h = HZ + 1`: a higher report of the seed contradicts this
(`crossed_parents_above_upTo`); so every honest node has a same-height report, hence a target row
for the entry of `Q` signed by `ts(u) + 6Δ` (`sign_of_report`, `row_target_of_sign`; no `fin`), and
`P₀` crosses by timeout (`cross_of_signed_rows_upTo`, age `ThSlot ≤ u`). -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

/-- **Entry-slot constancy:** while the height stays along ancestry, the entry slot stays. -/
private theorem ThSlot_eq_of_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W)
    (hh : (st.σ W.root).h = (st.σ A.root).h) :
    (st.σ W.root).ThSlot = (st.σ A.root).ThSlot := by
  induction h with
  | refl => rfl
  | @tail Y Y' hAY hYY' ih =>
    obtain ⟨-, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hY' hp
    have h₁ := Healing.h_le_of_store_anc hr hAY
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, e', -⟩ | ⟨e, -, -⟩
    · rw [e']; exact ih (by rw [← e]; exact hh)
    · omega

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The seed height (WS).** Under `ResetPremisesUpTo … b`, `CatchRun 2Δ` and
`HSSharedUpTo … b` (its `timeoutDelay`; `ḡ_S ≤ ts(u) + 6Δ`), an honest seed proposal `Q` at
slot `u > 0` with `drainTime a ≤ ts(u)` and `ḡ + 4Δ ≤ ts(u)`, and an honest proposal `P₀` at slot
`s₀ ≥ u + δt` with `ts(s₀) ≤ b` (`2 ≤ δt`): every honest store that holds `P₀` has
`HZ + 2 ≤ σ[P₀].h`. -/
theorem seed_height {g ΔR a b gS ΔF : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) (hs : Healing.HSSharedUpTo tr H dg gS ΔF b)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ : Nat} {Q P₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Healing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∀ y ∈ H, ∀ k, P₀ ∈ (tr.state y k).fg.tree →
      Healing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h := by
  classical
  have hrun := hp.run
  have hnc := hp.noColl
  have hΔ := sp.toParams.hΔ
  have hcoh := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  -- the two proposals
  obtain ⟨-, -, -, -, -, -, -, -, -, hQs, -⟩ := hQ.2
  obtain ⟨-, -, -, -, -, -, -, -, -, hP₀s, -⟩ := hP₀.2
  obtain ⟨kQ, hkQ⟩ := proposesAt_of_honestProposalRun hrun hQ
  obtain ⟨kX, hkX⟩ := proposesAt_of_honestProposalRun hrun hP₀
  have hpQ : proposer u ∈ H := hQ.1
  have hpH : proposer s₀ ∈ H := hP₀.1
  obtain ⟨-, hQm, -⟩ := Healing.accept_of_proposesAt hrun hnc hpQ hkQ
  have hQH : Q ∈ tr.HonestBlocks H := ⟨_, hpQ, kQ + 1, hQm⟩
  obtain ⟨Pr, hpar, hPr⟩ := Healing.proposal_parent_held hrun hnc hpH hkX
  obtain ⟨-, hXm, he⟩ := Healing.accept_of_proposesAt hrun hnc hpH hkX
  have hXH : P₀ ∈ tr.HonestBlocks H := ⟨_, hpH, kX + 1, hXm⟩
  have hPrH : Pr ∈ tr.HonestBlocks H := ⟨_, hpH, kX, hPr⟩
  have htk : tr.time kX = sp.ts s₀ := by rw [proposesAt_time hkX, hP₀s]
  -- time arithmetic
  have htd : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time) := hs.timeoutDelay
  have hts : sp.ts u + 4 * sp.Δ * (sp.toParams.fg.δt : Time) ≤ sp.ts s₀ := by
    have hcast : ((u + sp.toParams.fg.δt : Nat) : Int) ≤ (s₀ : Int) := by exact_mod_cast hus
    have := (SA.ts_le_iff sp).2 hcast
    simp only [SA.SAParams.ts] at this ⊢
    push_cast at this
    linarith
  have h2δ : (2 : Time) ≤ (sp.toParams.fg.δt : Time) := by exact_mod_cast hδ
  have h8 : sp.ts u + 8 * sp.Δ ≤ sp.ts s₀ := by nlinarith
  have hus2 : u + 2 ≤ s₀ := by omega
  have hub : sp.ts u + 6 * sp.Δ ≤ b := by linarith
  -- Step 1: H0 at the seed
  obtain ⟨v, r, l, O, ho, -, -, hrt⟩ := hp.reset_seed_before_slot hR
  have hun := hp.operational_unanimous hc hpQ rfl hkQ hQs hR (by linarith)
  have hR1 : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat) :=
    hR.trans ((SA.ts_le_iff sp).2 (by push_cast; omega))
  have hOQ := UpTo.old_origin_below_unanimous hp hc hQH
    (fun y hy j e hv hjb hs' => hun y hy j e hv hs' hjb) hgu hR1 (by linarith) ho hrt
  -- Step 2: Q ⪯ P₀ (C4), hence Q ⪯ Pr
  have hQP := honest_proposal_below_later_upTo hp hc hQ hR hP₀ hus2 hb
  have hne : Q ≠ P₀ := by
    intro h
    rw [h] at hQs
    omega
  have hQPr : Anc (tr.HonestBlocks H) Q Pr := by
    rcases Relation.ReflTransGen.cases_tail hQP with heq | ⟨Y, hQY, hY⟩
    · exact absurd heq.symm hne
    · obtain rfl : Y = Pr := hcoh.1 hY.1 hPrH (Option.some_injective _ (hY.2.2.symm.trans hpar))
      exact hQY
  -- the proposer's store at the proposal cut
  have hr := Compose.fg_reachable hrun.toLocalRun hpH kX
  have hQst := Healing.mem_of_honest_anc hrun hnc hpH hQPr hPr
  have hQPrs := Healing.store_anc_of_honest_anc hrun hnc hpH hQPr hPr
  have hOQs := Healing.store_anc_of_honest_anc hrun hnc hpH hOQ hQst
  have hOst := Healing.mem_of_honest_anc hrun hnc hpH hOQ hQst
  obtain ⟨-, -, -, -, -, -, -, -, -, hOv⟩ := hp.highOrigin_mem ho
  have hOh : Healing.HZ tr H g + 1 ≤ ((tr.state (proposer s₀) kX).fg.σ O.root).h := by
    rw [← Healing.σ_eq_honest hrun hnc ho.1 hpH hOv hOst]
    exact ho.2.2.2
  have hQh : Healing.HZ tr H g + 1 ≤ ((tr.state (proposer s₀) kX).fg.σ Q.root).h :=
    hOh.trans (Healing.h_le_of_store_anc hr hOQs)
  have hQPrh := Healing.h_le_of_store_anc hr hQPrs
  suffices hpost : Healing.HZ tr H g + 2 ≤ ((tr.post kX).fg.σ P₀.root).h by
    intro y hy k hk
    rw [he] at hpost
    rw [Healing.σ_eq_honest hrun hnc hy hpH hk hXm]
    exact hpost
  -- Case A/B: the parent is already above `HZ + 1`
  by_cases hPr2 : Healing.HZ tr H g + 2 ≤ ((tr.state (proposer s₀) kX).fg.σ Pr.root).h
  · have hPrm := Healing.mem_of_honest_anc hrun hnc hpH (.single ⟨hPrH, hXH, hpar⟩) hXm
    have hle' := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hpH (kX + 1))
      (.single ⟨hPrm, hXm, hpar⟩)
    rw [← Healing.σ_eq_honest hrun hnc hpH hpH hPr hPrm] at hle'
    rw [he]
    omega
  -- Case C: `σ[Q].h = σ[Pr].h = HZ + 1`
  have hQ1 : ((tr.state (proposer s₀) kX).fg.σ Q.root).h = Healing.HZ tr H g + 1 := by omega
  have hPr1 : ((tr.state (proposer s₀) kX).fg.σ Pr.root).h =
      ((tr.state (proposer s₀) kX).fg.σ Q.root).h := by omega
  -- C1: a report of the seed strictly above it is impossible
  have hH := healed_of_reset_canonical_full_upTo hp hc (h₀ := Healing.HZ tr H g + 1) le_rfl Q hR
  have hesc : ∀ x ∈ H, ∀ r ell C, SA.ToFGAt tr.projAC x r ell C →
      tr.time r ≤ sp.ts u + 6 * sp.Δ → Anc (tr.HonestBlocks H) Q C →
      ((tr.state x r).fg.σ Q.root).h < ((tr.state x r).fg.σ C.root).h → False := by
    intro x hx r ell C hto hrt' hQC hlt
    have hCm : C ∈ (tr.state x r).fg.tree :=
      Healing.mem_tree_of_frame hrun hx hto.1 (toFG_live_fast_lock hto).1
    have hQx := Healing.mem_of_honest_anc hrun hnc hx hQC hCm
    have htH : sp.ts u ≤ tr.time r := by
      have := report_slot_le_time hrun hnc hx hto hQC
      rwa [hQs] at this
    obtain ⟨Pr', hPr'H, hpar', -, habove⟩ :=
      crossed_parents_above_upTo hrun hnc hH hx hto htH hlt hP₀ (by linarith) hb
    obtain rfl : Pr' = Pr := hcoh.1 hPr'H hPrH (Option.some_injective _ (hpar'.symm.trans hpar))
    have := habove _ hpH kX hPr
    rw [Healing.σ_eq_honest hrun hnc hx hpH hQx hQst] at this
    omega
  have hPg : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hG := Healing.Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hpQ (kQ + 1))
    have heq := hcoh.1 hQH ⟨_, hpQ, kQ + 1, hG⟩ hg
    have hz : Q.slot = 0 := by rw [heq]; rfl
    omega
  rcases UpTo.report_cover_of_proposal hp hc hpQ rfl hkQ hQH hQs hu hPg hgu hR hub with
    hall | ⟨x, hx, r, e, C, hto, hrt', hQC, hlt⟩
  swap
  · exact (hesc x hx r e C hto hrt' hQC hlt).elim
  -- C2: the entry of the seed, its target rows, and the timeout crossing at `P₀`
  obtain ⟨⟨E, hE, hEr, hEQ, hEh, hETh⟩, -⟩ :=
    Goldilocks.Store.entry_state_of_source _ _ _ _ hr Q hQst
  have hETe : ((tr.state (proposer s₀) kX).fg.σ E.root).Th = E.root := hETh.trans hEr.symm
  have hEQh := Healing.honest_anc_of_store_anc hpH hEQ
  have hEhT : Healing.HZ tr H g + 1 ≤ ((tr.state (proposer s₀) kX).fg.σ E.root).h := by
    rw [hEh]; exact hQh
  have hPrTh : ((tr.state (proposer s₀) kX).fg.σ Pr.root).Th = E.root :=
    (Healing.Th_eq_of_anc hr hQPrs hPr1).trans hEr.symm
  have hThS : ((tr.state (proposer s₀) kX).fg.σ Pr.root).ThSlot ≤ u := by
    rw [ThSlot_eq_of_anc hr hQPrs hPr1, ← hQs]
    exact Goldilocks.Store.ThSlot_le_slot hr hQst
  let S : Finset (Fin sp.n) := Finset.univ.filter (· ∈ H)
  have hScard : sp.toParams.fg.q ≤ S.card := by
    have hcard : S.card = H.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp [S]
    rw [hcard]
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hf := hp.faults
    change (2 * sp.n + 2) / 3 ≤ _
    omega
  have hcross := Healing.cross_of_signed_rows_upTo hrun hs (v := sp.ts u + 6 * sp.Δ)
    hgS hpH hkX (by rw [htk]; linarith) (by rw [htk]; exact hb) hpar S
    (fun z hz => (Finset.mem_filter.1 hz).2) hScard ?_ (by rw [hP₀s]; omega)
  · rw [hcross.1]
    omega
  intro z hz
  have hzH : z ∈ H := (Finset.mem_filter.1 hz).2
  obtain ⟨r, ell, R, hrep, hrt', hQR⟩ := hall z hzH
  have hRm : R ∈ (tr.state z r).fg.tree :=
    Healing.mem_tree_of_frame hrun hzH hrep.1 (toFG_live_fast_lock hrep).1
  have hQz := Healing.mem_of_honest_anc hrun hnc hzH hQR hRm
  have hσQ := Healing.σ_eq_honest hrun hnc hzH hpH hQz hQst
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hzH r)
    (Healing.store_anc_of_honest_anc hrun hnc hzH hQR hRm)
  have hRh : ((tr.state z r).fg.σ R.root).h = ((tr.state (proposer s₀) kX).fg.σ E.root).h := by
    by_contra hneq
    refine hesc z hzH r ell R hrep hrt' hQR ?_
    rw [hσQ] at hle ⊢
    omega
  have hrb : tr.time r ≤ b := by linarith
  obtain ⟨io, _, jo, O', _, _, ho', hiob, _, hCO, _⟩ :=
    hp.high_report_origin hzH hrep hrb (by rw [hRh]; exact hEhT)
  have hER := hEQh.trans hQR
  have hEO := hER.trans hCO
  obtain ⟨j, att, hsg, hjt, hah⟩ :=
    hp.sign_of_report hzH hrep hrb hpH hE rfl hETe hEhT hER hRh ho' hiob hEO
  obtain ⟨-, haT, -⟩ :=
    hp.row_target_of_sign hzH hsg (hjt.trans hrb) hpH hE rfl hETe hEhT ho' hiob hEO hah
  exact ⟨j, att, hsg, hjt.trans hrt', hah.trans (hEh.trans hPr1.symm), haT.trans hPrTh.symm⟩

/-- `seed_height` in the form of the `hh₀` premise of `anchorSteps_gap2`: the proposer of `P₀`
holds `P₀` after its proposal cut, at height at least `HZ + 2`. -/
theorem seed_height_held {g ΔR a b gS ΔF : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) (hs : Healing.HSSharedUpTo tr H dg gS ΔF b)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ : Nat} {Q P₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Healing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∃ y ∈ H, ∃ k, P₀ ∈ (tr.state y k).fg.tree ∧
      Healing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h := by
  obtain ⟨kX, hkX⟩ := proposesAt_of_honestProposalRun hp.run hP₀
  obtain ⟨-, hXm, -⟩ := Healing.accept_of_proposesAt hp.run hp.noColl hP₀.1 hkX
  exact ⟨_, hP₀.1, kX + 1, hXm,
    seed_height hp hc hs hδ hQ hu hR hgu hP₀ hus hb hgS _ hP₀.1 (kX + 1) hXm⟩

end Consensus.Goldilocks.Refinement

end
