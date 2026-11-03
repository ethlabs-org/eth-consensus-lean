module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowAnchorRoute
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowUnanimous
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowParentsUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinPair
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposalWindowUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifiesSigned
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # Goldilocks Refinement: the route-A anchor steps at a general gap `c` (#136)

`AnchorStepsSupply` fixes the anchor gap at 2 slots and assumes `ΔF ≤ 2Δ`. That holds only for
`ΔF := Δ_p`. For a larger `ΔF` (for example `ΔF = 32Δ`) the anchors must be `c ≥ c_F` slots
apart, with `c_F := ⌈(6Δ + ΔF) / 4Δ⌉`. This module generalizes the gap-2 proofs.

* `anchorStep_gap`: one step `A → X`, with `A` at slot `s` and `X` at slot `s + c`, `2 ≤ c`.
  The premise `ΔF ≤ 2Δ` becomes the delivery premise `t_s + 6Δ + ΔF ≤ t_{s+c}`: the rows
  are signed by `t_s + 6Δ` and are delivered by `t_{s+c}`. `2 ≤ c` gives the adjacency
  (`anchors_chain_upTo`) and `t_s + 7Δ ≤ t_{s+c}` (`crossed_parents_above_upTo`).
* `anchorSteps_gap`: the three steps of the window, anchors at `s₀ + [0, c, 2c, 3c]`. The
  delivery premise is slot-free: `6Δ + ΔF ≤ 4Δ·c`.
* `cF_gap_delivery`, `gap_delivery_iff_cF`: `c_F ≤ c` if and only if `6Δ + ΔF ≤ 4Δ·c`.
  `cF_at_32`: `c_F = 10` when `ΔF = 32Δ`. `gap2_delivery`: `ΔF ≤ 2Δ` gives the premise at
  `c = 2`, and `anchorSteps_gap2'` recovers `anchorSteps_gap2` from `anchorSteps_gap`.
* `anchor_span_iff`: the span `3c ≤ δt` is the `hsl` premise of `coverage_of_anchor_window`
  for anchors at `s₀` and `s₀ + 3c`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-! ## Arithmetic of the gap -/

/-- `c` slots after `s`, the slot time is `4Δ·c` later. -/
theorem ts_add_gap (s c : Nat) : sp.ts (s + c : Nat) = sp.ts s + 4 * sp.Δ * c := by
  simp only [SAParams.ts]; push_cast; ring

/-- The slot-free delivery premise gives the delivery inequality at every slot. -/
theorem gap_delivery {ΔF : Time} {c : Nat} (h : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * c) (s : Nat) :
    sp.ts s + 6 * sp.Δ + ΔF ≤ sp.ts (s + c : Nat) := by
  have := ts_add_gap (sp := sp) s c
  linarith

/-! ## The anchor steps -/

/-- The slot of an honest proposal. -/
private theorem run_slot {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) : P.slot = s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hs, -⟩ := hP
  exact hs

/-- A proper ancestor of a block is an ancestor of its parent. -/
private theorem anc_parent' {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {A B Q : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc U A B) (hne : A ≠ B)
    (hBQ : B.parent = some Q.root) (hQ : Q ∈ U) : Anc U A Q := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hAY, hY⟩
  · exact absurd heq.symm hne
  obtain rfl : Y = Q := hU.1 hY.1 hQ (Option.some_injective _ (hY.2.2.symm.trans hBQ))
  exact hAY

/-- The facts of a post-drain honest anchor that `UpTo.report_cover_of_proposal` reads. -/
private theorem anchor_facts {g ΔR a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔR a b) {s : Nat}
    {A : SA.Blk sp.n (List (FG.Att sp.n))} (hA : Healing.HonestProposalRun tr H proposer s A)
    (hR : Healing.drainTime sp a ≤ sp.ts s) :
    (∃ k, tr.ProposesAt (proposer s) k A) ∧ A ∈ tr.HonestBlocks H ∧ A.slot = s ∧ 0 < s ∧
      A.root ≠ sp.genesisRoot ∧ gbar g + 4 * sp.Δ ≤ sp.ts s := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hp.run hA
  obtain ⟨-, hAm, -⟩ := Healing.accept_of_proposesAt hp.run hp.noColl hA.1 hk
  have hAH : A ∈ tr.HonestBlocks H := ⟨_, hA.1, k + 1, hAm⟩
  have hAs := run_slot hA
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨q, hq, _⟩ := hp.snapshot; exact ⟨q, hq⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := SA.gbar_nonneg g
    linarith
  have hau : sp.slot a + 2 * sp.k + 5 ≤ s := by
    rw [Healing.drainTime_eq] at hR
    exact_mod_cast (SA.ts_le_iff sp).1 hR
  have hu : 0 < s := by omega
  refine ⟨⟨k, hk⟩, hAH, hAs, hu, ?_, ?_⟩
  · intro he
    have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
    have hG := Healing.Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hA.1 k)
    have heq := hr.coherent.1 hAH ⟨_, hA.1, k, hG⟩ he
    have hz : A.slot = 0 := by rw [heq]; rfl
    omega
  · have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 2) ≤ sp.ts s :=
      (SA.ts_le_iff sp).2 (by omega)
    have hgap : sp.ts ((sp.slot a : Int) + 2) =
        sp.ts ((sp.slot a : Int) + 1) + 4 * sp.Δ := by
      simp only [SAParams.ts]; ring
    have := Healing.lt_cutZ sp g
    rw [hgap] at hle
    linarith

/-- **One route-A anchor step (gap `c`).** Honest proposals `A` at slot `s` and `X` at slot
`s + c`, `2 ≤ c`, after the drain and by the horizon, with `H_z + 2 ≤ σ[A].h` at an honest store
that holds `A`: `AnchorStep tr H A X`. The rows are signed by `t_s + 6Δ`, and the delivery
premise `t_s + 6Δ + ΔF ≤ t_{s+c}` delivers them by `t_{s+c}`. -/
theorem anchorStep_gap {g ΔR a b gS ΔF : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.HSSharedUpTo tr H dg gS ΔF b)
    {s c s' : Nat} (hc2 : 2 ≤ c) (hs' : s' = s + c)
    (hdel : sp.ts s + 6 * sp.Δ + ΔF ≤ sp.ts s')
    {A X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.HonestProposalRun tr H proposer s A)
    (hX : Healing.HonestProposalRun tr H proposer s' X)
    (hR : Healing.drainTime sp a ≤ sp.ts s) (hb : sp.ts s' ≤ b)
    (hgS : gbar gS ≤ sp.ts s + 6 * sp.Δ)
    (hh : ∃ y ∈ H, ∃ k, A ∈ (tr.state y k).fg.tree ∧
      Healing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ A.root).h) :
    AnchorStep tr H A X := by
  subst hs'
  have hrun := hp.run
  have hnc := hp.noColl
  have hΔ := sp.toParams.hΔ
  have h8 : sp.ts s + 8 * sp.Δ ≤ sp.ts (s + c : Nat) := by
    rw [ts_add_gap (sp := sp)]
    have : (2 : Time) ≤ c := by exact_mod_cast hc2
    nlinarith
  obtain ⟨⟨kA, hpropA⟩, hAHB, hAs, hu, hAg, hgu⟩ := anchor_facts hp hA hR
  obtain ⟨kX, hpropX⟩ := proposesAt_of_honestProposalRun hrun hX
  have hpX : proposer (s + c) ∈ H := hX.1
  obtain ⟨Pr, hpar, hPr⟩ := Healing.proposal_parent_held hrun hnc hpX hpropX
  have htX : tr.time kX = sp.ts (s + c : Nat) := by
    rw [proposesAt_time hpropX, run_slot hX]
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  have hAX : Anc (tr.HonestBlocks H) A X :=
    anchors_chain_upTo hp hc hA hR hX (by omega) hb (fun h => absurd h (by omega))
  have hne : A ≠ X := by
    intro he
    have := run_slot hX
    rw [← he, hAs] at this
    omega
  have hAPrH : Anc (tr.HonestBlocks H) A Pr :=
    anc_parent' hU hAX hne hpar ⟨_, hpX, kX, hPr⟩
  have hAPr := Healing.store_anc_of_honest_anc hrun hnc hpX hAPrH hPr
  have hAp := Healing.mem_of_honest_anc hrun hnc hpX hAPrH hPr
  have hhA : Healing.HZ tr H g + 2 ≤
      ((tr.state (proposer (s + c)) kX).fg.σ A.root).h := by
    obtain ⟨y, hy, k, hAy, hy2⟩ := hh
    rw [Healing.σ_eq_honest hrun hnc hpX hy hAp hAy]
    exact hy2
  have hTb : sp.ts s + 6 * sp.Δ ≤ b := by linarith
  refine anchorStep_of_or_crossed hrun hs (v := sp.ts s + 6 * sp.Δ) hgS hpX hpropX
    (by rw [htX]; linarith) (by rw [htX]; exact hb) hpar hPr hAPr ?_
  intro heq
  have hH := healed_of_reset_canonical_full_upTo hp hc
    (h₀ := Healing.HZ tr H g + 1) le_rfl A hR
  -- A higher honest report above `A` by `t_s + 6Δ` contradicts `heq`.
  have hcross : ∀ x ∈ H, ∀ r e C, SA.ToFGAt tr.projAC x r e C →
      tr.time r ≤ sp.ts s + 6 * sp.Δ → Anc (tr.HonestBlocks H) A C →
      ((tr.state x r).fg.σ A.root).h < ((tr.state x r).fg.σ C.root).h → False := by
    intro x hx r e C hto ht hAC hlt
    have htr : sp.ts s ≤ tr.time r := by
      have := report_slot_le_time hrun hnc hx hto hAC
      rw [hAs] at this
      exact this
    obtain ⟨Pr', hPr'H, hpar', -, habove⟩ :=
      crossed_parents_above_upTo hrun hnc hH hx hto htr hlt hX (by linarith) hb
    obtain rfl : Pr' = Pr := hU.1 hPr'H ⟨_, hpX, kX, hPr⟩
      (Option.some.inj (hpar'.symm.trans hpar))
    have hAx : A ∈ (tr.state x r).fg.tree :=
      Healing.mem_of_honest_anc hrun hnc hx hAC (Healing.toFG_mem_tree hrun hx hto)
    have := habove _ hpX kX hPr
    rw [Healing.σ_eq_honest hrun hnc hx hpX hAx hAp] at this
    omega
  rcases UpTo.report_cover_of_proposal hp hc hA.1 rfl hpropA hAHB hAs hu hAg hgu hR hTb with
    hall | ⟨x, hx, r, e, C, hto, ht, hAC, hlt⟩
  swap
  · exact (hcross x hx r e C hto ht hAC hlt).elim
  have hr := Compose.fg_reachable hrun.toLocalRun hpX kX
  obtain ⟨E, hE, hEr, hEA, hEh, hETh, hEJ, hEhj⟩ := Healing.entry_J_hj hr hAp
  have hTe : ((tr.state (proposer (s + c)) kX).fg.σ E.root).Th = E.root := by
    rw [hETh, hEr]
  have hhT : Healing.HZ tr H g + 1 ≤ ((tr.state (proposer (s + c)) kX).fg.σ E.root).h := by
    omega
  have hhj : ((tr.state (proposer (s + c)) kX).fg.σ E.root).bound →
      Healing.HZ tr H g + 1 ≤ ((tr.state (proposer (s + c)) kX).fg.σ E.root).hj := by
    intro hbd
    obtain ⟨-, h2⟩ := hbd
    omega
  have hreports : ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ sp.ts s + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) E C ∧
      ((tr.state z r).fg.σ C.root).h = ((tr.state (proposer (s + c)) kX).fg.σ E.root).h := by
    intro z hz
    obtain ⟨r, e, R, hto, ht, hAR⟩ := hall z hz
    refine ⟨r, e, R, hto, ht, (Healing.honest_anc_of_store_anc hpX hEA).trans hAR, ?_⟩
    have hRz := Healing.toFG_mem_tree hrun hz hto
    have hAz := Healing.mem_of_honest_anc hrun hnc hz hAR hRz
    have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hz r)
      (Healing.store_anc_of_honest_anc hrun hnc hz hAR hRz)
    rcases hle.lt_or_eq with hlt | heq'
    · exact (hcross z hz r e R hto ht hAR hlt).elim
    · rw [← heq', Healing.σ_eq_honest hrun hnc hz hpX hAz hAp, hEh]
  obtain ⟨ids, hcard, hids⟩ := hp.row_signers_of_reports hpX hE rfl hTe hhT hhj hTb hreports
  have hPrTh := Healing.Th_eq_of_anc hr hAPr heq
  obtain ⟨hPrJ, hPrhj⟩ := Healing.J_hj_eq_of_anc hr hAPr heq
  refine ⟨ids, fun z hz => (hids z hz).1, hcard, fun z hz => ?_⟩
  obtain ⟨-, att, j, hsig, -, hah, haT, hato, hjt, hfin⟩ := hids z hz
  refine ⟨j, att, hsig, hjt, ?_, ?_, hato, fun hbd _ => ?_⟩
  · rw [hah, hEh, heq]
  · rw [haT, hEr, hPrTh]
  · have hbE : ((tr.state (proposer (s + c)) kX).fg.σ E.root).bound := by
      obtain ⟨h1, h2⟩ := hbd
      exact ⟨by omega, by omega⟩
    rw [hfin hbE, hEJ, hEhj, hPrJ, hPrhj]

/-- A height bound at an honest anchor carries to a later honest proposal above it. -/
private theorem height_next {g ΔR a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s s' : Nat}
    {A X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.HonestProposalRun tr H proposer s A)
    (hX : Healing.HonestProposalRun tr H proposer s' X) (hss : s + 2 ≤ s')
    (hR : Healing.drainTime sp a ≤ sp.ts s) (hb : sp.ts s' ≤ b) {c : Nat}
    (hh : ∃ y ∈ H, ∃ k, A ∈ (tr.state y k).fg.tree ∧ c ≤ ((tr.state y k).fg.σ A.root).h) :
    ∃ y ∈ H, ∃ k, X ∈ (tr.state y k).fg.tree ∧ c ≤ ((tr.state y k).fg.σ X.root).h := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hAX : Anc (tr.HonestBlocks H) A X :=
    anchors_chain_upTo hp hc hA hR hX (by omega) hb (fun h => absurd h (by omega))
  obtain ⟨kX, hpropX⟩ := proposesAt_of_honestProposalRun hrun hX
  obtain ⟨-, hXm, -⟩ := Healing.accept_of_proposesAt hrun hnc hX.1 hpropX
  have hAz := Healing.mem_of_honest_anc hrun hnc hX.1 hAX hXm
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hX.1 (kX + 1))
    (Healing.store_anc_of_honest_anc hrun hnc hX.1 hAX hXm)
  obtain ⟨y, hy, k, hAy, hcy⟩ := hh
  rw [Healing.σ_eq_honest hrun hnc hX.1 hy hAz hAy] at hle
  exact ⟨_, hX.1, kX + 1, hXm, by omega⟩

/-- **The three route-A anchor steps (gap `c`).** Four honest proposals `P i` at the slots
`s₀ + [0, c, 2c, 3c]`, `2 ≤ c`, after the drain, `t_{s₀+3c} ≤ b`, the HS premises with the
delivery premise `6Δ + ΔF ≤ 4Δ·c` and `ḡ_S ≤ t_{s₀} + 6Δ`, and `H_z + 2 ≤ σ[P₀].h` at an
honest store that holds `P₀`: `AnchorStep tr H (P i) (P (i+1))` for `i < 3`. -/
theorem anchorSteps_gap {g ΔR a b gS ΔF : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.HSSharedUpTo tr H dg gS ΔF b) {c : Nat} (hc2 : 2 ≤ c)
    (hdel : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * c) {s₀ : Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s₀ + ![0, c, 2 * c, 3 * c] i) (P i))
    (hR : Healing.drainTime sp a ≤ sp.ts s₀) (hb : sp.ts (s₀ + 3 * c : Nat) ≤ b)
    (hgS : gbar gS ≤ sp.ts s₀ + 6 * sp.Δ)
    (hh₀ : ∃ y ∈ H, ∃ k, P 0 ∈ (tr.state y k).fg.tree ∧
      Healing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ (P 0).root).h) :
    ∀ i : Fin 3, AnchorStep tr H (P i.castSucc) (P i.succ) := by
  have hP0 : Healing.HonestProposalRun tr H proposer s₀ (P 0) := by simpa using hP 0
  have hP1 : Healing.HonestProposalRun tr H proposer (s₀ + c) (P 1) := by simpa using hP 1
  have hP2 : Healing.HonestProposalRun tr H proposer (s₀ + 2 * c) (P 2) := by
    simpa using hP 2
  have hP3 : Healing.HonestProposalRun tr H proposer (s₀ + 3 * c) (P 3) := by
    simpa using hP 3
  have hmono : ∀ m n : Nat, m ≤ n → sp.ts m ≤ sp.ts n := fun m n h =>
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hΔ := sp.toParams.hΔ
  have h1 := height_next hp hc hP0 hP1 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have h2 := height_next hp hc hP0 hP2 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have st0 := anchorStep_gap hp hc hs hc2 rfl (gap_delivery hdel s₀) hP0 hP1 hR
    ((hmono _ _ (by omega)).trans hb) hgS hh₀
  have st1 := anchorStep_gap hp hc hs hc2 (by omega) (by
      have := gap_delivery hdel (s₀ + c)
      have e : s₀ + c + c = s₀ + 2 * c := by omega
      rwa [e] at this) hP1 hP2
    (hR.trans (hmono _ _ (by omega))) ((hmono _ _ (by omega)).trans hb)
    (by linarith [hmono s₀ (s₀ + c) (by omega)]) h1
  have st2 := anchorStep_gap hp hc hs hc2 (by omega) (by
      have := gap_delivery hdel (s₀ + 2 * c)
      have e : s₀ + 2 * c + c = s₀ + 3 * c := by omega
      rwa [e] at this) hP2 hP3
    (hR.trans (hmono _ _ (by omega))) hb
    (by linarith [hmono s₀ (s₀ + 2 * c) (by omega)]) h2
  intro i
  fin_cases i
  exacts [st0, st1, st2]

end Consensus.Goldilocks.Refinement

end
