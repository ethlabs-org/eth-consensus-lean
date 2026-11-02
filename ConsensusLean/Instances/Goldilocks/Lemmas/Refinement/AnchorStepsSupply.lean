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

/-! # Goldilocks Refinement: the supply of the route-A anchor steps (#136, item 2)

consensus-lean#136, route A (anchors at the slots `s₀ + [0, 2, 4, 6]`). Paper: workbench
`route_a_gap2.md` §1, `anchor_row_supplier.md` (r2), `anchor_tick_ac_producer.md`.

* `anchorStep_gap2`: one step `A → X` between honest proposals two slots apart. At the tick
  `t_s + 6Δ`, `UpTo.report_cover_of_proposal` gives a report `⪰ A` from every honest node, or an
  honest report strictly above `A`. A higher report puts the parent of `X` above `A`
  (`crossed_parents_above_upTo`), so the rows are not needed. Otherwise every report is at the
  height of `A`, and `row_signers_of_reports` gives a quorum of exact rows of the entry of `A`,
  signed by `t_s + 6Δ`. With `ΔF ≤ 2Δ` they are delivered before `t_{s+2} = t_s + 8Δ`.
  The fin-highness premise follows from `H_z + 2 ≤ σ[A].h` and the definition of `bound`.
* `anchorSteps_gap2`: the three steps of the window. The height premise is explicit at `P₀`
  only; each step gives it at the next anchor.

Premises kept explicit: `ResetPremisesUpTo … b`, `CatchRun 2Δ`, `HSSharedUpTo … b` (with its
`timeoutDelay`), `ΔF ≤ 2Δ`, the four honest proposals, `drainTime a ≤ t_{s₀}`, `t_{s₀+6} ≤ b`,
`ḡ_S ≤ t_{s₀} + 6Δ`, and `H_z + 2 ≤ σ[P₀].h`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Two slots after `s`, the slot time is `8Δ` later. -/
private theorem ts_add_two (s : Nat) : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
  simp only [SAParams.ts]; push_cast; ring

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

/-- **One route-A anchor step (gap 2).** Honest proposals `A` at slot `s` and `X` at slot
`s + 2`, after the drain and by the horizon, with `H_z + 2 ≤ σ[A].h` at an honest store that
holds `A`: `AnchorStep tr H A X`. The rows are signed by `t_s + 6Δ`, and `ΔF ≤ 2Δ` delivers
them before `t_{s+2}`. -/
theorem anchorStep_gap2 {g ΔR a b gS ΔF : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.HSSharedUpTo tr H dg gS ΔF b) (hΔF : ΔF ≤ 2 * sp.Δ)
    {s s' : Nat} (hs' : s' = s + 2) {A X : SA.Blk sp.n (List (FG.Att sp.n))}
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
  have h8 := ts_add_two (sp := sp) s
  obtain ⟨⟨kA, hpropA⟩, hAHB, hAs, hu, hAg, hgu⟩ := anchor_facts hp hA hR
  obtain ⟨kX, hpropX⟩ := proposesAt_of_honestProposalRun hrun hX
  have hpX : proposer (s + 2) ∈ H := hX.1
  obtain ⟨Pr, hpar, hPr⟩ := Healing.proposal_parent_held hrun hnc hpX hpropX
  have htX : tr.time kX = sp.ts (s + 2 : Nat) := by
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
      ((tr.state (proposer (s + 2)) kX).fg.σ A.root).h := by
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
  have hTe : ((tr.state (proposer (s + 2)) kX).fg.σ E.root).Th = E.root := by
    rw [hETh, hEr]
  have hhT : Healing.HZ tr H g + 1 ≤ ((tr.state (proposer (s + 2)) kX).fg.σ E.root).h := by
    omega
  have hhj : ((tr.state (proposer (s + 2)) kX).fg.σ E.root).bound →
      Healing.HZ tr H g + 1 ≤ ((tr.state (proposer (s + 2)) kX).fg.σ E.root).hj := by
    intro hbd
    obtain ⟨-, h2⟩ := hbd
    omega
  have hreports : ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ sp.ts s + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) E C ∧
      ((tr.state z r).fg.σ C.root).h = ((tr.state (proposer (s + 2)) kX).fg.σ E.root).h := by
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
  · have hbE : ((tr.state (proposer (s + 2)) kX).fg.σ E.root).bound := by
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

/-- **The three route-A anchor steps.** Four honest proposals `P i` at the slots
`s₀ + [0, 2, 4, 6]` after the drain, `t_{s₀+6} ≤ b`, the HS premises with `ΔF ≤ 2Δ` and
`ḡ_S ≤ t_{s₀} + 6Δ`, and `H_z + 2 ≤ σ[P₀].h` at an honest store that holds `P₀` (item 1):
`AnchorStep tr H (P i) (P (i+1))` for `i < 3` (the form of `FinalWindowData.AnchorSteps`). -/
theorem anchorSteps_gap2 {g ΔR a b gS ΔF : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.HSSharedUpTo tr H dg gS ΔF b) (hΔF : ΔF ≤ 2 * sp.Δ) {s₀ : Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s₀ + ![0, 2, 4, 6] i) (P i))
    (hR : Healing.drainTime sp a ≤ sp.ts s₀) (hb : sp.ts (s₀ + 6 : Nat) ≤ b)
    (hgS : gbar gS ≤ sp.ts s₀ + 6 * sp.Δ)
    (hh₀ : ∃ y ∈ H, ∃ k, P 0 ∈ (tr.state y k).fg.tree ∧
      Healing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ (P 0).root).h) :
    ∀ i : Fin 3, AnchorStep tr H (P i.castSucc) (P i.succ) := by
  have hP0 : Healing.HonestProposalRun tr H proposer s₀ (P 0) := by simpa using hP 0
  have hP1 : Healing.HonestProposalRun tr H proposer (s₀ + 2) (P 1) := by simpa using hP 1
  have hP2 : Healing.HonestProposalRun tr H proposer (s₀ + 4) (P 2) := by simpa using hP 2
  have hP3 : Healing.HonestProposalRun tr H proposer (s₀ + 6) (P 3) := by simpa using hP 3
  have hmono : ∀ m n : Nat, m ≤ n → sp.ts m ≤ sp.ts n := fun m n h =>
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hΔ := sp.toParams.hΔ
  have h1 := height_next hp hc hP0 hP1 le_rfl hR ((hmono _ _ (by omega)).trans hb) hh₀
  have h2 := height_next hp hc hP0 hP2 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have st0 := anchorStep_gap2 hp hc hs hΔF rfl hP0 hP1 hR
    ((hmono _ _ (by omega)).trans hb) hgS hh₀
  have st1 := anchorStep_gap2 hp hc hs hΔF (by omega) hP1 hP2
    (hR.trans (hmono _ _ (by omega))) ((hmono _ _ (by omega)).trans hb)
    (by linarith [hmono s₀ (s₀ + 2) (by omega)]) h1
  have st2 := anchorStep_gap2 hp hc hs hΔF (by omega) hP2 hP3
    (hR.trans (hmono _ _ (by omega))) hb
    (by linarith [hmono s₀ (s₀ + 4) (by omega)]) h2
  intro i
  fin_cases i
  exacts [st0, st1, st2]

end Consensus.Goldilocks.Refinement

end
