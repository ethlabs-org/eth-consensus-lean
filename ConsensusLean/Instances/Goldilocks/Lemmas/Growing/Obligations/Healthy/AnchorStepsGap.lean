module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowFieldsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.AnchorStepsGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowCrossing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalUnanimous
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinPair
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The route-A anchor steps at a gap `c`, under growing faults

The growing form of `Obligations/AnchorStepsGap`. A height witness is an honest holder at a cut,
honest at that cut's time; replay states of a block agree across independently honest holders
(`Healing.Growing.σ_eq_honest_at`), so a height bound read at one holder is read at every other.

* `anchorStep_gap_at`: one step `A → X`, `A` at slot `s`, `X` at slot `s + c`, `2 ≤ c`, with the
  delivery premise `t_s + 6Δ + ΔF ≤ t_{s+c}`;
* `anchorSteps_gap_at`: the three steps of the window, anchors at `s₀ + [0, c, 2c, 3c]`, with the
  slot-free delivery premise `6Δ + ΔF ≤ 4Δ·c`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A proper ancestor of a block is an ancestor of its parent. -/
private theorem anc_parent_at {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {A B Q : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc U A B) (hne : A ≠ B)
    (hBQ : B.parent = some Q.root) (hQ : Q ∈ U) : Anc U A Q := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hAY, hY⟩
  · exact absurd heq.symm hne
  obtain rfl : Y = Q := hU.1 hY.1 hQ (Option.some_injective _ (hY.2.2.symm.trans hBQ))
  exact hAY

/-- The facts of a post-drain honest anchor that `report_cover_of_unanimous_at` reads. -/
private theorem anchor_facts_at {g ΔR a b : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b) {s : Nat}
    {A : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.Growing.HonestProposalRun tr H proposer s A)
    (hR : Healing.drainTime sp a ≤ sp.ts s) :
    (∃ k, tr.ProposesAt (proposer s) k A) ∧ A ∈ tr.HonestBlocksAt H ∧ A.slot = s ∧ 0 < s ∧
      A.root ≠ sp.genesisRoot ∧ gbar g + 4 * sp.Δ ≤ sp.ts s := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨k, hk, hm, -, hAm⟩ := proposal_held_at hp.run hp.noColl hA
  have h0 := hp.run.time_nonneg k
  have hle1 : ∀ q < k + 1, tr.time q ≤ tr.time k := fun _ hq => hp.run.time_mono (by omega)
  have hAH : A ∈ tr.HonestBlocksAt H := ⟨_, k + 1, tr.time k, h0, hle1, hm, hAm⟩
  have hAs := honestProposalRun_slot_at hA
  have hca := hp.cutZ_lt_reset_at
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
    have hG := Healing.Store.genesis_mem (Healing.Growing.fg_reachable_at hp.run h0 hle1 hm)
    have heq := (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1 hAH
      ⟨_, k + 1, tr.time k, h0, hle1, hm, hG⟩ he
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

/-- **One route-A anchor step (gap `c`)** under growing faults. Honest proposals `A` at slot `s`
and `X` at slot `s + c`, `2 ≤ c`, after the drain and by the horizon, with `H_z + 2 ≤ σ[A].h` at
a holder honest at its cut: `AnchorStepAt tr H A X`. -/
theorem anchorStep_gap_at {g ΔR a b gS ΔF : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b)
    {s c s' : Nat} (hc2 : 2 ≤ c) (hs' : s' = s + c)
    (hdel : sp.ts s + 6 * sp.Δ + ΔF ≤ sp.ts s')
    {A X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.Growing.HonestProposalRun tr H proposer s A)
    (hX : Healing.Growing.HonestProposalRun tr H proposer s' X)
    (hR : Healing.drainTime sp a ≤ sp.ts s) (hb : sp.ts s' ≤ b)
    (hgS : gbar gS ≤ sp.ts s + 6 * sp.Δ)
    (hh : ∃ y k, y ∈ H (tr.time k) ∧ A ∈ (tr.state y k).fg.tree ∧
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ A.root).h) :
    AnchorStepAt tr H A X := by
  subst hs'
  have hrun := hp.run
  have hnc := hp.noColl
  have hΔ := sp.toParams.hΔ
  have h8 : sp.ts s + 8 * sp.Δ ≤ sp.ts (s + c : Nat) := by
    rw [ts_add_gap (sp := sp)]
    have : (2 : Time) ≤ c := by exact_mod_cast hc2
    linarith [mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_four hΔ.le)]
  obtain ⟨⟨kA, hpropA⟩, hAHB, hAs, hu, hAg, hgu⟩ := anchor_facts_at hp hA hR
  obtain ⟨kX, hpropX, hpX, -, -⟩ := proposal_held_at hrun hnc hX
  obtain ⟨Pr, hpar, hPr⟩ := proposal_parent_held_at hrun hnc hpX hpropX
  have htX : tr.time kX = sp.ts (s + c : Nat) := by
    rw [hpropX.2.2, honestProposalRun_slot_at hX, sp.slotTime_eq]; rfl
  have h0 := hrun.time_nonneg kX
  have hle0 : ∀ q < kX, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hAX : Anc (tr.HonestBlocksAt H) A X :=
    anchors_chain_upTo_at hp hc hA hR hX (by omega) hb (fun h => absurd h (by omega))
  have hne : A ≠ X := by
    intro he
    have := honestProposalRun_slot_at hX
    rw [← he, hAs] at this
    omega
  have hPrH : Pr ∈ tr.HonestBlocksAt H := ⟨_, kX, tr.time kX, h0, hle0, hpX, hPr⟩
  have hAPrH : Anc (tr.HonestBlocksAt H) A Pr := anc_parent_at hU hAX hne hpar hPrH
  have hAPr := Healing.Growing.store_anc_of_honest_anc_at hrun hnc h0 hle0 hpX hAPrH hPr
  have hAp := Healing.Growing.mem_of_honest_anc_at hrun hnc h0 hle0 hpX hAPrH hPr
  have hhA : Healing.Growing.HZ tr H g + 2 ≤
      ((tr.state (proposer (s + c)) kX).fg.σ A.root).h := by
    obtain ⟨y, k, hy, hAy, hy2⟩ := hh
    rw [Healing.Growing.σ_eq_honest_at hrun hnc h0 hle0 hpX (hrun.time_nonneg k)
      (fun _ hq => hrun.time_mono hq.le) hy hAp hAy]
    exact hy2
  have hTb : sp.ts s + 6 * sp.Δ ≤ b := by linarith
  refine anchorStep_of_or_crossed_at hrun hs (v := sp.ts s + 6 * sp.Δ) hgS hpX hpropX
    (by rw [htX]; linarith) (by rw [htX]; exact hb) hpar hPr hAPr ?_
  intro heq
  -- A higher report above `A` by `t_s + 6Δ`, of a node honest at it, contradicts `heq`.
  have hcross : ∀ x r e C, x ∈ H (tr.time r) → SA.ToFGAt tr.projAC x r e C →
      tr.time r ≤ sp.ts s + 6 * sp.Δ → Anc (tr.HonestBlocksAt H) A C →
      ((tr.state x r).fg.σ A.root).h < ((tr.state x r).fg.σ C.root).h → False := by
    intro x r e C hx hto ht hAC hlt
    have hleR : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono hq.le
    have htr : sp.ts s ≤ tr.time r := by
      have := report_slot_le_time_at hrun hnc hx hto hAC
      rwa [hAs] at this
    obtain ⟨Pr', hPr'H, hpar', -, habove⟩ :=
      crossed_parents_above_upTo_at hp hc hx hto (hR.trans htr) hlt hX (by linarith) hb
    obtain rfl : Pr' = Pr := hU.1 hPr'H hPrH (Option.some.inj (hpar'.symm.trans hpar))
    have hAx : A ∈ (tr.state x r).fg.tree :=
      Healing.Growing.mem_of_honest_anc_at hrun hnc (hrun.time_nonneg r) hleR hx hAC
        (Healing.Growing.toFG_mem_tree_at hrun hx hto)
    have := habove _ kX (tr.time kX) h0 hle0 hpX hPr
    rw [Healing.Growing.σ_eq_honest_at hrun hnc (hrun.time_nonneg r) hleR hx h0 hle0 hpX hAx
      hAp] at this
    omega
  have hR1 : Healing.drainTime sp a ≤ sp.ts (s + 1 : Nat) :=
    hR.trans ((SA.ts_le_iff sp).2 (by push_cast; omega))
  have hun := hp.operational_unanimous_at hc hA.1 rfl hpropA hAs hR (by linarith)
  rcases Healing.Growing.report_cover_of_unanimous_at hp hc hAHB hAs hu hAg
      (fun y j e hy hv hjb hs' => hun y j e hy hv hs' hjb) hgu hR1 hTb with
    hall | ⟨x, r, e, C, hx, hto, ht, hAC, hlt⟩
  swap
  · exact (hcross x r e C hx hto ht hAC hlt).elim
  have hr := Healing.Growing.fg_reachable_at hrun h0 hle0 hpX
  obtain ⟨E, hE, hEr, hEA, hEh, hETh, hEJ, hEhj⟩ := Healing.entry_J_hj hr hAp
  have hTe : ((tr.state (proposer (s + c)) kX).fg.σ E.root).Th = E.root := by
    rw [hETh, hEr]
  have hhT : Healing.Growing.HZ tr H g + 1 ≤
      ((tr.state (proposer (s + c)) kX).fg.σ E.root).h := by
    omega
  have hhj : ((tr.state (proposer (s + c)) kX).fg.σ E.root).previousHeightJustified →
      Healing.Growing.HZ tr H g + 1 ≤ ((tr.state (proposer (s + c)) kX).fg.σ E.root).hj := by
    intro hbd
    obtain ⟨-, h2⟩ := hbd
    omega
  have hd0 : 0 ≤ sp.ts s + 6 * sp.Δ := by linarith [SA.gbar_nonneg g]
  have hreports : ∀ z, z ∈ H (sp.ts s + 6 * sp.Δ) → ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ sp.ts s + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) E C ∧
      ((tr.state z r).fg.σ C.root).h = ((tr.state (proposer (s + c)) kX).fg.σ E.root).h := by
    intro z hz
    obtain ⟨r, e, R, hto, ht, hAR⟩ := hall z hz
    have hzr : z ∈ H (tr.time r) := hrun.antitone ht hz
    have hleR : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono hq.le
    have hr0 := hrun.time_nonneg r
    refine ⟨r, e, R, hto, ht,
      (Healing.Growing.honest_anc_of_store_anc_at h0 hle0 hpX hEA).trans hAR, ?_⟩
    have hRz := Healing.Growing.toFG_mem_tree_at hrun hzr hto
    have hAz := Healing.Growing.mem_of_honest_anc_at hrun hnc hr0 hleR hzr hAR hRz
    have hle := Healing.h_le_of_store_anc (Healing.Growing.fg_reachable_at hrun hr0 hleR hzr)
      (Healing.Growing.store_anc_of_honest_anc_at hrun hnc hr0 hleR hzr hAR hRz)
    rcases hle.lt_or_eq with hlt | heq'
    · exact (hcross z r e R hzr hto ht hAR hlt).elim
    · rw [← heq', Healing.Growing.σ_eq_honest_at hrun hnc hr0 hleR hzr h0 hle0 hpX hAz hAp, hEh]
  obtain ⟨ids, hcard, hids⟩ :=
    hp.row_signers_of_reports_at h0 hle0 hpX hE rfl hTe hhT hhj hd0 hTb hreports
  have hPrTh := Healing.Th_eq_of_anc hr hAPr heq
  obtain ⟨hPrJ, hPrhj⟩ := Healing.J_hj_eq_of_anc hr hAPr heq
  refine ⟨ids, hcard, fun z hz => ?_⟩
  obtain ⟨hzd, att, j, hsig, -, hah, haT, hato, hjt, hfin⟩ := hids z hz
  refine ⟨j, att, hrun.antitone hjt hzd, hsig, hjt, ?_, ?_, hato, fun hbd _ => ?_⟩
  · rw [hah, hEh, heq]
  · rw [haT, hEr, hPrTh]
  · have hbE : ((tr.state (proposer (s + c)) kX).fg.σ E.root).previousHeightJustified := by
      obtain ⟨h1, h2⟩ := hbd
      exact ⟨by omega, by omega⟩
    rw [hfin hbE, hEJ, hEhj, hPrJ, hPrhj]

/-- A height bound at a holder honest at its cut carries to a later honest proposal above it,
read at its proposer just after the proposal cut. -/
private theorem height_next_at {g ΔR a b : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s s' : Nat}
    {A X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.Growing.HonestProposalRun tr H proposer s A)
    (hX : Healing.Growing.HonestProposalRun tr H proposer s' X) (hss : s + 2 ≤ s')
    (hR : Healing.drainTime sp a ≤ sp.ts s) (hb : sp.ts s' ≤ b) {c : Nat}
    (hh : ∃ y k, y ∈ H (tr.time k) ∧ A ∈ (tr.state y k).fg.tree ∧
      c ≤ ((tr.state y k).fg.σ A.root).h) :
    ∃ y k, y ∈ H (tr.time k) ∧ X ∈ (tr.state y k).fg.tree ∧
      c ≤ ((tr.state y k).fg.σ X.root).h := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hAX : Anc (tr.HonestBlocksAt H) A X :=
    anchors_chain_upTo_at hp hc hA hR hX (by omega) hb (fun h => absurd h (by omega))
  obtain ⟨kX, -, hm, ht, hXm⟩ := proposal_held_at hrun hnc hX
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono (by omega)
  have h0 := hrun.time_nonneg kX
  have hAz := Healing.Growing.mem_of_honest_anc_at hrun hnc h0 hle1 hm hAX hXm
  have hle := Healing.h_le_of_store_anc (Healing.Growing.fg_reachable_at hrun h0 hle1 hm)
    (Healing.Growing.store_anc_of_honest_anc_at hrun hnc h0 hle1 hm hAX hXm)
  obtain ⟨y, k, hy, hAy, hcy⟩ := hh
  rw [Healing.Growing.σ_eq_honest_at hrun hnc h0 hle1 hm (hrun.time_nonneg k)
    (fun _ hq => hrun.time_mono hq.le) hy hAz hAy] at hle
  exact ⟨_, kX + 1, ht ▸ hm, hXm, by omega⟩

/-- **The three route-A anchor steps (gap `c`)** under growing faults. Four honest proposals
`P i` at the slots `s₀ + [0, c, 2c, 3c]`, `2 ≤ c`, after the drain, `t_{s₀+3c} ≤ b`, the HS
premises with `6Δ + ΔF ≤ 4Δ·c` and `ḡ_S ≤ t_{s₀} + 6Δ`, and `H_z + 2 ≤ σ[P₀].h` at a holder
honest at its cut: `AnchorStepAt tr H (P i) (P (i+1))` for `i < 3`. -/
theorem anchorSteps_gap_at {g ΔR a b gS ΔF : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b) {c : Nat} (hc2 : 2 ≤ c)
    (hdel : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * c) {s₀ : Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.Growing.HonestProposalRun tr H proposer
      (s₀ + ![0, c, 2 * c, 3 * c] i) (P i))
    (hR : Healing.drainTime sp a ≤ sp.ts s₀) (hb : sp.ts (s₀ + 3 * c : Nat) ≤ b)
    (hgS : gbar gS ≤ sp.ts s₀ + 6 * sp.Δ)
    (hh₀ : ∃ y k, y ∈ H (tr.time k) ∧ P 0 ∈ (tr.state y k).fg.tree ∧
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ (P 0).root).h) :
    ∀ i : Fin 3, AnchorStepAt tr H (P i.castSucc) (P i.succ) := by
  have hP0 : Healing.Growing.HonestProposalRun tr H proposer s₀ (P 0) := by simpa using hP 0
  have hP1 : Healing.Growing.HonestProposalRun tr H proposer (s₀ + c) (P 1) := by
    simpa using hP 1
  have hP2 : Healing.Growing.HonestProposalRun tr H proposer (s₀ + 2 * c) (P 2) := by
    simpa using hP 2
  have hP3 : Healing.Growing.HonestProposalRun tr H proposer (s₀ + 3 * c) (P 3) := by
    simpa using hP 3
  have hmono : ∀ m n : Nat, m ≤ n → sp.ts m ≤ sp.ts n := fun m n h =>
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hΔ := sp.toParams.hΔ
  have h1 := height_next_at hp hc hP0 hP1 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have h2 := height_next_at hp hc hP0 hP2 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have st0 := anchorStep_gap_at hp hc hs hc2 rfl (gap_delivery hdel s₀) hP0 hP1 hR
    ((hmono _ _ (by omega)).trans hb) hgS hh₀
  have st1 := anchorStep_gap_at hp hc hs hc2 (by omega) (by
      have := gap_delivery hdel (s₀ + c)
      have e : s₀ + c + c = s₀ + 2 * c := by omega
      rwa [e] at this) hP1 hP2
    (hR.trans (hmono _ _ (by omega))) ((hmono _ _ (by omega)).trans hb)
    (by linarith [hmono s₀ (s₀ + c) (by omega)]) h1
  have st2 := anchorStep_gap_at hp hc hs hc2 (by omega) (by
      have := gap_delivery hdel (s₀ + 2 * c)
      have e : s₀ + 2 * c + c = s₀ + 3 * c := by omega
      rwa [e] at this) hP2 hP3
    (hR.trans (hmono _ _ (by omega))) hb
    (by linarith [hmono s₀ (s₀ + 2 * c) (by omega)]) h2
  intro i
  fin_cases i
  exacts [st0, st1, st2]

end Consensus.Goldilocks.Obligations.Growing

end
