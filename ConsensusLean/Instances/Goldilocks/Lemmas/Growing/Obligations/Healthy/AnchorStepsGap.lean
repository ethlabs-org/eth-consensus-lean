module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowFieldsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowSupply
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedToFG
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCoverDelayed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.AnchorStepsGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowCrossing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalUnanimous
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinPair
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DrainedAnchorSlot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The route-A anchor steps at a gap `c`, under growing faults

The growing form of `Obligations/AnchorStepsGap`. A height witness is an honest holder at a cut,
honest at that cut's time; replay states of a block agree across independently honest holders
(`Healing.Growing.σ_eq_honest_at`), so a height bound read at one holder is read at every other.

The signing gap is paid at each report deadline. `anchorSteps_gap_delayed_at` links the four
anchors at `s₀ + [0, c, 2c, 3c]` using the budget `6Δ + G·Δ + ΔF ≤ 4Δ·c`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}
variable {hold : Time}

/-- The facts of a post-drain honest anchor used to obtain report coverage. -/
private theorem anchor_facts_at {g ΔR a b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold) {s : Nat}
    {A : AC.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.Growing.HonestProposalRun tr H proposer s A)
    (hR : Healing.drainTime sp a ≤ sp.ts s) :
    (∃ k, tr.ProposesAt (proposer s) k A) ∧ A ∈ tr.HonestBlocksAt H ∧ A.slot = s ∧ 0 < s ∧
      A.root ≠ sp.genesisRoot ∧ gbar g + 4 * sp.Δ ≤ sp.ts s := by
  obtain ⟨k, hk, hm, -, hAm⟩ := proposal_held_at hp.run hp.noColl hA
  have h0 := hp.run.time_nonneg k
  have hle1 : ∀ q < k + 1, tr.time q ≤ tr.time k := fun _ hq => hp.run.time_mono (by omega)
  have hAH : A ∈ tr.HonestBlocksAt H := ⟨_, k + 1, tr.time k, h0, hle1, hm, hAm⟩
  have hAs := honestProposalRun_slot_at hA
  obtain ⟨hau, hgu⟩ := drained_anchor_slot hp.cutZ_lt_reset_at hR
  have hu : 0 < s := by omega
  refine ⟨⟨k, hk⟩, hAH, hAs, hu, fun he => ?_, hgu⟩
  have hG := Healing.Store.genesis_mem (Healing.Growing.fg_reachable_at hp.run h0 hle1 hm)
  have heq := (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1 hAH
    ⟨_, k + 1, tr.time k, h0, hle1, hm, hG⟩ he
  have hz : A.slot = 0 := by rw [heq]; rfl
  omega

/-- **One route-A anchor step (gap `c`) under a signing delay `D`.** Honest proposals `A` at
slot `s` and `X` at slot `s + c`, `2 ≤ c`, after the drain and by the horizon, with
`H_z + 2 ≤ σ[A].h` at a holder honest at its cut, rows supplied within `D` of the reports
by signers honest a hold later (`RowSupplyWithin`), rows signed by `t_s + 6Δ + D` delivered to
`X`'s proposer (`hdel`), and a higher report by then seen by it
(`hcr`): `AnchorStepAt tr H A X`. -/
private theorem anchorStep_of_reports_within_at {g ΔR a b gS ΔF D hold : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b hold)
    (hhold : 0 ≤ hold)
    {s c s' : Nat} (hc2 : 2 ≤ c) (hs' : s' = s + c)
    (hsup : Healing.Growing.RowSupplyWithin tr H g b D hold) (hD : 0 ≤ D)
    {G : Nat}
    (hdel : sp.ts s + 6 * sp.Δ + G * sp.Δ + D + ΔF ≤ sp.ts s')
    (hcr : sp.ts s + 6 * sp.Δ + G * sp.Δ + D + sp.Δ ≤ sp.ts s')
    {A X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hcover : ∀ (_ : A ∈ tr.HonestBlocksAt H) (_ : A.slot = s)
      (_ : 0 < s) (_ : A.root ≠ sp.genesisRoot)
      (_ : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
        e.msg.slot = s → e.msg.head = A.root)
      (_ : gbar g + 4 * sp.Δ ≤ sp.ts s)
      (_ : Healing.drainTime sp a ≤ sp.ts (s + 1 : Nat))
      (_ : sp.ts s + 6 * sp.Δ + G * sp.Δ ≤ b),
      (∀ y, y ∈ H (sp.ts s + 6 * sp.Δ + G * sp.Δ) → ∃ r e R,
        AC.ToFGAt tr.projAC y r e R ∧ tr.time r ≤ sp.ts s + 6 * sp.Δ + G * sp.Δ ∧
        Anc (tr.HonestBlocksAt H) A R) ∨
      (∃ x r e C, x ∈ H (max (Healing.cutZ sp.toParams g) (tr.time r)) ∧
        AC.ToFGAt tr.projAC x r e C ∧ tr.time r ≤ sp.ts s + 6 * sp.Δ + G * sp.Δ ∧
        Anc (tr.HonestBlocksAt H) A C ∧
        ((tr.state x r).fg.σ A.root).h < ((tr.state x r).fg.σ C.root).h))
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
  have hG : (0 : Time) ≤ G * sp.Δ := mul_nonneg (Int.natCast_nonneg _) hΔ.le
  obtain ⟨⟨kA, hpropA⟩, hAHB, hAs, hu, hAg, hgu⟩ := anchor_facts_at hp hA hR
  obtain ⟨kX, hpropX, hpX, -, -⟩ := proposal_held_at hrun hnc hX
  obtain ⟨Pr, hpar, hPr⟩ := proposal_parent_held_at hrun hnc hpX hpropX
  have htX : tr.time kX = sp.ts (s + c : Nat) := by
    rw [hpropX.2.2, honestProposalRun_slot_at hX, sp.slotTime_eq]; rfl
  have h0 := hrun.time_nonneg kX
  have hle0 : ∀ q < kX, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hAX : Anc (tr.HonestBlocksAt H) A X :=
    anchors_chain_upTo_at hp hA hR hX (by omega) hb (fun h => absurd h (by omega))
  have hne : A ≠ X := by
    intro he
    have := honestProposalRun_slot_at hX
    rw [← he, hAs] at this
    omega
  have hPrH : Pr ∈ tr.HonestBlocksAt H := ⟨_, kX, tr.time kX, h0, hle0, hpX, hPr⟩
  have hAPrH : Anc (tr.HonestBlocksAt H) A Pr := Compose.anc_parent hU hAX hne hpar hPrH
  have hAPr := Healing.Growing.store_anc_of_honest_anc_at hrun hnc h0 hle0 hpX hAPrH hPr
  have hAp := Healing.Growing.mem_of_honest_anc_at hrun hnc h0 hle0 hpX hAPrH hPr
  have hhA : Healing.Growing.HZ tr H g + 2 ≤
      ((tr.state (proposer (s + c)) kX).fg.σ A.root).h := by
    obtain ⟨y, k, hy, hAy, hy2⟩ := hh
    rw [Healing.Growing.σ_eq_honest_at hrun hnc h0 hle0 hpX (hrun.time_nonneg k)
      (fun _ hq => hrun.time_mono hq.le) hy hAp hAy]
    exact hy2
  have hTb : sp.ts s + 6 * sp.Δ + G * sp.Δ ≤ b := by linarith
  have hTDb : sp.ts s + 6 * sp.Δ + G * sp.Δ + D + hold ≤ b := by
    linarith [hs.sync.hold_le]
  refine anchorStep_of_or_crossed_at hrun hs hhold
    (v := sp.ts s + 6 * sp.Δ + G * sp.Δ + D) (by linarith) hpX
    hpropX (by rw [htX]; linarith) (by rw [htX]; exact hb) hpar hPr hAPr ?_
  intro heq
  -- A higher report above `A` by `t_s + 6Δ`, of a node honest at it, contradicts `heq`.
  have hcross : ∀ x r e C, x ∈ H (tr.time r) → AC.ToFGAt tr.projAC x r e C →
      tr.time r ≤ sp.ts s + 6 * sp.Δ + G * sp.Δ → Anc (tr.HonestBlocksAt H) A C →
      ((tr.state x r).fg.σ A.root).h < ((tr.state x r).fg.σ C.root).h → False := by
    intro x r e C hx hto ht hAC hlt
    have hleR : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono hq.le
    have htr : sp.ts s ≤ tr.time r := by
      have := report_slot_le_time_at hrun hnc hx hto hAC
      rwa [hAs] at this
    obtain ⟨Pr', hPr'H, hpar', -, habove⟩ :=
      crossed_parents_above_upTo_at hp hx hto (hR.trans htr) hlt hX (by linarith) hb
    obtain rfl : Pr' = Pr := hU.1 hPr'H hPrH (Option.some.inj (hpar'.symm.trans hpar))
    have hAx : A ∈ (tr.state x r).fg.tree :=
      Healing.Growing.mem_of_honest_anc_at hrun hnc (hrun.time_nonneg r) hleR hx hAC
        (Healing.Growing.toFG_mem_tree_at hrun hx hto)
    have := habove _ kX (tr.time kX) h0 hle0 hpX hPr
    rw [Healing.Growing.σ_eq_honest_at hrun hnc (hrun.time_nonneg r) hleR hx h0 hle0 hpX hAx
      hAp] at this
    omega
  have hR1 : Healing.drainTime sp a ≤ sp.ts (s + 1 : Nat) :=
    hR.trans ((AC.ts_le_iff sp).2 (by push_cast; omega))
  have hun := hp.operational_unanimous_at hA.1 rfl hpropA hAs hR (by linarith)
  rcases hcover hAHB hAs hu hAg
      (fun y j e hy hv hjb hs' => hun y j e hy hv hs' hjb) hgu hR1 hTb with
    hall | ⟨x, r, e, C, hx, hto, ht, hAC, hlt⟩
  swap
  · exact (hcross x r e C (hrun.antitone (le_max_right _ _) hx) hto ht hAC hlt).elim
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
  have hd0 : 0 ≤ sp.ts s + 6 * sp.Δ := by linarith [Healing.gbar_nonneg g]
  have hreports : ∀ z, z ∈ H
      (max (Healing.cutZ sp.toParams g) (sp.ts s + 6 * sp.Δ + G * sp.Δ)) →
      ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ sp.ts s + 6 * sp.Δ + G * sp.Δ ∧ Anc (tr.HonestBlocksAt H) E C ∧
      ((tr.state z r).fg.σ C.root).h = ((tr.state (proposer (s + c)) kX).fg.σ E.root).h := by
    intro z hzz
    have hz := hrun.antitone (le_max_right _ _) hzz
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
  rcases hsup.supply h0 hle0 hpX hE rfl hTe hhT hhj (by linarith [hd0]) hTDb hreports with
    ⟨ids, hcard, hids⟩ | ⟨x, r, e, C, hx, hto, hdr, hrD, hlt⟩
  swap
  · -- A delayed vote used a higher source: its report lifts `X`'s parent above the entry.
    obtain ⟨Pr', hPr'H, hpar', -, habove⟩ :=
      crossed_parents_above_upTo_at hp hx hto (hR.trans (by linarith)) hlt hX (by linarith) hb
    obtain rfl : Pr' = Pr := hU.1 hPr'H hPrH (Option.some.inj (hpar'.symm.trans hpar))
    have := habove _ kX (tr.time kX) h0 hle0 hpX hPr
    rw [hEh, heq] at this
    omega
  have hPrTh := Healing.Th_eq_of_anc hr hAPr heq
  obtain ⟨hPrJ, hPrhj⟩ := Healing.J_hj_eq_of_anc hr hAPr heq
  refine ⟨ids, hcard, fun z hz => ?_⟩
  obtain ⟨hzd, att, j, hsig, -, hah, haT, hato, hjt, hfin⟩ := hids z hz
  refine ⟨j, att, hrun.antitone (le_max_right _ _) hzd, hsig, hjt, ?_, ?_, hato,
    fun hbd _ => ?_⟩
  · rw [hah, hEh, heq]
  · rw [haT, hEr, hPrTh]
  · have hbE : ((tr.state (proposer (s + c)) kX).fg.σ E.root).previousHeightJustified := by
      obtain ⟨h1, h2⟩ := hbd
      exact ⟨by omega, by omega⟩
    rw [hfin hbE, hEJ, hEhj, hPrJ, hPrhj]

/-- One anchor step using reports delayed by the signing calendar, with no additional row delay. -/
theorem anchorStep_gap_delayed_at {g ΔR a b gS ΔF hold : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    {sign : Fin sp.n → Time → Bool} (hcal : RunTrace.SignCalendarAt tr proposer dg H sign)
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b hold)
    (hhold : 0 ≤ hold)
    {s c s' G : Nat} (hc2 : 2 ≤ c) (hs' : s' = s + c)
    (hgap : SignGapAt sp.toParams sign G (sp.ts s + 6 * sp.Δ))
    (hdel : sp.ts s + 6 * sp.Δ + G * sp.Δ + ΔF ≤ sp.ts s')
    (hcr : sp.ts s + 7 * sp.Δ + G * sp.Δ ≤ sp.ts s')
    {A X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.Growing.HonestProposalRun tr H proposer s A)
    (hX : Healing.Growing.HonestProposalRun tr H proposer s' X)
    (hR : Healing.drainTime sp a ≤ sp.ts s) (hb : sp.ts s' ≤ b)
    (hgS : gbar gS ≤ sp.ts s + 6 * sp.Δ)
    (hh : ∃ y k, y ∈ H (tr.time k) ∧ A ∈ (tr.state y k).fg.tree ∧
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ A.root).h) :
    AnchorStepAt tr H A X := by
  apply anchorStep_of_reports_within_at hp hs hhold hc2 hs' (hp.rowSupplyWithin_zero hhold)
    le_rfl
    (G := G) (by simpa using hdel) (by linarith) _ hA hX hR hb hgS hh
  intro hAH hAs hu hAg hun hgu hR hb
  exact Healing.Growing.report_cover_delayed_of_unanimous_at hp hcal hgap
    hAH hAs hu hAg hun hgu hR hb

/-- A height bound at a holder honest at its cut carries to a later honest proposal above it,
read at its proposer just after the proposal cut. -/
private theorem height_next_at {g ΔR a b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    {s s' : Nat}
    {A X : AC.Blk sp.n (List (FG.Att sp.n))}
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
    anchors_chain_upTo_at hp hA hR hX (by omega) hb (fun h => absurd h (by omega))
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

/-- The three anchor steps with a signing-gap bound at each public anchor. Reports carry
the calendar delay; the same-report rows have delay zero. -/
theorem anchorSteps_gap_delayed_at {g ΔR a b gS ΔF hold : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    {sign : Fin sp.n → Time → Bool} (hcal : RunTrace.SignCalendarAt tr proposer dg H sign)
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b hold)
    (hhold : 0 ≤ hold)
    {c G : Nat} (hc2 : 2 ≤ c)
    (hdel : 6 * sp.Δ + G * sp.Δ + ΔF ≤ 4 * sp.Δ * c)
    (hrelay : 7 * sp.Δ + G * sp.Δ ≤ 4 * sp.Δ * c) {s₀ : Nat}
    (hgap : ∀ s, s₀ ≤ s → s ≤ s₀ + 2 * c →
      SignGapAt sp.toParams sign G (sp.ts s + 6 * sp.Δ))
    {P : Fin 4 → AC.Blk sp.n (List (FG.Att sp.n))}
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
    (AC.ts_le_iff sp).2 (by exact_mod_cast h)
  have h1 := height_next_at hp hP0 hP1 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have h2 := height_next_at hp hP0 hP2 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have hbudget {s t : Nat} (ht : t = s + c) :
      sp.ts s + 6 * sp.Δ + G * sp.Δ + ΔF ≤ sp.ts t ∧
        sp.ts s + 7 * sp.Δ + G * sp.Δ ≤ sp.ts t := by
    rw [ht, ts_add_gap (sp := sp)]
    exact ⟨by linarith, by linarith⟩
  have st0 := anchorStep_gap_delayed_at hp hcal hs hhold hc2 rfl
    (hgap s₀ le_rfl (by omega)) (hbudget (s := s₀) rfl).1 (hbudget (s := s₀) rfl).2
    hP0 hP1 hR ((hmono _ _ (by omega)).trans hb) hgS hh₀
  have e1 : s₀ + 2 * c = (s₀ + c) + c := by omega
  have st1 := anchorStep_gap_delayed_at hp hcal hs hhold hc2 e1
    (hgap (s₀ + c) (by omega) (by omega)) (hbudget e1).1 (hbudget e1).2 hP1 hP2
    (hR.trans (hmono _ _ (by omega))) ((hmono _ _ (by omega)).trans hb)
    (by linarith [hmono s₀ (s₀ + c) (by omega)]) h1
  have e2 : s₀ + 3 * c = (s₀ + 2 * c) + c := by omega
  have st2 := anchorStep_gap_delayed_at hp hcal hs hhold hc2 e2
    (hgap (s₀ + 2 * c) (by omega) le_rfl) (hbudget e2).1 (hbudget e2).2 hP2 hP3
    (hR.trans (hmono _ _ (by omega))) hb
    (by linarith [hmono s₀ (s₀ + 2 * c) (by omega)]) h2
  intro i
  fin_cases i
  exacts [st0, st1, st2]

end Consensus.Goldilocks.Obligations.Growing

end
