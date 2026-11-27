module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowFieldsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedToFG
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCoverDelayed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowCrossing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalUnanimous
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalPersistence
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinPair
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The seed height of the route-A window, under growing faults

On the canonical growing trace, an honest seed proposal `Q` at a slot `u` after the
drain, and an honest proposal `P₀` at a slot `s₀ ≥ u + δt` by the horizon `b`, give
`H_z + 2 ≤ σ[P₀].h` at every holder of `P₀` honest at an observation time after the holder's
earlier cuts (`seed_height_at`), and at the proposer of `P₀` just after its proposal cut
(`seed_height_held_at`, the height witness of `anchorSteps_gap_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
variable {hold : Time}

/-- **The seed height** under growing faults. With the finite reset premises, Catch(2Δ), the HS
premises through `b` (`ḡ_S ≤ t_u + 6Δ`), an honest seed proposal `Q` at slot `u > 0` with
`drainTime a ≤ t_u` and `ḡ + 4Δ ≤ t_u`, and an honest proposal `P₀` at slot `s₀ ≥ u + δt` with
`t_{s₀} ≤ b` (`2 ≤ δt`): every holder of `P₀` honest at an observation time `t` after its earlier
cuts has `H_z + 2 ≤ σ[P₀].h`. -/
private theorem seed_height_of_reports_at {g ΔR a b gS ΔF hold : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b hold)
    (hhold : 0 ≤ hold)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ : Nat} {Q P₀ : AC.Blk sp.n (List (FG.Att sp.n))}
    {G : Nat}
    (hcover : ∀ (_ : Q ∈ tr.HonestBlocksAt H) (_ : Q.slot = u)
      (_ : 0 < u) (_ : Q.root ≠ sp.genesisRoot)
      (_ : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
        e.msg.slot = u → e.msg.head = Q.root)
      (_ : gbar g + 4 * sp.Δ ≤ sp.ts u)
      (_ : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
      (_ : sp.ts u + 6 * sp.Δ + G * sp.Δ ≤ b),
      (∀ y, y ∈ H (sp.ts u + 6 * sp.Δ + G * sp.Δ) → ∃ r e R,
        AC.ToFGAt tr.projAC y r e R ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ + G * sp.Δ ∧
        Anc (tr.HonestBlocksAt H) Q R) ∨
      (∃ x r e C, x ∈ H (max (Healing.cutZ sp.toParams g) (tr.time r)) ∧
        AC.ToFGAt tr.projAC x r e C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ + G * sp.Δ ∧
        Anc (tr.HonestBlocksAt H) Q C ∧
        ((tr.state x r).fg.σ Q.root).h < ((tr.state x r).fg.σ C.root).h))
    (htd : 6 * sp.Δ + G * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hcr : 7 * sp.Δ + G * sp.Δ ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hQ : Healing.Growing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.Growing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∀ y k t, 0 ≤ t → (∀ q < k, tr.time q ≤ t) → y ∈ H t → P₀ ∈ (tr.state y k).fg.tree →
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h := by
  classical
  have hrun := hp.run
  have hnc := hp.noColl
  have hΔ := sp.toParams.hΔ
  have hcoh := Compose.Growing.honest_blocks_coherent hrun hnc
  -- the two proposals
  have hQs := honestProposalRun_slot_at hQ
  have hP₀s := honestProposalRun_slot_at hP₀
  obtain ⟨kQ, hkQ, hpQ, -, hQm⟩ := proposal_held_at hrun hnc hQ
  have hleQ : ∀ q < kQ + 1, tr.time q ≤ tr.time kQ := fun _ hq => hrun.time_mono (by omega)
  have hQH : Q ∈ tr.HonestBlocksAt H :=
    ⟨_, kQ + 1, tr.time kQ, hrun.time_nonneg kQ, hleQ, hpQ, hQm⟩
  obtain ⟨kX, hkX, hpH, -, hXm⟩ := proposal_held_at hrun hnc hP₀
  obtain ⟨Pr, hpar, hPr⟩ := proposal_parent_held_at hrun hnc hpH hkX
  obtain ⟨-, -, he⟩ := accept_of_proposesAt_at hrun hnc hpH hkX
  have h0 := hrun.time_nonneg kX
  have hle0 : ∀ q < kX, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono hq.le
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono (by omega)
  have hXH : P₀ ∈ tr.HonestBlocksAt H := ⟨_, kX + 1, tr.time kX, h0, hle1, hpH, hXm⟩
  have hPrH : Pr ∈ tr.HonestBlocksAt H := ⟨_, kX, tr.time kX, h0, hle0, hpH, hPr⟩
  have htk : tr.time kX = sp.ts s₀ := by
    rw [hkX.2.2, hP₀s, sp.slotTime_eq]; rfl
  -- time arithmetic
  have hG : (0 : Time) ≤ G * sp.Δ := mul_nonneg (Int.natCast_nonneg _) hΔ.le
  have hts : sp.ts u + 4 * sp.Δ * (sp.toParams.fg.δt : Time) ≤ sp.ts s₀ := by
    have hcast : ((u + sp.toParams.fg.δt : Nat) : Int) ≤ (s₀ : Int) := by exact_mod_cast hus
    have := (AC.ts_le_iff sp).2 hcast
    simp only [AC.ACParams.ts] at this ⊢
    push_cast at this
    linarith
  have h2δ : (2 : Time) ≤ (sp.toParams.fg.δt : Time) := by exact_mod_cast hδ
  have h8 : sp.ts u + 8 * sp.Δ ≤ sp.ts s₀ := by
    linarith [mul_le_mul_of_nonneg_left h2δ (mul_nonneg zero_le_four sp.toParams.hΔ.le)]
  have hus2 : u + 2 ≤ s₀ := by omega
  have hub : sp.ts u + 6 * sp.Δ ≤ b := by linarith
  have hd0 : 0 ≤ sp.ts u + 6 * sp.Δ := by linarith [AC.gbar_nonneg g]
  have hubG : sp.ts u + 6 * sp.Δ + G * sp.Δ ≤ b := by linarith [hs.sync.deltaF]
  -- Step 1: H0 at the seed
  obtain ⟨v, r, l, O, ho, -, -, hrt⟩ := hp.reset_seed_before_slot_at hR
  have hun := hp.operational_unanimous_at hQ.1 rfl hkQ hQs hR (by linarith)
  have hR1 : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat) :=
    hR.trans ((AC.ts_le_iff sp).2 (by push_cast; omega))
  have hOQ := Healing.Growing.old_origin_below_unanimous_at hp hQH
    (fun y j e hy hv hjb hs' => hun y j e hy hv hs' hjb) hgu hR1 (by linarith) ho hrt
  -- Step 2: Q ⪯ P₀, hence Q ⪯ Pr
  have hQP := honest_proposal_below_later_upTo_at hp hQ hR hP₀ hus2 hb
  have hne : Q ≠ P₀ := by
    intro h
    rw [h] at hQs
    omega
  have hQPr : Anc (tr.HonestBlocksAt H) Q Pr := by
    rcases Relation.ReflTransGen.cases_tail hQP with heq | ⟨Y, hQY, hY⟩
    · exact absurd heq.symm hne
    · obtain rfl : Y = Pr :=
        hcoh.1 hY.1 hPrH (Option.some_injective _ (hY.2.2.symm.trans hpar))
      exact hQY
  -- the proposer's store at the proposal cut
  have hr := Healing.Growing.fg_reachable_at hrun h0 hle0 hpH
  have hQst := Healing.Growing.mem_of_honest_anc_at hrun hnc h0 hle0 hpH hQPr hPr
  have hQPrs := Healing.Growing.store_anc_of_honest_anc_at hrun hnc h0 hle0 hpH hQPr hPr
  have hOQs := Healing.Growing.store_anc_of_honest_anc_at hrun hnc h0 hle0 hpH hOQ hQst
  have hOst := Healing.Growing.mem_of_honest_anc_at hrun hnc h0 hle0 hpH hOQ hQst
  have hOv := Healing.Growing.highOrigin_mem_at hrun hnc ho
  have hOh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state (proposer s₀) kX).fg.σ O.root).h := by
    rw [← Healing.Growing.σ_eq_honest_at hrun hnc (hrun.time_nonneg r)
      (fun _ hq => hrun.time_mono hq.le) (hrun.antitone (le_max_right _ _) ho.1) h0 hle0 hpH hOv
      hOst]
    exact ho.2.2.2
  have hQh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state (proposer s₀) kX).fg.σ Q.root).h :=
    hOh.trans (Healing.h_le_of_store_anc hr hOQs)
  have hQPrh := Healing.h_le_of_store_anc hr hQPrs
  suffices hpost : Healing.Growing.HZ tr H g + 2 ≤ ((tr.post kX).fg.σ P₀.root).h by
    intro y k t ht hle hy hk
    rw [he] at hpost
    rw [Healing.Growing.σ_eq_honest_at hrun hnc ht hle hy h0 hle1 hpH hk hXm]
    exact hpost
  have hr1 := Healing.Growing.fg_reachable_at hrun h0 hle1 hpH
  -- Case A/B: the parent is already above `HZ + 1`
  by_cases hPr2 : Healing.Growing.HZ tr H g + 2 ≤ ((tr.state (proposer s₀) kX).fg.σ Pr.root).h
  · have hPrm := Healing.Growing.mem_of_honest_anc_at hrun hnc h0 hle1 hpH
      (.single ⟨hPrH, hXH, hpar⟩) hXm
    have hle' := Healing.h_le_of_store_anc hr1 (.single ⟨hPrm, hXm, hpar⟩)
    rw [← Healing.Growing.σ_eq_honest_at hrun hnc h0 hle0 hpH h0 hle1 hpH hPr hPrm] at hle'
    rw [he]
    omega
  -- Case C: `σ[Q].h = σ[Pr].h = HZ + 1`
  have hQ1 : ((tr.state (proposer s₀) kX).fg.σ Q.root).h = Healing.Growing.HZ tr H g + 1 := by
    omega
  have hPr1 : ((tr.state (proposer s₀) kX).fg.σ Pr.root).h =
      ((tr.state (proposer s₀) kX).fg.σ Q.root).h := by omega
  -- C1: a report of the seed strictly above it is impossible
  have hesc : ∀ x r ell C, x ∈ H (tr.time r) → AC.ToFGAt tr.projAC x r ell C →
      tr.time r ≤ sp.ts u + 6 * sp.Δ + G * sp.Δ → Anc (tr.HonestBlocksAt H) Q C →
      ((tr.state x r).fg.σ Q.root).h < ((tr.state x r).fg.σ C.root).h → False := by
    intro x r ell C hx hto hrt' hQC hlt
    have hleR : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono hq.le
    have hCm := Healing.Growing.toFG_mem_tree_at hrun hx hto
    have hQx := Healing.Growing.mem_of_honest_anc_at hrun hnc (hrun.time_nonneg r) hleR hx hQC
      hCm
    have htH : sp.ts u ≤ tr.time r := by
      have := report_slot_le_time_at hrun hnc hx hto hQC
      rwa [hQs] at this
    obtain ⟨Pr', hPr'H, hpar', -, habove⟩ :=
      crossed_parents_above_upTo_at hp hx hto (hR.trans htH) hlt hP₀ (by linarith) hb
    obtain rfl : Pr' = Pr :=
      hcoh.1 hPr'H hPrH (Option.some_injective _ (hpar'.symm.trans hpar))
    have := habove _ kX (tr.time kX) h0 hle0 hpH hPr
    rw [Healing.Growing.σ_eq_honest_at hrun hnc (hrun.time_nonneg r) hleR hx h0 hle0 hpH hQx
      hQst] at this
    omega
  have hPg : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hG := Healing.Store.genesis_mem
      (Healing.Growing.fg_reachable_at hrun (hrun.time_nonneg kQ) hleQ hpQ)
    have heq := hcoh.1 hQH ⟨_, kQ + 1, tr.time kQ, hrun.time_nonneg kQ, hleQ, hpQ, hG⟩ hg
    have hz : Q.slot = 0 := by rw [heq]; rfl
    omega
  rcases hcover hQH hQs hu hPg
      (fun y j e hy hv hjb hs' => hun y j e hy hv hs' hjb) hgu hR1 hubG with
    hall | ⟨x, r, e, C, hx, hto, hrt', hQC, hlt⟩
  swap
  · exact (hesc x r e C (hrun.antitone (le_max_right _ _) hx) hto hrt' hQC hlt).elim
  -- C2: the entry of the seed, its target attestations, and the timeout crossing at `P₀`
  obtain ⟨⟨E, hE, hEr, hEQ, hEh, hETh⟩, -⟩ :=
    Goldilocks.Store.entry_state_of_source _ _ _ _ hr Q hQst
  have hETe : ((tr.state (proposer s₀) kX).fg.σ E.root).Th = E.root := hETh.trans hEr.symm
  have hEQh := Healing.Growing.honest_anc_of_store_anc_at h0 hle0 hpH hEQ
  have hEhT : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state (proposer s₀) kX).fg.σ E.root).h := by
    rw [hEh]; exact hQh
  have hPrTh : ((tr.state (proposer s₀) kX).fg.σ Pr.root).Th = E.root :=
    (Healing.Th_eq_of_anc hr hQPrs hPr1).trans hEr.symm
  have hThS : ((tr.state (proposer s₀) kX).fg.σ Pr.root).ThSlot ≤ u := by
    rw [Healing.ThSlot_eq_of_anc hr hQPrs hPr1, ← hQs]
    exact Healing.ThSlot_le_slot hr hQst
  -- the quorum: the nodes still honest when a row signed by `t_u + 6Δ + GΔ` is released
  have hubGh : sp.ts u + 6 * sp.Δ + G * sp.Δ + hold ≤ b := by linarith [hs.sync.hold_le]
  let S : Finset (Fin sp.n) :=
    Finset.univ.filter (· ∈ H (sp.ts u + 6 * sp.Δ + G * sp.Δ + hold))
  have hScard : sp.toParams.fg.q ≤ S.card := by
    have hcard : S.card = (H (sp.ts u + 6 * sp.Δ + G * sp.Δ + hold)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp [S]
    rw [hcard]
    have hn : (H (sp.ts u + 6 * sp.Δ + G * sp.Δ + hold)).ncard +
        (H (sp.ts u + 6 * sp.Δ + G * sp.Δ + hold))ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hf := hp.faults _ (show 0 ≤ sp.ts u + 6 * sp.Δ + G * sp.Δ + hold by linarith) hubGh
    change (2 * sp.n + 2) / 3 ≤ _
    omega
  have hcross := Healing.Growing.cross_of_signed_rows_upTo_at hrun hs hhold
    (v := sp.ts u + 6 * sp.Δ + G * sp.Δ) (by linarith) hpH hkX
    (by rw [htk]; linarith) (by rw [htk]; exact hb) hpar S
    hScard ?_
    (by rw [hP₀s]; omega)
  · rw [hcross.1]
    omega
  have hczu : Healing.cutZ sp.toParams g ≤ sp.ts u + 6 * sp.Δ := by
    have hk := sp.two_le_k
    have hts := hp.clean_window_timing_at (s := u) (by
      rw [Healing.cleanLabel_eq]
      rw [Healing.drainTime_eq] at hR1
      have := (AC.ts_le_iff sp).1 hR1
      push_cast at this
      omega) u (by omega)
    linarith [sp.toParams.hΔ]
  intro z hz
  have hzH' : z ∈ H (sp.ts u + 6 * sp.Δ + G * sp.Δ + hold) := (Finset.mem_filter.1 hz).2
  have hzH : z ∈ H (sp.ts u + 6 * sp.Δ + G * sp.Δ) := hrun.antitone (by linarith) hzH'
  obtain ⟨r, ell, R, hrep, hrt', hQR⟩ := hall z hzH
  have hzrz : z ∈ H (max (Healing.cutZ sp.toParams g) (tr.time r)) :=
    hrun.antitone (max_le (by linarith [hczu]) hrt') hzH
  have hzr : z ∈ H (tr.time r) := hrun.antitone hrt' hzH
  have hleR : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono hq.le
  have hr0 := hrun.time_nonneg r
  have hRm := Healing.Growing.toFG_mem_tree_at hrun hzr hrep
  have hQz := Healing.Growing.mem_of_honest_anc_at hrun hnc hr0 hleR hzr hQR hRm
  have hσQ := Healing.Growing.σ_eq_honest_at hrun hnc hr0 hleR hzr h0 hle0 hpH hQz hQst
  have hle := Healing.h_le_of_store_anc (Healing.Growing.fg_reachable_at hrun hr0 hleR hzr)
    (Healing.Growing.store_anc_of_honest_anc_at hrun hnc hr0 hleR hzr hQR hRm)
  have hRh : ((tr.state z r).fg.σ R.root).h = ((tr.state (proposer s₀) kX).fg.σ E.root).h := by
    by_contra hneq
    refine hesc z r ell R hzr hrep hrt' hQR ?_
    rw [hσQ] at hle ⊢
    omega
  have hrb : tr.time r ≤ b := by linarith
  have ho' := hp.high_or_covered_at hzrz hrep hrb (by rw [hRh]; exact hEhT)
  have hB : R ∈ tr.HonestBlocksAt H := Compose.Growing.mem_honestBlocksAt hrun hzr hRm
  have hER := hEQh.trans hQR
  obtain ⟨j, att, hsg, hjt, hah⟩ :=
    hp.sign_of_report_at hzrz hrep hrb h0 hle0 hpH hE rfl hETe hEhT hER hRh ho' hB hER
  obtain ⟨-, haT, -⟩ :=
    hp.row_target_of_sign_at (hrun.antitone (max_le_max le_rfl hjt) hzrz) hsg (hjt.trans hrb) h0
      hle0 hpH hE rfl hETe hEhT ho' hB hER hah
  exact ⟨j, att, hzH', hsg, hjt.trans hrt', hah.trans (hEh.trans hPr1.symm),
    haT.trans hPrTh.symm⟩

/-- Seed height from a calendar whose reports arrive within the timeout budget. -/
theorem seed_height_delayed_at {g ΔR a b gS ΔF hold : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    {sign : Fin sp.n → Time → Bool} (hcal : RunTrace.SignCalendarAt tr proposer dg H sign)
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b hold)
    (hhold : 0 ≤ hold)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ G : Nat}
    (hgap : SignGapAt sp.toParams sign G (sp.ts u + 6 * sp.Δ))
    (htd : 6 * sp.Δ + G * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hcr : 7 * sp.Δ + G * sp.Δ ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    {Q P₀ : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Healing.Growing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.Growing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∀ y k t, 0 ≤ t → (∀ q < k, tr.time q ≤ t) → y ∈ H t → P₀ ∈ (tr.state y k).fg.tree →
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h :=
  seed_height_of_reports_at hp hs hhold hδ
    (fun hQH hQs hu hQg hun hgu hR hb =>
      Healing.Growing.report_cover_delayed_of_unanimous_at hp hcal hgap
        hQH hQs hu hQg hun hgu hR hb) htd hcr hQ hu hR hgu hP₀ hus hb hgS

/-- The responsive seed-height statement, with its original assumptions. -/
theorem seed_height_at {g ΔR a b gS ΔF hold : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    (hsign : RunTrace.GrowingAllTicksSign tr proposer dg H)
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b hold)
    (hhold : 0 ≤ hold)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ : Nat} {Q P₀ : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Healing.Growing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.Growing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∀ y k t, 0 ≤ t → (∀ q < k, tr.time q ≤ t) → y ∈ H t → P₀ ∈ (tr.state y k).fg.tree →
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h := by
  have hδ' : (2 : Time) ≤ sp.toParams.fg.δt := by exact_mod_cast hδ
  have hΔ := sp.toParams.hΔ
  apply seed_height_of_reports_at hp hs hhold hδ (G := 0) _
    (by simpa [Params.fg] using hs.timeoutDelay)
    (by simp only [Nat.cast_zero, zero_mul, add_zero]; nlinarith) hQ hu hR hgu hP₀ hus hb hgS
  intro hQH hQs hu hQg hun hgu hR hb
  simpa only [Nat.cast_zero, zero_mul, add_zero] using
    Healing.Growing.report_cover_of_unanimous_at hp hsign hQH hQs hu hQg hun hgu hR
      (by simpa using hb)

/-- `seed_height_at` in the form of the height premise of `anchorSteps_gap_at`: the proposer of
`P₀` holds `P₀` just after its proposal cut, honest at that cut, at height at least `H_z + 2`. -/
theorem seed_height_held_at {g ΔR a b gS ΔF hold : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    (hsign : RunTrace.GrowingAllTicksSign tr proposer dg H)
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b hold)
    (hhold : 0 ≤ hold)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ : Nat} {Q P₀ : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Healing.Growing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.Growing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∃ y k, y ∈ H (tr.time k) ∧ P₀ ∈ (tr.state y k).fg.tree ∧
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h := by
  obtain ⟨kX, -, hm, ht, hXm⟩ := proposal_held_at hp.run hp.noColl hP₀
  refine ⟨_, kX + 1, ht ▸ hm, hXm,
    seed_height_at hp hsign hs hhold hδ hQ hu hR hgu hP₀ hus hb hgS _
    (kX + 1) (tr.time kX) (hp.run.time_nonneg kX)
    (fun _ hq => hp.run.time_mono (by omega)) hm hXm⟩

/-- The delayed seed-height bound at an honest holder just after its proposal cut. -/
theorem seed_height_held_delayed_at {g ΔR a b gS ΔF hold : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b cm βK hold)
    {sign : Fin sp.n → Time → Bool} (hcal : RunTrace.SignCalendarAt tr proposer dg H sign)
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b hold)
    (hhold : 0 ≤ hold)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ G : Nat}
    (hgap : SignGapAt sp.toParams sign G (sp.ts u + 6 * sp.Δ))
    (htd : 6 * sp.Δ + G * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hcr : 7 * sp.Δ + G * sp.Δ ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    {Q P₀ : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Healing.Growing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.Growing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∃ y k, y ∈ H (tr.time k) ∧ P₀ ∈ (tr.state y k).fg.tree ∧
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h := by
  obtain ⟨kX, -, hm, ht, hXm⟩ := proposal_held_at hp.run hp.noColl hP₀
  refine ⟨_, kX + 1, ht ▸ hm, hXm,
    seed_height_delayed_at hp hcal hs hhold hδ hgap htd hcr hQ hu hR hgu hP₀ hus hb hgS _
      (kX + 1) (tr.time kX) (hp.run.time_nonneg kX)
      (fun _ hq => hp.run.time_mono (by omega)) hm hXm⟩

end Consensus.Goldilocks.Obligations.Growing

end
