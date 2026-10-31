module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Phase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo

public section

/-! # Goldilocks Healing, HS.3: the setting of frozen-tree agreement

`hs234-exact-interface.md` §4 (HS.3 (a), with the restored settled premise of #95), the facts
that do not compare walks:

* **The phase-interval sandwich** (`phaseOn_squeeze`, `phaseOn_voter`): the phase `(m, c)` at
  `i₀` (settled) and at a later cut `b` is the phase at every cut between (the frontier is
  squeezed to `m`, `Σ.h_max` only grows; then the case rank is squeezed and the top `J` kept,
  `phaseAt_mono`). With `PhaseOn i k` and `i₀ ≤ i ≤ k` it gives `PhaseOn i₀ k` without a new
  hypothesis; `i ≤ k` holds for every slot-`s` vote (`start_le_voter`: `time i ≤ t_{s−1} + 3Δ <
  t_s ≤` the vote's time).
* **The ready proposal is an honest proposal** of the AC projection (`honestProposalRun_of_ready`:
  the own block is the tick's proposal, accepted at once, C0.3), so HS.2's proposal clause
  applies to it.
* **The voter block tree of slot `s` has no block of a later slot** (`voterBlockTree_slot_le`,
  from `Geo.stamp_origin`).
* **The setting** `AgreeSetting`: HS.3 (a)'s premises with the proposal's `ac_proposal` call
  (`Compose.proposal_data`), its duty head `d` (`P.parent = d.head`) and payload `pay`
  (`agreeSetting_of`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-! ### Block stamps -/

section Stamps

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro}

private theorem admitVote_blockStamp (A : SA.SAState sp.n) (t : Time) (v : SA.Vote sp.n) :
    (SA.admitVote sp A t v).blockStamp = A.blockStamp := by
  unfold SA.admitVote
  split_ifs <;> rfl

private theorem optimistic_blockStamp (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold SA.optimisticConfirmation SA.updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

/-- **The voter block tree of slot `s` has no block of a later slot**: at an honest vote, a block
of it received before the freeze `t_{s−1} + 3Δ` was in a frame at an earlier call, before `t_s`,
and frames hold no block of a future slot (genesis has slot `0`); any other block is an ancestor
of a slot-`s` block. -/
theorem voterBlockTree_slot_le (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt tr y j ℓ e) {s : Nat}
    (hgen : ∀ X ∈ ℓ.frame.tree, X.root = sp.genesisRoot → X.slot = 0)
    {W : SA.Blk sp.n FGP} (hW : W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame s) : W.slot ≤ s := by
  obtain ⟨hWt, hst | ⟨P', hP', hP's, hWP'⟩⟩ := hW
  · have heq : e.readPoint.blockStamp = (tr.post j).blockStamp := by
      rw [SA.post_of_castAt hr hy hc, optimistic_blockStamp, admitVote_blockStamp]
    rw [heq] at hst
    rcases stamp_origin hr hy j ℓ hc.1 W hWt with hgn | ⟨k, -, ℓk, hck, hWk, hsk⟩
    · rw [hgen W hWt hgn]; exact Nat.zero_le _
    rw [hsk] at hst
    have ht : tr.time k < sp.ts ((s : Int) - 1) + 3 * sp.Δ := by
      have h := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
      exact h
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    have hlt : sp.slot (tr.time k) < s := by
      by_contra hn
      have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) (s : Int)).2
        (by exact_mod_cast not_lt.1 hn)
      have : sp.ts ((s : Int) - 1) + 4 * sp.Δ = sp.ts s := by simp only [SAParams.ts]; ring
      linarith
    exact (SA.frame_slot_le sp hr hy hck W hWk).trans hlt.le
  · rw [← hP's]
    exact (Anc.slot_le (SA.frameIn_of_callAt hr hy hc.1).1.coherent hWP').1

end Stamps

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ i m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-! ### The phase-interval sandwich -/

/-- Every cut with a frontier has a phase case. -/
private theorem phaseAt_some {k m : Nat} (hF : FrontierAt tr.projFG H k m) :
    ∃ c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n))), PhaseAt tr.projFG H k m c := by
  classical
  by_cases hJ : ∃ J, JustifiedAt tr.projFG H k (m - 1) J
  · obtain ⟨J, hJ⟩ := hJ
    by_cases hC : ContestAt tr.projFG H k m J
    · exact ⟨.contest J, hF, hJ, hC⟩
    · exact ⟨.top J, hF, hJ, hC⟩
  · exact ⟨.gap, hF, fun J h => hJ ⟨J, h⟩⟩

/-- Two cases with the same rank and the first's top `J` kept are equal. -/
private theorem case_eq {β : Type} {c c' : PhaseCase β} (h₁ : c.rank ≤ c'.rank)
    (h₂ : c'.rank ≤ c.rank) (ht : ∀ J, c.topJ = some J → c'.topJ = some J) : c = c' := by
  cases c <;> cases c' <;> simp only [PhaseCase.rank, PhaseCase.topJ] at h₁ h₂ ht
  all_goals first
    | rfl
    | omega
    | rw [Option.some.inj (ht _ rfl)]

/-- **The phase-interval sandwich** (`hs234-exact-interface.md` §4): the phase `(m, c)` at two
cuts `a ≤ b` is the phase at every cut between them. -/
theorem phaseOn_squeeze (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF) {a b : Nat}
    (ha : PhaseAt tr.projFG H a m c) (hb : PhaseAt tr.projFG H b m c) :
    PhaseOn tr.projFG H a b m c := by
  obtain ⟨hfg, hq⟩ := fg_run_of_hs hrun hs
  intro k h₁ h₂
  obtain ⟨⟨y₀, hy₀, hm₀⟩, -⟩ := ha.frontierAt
  have hFb := hb.frontierAt.2
  have hF : FrontierAt tr.projFG H k m := by
    refine ⟨⟨y₀, hy₀, le_antisymm ?_ ?_⟩, fun y hy => ?_⟩
    · have := hFb y₀ hy₀
      have := hmax_mono hrun.toLocalRun hy₀ h₂
      simp only [projFG_store_eq hrun hy₀] at *
      omega
    · have := hmax_mono hrun.toLocalRun hy₀ h₁
      simp only [projFG_store_eq hrun hy₀] at *
      omega
    · have := hFb y hy
      have := hmax_mono hrun.toLocalRun hy h₂
      simp only [projFG_store_eq hrun hy] at *
      omega
  obtain ⟨c', hc'⟩ := phaseAt_some hF
  obtain ⟨r₁, t₁⟩ := phaseAt_mono hfg hq h₁ ha hc'
  obtain ⟨r₂, t₂⟩ := phaseAt_mono hfg hq h₂ hc' hb
  rwa [case_eq r₂ r₁ t₂] at hc'

/-- A cut at a time `≥ w` is at or after the settled cut `i₀`. -/
theorem le_of_settledIn (hw : SettledIn tr H g w i₀ m c) {k : Nat} (hk : w ≤ tr.time k) :
    i₀ ≤ k := by
  by_contra h
  have := hw.2.1.2 k (not_le.1 h)
  linarith

/-- **The phase from the settled cut** (`hs234-exact-interface.md` §4): with `i ≤ k` and the
phase `(m, c)` on `[i, k]`, the phase is `(m, c)` on `[i₀, k]` (the sandwich on `[i₀, i]`). -/
theorem phaseOn_voter (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hw : SettledIn tr H g w i₀ m c) {k : Nat} (hik : i ≤ k)
    (hph : PhaseOn tr.projFG H i k m c) : PhaseOn tr.projFG H i₀ k m c := by
  intro k' h₁ h₂
  rcases le_or_gt i k' with h | h
  · exact hph k' h h₂
  · exact phaseOn_squeeze hrun hs hw.2.2 (hph i le_rfl hik) k' h₁ h.le

/-- **Every slot-`s` vote is after the start cut** `i` when `time i ≤ t_{s−1} + 3Δ`: the vote is
cast at a time of slot `s`, at or after `t_s = t_{s−1} + 4Δ`. -/
theorem start_le_voter (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr) {s : Nat}
    (hti : tr.time i ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (hes : e.msg.slot = s) : i ≤ k := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, hys, -, -⟩ := SA.castAt_spec hr hy hv
  have hvt : sp.ts s ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hrun.toLocalRun.time_nonneg k) s).2
      (by have := hys.le; rw [hes] at this; exact_mod_cast this)
  have hts : sp.ts ((s : Int) - 1) + 4 * sp.Δ = sp.ts s := by
    simp only [SAParams.ts]; ring
  by_contra hn
  have := hrun.toLocalRun.time_mono (not_le.1 hn).le
  linarith


/-! ### The ready proposal is an honest proposal -/

/-- **A ready proposal is an honest proposal** of the AC projection: the own block `P` is made by
the tick's `ac_proposal` cut and accepted at once (C0.3), at `t_s`. -/
theorem honestProposalRun_of_ready (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {kP s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H p kP s P) : HonestProposalRun tr H s P := by
  have h := hrun.toLocalRun
  obtain ⟨hp, rfl, -, ⟨⟨⟨acc, hc⟩, hpos⟩, -, htk⟩, hPs, -⟩ := hP
  refine ⟨hp, ?_⟩
  rcases Compose.blockCall_cases h hp hc with hg |
    ⟨j, x, rfl, hg, hpr, d, pay, hdp, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  obtain ⟨hc1, ht1, hst1⟩ := tick_proposal_call h hp hg hpr
  obtain ⟨hacc, ht2⟩ := own_block_accepted h hreq hrun.genesis_root_ok hnc hp hg hpr hdp
  obtain ⟨hacc3, ht3, -⟩ := ac_block_after h hp hacc
  have hts : tr.time (j + 2) = sp.ts s := by
    rw [htk, sp.slotTime_eq, hPs]; rfl
  subst hB
  refine ⟨j + 1, ⟨.proposal, Node.frame (Node.tickStep dg _ (tr.state _ j) (tr.time (j + 2)) x
    .acTick).1, []⟩, d, pay, Compose.projAC_callAt.2 hc1, rfl, ?_, ht1.trans hts, rfl, hPs, rfl,
    rfl, j + 3, by omega, hacc3, ht3.trans (ht2.trans hts)⟩
  have ht1' : tr.projAC.time (j + 1) = tr.time (j + 2) := ht1
  rw [Compose.projAC_state h hp, hst1, ht1']
  exact hdp

/-! ### The setting -/

section Setting

variable {p : Fin sp.n} {kP s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}

/-- **The setting of HS.3 (a)**: its premises (with the settled premise of #95), and the
proposal's `ac_proposal` call at cut `iP`, at `t_s`, with duty head `d` (`P.parent = d.head`)
and payload `pay`. -/
structure AgreeSetting (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF w : Time) (i₀ i m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (p : Fin sp.n) (kP s : Nat)
    (P : SA.Blk sp.n (List (FG.Att sp.n))) (iP : Nat) (ℓp : ACLabel (goldilocksNode sp ro))
    (d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)) (pay : Payload sp.n) : Prop where
  run : GoldilocksRun dg H tr
  shared : HSShared tr H dg g ΔF
  catchUp : CatchRun tr H g (2 * sp.Δ)
  settled : SettledIn tr H g w i₀ m c
  settled_le : i₀ ≤ i
  ready : ReadyProposal tr H p kP s P
  start_le : i ≤ kP
  start_time : tr.time i ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ
  gbar_le : gbar g ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ
  phase : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
    PhaseOn tr.projFG H i k m c
  call : tr.projAC.CallAt p iP ℓp
  call_proposal : ℓp.call = .proposal
  payload : (SA.acProposal sp (tr.projAC.state p iP) ℓp.frame (tr.time iP)).2 = some (d, pay)
  time : tr.time iP = sp.ts s
  parent : P.parent = some d.head.root

/-- HS.3 (a)'s premises give the setting, with the proposal's `ac_proposal` call
(`Compose.proposal_data`). -/
theorem agreeSetting_of (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) (hi₀ : i₀ ≤ i)
    (hP : ReadyProposal tr H p kP s P) (hikP : i ≤ kP)
    (hti : tr.time i ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ)
    (hg : gbar g ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ)
    (hph : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      PhaseOn tr.projFG H i k m c) :
    ∃ iP ℓp d pay, AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay := by
  obtain ⟨iP, ℓp, d, pay, hcP, hcall, hd, ht, hpar, -⟩ :=
    Compose.proposal_data hrun hP.1 hP.2.2.2.1 hP.2.2.2.2.1
  exact ⟨iP, ℓp, d, pay, hrun, hs, hc, hw, hi₀, hP, hikP, hti, hg, hph, hcP, hcall, hd, ht, hpar⟩

/-- The proposal's slot is positive: `t_s > t_{s−1} + 3Δ ≥ time(i) ≥ w ≥ ḡ + 8Δ > 0`. -/
theorem AgreeSetting.one_le_slot {iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) : 1 ≤ s := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hwi : w ≤ tr.time i := hS.settled.2.1.1.trans (hS.run.toLocalRun.time_mono hS.settled_le)
  have hts : sp.ts ((s : Int) - 1) + 4 * sp.Δ = sp.ts s := by simp only [SAParams.ts]; ring
  by_contra h0
  obtain rfl : s = 0 := by omega
  have : sp.ts ((0 : Nat) : Int) = 0 := by simp [SAParams.ts]
  have := gbar_nonneg g
  have := (le_max_right _ _).trans hS.settled.1.late
  linarith [hS.start_time]

end Setting

end Consensus.Goldilocks.Healing

end
