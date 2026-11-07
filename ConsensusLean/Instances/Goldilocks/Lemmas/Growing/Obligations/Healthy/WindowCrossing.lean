module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowCorePending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedC4
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowParents
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifiesSigned
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Crossings and anchor height steps of the route-A window, under growing faults

The growing forms of the trace lemmas of `Obligations/WindowAnchorStep`,
`Obligations/WindowUnanimous` and `Obligations/WindowParentsUpTo` that the seed height and the
anchor steps read. Each node is honest at its own cut; a reader of a held state is honest at an
observation time after the state's cuts:

* `proposal_parent_held_at`: an honest proposal's parent is held by its proposer at the cut;
* `anchor_height_step_or_crossed_at`, `anchorStep_of_or_crossed_at`: the anchor height step,
  from a quorum of target attestations signed by signers honest at their signing;
* `report_slot_le_time_at`: a report above `P` is not before the slot of `P`;
* `crossed_parents_above_upTo_at`: the parent of a later honest proposal is above a report, and
  above its height at every holder (C3 of the healed window, from the clean-source lemmas). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The parent of a proposal is held**: the parent of a block proposed at a cut of a node
honest at it is in the node's tree at the cut (the static `proposal_parent_held` on the prefix
through the cut). -/
theorem proposal_parent_held_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X) :
    ∃ Pr : SA.Blk sp.n (List (FG.Att sp.n)), X.parent = some Pr.root ∧
      Pr ∈ (tr.state p kX).fg.tree := by
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  obtain ⟨Pr, hpar, hPr⟩ := Healing.proposal_parent_held (hrun.upTo (hrun.time_nonneg kX))
    (hnc.upTo _) hp hX'
  rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at hPr
  exact ⟨Pr, hpar, hPr⟩

/-- **The anchor height step, attestations only at the old height**, under growing faults. An
honest anchor `X` (proposal cut `kX`, parent `Pr`) with `A ⪯ Pr` in the proposer's store: when
`σ[Pr]` is still at the height of `A`, a quorum of target attestations for its entry signed by `v`,
each by a signer honest at its signing, gives `σ[A].h + 1 ≤ σ[X].h` on the post-store. -/
theorem anchor_height_step_or_crossed_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : Healing.Growing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {A X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hpar : X.parent = some Pr.root) (hPr : Pr ∈ (tr.state p kX).fg.tree)
    (hAPr : (tr.state p kX).fg.Anc A Pr)
    (hrows : ((tr.state p kX).fg.σ Pr.root).h = ((tr.state p kX).fg.σ A.root).h →
      ∃ S : Finset (Fin sp.n), sp.toParams.fg.q ≤ S.card ∧
      ∀ y ∈ S, ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ v ∧
        att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
        att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ att.timeout = false ∧
        (((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
          (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J) ∈
            ((tr.state p kX).fg.σ Pr.root).pending →
          att.fin = some (((tr.state p kX).fg.σ Pr.root).hj,
            ((tr.state p kX).fg.σ Pr.root).J))) :
    ((tr.state p kX).fg.σ A.root).h + 1 ≤ ((tr.post kX).fg.σ X.root).h := by
  have hnc := hs.noColl
  have h0 := hrun.time_nonneg kX
  have hle0 : ∀ q < kX, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono hq.le
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono (by omega)
  have hr1 := Healing.Growing.fg_reachable_at hrun h0 hle1 hp
  have hle := Healing.h_le_of_store_anc (Healing.Growing.fg_reachable_at hrun h0 hle0 hp) hAPr
  obtain ⟨-, hXm, he⟩ := accept_of_proposesAt_at hrun hnc hp hX
  by_cases heq : ((tr.state p kX).fg.σ Pr.root).h = ((tr.state p kX).fg.σ A.root).h
  · obtain ⟨S, hS, hsig⟩ := hrows heq
    have hj := (Healing.Growing.justify_of_signed_rows'_upTo_at hrun hs hv hp hX hvx hkb hpar
      S hS hsig).1
    have hlt := Healing.Store.hj_lt_h hr1 hXm
    rw [← he] at hlt
    omega
  · have hXH : X ∈ tr.HonestBlocksAt H := ⟨p, kX + 1, tr.time kX, h0, hle1, hp, hXm⟩
    have hPrX : Anc (tr.HonestBlocksAt H) Pr X :=
      .single ⟨⟨p, kX, tr.time kX, h0, hle0, hp, hPr⟩, hXH, hpar⟩
    have hPrm := Healing.Growing.mem_of_honest_anc_at hrun hnc h0 hle1 hp hPrX hXm
    have hle' := Healing.h_le_of_store_anc hr1 (.single ⟨hPrm, hXm, hpar⟩)
    rw [← Healing.Growing.σ_eq_honest_at hrun hnc h0 hle0 hp h0 hle1 hp hPr hPrm] at hle'
    rw [he]
    omega

/-- **An anchor step from `anchor_height_step_or_crossed_at`.** With its premises,
`AnchorStepAt tr H A X`, observed at the proposer of `X` at the proposal cut and just after it. -/
theorem anchorStep_of_or_crossed_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : Healing.Growing.HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {A X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hpar : X.parent = some Pr.root) (hPr : Pr ∈ (tr.state p kX).fg.tree)
    (hAPr : (tr.state p kX).fg.Anc A Pr)
    (hrows : ((tr.state p kX).fg.σ Pr.root).h = ((tr.state p kX).fg.σ A.root).h →
      ∃ S : Finset (Fin sp.n), sp.toParams.fg.q ≤ S.card ∧
      ∀ y ∈ S, ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ v ∧
        att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
        att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ att.timeout = false ∧
        (((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
          (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J) ∈
            ((tr.state p kX).fg.σ Pr.root).pending →
          att.fin = some (((tr.state p kX).fg.σ Pr.root).hj,
            ((tr.state p kX).fg.σ Pr.root).J))) :
    AnchorStepAt tr H A X := by
  have hst := anchor_height_step_or_crossed_at hrun hs hv hp hX hvx hkb hpar hPr hAPr hrows
  obtain ⟨ha, hXm, he⟩ := accept_of_proposesAt_at hrun hs.noColl hp hX
  obtain ⟨-, -, -, ht⟩ := accept_next_at hrun hp ha
  have h0 := hrun.time_nonneg kX
  have hle0 : ∀ q < kX, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono hq.le
  have hA := Healing.Growing.mem_of_honest_anc_at hrun hs.noColl h0 hle0 hp
    (Healing.Growing.honest_anc_of_store_anc_at h0 hle0 hp hAPr) hPr
  rw [he] at hst
  exact anchorStepAt_iff.mpr ⟨p, kX, kX + 1, hp, ht ▸ hp, hA, hXm, hst⟩

/-- **A report above `P` is not before the slot of `P`**, for a reporter honest at its report. -/
theorem report_slot_le_time_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} {r : Nat} (hz : z ∈ H (tr.time r))
    {ell : ACLabel (goldilocksNode sp ro)} {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC z r ell C) (hPC : Anc (tr.HonestBlocksAt H) P C) :
    sp.ts (P.slot : Int) ≤ tr.time r := by
  have hd := hrun.time_nonneg r
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time r)) (tr.upTo (tr.time r))
    proposer (hrun.upTo hd) (hnc.upTo _)).localRun
  have hto' := (Healing.Growing.toFGAt_upTo_iff hrun.time_mono le_rfl).mpr hto
  have hCs : C.slot ≤ sp.slot (tr.time r) :=
    SA.frame_slot_le sp hr hz hto'.1 C (toFG_live_fast_lock hto).1
  have hPs := Healing.slot_le_of_anc (Compose.Growing.honest_blocks_coherent hrun hnc) hPC
  exact (SA.ts_le_iff_le_slot sp hd _).2 (by omega)

/-- **Parents above a crossing report, through the horizon**, under growing faults. A report
`C` of a node honest at its report, after the drain, at height above `h`, and an honest proposal
`P` of a slot `s` with `t_r + Δ ≤ t_s ≤ b`: the parent `Pr` of `P` is an honest block above `C`,
of height above `h` at every holder honest at an observation time after the holder's cuts. -/
theorem crossed_parents_above_upTo_at {g ΔF a b : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {z : Fin sp.n} {r : Nat} (hz : z ∈ H (tr.time r)) {ell : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC z r ell C)
    (hR : Healing.drainTime sp a ≤ tr.time r) {h : Nat}
    (hlt : h < ((tr.state z r).fg.σ C.root).h)
    {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) (hs : tr.time r + sp.Δ ≤ sp.ts s)
    (hsb : sp.ts s ≤ b) :
    ∃ Pr ∈ tr.HonestBlocksAt H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocksAt H) C Pr ∧
      ∀ y k t, 0 ≤ t → (∀ q < k, tr.time q ≤ t) → y ∈ H t → Pr ∈ (tr.state y k).fg.tree →
        h < ((tr.state y k).fg.σ Pr.root).h := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hΔ := sp.toParams.hΔ
  have hk0 := hrun.time_nonneg r
  have hleR : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono hq.le
  have hCz : C ∈ (tr.state z r).fg.tree := Healing.Growing.toFG_mem_tree_at hrun hz hto
  -- C3 at the report, on the prefix through it
  suffices hC3 : ∃ Pr ∈ tr.HonestBlocksAt H, P.parent = some Pr.root ∧
      Anc (tr.HonestBlocksAt H) C Pr by
    obtain ⟨Pr, hPr, hpar, hCPr⟩ := hC3
    refine ⟨Pr, hPr, hpar, hCPr, fun y k t ht hle hy hPrk => ?_⟩
    have hCk := Healing.Growing.mem_of_honest_anc_at hrun hnc ht hle hy hCPr hPrk
    have hle' := Healing.h_le_of_store_anc (Healing.Growing.fg_reachable_at hrun ht hle hy)
      (Healing.Growing.store_anc_of_honest_anc_at hrun hnc ht hle hy hCPr hPrk)
    rw [Healing.Growing.σ_eq_honest_at hrun hnc hk0 hleR hz ht hle hy hCz hCk] at hlt
    omega
  obtain ⟨hCf, l, hl, hlb, hlf, -⟩ := toFG_live_fast_lock hto
  obtain ⟨l₀, hl₀, B, hB, hBr, hlive', rfl⟩ := hl
  have hU' := RunTrace.honestBlocks_upTo_subset hrun.time_mono (H := H) hk0
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time r)) (tr.upTo (tr.time r))
    proposer (hrun.upTo hk0) (hnc.upTo _)).localRun
  have hst : (tr.upTo (tr.time r)).projAC.state z r = tr.projAC.state z r := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC z hleR
  have hck : (tr.upTo (tr.time r)).projAC.CallAt z r ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hto.1
  have hl₀' : l₀ ∈ ((tr.upTo (tr.time r)).projAC.state z r).locks := by rw [hst]; exact hl₀
  have hwf := SA.locksWF_state hr hz r
  rw [hst] at hwf
  have hlive : sp.slot (tr.time r) ≤ l₀.slot + sp.k := le_trans hlive' (hwf.cap hl₀)
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hz hck
  have hvB := SA.viableAncestor_anc hPhi hB
  obtain rfl : C = ell.frame.viableAncestor B :=
    hr.coherent.1 (hPhiU hCf) (hPhiU hvB.1) hlb.symm
  obtain ⟨r', hrk, CV, ℓ', D, hcr, hfl, L, hL, hLr, hLD⟩ :=
    Healing.stored_fast_lock_provenance hr hz r l₀ hl₀' hlf
  rw [hr.coherent.1 hL (hPhiU hB) (hLr.trans hBr.symm)] at hLD
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell' = ℓ' := Option.some.inj (hc'.2.symm.trans hcr.2)
  obtain ⟨hPhi', hPhiU'⟩ := SA.frameIn_of_callAt hr hz hc'
  have hXD : Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor B) D :=
    Anc.mono hU' ((hvB.2.mono hPhiU).trans
      (hLD.trans ((SA.viableAncestor_anc hPhi' hD).2.mono hPhiU')))
  have hrt : tr.time r' ≤ tr.time r := hrun.time_mono hrk.le
  have hflt : SA.FastLockAt tr.projAC z r' l₀.slot D CV :=
    (Healing.Growing.fastLockAt_upTo_iff hrun.time_mono hrt).mp hfl
  have hzr : z ∈ H (tr.time r') := hrun.antitone hrt hz
  obtain ⟨hpH, i, ell₂, dd, pay, hci, hcall, hdd, hti, hpar, -⟩ := hP
  change tr.time i = sp.ts s at hti
  have hpi : proposer s ∈ H (tr.time i) := hrun.antitone (by
    rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  -- the horizon bounds
  have hib : tr.time i ≤ b := hti ▸ hsb
  have hrb : tr.time r' ≤ b := by linarith
  -- the slot bounds
  have hRk := hR
  rw [Healing.drainTime_eq] at hRk
  have hsk := (SA.ts_le_iff_le_slot sp hk0 _).1 hRk
  have hks' : ¬ sp.ts s ≤ tr.time r := by linarith
  rw [SA.ts_le_iff_le_slot sp hk0] at hks'
  have hlab : Healing.cleanLabel sp a + sp.k + 2 ≤ l₀.slot := by
    rw [Healing.cleanLabel_eq]; omega
  have hRs : Healing.drainTime sp a ≤ sp.ts s := by
    rw [Healing.drainTime_eq]; exact (SA.ts_le_iff sp).2 (by push_cast; omega)
  have hQ : Anc (tr.HonestBlocksAt H) D dd.head → ∃ Pr ∈ tr.HonestBlocksAt H,
      P.parent = some Pr.root ∧ Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor B) Pr := by
    intro hDQ
    have h0i := hrun.time_nonneg i
    have hri := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i))
      (tr.upTo (tr.time i)) proposer (hrun.upTo h0i) (hnc.upTo _)).localRun
    have hci' : (tr.upTo (tr.time i)).projAC.CallAt (proposer s) i ell₂ := by
      rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hci
    obtain ⟨hPhiP, hPhiPU⟩ := SA.frameIn_of_callAt hri hpi hci'
    obtain ⟨hst', hsQ⟩ := Compose.acProposal_start_anc_head hPhiP hdd
    have hQt : dd.head ∈ ell₂.frame.tree := by
      rcases eq_or_ne dd.start dd.head with he | he
      · exact he ▸ hst'
      · exact (Anc.mem hsQ he).2
    exact ⟨dd.head, RunTrace.honestBlocks_upTo_subset hrun.time_mono h0i (hPhiPU hQt), hpar,
      hXD.trans hDQ⟩
  have hclean : l₀.slot + 2 ≤ s → Anc (tr.HonestBlocksAt H) D dd.head := fun h2 =>
    hp.clean_source_proposal_parent_before_at hc hzr hpi (Or.inl ⟨CV, hflt⟩) hlab h2 hrb hRs
      hci hcall hdd hti hib
  rcases hflt with hup | hop
  · obtain ⟨-, -, ⟨-, -, ht, -⟩, -⟩ := hup
    have ht' : tr.time r' = sp.ts l₀.slot + 6 * sp.Δ := ht
    have h2 : l₀.slot + 2 ≤ s := by
      have hlt : sp.ts (l₀.slot + 1 : Nat) < sp.ts s := by
        have : sp.ts (l₀.slot + 1 : Nat) = sp.ts l₀.slot + 4 * sp.Δ := by
          simp only [SA.SAParams.ts]; push_cast; ring
        linarith
      have := (SA.ts_lt_iff sp).1 hlt
      omega
    exact hQ (hclean h2)
  · rcases Nat.lt_or_ge (l₀.slot + 1) s with h2 | h1
    · exact hQ (hclean (by omega))
    · have hsl : sp.slot (tr.time r') = l₀.slot := hop.choose_spec.choose_spec.2.1
      have hsm := SA.slot_mono sp (hrun.time_nonneg r') hrt
      obtain rfl : s = l₀.slot + 1 := by omega
      exact hQ (hp.clean_optimistic_proposal_parent_at hc hzr hpi hop hlab hrb hRs hci hcall hdd
        hti hib)

end Consensus.Goldilocks.Obligations.Growing

end
