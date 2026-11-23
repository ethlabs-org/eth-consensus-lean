module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifiesSigned
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Recovery: the retained proposal's literal good window

Actual signed attestations reach the retained proposer's pool before its proposal cut. The carrier
is accepted by every honest validator: post-drain unanimity and the driven vote at `t_u + Δ`
force each validator to have accepted the proposed block, independently of its later cache.
-/

namespace Consensus.Goldilocks.Healing.Recovery

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- Every honest validator has accepted the ready proposal by `t_u + 2Δ`: at its tick there, its
finality is compatible with the proposal (`finalized_compatible_before_update`). Below the
proposal, the relay of an honest slot-`u` voter's frame (which holds the unanimous head by
`t_u + Δ`) reaches it; above, it holds the proposal with its finality. The later window deadline
leaves a strict margin. -/
theorem ready_proposal_accepted_everywhere (hp : ResetPremises tr H K proposer dg g ΔF a)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : ReadyProposal tr H proposer p k u W) (hR : drainTime sp a ≤ sp.ts u)
    (hu : 0 < u) (hg : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) :
    ∀ y ∈ H, ∃ j, tr.AcceptAt y j W ∧ tr.time j ≤ sp.ts u + 2 * sp.Δ := by
  have hΔ := sp.toParams.hΔ
  have hac := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun
  have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
  have ha0 : 0 ≤ a := by linarith [lt_cutZ (sp := sp) g, AC.gbar_nonneg g]
  have hau : a ≤ sp.ts u := (lt_drainTime ha0).le.trans hR
  have hpU := hp.toUpTo tr H (show a ≤ sp.ts u + 6 * sp.Δ by linarith)
  have hR' : drainTime sp a ≤ sp.ts (u + 1 : Nat) :=
    hR.trans ((AC.ts_le_iff sp).2 (by push_cast; omega))
  obtain ⟨_, hWt, _⟩ := accept_of_proposesAt hp.run hp.noColl hW.1 hW.2.2.2.1
  have hWU : W ∈ tr.HonestBlocks H := ⟨p, hW.1, k + 1, hWt⟩
  have hun := ready_unanimous hp hcatch hW hR
  -- an honest slot-`u` voter holds `W` in its frame by `t_u + Δ`
  obtain ⟨z, hz, q, v, ⟨ellv, hv⟩, hvs, hq⟩ :=
    Obligations.UpTo.exists_honest_vote_in_slot hpU hcatch hR' (by linarith)
  obtain ⟨⟨D, hD, hDr, _⟩, _⟩ := Compose.cast_head_fcRoot hr hac.vstart hz hv
  have hDW : D = W := hr.coherent.1 ((AC.frameIn_of_callAt hr hz hv.1).2 hD) hWU
    (hDr.trans (hun z hz q v ⟨ellv, hv⟩ hvs))
  rw [hDW] at hD
  have hq' : tr.time q ≤ sp.ts u + sp.Δ := hq
  intro y hy
  -- the tick of `y` at `t_u + 2Δ`
  have hS := healthy_base_of_reset_catch_before hpU hcatch
  have hg' := slotAfter_le (sp := sp) g
  obtain ⟨c, ell, hc, -, htc⟩ := hS.driven.tick y hy (sp.ts u + 2 * sp.Δ)
    (by linarith [AC.gbar_nonneg g]) ⟨4 * u + 2, by simp only [ACParams.ts]; ring⟩
    (hS.awake y hy _ (by rw [gbar_slotAfter]; linarith) (by linarith))
  have htc' : tr.time c = sp.ts u + 2 * sp.Δ := htc
  have hWy : W ∈ (tr.state y c).fg.tree := by
    rcases Obligations.UpTo.finalized_compatible_before_update hpU hcatch hWU hW.2.2.2.2.1 hu
        (fun x hx j e hv _ hs => hun x hx j e hv hs) hg hR' (by linarith) hy (k := c)
        (by linarith) (by linarith) with hFW | hWF
    · have hF : Anc (tr.HonestBlocks H) ell.frame.F W := by
        rw [Compose.frame_of_projAC hp.run hy hc]
        exact hFW
      exact mem_tree_of_frame hp.run hy hc (hpU.reset_frame_relay hcatch hz hy hv.1 hc hD
        (by linarith) (by linarith) (by linarith) (by linarith) hF)
    · have hFm := (Store.cache_invariants _ _ _ _
        (Compose.fg_reachable hp.run.toLocalRun hy c)).1
      exact mem_of_honest_anc hp.run hp.noColl hy hWF hFm
  have hng : W ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
    intro he
    have hslot := hW.2.2.2.2.1
    rw [he] at hslot
    change 0 = u at hslot
    omega
  obtain ⟨i, hic, hi⟩ := (Compose.tree_cases hp.run.toLocalRun hy hWy).resolve_left hng
  exact ⟨i, hi, (hp.run.time_mono hic.le).trans htc'.le⟩

/-- The composition's actual honest proposal includes every pooled attestation for its parent's
current entry that is not on the parent's chain (the good window's P5): `proposal_attestations`
keeps every pooled attestation valid against the parent's state, and those for the current entry
are valid. -/
private theorem proposal_includes_pool (hp : ResetPremises tr H K proposer dg g ΔF a)
    {w : Fin sp.n} (hw : w ∈ H) {k : Nat} {W Pr : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt w k W) (hPr : Pr ∈ (tr.state w k).fg.tree)
    (hpar : W.parent = some Pr.root) :
    ∀ att ∈ (tr.state w k).fg.atts, att.h = ((tr.state w k).fg.σ Pr.root).h →
      att.T = ((tr.state w k).fg.σ Pr.root).Th → ¬ (tr.state w k).fg.OnChain Pr att →
        att ∈ W.fgPayload := by
  obtain ⟨hacc, _, _⟩ := accept_of_proposesAt hp.run hp.noColl hw hW
  rcases Compose.blockCall_cases hp.run.toLocalRun hw hacc with hg |
    ⟨j, x, _, _, _, d, pay, _, hB, _, _, _, hfg⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hW.1.2
  have hpay : W.fgPayload = (tr.state w k).fg.proposalAttestations d.head := by
    rw [hfg, hB]; rfl
  have hroot : d.head.root = Pr.root := by
    have : W.parent = some d.head.root := by rw [hB]; rfl
    exact Option.some.inj (this.symm.trans hpar)
  intro att ha hh hT hn
  rw [hpay]
  simp only [Store.proposalAttestations, List.mem_filter, decide_eq_true_eq]
  refine ⟨ha, by rw [hroot]; exact Or.inl ⟨hh, hT⟩, fun ⟨X, hX, hXd, haX⟩ => hn ⟨X, hX, ?_, haX⟩⟩
  have hd := mem_of_anc_right hXd hX
  have he : d.head = Pr := (honest_coherent hp).1 ⟨w, hw, k, hd⟩ ⟨w, hw, k, hPr⟩ hroot
  rwa [he] at hXd

/-- Exact signed entry attestations, delivered before the retained ready proposal, form the literal
`GoodWindow`. Neither report times nor signing times need a freshness lower bound. -/
theorem good_window_of_rows (hp : ResetPremises tr H K proposer dg g ΔF a)
    (hs : HSShared tr H K dg g ΔF) {y w : Fin sp.n} (hy : y ∈ H) (hw : w ∈ H)
    {m k cF kF : Nat} {T W Pr : AC.Blk sp.n (List (FG.Att sp.n))}
    (hT : T ∈ (tr.state y m).fg.tree) (he : ((tr.state y m).fg.σ T.root).Th = T.root)
    (hW : tr.ProposesAt w k W) (hpar : W.parent = some Pr.root)
    (hTPr : Anc (tr.HonestBlocks H) T Pr)
    (hlo : T.slot + cF ≤ W.slot) (hhi : W.slot ≤ T.slot + cF + kF)
    (hg : AC.gbar g ≤ sp.ts T.slot)
    (hcf : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time))
    (hto : cF + kF ≤ sp.toParams.δt)
    (ids : Finset (Fin sp.n)) (hq : sp.toParams.fg.q ≤ ids.card)
    (hrows : ∀ z ∈ ids, z ∈ H ∧ ∃ att j, tr.SignAt z j att ∧ att.val = z ∧
      att.h = ((tr.state y m).fg.σ T.root).h ∧ att.T = T.root ∧ att.timeout = false ∧
      tr.time j ≤ sp.ts T.slot + 6 * sp.Δ ∧
      (((tr.state y m).fg.σ T.root).previousHeightJustified →
        att.fin = some (((tr.state y m).fg.σ T.root).hj, ((tr.state y m).fg.σ T.root).J))) :
    ∃ R, Store.GoodWindow sp.toParams (Payload sp.n) H tr.projFG cF T 0 kF w k W Pr R := by
  classical
  obtain ⟨Pr', hpar', hPr'⟩ := proposal_parent_held hp.run hp.noColl hw hW
  have hPrU : Pr ∈ tr.HonestBlocks H := mem_of_anc_right hTPr ⟨y, hy, m, hT⟩
  have hPr : Pr ∈ (tr.state w k).fg.tree := by
    have heq := (honest_coherent hp).1 ⟨w, hw, k, hPr'⟩ hPrU
      (Option.some.inj (hpar'.symm.trans hpar))
    rwa [heq] at hPr'
  have hTw := mem_tree_of_anc hp hw hTPr hPr
  have hσ := σ_eq_run hp hw hy hTw hT
  have hstore : tr.projFG.store w k = (tr.state w k).fg :=
    congrArg Prod.fst (Compose.projFG_state hp.run.toLocalRun hw k)
  have htime : tr.time k = sp.ts W.slot := by rw [hW.2.2, sp.slotTime_eq]; rfl
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hdelivery : sp.ts T.slot + 6 * sp.Δ + ΔF ≤ tr.time k := by
    rw [htime]
    have hslots : sp.ts (T.slot + cF : Nat) ≤ sp.ts W.slot :=
      (AC.ts_le_iff sp).2 (by exact_mod_cast hlo)
    simp only [ACParams.ts] at hslots ⊢
    push_cast at hslots
    linarith
  choose att j hsig hval hh hroot hto' ht hfin using fun z : ids => (hrows z z.property).2
  let R := Finset.univ.image att
  have hvals : R.image FG.Att.val = ids := by
    ext z
    simp only [R, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨row, ⟨v, rfl⟩, hv⟩
      rw [hval v] at hv
      exact hv ▸ v.property
    · intro hz
      exact ⟨att ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, hval ⟨z, hz⟩⟩
  refine ⟨R, ?_⟩
  constructor
  · refine ⟨hw, Compose.projFG_callAt.2 (accept_of_proposesAt hp.run hp.noColl hw hW).1,
      hW.2.1, hW.2.2.symm, ?_, hpar, ?_⟩
    · rwa [hstore]
    · simpa only [hstore] using proposal_includes_pool hp hw hW hPr hpar
  · rw [hstore]
    exact ⟨hTw, by rw [hσ]; exact he⟩
  · rw [hstore]
    exact anc_tree_of_anc hp hw hTPr hPr
  · simpa only [Nat.add_zero] using And.intro hlo hhi
  · rwa [hvals]
  · intro row hr
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hr
    simpa only [hstore, hσ] using And.intro (hh z) ⟨hroot z, hto' z, hfin z⟩
  · intro row hr
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hr
    right
    intro _
    obtain ⟨src, hc⟩ := hsig z
    refine ⟨j z, ⟨src, ?_⟩, ?_⟩
    · rw [hval z]
      exact Compose.projFG_callAt.2 hc
    · rw [sp.slotTime_eq, Nat.add_zero]
      change tr.time (j z) ≤ 4 * sp.Δ * (T.slot : Int) + 6 * sp.Δ
      simpa only [ACParams.ts] using ht z
  · intro row hr
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hr
    right
    obtain ⟨i, hik, hi⟩ := rows_delivered hs (by linarith) hw hW hdelivery
      (hrows z z.property).1 (hsig z) (ht z)
    rw [hstore]
    exact processed_att_retained hp.run.toLocalRun hw hi hik
  · simpa only [Nat.zero_add] using hto

end Consensus.Goldilocks.Healing.Recovery

end
