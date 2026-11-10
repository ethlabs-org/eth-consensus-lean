module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
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

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- Driven unanimous votes force actual acceptance of the ready proposal everywhere,
by `t_u + Δ`. The later window deadline leaves a strict margin. -/
theorem ready_proposal_accepted_everywhere (hp : ResetPremises tr H proposer dg g ΔF a)
    (hs : HSShared tr H dg g ΔF) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : ReadyProposal tr H proposer p k u W) (hR : drainTime sp a ≤ sp.ts u)
    (hu : 0 < u) (hg : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) :
    ∀ y ∈ H, ∃ j, tr.AcceptAt y j W ∧ tr.time j ≤ sp.ts u + sp.Δ := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hb : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g :=
    ⟨hac, projection_driven hp.run hp.noColl hs.genesisRoot hp.healthy,
      projection_healthy hp.run hp.noColl hp.healthy, projection_catch_of_run hp.run hcatch⟩
  obtain ⟨_, hWt, _⟩ := accept_of_proposesAt hp.run hp.noColl hW.1 hW.2.2.2.1
  have hWU : W ∈ tr.HonestBlocks H := ⟨p, hW.1, k + 1, hWt⟩
  intro y hy
  obtain ⟨j, e, hv, hes⟩ := SA.honest_votes_in_slot hb hg y hy
  have hhead := ready_unanimous hp hcatch hW hR y hy j e hv hes
  obtain ⟨ell, hcall, hem⟩ := hv
  obtain ⟨⟨D, hD, hDr, _⟩, ht⟩ := Compose.cast_head_fcRoot hac.localRun hy ⟨hcall, hem⟩
  have hDW : D = W := hac.localRun.coherent.1
    ((SA.frameIn_of_callAt hac.localRun hy hcall).2 hD) hWU (hDr.trans hhead)
  rw [hDW] at hD
  have hWy := mem_tree_of_frame hp.run hy hcall hD
  have hng : W ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
    intro he
    have hslot := hW.2.2.2.2.1
    rw [he] at hslot
    change 0 = u at hslot
    omega
  obtain ⟨i, hij, hi⟩ := (Compose.tree_cases hp.run.toLocalRun hy hWy).resolve_left hng
  refine ⟨i, hi, (hp.run.time_mono hij.le).trans ?_⟩
  rw [hes] at ht
  exact ht

/-- The composition's actual honest proposal has the uncapped pool-inclusion property
required by the FG good window. -/
private theorem proposal_includes_pool (hp : ResetPremises tr H proposer dg g ΔF a)
    {w : Fin sp.n} (hw : w ∈ H) {k : Nat} {W Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt w k W) (hPr : Pr ∈ (tr.state w k).fg.tree)
    (hpar : W.parent = some Pr.root) :
    ∀ att ∈ (tr.state w k).fg.atts, ((tr.state w k).fg.σ Pr.root).validAtt att →
      ¬ (tr.state w k).fg.OnChain Pr att → att ∈ W.fgPayload := by
  obtain ⟨hacc, _, _⟩ := accept_of_proposesAt hp.run hp.noColl hw hW
  rcases Compose.blockCall_cases hp.run.toLocalRun hw hacc with hg |
    ⟨j, x, _, _, _, d, pay, _, hB, _, _, _, hfg⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hW.1.2
  have hpay : W.fgPayload = (tr.state w k).fg.proposalAttestations d.head := by
    rw [hfg, hB]; rfl
  have hroot : d.head.root = Pr.root := by
    have : W.parent = some d.head.root := by rw [hB]; rfl
    exact Option.some.inj (this.symm.trans hpar)
  intro att ha hv hn
  rw [hpay]
  simp only [Store.proposalAttestations, List.mem_filter, decide_eq_true_eq]
  refine ⟨ha, by rw [hroot]; exact hv, fun ⟨X, hX, hXd, haX⟩ => hn ⟨X, hX, ?_, haX⟩⟩
  have hd := mem_of_anc_right hXd hX
  have he : d.head = Pr := (honest_coherent hp).1 ⟨w, hw, k, hd⟩ ⟨w, hw, k, hPr⟩ hroot
  rwa [he] at hXd

/-- Exact signed entry attestations, delivered before the retained ready proposal, form the literal
`GoodWindow`. Neither report times nor signing times need a freshness lower bound. -/
theorem good_window_of_rows (hp : ResetPremises tr H proposer dg g ΔF a)
    (hs : HSShared tr H dg g ΔF) {y w : Fin sp.n} (hy : y ∈ H) (hw : w ∈ H)
    {m k cF kF : Nat} {T W Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hT : T ∈ (tr.state y m).fg.tree) (he : ((tr.state y m).fg.σ T.root).Th = T.root)
    (hW : tr.ProposesAt w k W) (hpar : W.parent = some Pr.root)
    (hTPr : Anc (tr.HonestBlocks H) T Pr)
    (hlo : T.slot + cF ≤ W.slot) (hhi : W.slot ≤ T.slot + cF + kF)
    (hg : SA.gbar g ≤ sp.ts T.slot)
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
      (SA.ts_le_iff sp).2 (by exact_mod_cast hlo)
    simp only [SAParams.ts] at hslots ⊢
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
      simpa only [SAParams.ts] using ht z
  · intro row hr
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hr
    right
    obtain ⟨i, hik, hi⟩ := rows_delivered hs (by linarith) hw hW hdelivery
      (hrows z z.property).1 (hsig z) (ht z)
    rw [hstore]
    exact processed_att_retained hp.run hw hi hik
  · simpa only [Nat.zero_add] using And.intro hto (show 1 ≤ FG.FGParams.KW by decide)

end Consensus.Goldilocks.Healing.Recovery

end
