module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Finite frame relay and the actual proposal walk

* `frame_relay_before`: finite frame transport for head equality.
* `proposal_views_agree_before`: the finite view comparison at an actual cast.
* `full_frame_viable_witness`, `proposal_parent_viable_full_frame`: the full current frame has a
  viable head above its fork-choice root, and the actual proposal parent is viable in it.
* `proposal_walk_end`: the actual full-frame proposal walk stops at its duty head.

None of them assumes a settled phase. Saved results compare actual stored origins; the proofs use
emission read points, remapped locks and viableAncestor, not a lease or pivot-cover premise. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- Finite frame transport for head equality. The receiver's finalized-ancestor guard
is explicit; old acceptances use Catch and newer ones use their relay deadline.
No settled phase, shared finalized root or frame equality is required. -/
private theorem frame_relay_before {K : AC.CommitteeDict sp.n}
    (hS : AC.HealthyBaseUpTo K tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := hS.run.localRun
  rcases Compose.frame_anc_acceptedU hr.toU hx q ellx hcx B hB B .refl with
      hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hy j elly hcy
    obtain rfl : B = G := hr.coherent.1 ((AC.frameIn_of_callAt hr hx hcx).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (AC.frameIn_of_callAt hr hy hcy).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  have hkt : tr.time k + sp.Δ ≤ tr.time j := by
    have := hr.time_mono hk
    change tr.time k ≤ tr.time q at this
    linarith
  by_cases hnew : gbar g ≤ tr.time k
  · have hdl : tr.projAC.deadline y j (tr.time k) ≤ tr.time j := by
      have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
        (fun r _ hrs => hnr y hy r (Compose.projAC_restartAt.mp hrs)) (tr.time k)
      change _ ≤ max (tr.time k) (gbar g) + sp.Δ at hd
      rw [max_eq_left hnew] at hd
      exact hd.trans hkt
    obtain ⟨a, haj, hacc, -⟩ := hS.sync.relay x hx k B ha hnew y hy j elly hcy
      (hdl.trans hjb) hdl hF
    exact AC.mem_tree_of_acceptAtU sp hr.toU hy hacc haj hcy hF
  · obtain ⟨a, haj, hacc, -⟩ := hS.catchUp.relay x hx k B ha (not_le.mp hnew)
      y hy j elly hcy hg hjb hF
    exact AC.mem_tree_of_acceptAtU sp hr.toU hy hacc haj hcy hF

/-- The finite view comparison at an actual cast. Pre-freeze blocks
relay to the proposer; payload support heads are held at an early ready cast
or relay by the deadline. The statement has no settled/phase assumption. -/
theorem proposal_views_agree_before {K : AC.CommitteeDict sp.n}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hS : AC.HealthyBaseUpTo K tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g)) {s : Nat}
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)} {pay : Payload sp.n}
    (hp : AC.ProposalAt tr.projAC z ip ellp pay) (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : P.acPayload = pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {elly : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hP : P ∈ elly.frame.tree) (hjb : tr.time j ≤ b) :
    AC.equivocators (AC.View.ofLists pay).votes =
        AC.equivocators (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      AC.voters (AC.View.ofLists pay).votes =
        AC.voters (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        AC.supporters ellp.frame (AC.View.ofLists pay) s X =
          AC.supporters elly.frame (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := AC.ts_succ s
  have hslot := (AC.castAt_specU hr.toU hy hc).2.1.symm.trans hes
  have hjlo : sp.ts (s + 1 : Nat) ≤ tr.time j :=
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by rw [hslot])
  have hipb : tr.time ip ≤ b := by rw [hti]; exact hjlo.trans hjb
  have hPhiY := AC.frameIn_of_callAt hr hy hc.1
  have hPhiP := AC.frameIn_of_callAt hr hz hp.1
  apply AC.view_agree_window_before hS.run hS.run.vstart
    hz hy hdesignated hp hti hc hes
    ⟨P, hP, hPs, hpay⟩ (AC.serviceWindowBefore_of_sync hS.sync) (by linarith only [hm, hΔ]) hipb
    hjb
  · intro B hB _ hstamp hFB
    rw [AC.readPoint_blockStamp_eqU hr.toU hy hc] at hstamp
    rcases stamp_origin hr hy j elly hc.1 B hB with hg | ⟨q, -, ellq, hq, hBq, hsq⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hz ip ellp hp.1
      obtain rfl : B = G := hr.coherent.1 (hPhiY.2 hB) hGU (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hFB with he | ⟨c, _, hpar⟩
      · exact he ▸ hPhiP.1.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    have hqt : tr.time q < sp.ts s + 3 * sp.Δ := by
      rw [hsq] at hstamp
      have ht := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hstamp)
      change tr.time q < AC.freeze sp (s + 1) at ht
      simpa only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] using ht
    exact frame_relay_before hS hnr hy hz hq hp.1 hBq
      (by rw [hti, hts]; linarith only [hm, hΔ]) (by rw [hti, hts]; linarith only [hqt]) hipb hFB
  · intro v hv B hB hBr hFB
    by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
    · obtain ⟨⟨P', hP', hPs', hsup⟩, -⟩ := AC.cast_readyU hr.toU hy hc (by rw [hes]; exact hearly)
      rw [hes] at hPs' hsup
      obtain rfl := proposal_frame_unique hrun hnc hz hdesignated hactual hPs
        (by clear * -; omega) hy hc.1 hP' hPs'
      have hvs : v.slot + 1 = s + 1 := by
        obtain ⟨d, hd⟩ := hp.2.2
        have hpayeq : pay = AC.voteViewList (tr.projAC.state z ip) ellp.frame
            ((sp.slot (tr.time ip) : Int) - 1) ⊤ := by
          unfold AC.acProposal at hd
          split_ifs at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          exact hd.2.symm
        have hsi : sp.slot (tr.time ip) = s + 1 := AC.proposal_slot (tr := tr.projAC) hti
        rw [hpayeq, hsi] at hv
        simp only [show ((s + 1 : Nat) : Int) - 1 = (s : Int) by clear * -; omega,
          AC.voteViewList, AC.ACState.poolAt, Int.toNat_natCast, List.filter_filter,
          List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
          Bool.and_eq_true, decide_eq_true_eq] at hv
        rw [AC.state_pool_slotU sp hr.toU hS.run.vstart hz ip s v hv.1]
      obtain ⟨B', hB', hBr', -⟩ := hsup v (by rw [AC.declaredSupportVotes, hpay]; exact hv) hvs
      rwa [hr.coherent.1 (hPhiP.2 hB) (hPhiY.2 hB') (hBr.trans hBr'.symm)]
    · exact frame_relay_before hS hnr hz hy hp.1 hc.1 hB
        (by linarith only [hm, hΔ, hts, hjlo]) (by rw [hti]; exact not_lt.1 hearly) hjb hFB

/-- The full current frame has a viable head above its fork-choice root.
Kind J uses the justification cache; the other cases use the hmax cache.
Unlike a frozen voter domain, the proposal domain cannot lose this witness. -/
theorem full_frame_viable_witness (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∃ Q ∈ (Node.frame (tr.state y i)).tree,
      Q ∈ (Node.frame (tr.state y i)).viableHeads ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot Q := by
  classical
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨_, hJt, _, ⟨B, hB, hBJ, hBh⟩, _, ⟨Q, hQ, hQh⟩, _⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hr
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬ (tr.state y i).fg.Contest
  · obtain ⟨E, hE, hEr, hh⟩ := J_entry_h hr hB
    have he : E = (tr.state y i).fg.J :=
      (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.1.1 hE hJt (hEr.trans hBJ)
    rw [he, hBh] at hh
    have hheight : (tr.state y i).fg.headHeightFloor ≤
        ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h := by
      change (if _ then _ else _) ≤ _
      rw [ite_eq_right hk.2, hk.1]
      clear * - hh; omega
    obtain ⟨hQt, hroot, hv⟩ := floor_ancestor_mem_frame hrun hnc hf hy hy hJt
      hheight (fun _ _ => Relation.ReflTransGen.refl) hJt Relation.ReflTransGen.refl
    exact ⟨_, hQt, hv, hroot⟩
  · obtain ⟨hQt, hroot, hv⟩ := floor_ancestor_mem_frame hrun hnc hf hy hy hQ
      ((Goldilocks.Store.headHeightFloor_bounds (tr.state y i).fg).2.trans_eq hQh.symm)
      (fun hm hc => (hk ⟨hm, hc⟩).elim) hQ Relation.ReflTransGen.refl
    exact ⟨Q, hQt, hv, hroot⟩

/-- The actual proposal parent is viable in the full current frame. The old
settled-phase supplier is unnecessary: the cache witness and current-frame
AncestorCandidate anchor suffice, including label-(p−1) optimistic locks. -/
theorem proposal_parent_viable_full_frame
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {i s : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.toParams.slotTime s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 =
      some (d, pay)) : d.head ∈ ell.frame.viableHeads := by
  have hac := Compose.goldilocks_ac_projection_from hrun hnc
  obtain ⟨Q, hQ, hv, hroot⟩ := full_frame_viable_witness hrun hnc hf hy i
  rw [← Compose.frame_of_projAC hrun hy hc] at hQ hv hroot
  exact proposal_head_viable hac.localRun hrun.vstart hy hc hcall hti hp
    ⟨(AC.frameIn_of_callAt hac.localRun hy hc).1.fcRoot_mem,
      Relation.ReflTransGen.refl, Q, hQ, hv, hroot⟩

/-- The actual full-frame proposal walk stops at its duty head. This is the
finite walk supplied by acProposal, without any settled-phase interface. -/
theorem proposal_walk_end (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} (hz : z ∈ H) {ip : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)} (hcp : tr.projAC.CallAt z ip ellp)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (AC.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) :
    d.start ∈ ellp.frame.tree ∧
      ellp.frame.Anc ellp.frame.fcRoot d.start ∧
      AC.WalkEnd (sp := sp) (ellp.frame.viableTree ellp.frame.tree)
        (AC.headScore sp ellp.frame (AC.View.ofLists pay) ((sp.slot (tr.time ip) : Int) - 1))
        (AC.headEligible sp ellp.frame (tr.time ip) (AC.View.ofLists pay)
          ((sp.slot (tr.time ip) : Int) - 1)) d.start d.head := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  have hPhi := (AC.frameIn_of_callAt hr hz hcp).1
  have key (A : AC.ACState sp.n) (V : AC.View sp.n) (σ : Int) :
      AC.getAnchor sp A ellp.frame (tr.time ip) ∈ ellp.frame.tree ∧
      ellp.frame.Anc ellp.frame.fcRoot (AC.getAnchor sp A ellp.frame (tr.time ip)) ∧
      AC.WalkEnd (sp := sp) (ellp.frame.viableTree ellp.frame.tree)
        (AC.headScore sp ellp.frame V σ)
        (AC.headEligible sp ellp.frame (tr.time ip) V σ)
        (AC.getAnchor sp A ellp.frame (tr.time ip))
        (AC.getHead sp A ellp.frame (tr.time ip) (ellp.frame.viableTree ellp.frame.tree) V σ) := by
    have hroot := AC.fcRoot_anc_getAnchor hPhi A (tr.time ip)
    have hstart : AC.getAnchor sp A ellp.frame (tr.time ip) ∈ ellp.frame.tree := by
      rcases eq_or_ne ellp.frame.fcRoot (AC.getAnchor sp A ellp.frame (tr.time ip)) with he | he
      · exact he ▸ hPhi.fcRoot_mem
      · exact (Anc.mem hroot he).2
    refine ⟨hstart, hroot, ?_⟩
    exact AC.walkEnd_ghost hPhi.coherent (fun X hX => hX.1)
      (hPhi.finite.subset fun X hX => hX.1)
      (Set.ncard_le_ncard (fun X hX => hX.1) hPhi.finite) _
  unfold AC.acProposal at hp
  split_ifs at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact key _ _ _

end Consensus.Goldilocks.Healing

end
