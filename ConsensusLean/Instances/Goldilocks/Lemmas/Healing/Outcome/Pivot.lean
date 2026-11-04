module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotSourceVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

/-! # Goldilocks Healing: the pivot of an honest ready proposal after the drain (interface)

Post-reset `Compose.pivot_before` (A1.7, workbench#12 §2) for `ready_unanimous`: an honest ready
proposal `P` at `t_u ≥ R` has duty head `Q = P.parent`. Under reset premises, `Catch(2Δ)`
and three OPEN compatibility/support suppliers, its walk contains `D` with a viable
path to `Q`. Each honest slot-`u` voter whose earlier honest slot-`u` votes are `P` walks
through `P` or that path. Voters need not reach the proposer's own unlocked anchor.

The proof replaces Sleepy old origins with `OldSrc u`, HR.4 high origins before `t_u`:
* HR.4 (R3) puts every old source below every honest slot-`u` vote;
* stored proposal locks are compatible with old sources; non-current live vote locks have
  viable ancestors below the proposal parent (OPEN source-service obligations);
* an earlier honest supporter puts slot-`u` locks below `P`;
* `D` is deepest among the walk's start and the old sources on the walk.

Held viability lets the walk pass old sources. Fork-choice roots are genesis or below an old
source: high `J` uses a crossing row; low `J` uses the relayed reset seed and no top-height contest.
No universal low-row premise is needed. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-! ### The anchors -/

/-- Finite voter anchors lie below the old-source bound or on the proposal chain. -/
theorem ResetPremisesUpTo.reset_vote_anchor {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} {P Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPU : P ∈ tr.HonestBlocks H) (hR : drainTime sp a ≤ sp.ts u)
    (hPQ : P.parent = some Q.root) (hQU : Q ∈ tr.HonestBlocks H)
    (hDQ : Anc (tr.HonestBlocks H) D Q) (hDU : D ∈ tr.HonestBlocks H)
    (hDold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocks H) O D)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root)
    (hlocks : ∀ l ∈ e.readPoint.locks, l.slot ≠ u →
      sp.slot (tr.time j) ≤ l.slot + sp.k →
      ∀ L ∈ ell.frame.tree, L.root = l.block →
        Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) Q) :
    Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocks H) D (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) ∧
        Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) P) := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hDP : Anc (tr.HonestBlocks H) D P := hDQ.trans (.single ⟨hQU, hPU, hPQ⟩)
  have hat := Compose.anchor_tree hPhi e.readPoint (tr.time j)
  have haS := Compose.anchor_mem ell.frame e.readPoint (tr.time j)
  generalize SA.getAnchor sp e.readPoint ell.frame (tr.time j) = an at hat haS ⊢
  rcases haS with ⟨_, l', hl', hl'r⟩ | haf
  swap
  · rw [Set.mem_singleton_iff.1 haf]
    exact Or.inl (hp.reset_vote_root_below_bound hR hDU hDold hy hcy hes hjb)
  obtain ⟨l, hl, B, hB, hBr, hlive, rfl⟩ := hl'
  obtain rfl : an = ell.frame.viableAncestor B :=
    hPhi.coherent.1 hat (SA.viableAncestor_anc hPhi hB).1 hl'r.symm
  have haB : Anc (tr.HonestBlocks H) (ell.frame.viableAncestor B) B :=
    Anc.mono hPhiU (SA.anc_viableAncestor _ B)
  by_cases hls : l.slot = u
  · obtain ⟨Phi', A', D', _, hPhi'U, _, h34, hpool, _, L, hLU, hLr, hLD'⟩ :=
      SA.lock_origin_readPoint hrun hy hcy l hl (by rw [hes, hls]; omega)
    obtain rfl : L = B := hU.1 hLU (hPhiU hB) (hLr.trans hBr.symm)
    have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos y; omega
    obtain ⟨x, ⟨v, hv, rfl, R, hRt, hRr, hDR⟩, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A' Phi' l.slot D') (by omega)
    have hvH : v.val ∈ H := not_not.1 hxH
    obtain ⟨hvs, j', hj', e', hv', rfl⟩ := hpool v hv hvH
    have hRP : R = P := hU.1 (hPhi'U hRt) hPU
      (hRr.trans (hE _ hvH j' hj' e' hv' (hvs.trans hls)))
    rw [hRP] at hDR
    have haP := haB.trans (hLD'.trans (Anc.mono hPhi'U hDR))
    rcases Anc.total hU haP hDP with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haP⟩
  · have haQ := hlocks l hl hls
      (hlive.trans ((SA.castAt_readPoint_locksWF hr hy hcy).cap hl)) B hB hBr
    rcases Anc.total hU haQ hDQ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haQ.trans (.single ⟨hQU, hPU, hPQ⟩)⟩

set_option linter.unusedVariables false in
/-- **A voter's anchor is below `D`, or on `P`'s chain above `D`**: for a block `D` above every
old source and below `Q = P.parent`, at an honest slot-`u` vote whose earlier honest slot-`u`
votes are `P`. A live lock of slot `u` sits below an optimistic selection with an honest
supporter among the earlier votes, so below `P`; one of another slot has its viable ancestor
below the proposal parent by the explicit source-service supplier; `fc_root` by
`reset_vote_fcRoot`. -/
private theorem reset_vote_anchor (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hPQ : P.parent = some Q.root) (hQU : Q ∈ tr.HonestBlocks H)
    (hDQ : Anc (tr.HonestBlocks H) D Q) (hDU : D ∈ tr.HonestBlocks H)
    (hDold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O D)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = u)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root)
    (hlocks : ∀ l ∈ e.readPoint.locks, l.slot ≠ u →
      sp.slot (tr.time j) ≤ l.slot + sp.k →
      ∀ L ∈ ℓy.frame.tree, L.root = l.block →
        Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor L) Q) :
    Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocks H) D (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
        Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
        P ∈ tr.HonestBlocks H) := by
  have hPU : P ∈ tr.HonestBlocks H := by
    have hacc := Compose.proposal_accepted hp.run hp.noColl hP.1 hP.2.2.2.1
    refine ⟨p, hP.1, k + 1, ?_⟩
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hP.1 _)).1 P _
        (hp.run.toLocalRun.cutLaw p hP.1 _ _ hacc).2.1]
    exact Set.mem_insert _ _
  exact ((hp.toUpTo tr H (le_max_left a (tr.time j))).reset_vote_anchor hPU hR hPQ hQU hDQ hDU
    (fun x r l O ho hrt _ => hDold O (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩)) hy hcy hes
    (le_max_right _ _) hE hlocks).imp_right fun h => ⟨h.1, h.2, hPU⟩

/-- A bounded old-origin upper bound reaches the actual voter's height floor. -/
theorem ResetPremisesUpTo.reset_vote_floor_above_old {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocks H) O B) :
    (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy j
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot hR
  have hBh := hp.high_of_anc ho₀ hy hB (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb)
  have hnc := hp.no_high_contest hy j (fun q hq => (hp.run.time_mono hq.le).trans hjb)
  by_contra hle
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state y j).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state y j).fg.headHeightFloor = (tr.state y j).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hreach hC (h := (tr.state y j).fg.hmax - 1) (by omega) (by omega)
  obtain ⟨W, hW, att, ha, v, hv, d, hdj, hs, _, r, hrd, l, O, ho, hEO⟩ :=
    hp.left_entry_origin hy hE hET (by omega) hEC (by omega)
  have hlu : l < u := hes ▸ hp.row_origin_label_lt hy hc hW ha hv hs hdj hrd ho
  obtain ⟨_, D, CV, _, hf, _⟩ := hp.highOrigin_mem ho
  have hrt : tr.time r < sp.ts u := hp.fastLock_time_lt hf hlu
    ((hp.run.time_mono (by omega)).trans (hes ▸ (Compose.cast_head_fcRoot hr hy hc).2))
  have hEB := hEO.trans (hBold v r l O ho hrt ((hp.run.time_mono (by omega)).trans hjb))
  have := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hy hEB hB)
  omega

/-- A held block extending every pre-slot origin reaches the voter's height floor. -/
theorem reset_vote_floor_above_old
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) O B) :
    (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h :=
  (hp.toUpTo tr H (le_max_left a (tr.time j))).reset_vote_floor_above_old hy hR hc hes
    (le_max_right _ _) hB (fun x r l O ho hrt _ => hBold x r l O ho hrt)

/-- Actual bounded proposal and cast evidence bound the voter root by the proposal. -/
theorem ResetPremisesUpTo.reset_vote_root_below_proposal {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} (hpH : p ∈ H) {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt p k P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {elly : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j elly e)
    (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocks H) elly.frame.fcRoot P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQU := hPhiU (Compose.mem_of_anc_left hsQ hst)
  have hacc := Compose.proposal_accepted hp.run hp.noColl hpH hactual
  have hPU : P ∈ tr.HonestBlocks H := by
    refine ⟨p, hpH, k + 1, ?_⟩
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hpH _)).1 P _
        (hp.run.toLocalRun.cutLaw p hpH _ _ hacc).2.1]
    exact Set.mem_insert _ _
  apply hp.reset_vote_root_below_bound hR hPU (fun x r l O ho hrt _ => ?_) hy hcy hes hjb
  exact (hp.reset_proposal_passes hc hpH hR hci hcall hd hti hib O ⟨x, r, l, ho, hrt⟩).trans
    (.single ⟨hQU, hPU, hPQ⟩)

set_option linter.unusedVariables false in
/-- Before the first disagreeing vote, the voter root is below the actual proposal. -/
theorem reset_vote_root_below_proposal
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {elly : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j elly e)
    (hes : e.msg.slot = u)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root) : Anc (tr.HonestBlocks H) elly.frame.fcRoot P :=
  (hp.toUpTo tr H (le_max_left a (max (tr.time i) (tr.time j)))).reset_vote_root_below_proposal
    hc hP.1 hP.2.2.2.1 hR hci hcall hd hti ((le_max_left _ _).trans (le_max_right _ _)) hPQ hy hcy
    hes ((le_max_right _ _).trans (le_max_right _ _))

/-- **The pivot after the drain** (open: through the four residual steps above). -/
theorem reset_pivot (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      (∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads) ∧
      ∀ y ∈ H, ∀ j ℓy e, SA.CastAt tr.projAC y j ℓy e → e.msg.slot = u →
        (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
          e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame u))
            (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) := by
  have hrun := hp.run
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  have hpH : p ∈ H := hP.1
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hpH hci
  -- the proposal walk, from its start to `Q`
  obtain ⟨hstart, hsQ⟩ := Compose.acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := Compose.mem_of_anc_left hsQ hstart
  have hpass := reset_proposal_passes hp hc hP hR hci hcall hd hti hPQ
  -- `D`: the deepest of the start and the old sources on the proposal walk
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦp (S := {X | X ∈ ℓp.frame.tree ∧
      ℓp.frame.Anc d.start X ∧ ℓp.frame.Anc X d.head ∧ (X = d.start ∨ OldSrc tr H g u X)})
    (fun X hX => hX.1) ⟨d.start, hstart, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hΦp (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hΦp.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O D := by
    intro O hO
    have hOQ := hpass O hO
    rcases Anc.total hU hOQ (Anc.mono hΦpU hsQ) with h | h
    · exact h.trans (Anc.mono hΦpU hsD)
    have hOt := Compose.mem_between hU hΦp hΦpU hstart hQt h hOQ
    exact Anc.mono hΦpU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hΦp hΦpU hstart h hOt,
      SA.anc_tree_of_anc_U hU hΦp hΦpU hOt hOQ hQt, Or.inr hO⟩)
  refine ⟨D, hsD, hDQ,
    reset_suffix_viable hp hc hP hR hci hcall hd hti hPQ D hDt hsD hDold,
    fun y hy j ℓy e hcy hes hE => ?_⟩
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hhead := (SA.castAt_spec hr hy hcy).2.2.2
  rw [hes] at hhead
  have hat := Compose.anchor_tree hΦ e.readPoint (tr.time j)
  have hah : ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame u))
        (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) :=
    SA.anc_ghost (fun B hB => (SA.voteDomain_subset_tree hB.1)) _ hat
  have hht := Compose.mem_of_anc_left hah hat
  -- The vote's head extends `D`: direct start support, or HR.4 (R3).
  have hDh : Anc (tr.HonestBlocks H) D (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
      (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame u))
      (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) := by
    rw [oldSrc_iff] at hDk
    rcases hDk with rfl | ⟨x, i', j', ho, hti'⟩
    · exact proposal_start_supported hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
    obtain ⟨Hd, hHd, hHdr, hDHd⟩ :=
      (hret.votes x i' j' D ho y hy j ℓy e hcy (by rw [hes]; exact label_lt_of_old hp ho hti')).1
    rwa [hU.1 hHd (hΦU hht) (hHdr.trans hhead)] at hDHd
  rcases reset_vote_anchor hp hc hP hR hPQ (hΦpU hQt) (Anc.mono hΦpU hDQ) (hΦpU hDt)
      hDold hy hcy hes hE (fun l hl hne hlive L hL hLr =>
        vote_old_live_lock_below_parent hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
          hl hne hlive hL hLr) with haD | ⟨hDa, haP, hPU⟩
  · have hDt' := Compose.mem_between hU hΦ hΦU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hΦ hΦU hat haD hDt',
      SA.anc_tree_of_anc_U hU hΦ hΦU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := Compose.anc_parent hU haP haPe hPQ (hΦpU hQt)
  have hat' := Compose.mem_between hU hΦp hΦpU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hΦp hΦpU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hΦp hΦpU hat' haQ hQt⟩, .refl, hah⟩

/-- The finite operational pivot after the drain, before the first disagreeing cast. -/
theorem ResetPremisesUpTo.reset_pivot {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} (hpH : p ∈ H) {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt p k P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root) :
    ∃ D, ellp.frame.Anc d.start D ∧ ellp.frame.Anc D d.head ∧
      (∀ X, ellp.frame.Anc D X → ellp.frame.Anc X d.head → X ∈ ellp.frame.viableHeads) ∧
      ∀ y ∈ H, ∀ j elly e, SA.CastAt tr.projAC y j elly e → e.msg.slot = u → tr.time j ≤ b →
        (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
          e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ellp.frame.Anc D X ∧ ellp.frame.Anc X d.head)) ∧
          elly.frame.Anc (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) X ∧
          elly.frame.Anc X (SA.getHead sp e.readPoint elly.frame (tr.time j)
            (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
            (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := hr.coherent
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨hstart, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := Compose.mem_of_anc_left hsQ hstart
  have hacc := Compose.proposal_accepted hp.run hp.noColl hpH hactual
  have hPU : P ∈ tr.HonestBlocks H := by
    refine ⟨p, hpH, k + 1, ?_⟩
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hpH _)).1 P _
        (hp.run.toLocalRun.cutLaw p hpH _ _ hacc).2.1]
    exact Set.mem_insert _ _
  have hpass := hp.reset_proposal_passes hc hpH hR hci hcall hd hti hib
  obtain ⟨D, hD⟩ := SA.exists_deepest hPhi (S := {X | X ∈ ellp.frame.tree ∧
      ellp.frame.Anc d.start X ∧ ellp.frame.Anc X d.head ∧ (X = d.start ∨ OldSrc tr H g u X)})
    (fun X hX => hX.1) ⟨d.start, hstart, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hPhi (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hPhi.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O D := by
    intro O hO
    have hOQ := hpass O (oldSrc_iff.1 hO)
    rcases Anc.total hU hOQ (Anc.mono hPhiU hsQ) with h | h
    · exact h.trans (Anc.mono hPhiU hsD)
    have hOt := Compose.mem_between hU hPhi hPhiU hstart hQt h hOQ
    exact Anc.mono hPhiU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hPhi hPhiU hstart h hOt,
      SA.anc_tree_of_anc_U hU hPhi hPhiU hOt hOQ hQt, Or.inr hO⟩)
  have hDold' : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocks H) O D :=
    fun x r l O ho hrt _ => hDold O (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩)
  refine ⟨D, hsD, hDQ,
    hp.reset_suffix_viable hpH hR hci hcall hd hti hib D hDt hsD hDold',
    fun y hy j elly e hcy hes hjb hE => ?_⟩
  obtain ⟨hPsi, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hhead := (SA.castAt_spec hr hy hcy).2.2.2
  rw [hes] at hhead
  have hat := Compose.anchor_tree hPsi e.readPoint (tr.time j)
  have hah : elly.frame.Anc (SA.getAnchor sp e.readPoint elly.frame (tr.time j))
      (SA.getHead sp e.readPoint elly.frame (tr.time j)
        (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
        (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) :=
    SA.anc_ghost (fun B hB => (SA.voteDomain_subset_tree hB.1)) _ hat
  have hht := Compose.mem_of_anc_left hah hat
  have hDh : Anc (tr.HonestBlocks H) D (SA.getHead sp e.readPoint elly.frame (tr.time j)
      (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
      (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
    rw [oldSrc_iff] at hDk
    rcases hDk with rfl | ⟨x, r, l, ho, hrt⟩
    · exact hp.proposal_start_supported hc hpH hR hci hcall hd hti hib hy hcy hes hjb
    have hri : r < i := by
      by_contra hn
      have ht := hp.run.time_mono (Nat.le_of_not_gt hn)
      rw [hti] at ht
      exact (not_lt_of_ge ht) hrt
    have hlu := hp.origin_label_lt_at_proposal hpH hci hcall hti hri ho
    obtain ⟨Hd, hHd, hHdr, hDHd⟩ := hp.high_origin_votes_before j hjb x r l D ho
      ((hp.run.time_mono hri.le).trans hib) y hy elly e hcy (by omega)
    rwa [hU.1 hHd (hPsiU hht) (hHdr.trans hhead)] at hDHd
  rcases hp.reset_vote_anchor hPU hR hPQ (hPhiU hQt) (Anc.mono hPhiU hDQ) (hPhiU hDt)
      hDold' hy hcy hes hjb hE (fun l hl hne hlive L hL hLr =>
        hp.vote_old_live_lock_below_parent hc hpH hR hci hcall hd hti hib hy hcy hes hjb
          hl hne hlive hL hLr) with haD | ⟨hDa, haP⟩
  · have hDt' := Compose.mem_between hU hPsi hPsiU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hPsi hPsiU hat haD hDt',
      SA.anc_tree_of_anc_U hU hPsi hPsiU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint elly.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := Compose.anc_parent hU haP haPe hPQ (hPhiU hQt)
  have hat' := Compose.mem_between hU hPhi hPhiU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hPhi hPhiU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hPhi hPhiU hat' haQ hQt⟩, .refl, hah⟩

end Consensus.Goldilocks.Healing

end
