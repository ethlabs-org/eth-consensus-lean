module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotWalk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.RootFloor
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
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: old-source proposal support

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- Every pre-slot high origin lies below the bounded operational proposal's parent. -/
theorem ResetPremisesUpTo.reset_proposal_passes {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ∀ O, (∃ x r l, HighOrigin tr H g x r l O ∧ tr.time r < sp.ts u) →
      Anc (tr.HonestBlocks H) O d.head := by
  rintro O ⟨x, r, l, ho, hrt⟩
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos p; omega
  have hri : r < i := by
    by_contra hn
    have ht := hp.run.time_mono (Nat.le_of_not_gt hn)
    rw [hti] at ht
    exact (not_lt_of_ge ht) hrt
  have hrb := (hp.run.time_mono hri.le).trans hib
  have hlu := hp.origin_label_lt_at_proposal hpH hci hcall hti hri ho
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by clear * - hlu; omega⟩
  have hsucc : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  have below : Anc (tr.HonestBlocks H) O ell.frame.fcRoot →
      Anc (tr.HonestBlocks H) O d.head := by
    intro hOF
    obtain ⟨_, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A, _, hstart, _⟩ := Compose.acProposal_walk hd
    rw [hstart] at hsQ
    exact hOF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A (tr.time i)).trans hsQ))
  rcases hp.proposal_holds_old hpH hci hcall hd hti hib ho hrt with hOt | hOF
  swap
  · obtain ⟨hstart, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
    exact hOF.trans (Anc.mono hPhiU ((hPhi.rooted.2 _ hstart).trans hsQ))
  rcases hp.held_high_origin_viable hpH hci hib ho hrb
      (by rw [hti]; exact (SA.ts_le_iff sp).mpr (by clear * - hlu; omega)) hOt with hV | hOF
  swap
  · exact below (hOF.mono hPhiU)
  have hFO := (hPhi.rooted.2 O hOt).mono hPhiU
  have hhigh := hp.proposal_stored_locks_compatible_old hc hpH hR hci hcall hti hib ho hrb
  have hhigh' : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.projAC.time i) s O := by
    change SA.HighLocksCompatible _ _ (tr.time i) s O
    simpa only [Nat.add_sub_cancel] using hhigh
  have hcut : cutZ sp.toParams g ≤ sp.ts s :=
    (hp.cutZ_le_ts_of_highOrigin ho).trans ((SA.ts_le_iff sp).mpr (by clear * - hlu; omega))
  have hsg : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := lt_cutZ sp g
    linarith only [hΔ, hcut, this]
  have hsb : sp.ts s + sp.Δ ≤ b := by rw [hti, hsucc] at hib; linarith only [hΔ, hib]
  have hrestart : ∀ z ∈ H, ∀ q, tr.time q ≤ b → tr.projAC.RestartAt z q →
      tr.time q ≤ sp.ts ((s : Int) - 1) := by
    intro z hz q hqb hrest
    apply (restart_le_before hp hz (Compose.projAC_restartAt.mp hrest) hqb).trans
    rw [cutZ_eq] at hcut
    have := (SA.ts_le_iff sp).mp hcut
    exact (SA.ts_le_iff sp).mpr (by clear * - this; omega)
  have hrs : ∀ q ≤ i, tr.projAC.RestartAt p q → tr.time q < sp.ts s := by
    intro q hqi hrest
    exact (hrestart p hpH q ((hp.run.time_mono hqi).trans hib) hrest).trans_lt
      ((SA.ts_lt_iff sp).mpr (by clear * -; omega))
  by_cases hls : l < s
  · have votes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg O := by
      rintro z hz q e ⟨ell', hcast⟩ hes
      have hqb : tr.time q ≤ b := by
        have ht := SA.vote_time_le hr hz ⟨ell', hcast⟩
        have hsl := (SA.castAt_spec hr hz hcast).2.1
        rw [← hsl, hes] at ht
        exact ht.trans hsb
      exact hp.high_origin_votes_before q hqb x r l O ho hrb z hz ell' e hcast (by
          clear * - hls hes; omega)
    have hhalf := SA.honest_voters_half_before hS hsg hsb
      (fun z hz q hqt hrest => hrestart z hz q (hqt.trans hsb) hrest)
    have hhalf' : sp.n ≤ 2 *
        {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s}.ncard := by
      change sp.n ≤ 2 * {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧
        e.msg.slot = s ∧ tr.time q ≤ sp.ts s + sp.Δ}.ncard at hhalf
      have hle := Set.ncard_le_ncard (s := {z | z ∈ H ∧ ∃ q e,
        SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧ tr.time q ≤ sp.ts s + sp.Δ})
        (t := {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s})
        (by rintro z ⟨hz, q, e, hv, hs, _⟩; exact ⟨hz, q, e, hv, hs⟩)
      omega
    refine SA.batch_proposal hS.run hf hhalf' votes hpH hci
      (SA.proposal_slot hti) hd ⟨hOt, Or.inl hV⟩ ?_ hhigh'
    intro z hz q e hv hes
    obtain ⟨H', hH', hHr', hOH⟩ := votes z hz q e hv hes
    obtain ⟨Hd, hHd, hHdr, _, hmem, _, hbs⟩ := SA.late_vote_held_of_frame_before hS hpH hci hsg
      (by change _ ≤ tr.time i; rw [hti, hsucc]; linarith only [hΔ]) hib
      (fun k hki t _ => Compose.ac_deadline_le_of_restarts
        (fun k' hk' hr' => (hrs k' (hk'.trans hki) hr').le) t) hrs hz hv hes
      (fun Hd hHd hHdr => by
        rw [hU.1 hHd hH' (hHdr.trans hHr'.symm)]
        exact hFO.trans hOH)
    exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHd, hHdr,
      (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩
  · have hls : l = s := by clear * - hlu hls; omega
    obtain ⟨ellx, D, CV, hcx, hfl, _, _, _, hOD, _⟩ := hp.highOrigin_mem ho
    rw [hls] at hfl
    rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | hop
    · have ht' : tr.time r = sp.ts s + 6 * sp.Δ := ht
      rw [hsucc] at hrt
      linarith only [hΔ, hrt, ht']
    have hODU := hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2
    refine optimistic_first_proposal_anc hS.run hf ho.1 hop hODU hpH hci
      (SA.proposal_slot hti) hd ⟨hOt, Or.inl hV⟩ ?_ hhigh'
    intro v hv
    obtain ⟨hvs, hsend, B, hB, hBr, hDB, hacc⟩ := fastLock_writer hr ho.1 (Or.inr hop) v hv
    have hFB := hFO.trans (hODU.trans hDB)
    refine SA.heldAtProposal_of_writer hr (hp.sync.syncAC hp.run (le_gbar g))
      (by linarith only [hΔ, hsg]) le_rfl ho.1 hpH hci hti hrs hvs hsend ⟨B, hB, hBr, hFB, ?_⟩
    rcases hacc with hg | ⟨q, hq, hqt⟩
    · exact Or.inl hg
    by_cases hg : SA.gbar g ≤ tr.time q
    · exact Or.inr (Or.inl ⟨q, hq, hg, hqt⟩)
    · obtain ⟨k, hki, hak, hkt⟩ := hS.catchUp.relay x ho.1 q B hq (not_le.mp hg) p hpH i ell hci
        (by change _ ≤ tr.time i; rw [hti, hsucc]; linarith only [hΔ, hsg]) hib hFB
      exact Or.inr (Or.inr ⟨k, hki, hak, by
          change tr.time k < _ at hkt ⊢; linarith only [hΔ, hsg, hkt]⟩)

/-- Every old source is below the proposal's duty head. Relay and high-origin viability put
the source on the walk; earlier-label votes or the same-label optimistic quorum favor its
chain. -/
theorem reset_proposal_passes (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (_hPQ : P.parent = some d.head.root) :
    ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O d.head :=
  fun O hO => (hp.toUpTo tr H (le_max_left a (tr.time i))).reset_proposal_passes hc hP.1 hR
    hci hcall hd hti (le_max_right _ _) O (oldSrc_iff.1 hO)

/-- A crossing below an origin written before a serving proposal is below its duty parent.
The explicit timestamp preserves the provenance needed by bounded report consumers. -/
theorem crossing_below_proposal_parent
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    {x : Fin sp.n} {r l : Nat} {X O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrt : tr.time r < sp.ts u)
    (hXO : Anc (tr.HonestBlocks H) X O) : Anc (tr.HonestBlocks H) X d.head :=
  hXO.trans (reset_proposal_passes hp hc hP hR hci hcall hd hti hPQ O
    (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩))

/-- A high left entry of the proposer's store lies below a bounded pre-slot high origin: its
crossing attestation's origin label is below the proposal slot. -/
private theorem ResetPremisesUpTo.proposal_entry_below_old {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u)
    (hib : tr.time i ≤ b) {E C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state p i).fg.tree) (hET : ((tr.state p i).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state p i).fg.σ E.root).h) (hEC : (tr.state p i).fg.Anc E C)
    (hlt : ((tr.state p i).fg.σ E.root).h < ((tr.state p i).fg.σ C.root).h) :
    ∃ O, (∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b) ∧
      Anc (tr.HonestBlocks H) E O := by
  obtain ⟨_, _, _, _, v, _, k', hki, _, _, r, hrk, l, O, ho, hEO⟩ :=
    hp.left_entry_origin hpH hE hET hEh hEC hlt
  have hlu := hp.origin_label_lt_at_proposal hpH hci hcall hti (by
      clear * - hki hrk; omega : r < i) ho
  obtain ⟨_, D, CV, _, hfl, _⟩ := hp.highOrigin_mem ho
  have hrt : tr.time r < sp.ts u := hp.fastLock_time_lt hfl hlu (by
    have := hp.run.time_mono (by clear * - hki hrk; omega : r ≤ i)
    rw [hti] at this
    have := sp.toParams.hΔ
    linarith)
  exact ⟨O, ⟨v, r, l, ho, hrt, (hp.run.time_mono (by clear * - hki hrk; omega)).trans hib⟩, hEO⟩

/-- Bounded pre-slot origins suffice to bound an actual proposal's height floor. -/
theorem ResetPremisesUpTo.proposal_floor_above_old {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} (hci : tr.projAC.CallAt p i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state p i).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocks H) O B) :
    (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h := by
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot hR
  refine headHeightFloor_le_of_entries_below (Compose.fg_reachable hp.run.toLocalRun hpH i)
    (hp.high_of_anc ho₀ hpH hB (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb))
    (hp.no_high_contest hpH i fun q hq => (hp.run.time_mono hq.le).trans hib)
    fun E hE C hET hEh hEC hlt => ?_
  obtain ⟨O, ⟨v, r, l, ho, hrt, hrb⟩, hEO⟩ :=
    hp.proposal_entry_below_old hpH hci hcall hti hib hE hET hEh hEC hlt
  exact hp.anc_tree_of_anc hpH (hEO.trans (hBold v r l O ho hrt hrb)) hB

/-- A block above every old source reaches the proposal's floor. Only high crossing
quorums matter: the reset seed already makes the block high. -/
theorem proposal_floor_above_old (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ℓp : ACLabel (goldilocksNode sp ro)} (hci : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal) (hti : tr.time i = sp.ts u)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state p i).fg.tree)
    (hBold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O B) :
    (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h :=
  (hp.toUpTo tr H (le_max_left a (tr.time i))).proposal_floor_above_old hpH hR hci hcall hti
    (le_max_right _ _) hB (fun x r l O ho hrt _ => hBold O (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩))

/-- The finite proposal root is genesis or below a bounded pre-slot high origin. -/
theorem ResetPremisesUpTo.reset_proposal_root_source {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ell.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b ∧
        Anc (tr.HonestBlocks H) ell.frame.fcRoot O := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  rw [hfr]
  refine (fcRoot_genesis_or_below_source hr hp.honest_coherent (fun X hX => ⟨p, hpH, i, hX⟩)
    (fun O => ∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b)
    (fun E hE C hET hEh hEC hlt =>
      hp.proposal_entry_below_old hpH hci hcall hti hib hE hET hEh hEC hlt)
    (fun O ⟨_, _, _, ho, _⟩ W hW hOW => hp.high_of_anc ho hpH hW hOW) fun hlow => ?_).imp
    (congrArg Block.root) fun ⟨O, ⟨v, r, l, ho, hrt, hrb⟩, hO⟩ => ⟨v, r, l, O, ho, hrt, hrb, hO⟩
  obtain ⟨v, r, l, O, ho, hrb, _, hrt⟩ := hp.reset_seed_before_slot hR
  have hheld := hp.proposal_holds_old hpH hci hcall hd hti hib ho hrt
  rw [hfr] at hheld
  exact ⟨O, ⟨v, r, l, ho, hrt, hrb⟩, hp.low_finalized_below_origin hpH i hlow ho, hheld⟩

/-- The proposal root is genesis or below an old source. High `J` has a crossing attestation signed
before the proposal. Low `J` is below the held reset seed by the root's no-contest condition. -/
theorem reset_proposal_fcRoot (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (_hPQ : P.parent = some d.head.root) :
    ℓp.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldSrc tr H g u O ∧ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot O :=
  ((hp.toUpTo tr H (le_max_left a (tr.time i))).reset_proposal_root_source hP.1 hR hci hcall hd
    hti (le_max_right _ _)).imp_right
    fun ⟨v, r, l, O, ho, hrt, _, hO⟩ => ⟨O, oldSrc_iff.2 ⟨v, r, l, ho, hrt⟩, hO⟩


end Consensus.Goldilocks.Healing
