module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotSupport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.RootFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.ProposalStart
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.CastEntry
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

/-! # Goldilocks Healing: source votes and viable suffixes

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- Actual bounded casts extend the start of a drained operational proposal. -/
theorem ResetPremisesUpTo.proposal_start_supported {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocks H) d.start
      (SA.getHead sp e.readPoint elly.frame (tr.time j)
        (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
        (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨hPsi, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hhead := SA.getHead_mem hPsi
    (T := elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
    (fun _ h => (SA.voteDomain_subset_tree h.1)) e.readPoint (tr.time j)
    (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)
  have hheadr := (SA.castAt_spec hr hy hcy).2.2.2
  rw [hes] at hheadr
  have extend : ∀ B, SA.VoteExtends (tr.HonestBlocks H) e.msg B →
      Anc (tr.HonestBlocks H) B
        (SA.getHead sp e.readPoint elly.frame (tr.time j)
          (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
          (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
    rintro B ⟨W, hW, hWr, hBW⟩
    obtain rfl := hr.coherent.1 hW (hPsiU hhead) (hWr.trans hheadr)
    exact hBW
  rcases proposal_start_root_or_clean_lock hPhi (SA.locksWF_state hr hpH i) hR hti hd with
    hroot | ⟨l₁, hl₁, hlo, B₁, hB₁, hB₁r, hsB₁⟩
  · rw [hroot]
    rcases hp.reset_proposal_root_source hpH hR hci hcall hd hti hib with
      hg | ⟨x, r, l, O, ho, hOld, hrb, hfO⟩
    · exact Compose.honest_genesis_root_anc hp.run hr.coherent (hPhiU hPhi.fcRoot_mem) hg
        (hPsiU hhead)
    apply hfO.trans (extend O ?_)
    have hri : r < i :=
      lt_of_not_ge fun h => (hp.run.time_mono h).not_gt (hOld.trans_eq hti.symm)
    have hlu := hp.origin_label_lt_at_proposal hpH hci hcall hti hri ho
    exact hp.high_origin_votes_before j hjb x r l O ho hrb y hy elly e hcy (by
        clear * - hes hlu; omega)
  obtain ⟨r, hri, D, horig, L, hLU, hLr, hLD⟩ :
      ∃ r < i, ∃ D,
        ((∃ CV, SA.FastLockAt tr.projAC p r l₁.slot D CV) ∨
          SA.SlowLockAt tr.projAC p r l₁.slot D) ∧
        ∃ L ∈ tr.HonestBlocks H, L.root = l₁.block ∧ Anc (tr.HonestBlocks H) L D := by
    cases hf : l₁.fast with
    | false =>
      obtain ⟨r, hri, D, hsl, hL⟩ := SA.slow_lock_provenance hr hpH i l₁ hl₁ hf
      exact ⟨r, hri, D, Or.inr hsl, hL⟩
    | true =>
      obtain ⟨r, hri, D, CV, hfl, hL⟩ := SA.fast_lock_provenance hr hpH i l₁ hl₁ hf
      exact ⟨r, hri, D, Or.inl ⟨CV, hfl⟩, hL⟩
  obtain rfl : L = B₁ := hr.coherent.1 hLU (hPhiU hB₁) (hLr.trans hB₁r.symm)
  have hlt : l₁.slot < u := Compose.proposal_locks_slot_of hp.run hp.noColl
    (by have := hp.faults; have := Fin.pos p; omega) hpH hci hcall hd hti l₁
    (Compose.projAC_state hp.run.toLocalRun hpH i ▸ hl₁)
  apply (Anc.mono hPhiU hsB₁).trans (hLD.trans (extend D ?_))
  rcases horig with ⟨CV, hf⟩ | hslow
  · exact hp.fast_source_votes_before hc hpH hf hlo ((hp.run.time_mono hri.le).trans hib)
      j hjb y hy elly e hcy (by clear * - hes hlt; omega)
  · exact hp.slow_source_votes_before hc hpH hslow hlo ((hp.run.time_mono hri.le).trans hib)
      j hjb y hy elly e hcy (by clear * - hes hlt; omega)

section SourceVotes

variable (hp : ResetPremises tr H proposer dg g ΔF a)
  (hc : CatchRun tr H g (2 * sp.Δ))
  {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
  (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
  {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
  (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
  (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = u)
  (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
    e'.msg.slot = u → e'.msg.head = P.root)

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
include hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE in
/-- The proposal anchor is supported when the receiving vote extends its actual raw
lock sources. Unlocking only moves the anchor back; the source writer remains the proposer.
The unused `hE` binder is retained to match `proposal_start_supported` exactly. The
source-vote premise is no longer needed: this is a corollary of the bounded form. -/
theorem proposal_start_supported_of_source_votes
    (hsources : ∀ r l B, r < i →
      ((∃ CV, SA.FastLockAt tr.projAC p r l B CV) ∨ SA.SlowLockAt tr.projAC p r l B) →
      cleanLabel sp a + sp.k + 2 ≤ l → l < u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B) :
    Anc (tr.HonestBlocks H) d.start
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame u))
        (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) :=
  (hp.toUpTo tr H (le_max_left a (max (tr.time i) (tr.time j)))).proposal_start_supported hc hP.1
    hR hci hcall hd hti ((le_max_left _ _).trans (le_max_right _ _)) hy hcy hes
    ((le_max_right _ _).trans (le_max_right _ _))

set_option linter.unusedSectionVars false in
include hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE in
/-- The proposal start is supported through clean raw-source vote induction. -/
theorem proposal_start_supported :
    Anc (tr.HonestBlocks H) d.start
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame u))
        (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) :=
  (hp.toUpTo tr H (le_max_left a (max (tr.time i) (tr.time j)))).proposal_start_supported hc hP.1
    hR hci hcall hd hti ((le_max_left _ _).trans (le_max_right _ _)) hy hcy hes
    ((le_max_right _ _).trans (le_max_right _ _))

end SourceVotes

/-- The finite proposal suffix above all old origins consists of viable heads. -/
theorem ResetPremisesUpTo.reset_suffix_viable {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (hDt : D ∈ ell.frame.tree)
    (hsD : ell.frame.Anc d.start D)
    (hDold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocks H) O D) :
    ∀ X, ell.frame.Anc D X → ell.frame.Anc X d.head → X ∈ ell.frame.viableHeads := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  exact proposal_suffix_viable_of_floor hPhi hPhiU (Compose.frame_of_projAC hp.run hpH hci) hd
    hDt hsD fun _ hX hDX => hp.proposal_floor_above_old hpH hR hci hcall hti hib hX
      fun x r l O ho hrt hrb => (hDold x r l O ho hrt hrb).trans hDX

/-- Above every old source, the proposal walk consists of viable heads. The reset seed makes
the suffix high; a higher floor would produce a high crossing below an old source, contradicting
its height. Together with `fc_root ⪯ start ⪯ D`, this proves viability. -/
theorem reset_suffix_viable (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (_hPQ : P.parent = some d.head.root)
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (hDt : D ∈ ℓp.frame.tree)
    (hsD : ℓp.frame.Anc d.start D) (hDold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O D) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads :=
  (hp.toUpTo tr H (le_max_left a (tr.time i))).reset_suffix_viable hP.1 hR hci hcall hd hti
    (le_max_right _ _) D hDt hsD
    (fun x r l O ho hrt _ => hDold O (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩))

/-- A finite post-drain voter root is genesis or below an earlier bounded high origin. -/
theorem ResetPremisesUpTo.reset_vote_root_source {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    ell.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b ∧
        Anc (tr.HonestBlocks H) ell.frame.fcRoot O := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hy j
  have hfr := Compose.frame_of_projAC hp.run hy hc.1
  have hF : ∀ O, Anc (tr.HonestBlocks H) (tr.state y j).fg.F O →
      Anc (tr.HonestBlocks H) ell.frame.F O := fun O h => by rw [hfr]; exact h
  rw [hfr]
  refine (fcRoot_genesis_or_below_source hr hp.honest_coherent (fun X hX => ⟨y, hy, j, hX⟩)
    (fun O => ∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b)
    (fun E hE C hET hEh hEC hlt => hp.cast_entry_below_old hy hc hes hjb hE hET hEh hEC hlt)
    (fun O ⟨_, _, _, ho, _⟩ W hW hOW => hp.high_of_anc ho hy hW hOW) fun hlow => ?_).imp
    (congrArg Block.root) fun ⟨O, ⟨v, r, l, ho, hrt, hrb⟩, hO⟩ => ⟨v, r, l, O, ho, hrt, hrb, hO⟩
  obtain ⟨v, r, l, O, ho, hrb, hlu, hrt⟩ := hp.reset_seed_before_slot hR
  have hFO := hp.low_finalized_below_origin hy j hlow ho
  have hOt := hp.high_origin_held_at_vote ho hy hc (by clear * - hes hlu; omega) (hF O hFO)
  exact ⟨O, ⟨v, r, l, ho, hrt, hrb⟩, hFO, Or.inl ⟨hOt, hp.anc_tree_of_anc hy hFO hOt⟩⟩

/-- The vote root is genesis or below an old source (hence satisfies the original disjunction).
An actual crossing attestation's origin label is strictly below the vote's label
(`row_origin_label_lt`); the low-`J` case relays the reset seed. -/
private theorem reset_vote_root_source (hp : ResetPremises tr H proposer dg g ΔF a)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = u) :
    ℓy.frame.fcRoot.root = sp.genesisRoot ∨
      (∃ O, OldSrc tr H g u O ∧ Anc (tr.HonestBlocks H) ℓy.frame.fcRoot O) := by
  rcases (hp.toUpTo tr H (le_max_left a (tr.time j))).reset_vote_root_source hR hy hcy hes
    (le_max_right _ _) with hg | ⟨v, r, l, O, ho, hrt, -, hroot⟩
  exacts [Or.inl hg, Or.inr ⟨O, oldSrc_iff.2 ⟨v, r, l, ho, hrt⟩, hroot⟩]

/-- A bound on bounded pre-slot origins bounds the actual post-drain voter root. -/
theorem ResetPremisesUpTo.reset_vote_root_below_bound {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocks H)
    (hbound : ∀ x r l B, HighOrigin tr H g x r l B → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocks H) B P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocks H) ell.frame.fcRoot P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  rcases hp.reset_vote_root_source hR hy hc hs hjb with hg | ⟨x, r, l, B, ho, ht, hrb, hroot⟩
  · obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
    exact Compose.honest_genesis_root_anc hp.run hr.coherent (hPhiU hPhi.fcRoot_mem) hg hP
  · exact hroot.trans (hbound x r l B ho ht hrb)

theorem reset_vote_fcRoot (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u)
    (_hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root) :
    ell.frame.fcRoot.root = sp.genesisRoot ∨
      (∃ O, OldSrc tr H g u O ∧ Anc (tr.HonestBlocks H) ell.frame.fcRoot O) ∨
      Anc (tr.HonestBlocks H) ell.frame.fcRoot P :=
  (reset_vote_root_source hp hR hy hc hs).imp_right Or.inl


end Consensus.Goldilocks.Healing
