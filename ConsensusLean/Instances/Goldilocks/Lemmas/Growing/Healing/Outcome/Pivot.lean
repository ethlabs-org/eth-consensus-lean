module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.RootFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.PivotAnchor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteParent
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalPasses
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.PivotSourceVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalMembers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.MemberTiming

public section

/-! # Viable proposal suffixes under growing faults -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {fgHold : Time}

/-- A held block above every pre-slot high origin is viable at the proposal reader. -/
theorem proposal_viable_above_old_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK fgHold)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp)} (hci : tr.projAC.CallAt p i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state p i).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O B)
    (hBcov : HighSourceCover tr H g a b → ∀ C s, HealedMemberBefore tr H g a b C s i → s < u →
      Anc (tr.HonestBlocksAt H) C B) :
    (tr.state p i).fg.IsViable B := by
  have ht := hp.run.time_nonneg i
  have hj : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hp.run.time_mono hq.le
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
  refine isViable_of_entries_below (fg_reachable_at hp.run ht hj hpH) hB
    (Outcome.high_of_anc_at hp.run hp.noColl ho₀ ht hj hpH hB (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb))
    fun E hE C hET hEh hEC hlt => ?_
  refine store_anc_of_honest_anc_at hp.run hp.noColl ht hj hpH ?_ hB
  rcases hp.proposal_entry_below_old_or_healed_at hpH hci hcall hti hib hE hET hEh hEC hlt with
    ⟨O, ⟨v, r, l, ho, hrt, hrb⟩, hEO⟩ | ⟨hc, M, s, hM, hsu, hEM⟩
  · exact hEO.trans (hBold v r l O ho hrt hrb)
  · exact hEM.trans (hBcov hc M s hM hsu)

/-- The proposal suffix above all pre-slot high origins consists of viable heads. -/
theorem reset_suffix_viable_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK fgHold)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (D : AC.Blk sp.n (List (FG.Att sp.n))) (hDt : D ∈ ell.frame.tree)
    (hsD : ell.frame.Anc d.start D)
    (hDold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O D)
    (hDcov : HighSourceCover tr H g a b → ∀ C s, HealedMemberBefore tr H g a b C s i → s < u →
      Anc (tr.HonestBlocksAt H) C D) :
    ∀ X, ell.frame.Anc D X → ell.frame.Anc X d.head → X ∈ ell.frame.viableHeads :=
  proposal_suffix_viable_of_floor (Outcome.frame_realized hp.run hpH hci)
    (Outcome.frame_tree_subset hp.run hpH hci) (Outcome.frame_of_call hp.run hpH hci) hd hDt hsD
    fun _ hX hDX => hp.proposal_viable_above_old_at hpH hR hci hcall hti hib hX
      (fun x r l O ho hrt hrb => (hDold x r l O ho hrt hrb).trans hDX)
      fun hc C s hM hs => (hDcov hc C s hM hs).trans hDX

/-- Pivot construction with the independently supplied proposal-start support. -/
theorem reset_pivot_of_start_supported_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK fgHold)
    {p : Fin sp.n} {k u : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts u + Regimes.Growing.hold sp))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root)
    (hstart : ∀ y j elly e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j elly e →
      e.msg.slot = u → tr.time j ≤ b →
      Anc (tr.HonestBlocksAt H) d.start
        (AC.getHead sp e.readPoint elly.frame (tr.time j)
          (elly.frame.viableTree (AC.voteDomain sp e.readPoint elly.frame u))
          (AC.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1))) :
    ∃ D, ellp.frame.Anc d.start D ∧ ellp.frame.Anc D d.head ∧
      (∀ X, ellp.frame.Anc D X → ellp.frame.Anc X d.head → X ∈ ellp.frame.viableHeads) ∧
      ∀ y j elly e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j elly e → e.msg.slot = u →
        tr.time j ≤ b →
        (∀ x j' e', x ∈ H (tr.time j') → j' < j → AC.VoteAt tr.projAC x j' e' →
          e'.msg.slot = u → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ellp.frame.Anc D X ∧ ellp.frame.Anc X d.head)) ∧
          elly.frame.Anc (AC.getAnchor sp e.readPoint elly.frame (tr.time j)) X ∧
          elly.frame.Anc X (AC.getHead sp e.readPoint elly.frame (tr.time j)
            (elly.frame.viableTree (AC.voteDomain sp e.readPoint elly.frame u))
            (AC.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  have hpI : p ∈ H (tr.time i) := hp.run.antitone
    (by rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hr :=
    (Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hPhi := Outcome.frame_realized hp.run hpI hci
  have hPhiU := Outcome.frame_tree_subset hp.run hpI hci
  have hkt : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hactual.2.2
  have hpK : p ∈ H (tr.time k) := hp.run.antitone
    (by rw [hkt]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hactual' : (tr.upTo (tr.time k)).ProposesAt p k P := by
    rcases hactual with ⟨⟨⟨acc, hc⟩, hpos⟩, hprop, ht⟩
    exact ⟨⟨⟨acc, (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩⟩, hpos⟩, hprop, ht⟩
  have hret := hp.run.upTo (hp.run.time_nonneg k)
  have hacc := Compose.proposal_accepted hret (hp.noColl.upTo _) hpK hactual'
  have hPU : P ∈ tr.HonestBlocksAt H := by
    apply RunTrace.honestBlocks_upTo_subset hp.run.time_mono (hp.run.time_nonneg k)
    refine ⟨p, hpK, k + 1, ?_⟩
    rw [(tr.upTo (tr.time k)).state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hret.toLocalRun hpK _)).1 P _
        (hret.toLocalRun.cutLaw p hpK _ _ hacc).2.1]
    exact Set.mem_insert _ _
  have hjupper : ∀ {y j elly e}, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j elly e →
      e.msg.slot = u → tr.time j ≤ sp.ts u + sp.Δ := fun {y j elly e} hy hcy hes => by
    have hrj := hr.upTo (hp.run.time_nonneg j)
    have hcy' := AC.upTo_castAt.mpr (And.intro le_rfl hcy)
    have hsl := (AC.castAt_specU hrj.toU hy hcy').2.1
    change e.msg.slot = sp.slot (tr.time j) at hsl
    have ht := AC.vote_time_leU hrj.toU hy ⟨elly, hcy'⟩
    change tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ at ht
    simpa only [← hsl, hes] using ht
  refine (proposal_pivot_of_supports (tr := tr) (u := u) hr.coherent hPhi hPhiU hd hPQ
    {O | (∃ x r l, HighOrigin tr H g x r l O ∧ tr.time r < sp.ts u) ∨
      (HighSourceCover tr H g a b ∧ ∃ s, HealedMemberBefore tr H g a b O s i ∧ s < u)}
    (fun y j elly e => y ∈ H (tr.time j) ∧ AC.CastAt tr.projAC y j elly e ∧ e.msg.slot = u ∧
      tr.time j ≤ b ∧ ∀ x j' e', x ∈ H (tr.time j') → j' < j → AC.VoteAt tr.projAC x j' e' →
        e'.msg.slot = u → e'.msg.head = P.root)
    (fun O hO => hO.elim
      (fun ⟨x, r, l, ho, hrt⟩ => hp.reset_proposal_passes_at hpI hR hci hcall hd hti hib O
        ⟨x, r, l, ho, hrt⟩)
      fun ⟨hc, s, hM, hs⟩ => hp.reset_proposal_passes_member_before_at hc hpI hR hci hcall hd
        hti hib hM hs)
    (fun D hDt hsD hDold => hp.reset_suffix_viable_at hpI hR hci hcall hd hti hib D hDt hsD
      (fun x r l O ho hrt _ => hDold O (Or.inl ⟨x, r, l, ho, hrt⟩))
      fun hc C s hM hs => hDold C (Or.inr ⟨hc, s, hM, hs⟩))
    (fun _ _ _ _ h => ⟨Outcome.frame_realized hp.run h.1 h.2.1.1,
      Outcome.frame_tree_subset hp.run h.1 h.2.1.1⟩)
    (fun _ j _ _ h => h.2.2.1 ▸ (AC.castAt_specU (hr.upTo (hp.run.time_nonneg j)).toU h.1
      (AC.upTo_castAt.mpr ⟨le_rfl, h.2.1⟩)).2.2.2)
    (fun y j elly e h => hstart y j elly e h.1 h.2.1 h.2.2.1 h.2.2.2.1)
    (fun O hO y j elly e ⟨hy, hcy, hes, hjb, _⟩ => by
      rcases hO with ⟨x, r, l, ho, hrt⟩ | ⟨hc, s, hM, hs⟩
      swap
      · exact hc.s2 O s hM.healedOrigin y j e
          (Compose.Growing.hVoteAt_iff.2 ⟨hy, elly, hcy⟩) hjb (by omega)
      have hri : r < i :=
        lt_of_not_ge fun h => (hp.run.time_mono h).not_gt (hrt.trans_eq hti.symm)
      have hlu := ProposalSources.origin_label_lt_at_proposal_at hp hpI hci hcall hti hib hri ho
      exact hp.high_origin_votes_before_at j hjb x r l O ho
        ((hp.run.time_mono hri.le).trans hib) y elly e hy hcy (by omega))
    (fun D hDU hQU hDQ hDold y j elly e ⟨hy, hcy, hes, hjb, hE⟩ =>
      hp.reset_vote_anchor_at hPU hR hPQ hQU hDQ hDU
        (fun x r l O ho hrt _ => hDold O (Or.inl ⟨x, r, l, ho, hrt⟩))
        (fun hc C s hM hs => hDold C (Or.inr ⟨hc, s,
          hp.member_before_proposal_of_cast_deadline_at hti (hjupper hy hcy hes) hM hs, hs⟩))
        hy hcy hes hjb hE
        fun l hl hne hlive L hL hLr => ProposalImpl.vote_old_live_lock_below_parent_at hp
          hpI hR hci hcall hd hti hib hy hcy hes hjb hl hne hlive hL hLr)).imp
    fun D ⟨hsD, hDQ, hV, h⟩ =>
      ⟨hsD, hDQ, hV, fun y j elly e hy hcy hes hjb hE => h y j elly e ⟨hy, hcy, hes, hjb, hE⟩⟩

open Regimes.Growing (hold)

/-- The deepest old-source pivot is viable and supported at every honest cast. -/
theorem reset_pivot_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK fgHold)
    {p : Fin sp.n} {k u : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts u + hold sp))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root) :
    ∃ D, ellp.frame.Anc d.start D ∧ ellp.frame.Anc D d.head ∧
      (∀ X, ellp.frame.Anc D X → ellp.frame.Anc X d.head → X ∈ ellp.frame.viableHeads) ∧
      ∀ y j elly e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j elly e → e.msg.slot = u →
        tr.time j ≤ b →
        (∀ x j' e', x ∈ H (tr.time j') → j' < j → AC.VoteAt tr.projAC x j' e' →
          e'.msg.slot = u → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ellp.frame.Anc D X ∧ ellp.frame.Anc X d.head)) ∧
          elly.frame.Anc (AC.getAnchor sp e.readPoint elly.frame (tr.time j)) X ∧
          elly.frame.Anc X (AC.getHead sp e.readPoint elly.frame (tr.time j)
            (elly.frame.viableTree (AC.voteDomain sp e.readPoint elly.frame u))
            (AC.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  refine hp.reset_pivot_of_start_supported_at hpH hactual hPs hR hci hcall hd hti hib hPQ ?_
  intro y j elly e hy hcy hes hjb
  have hpI : p ∈ H (tr.time i) := hp.run.antitone
    (by rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  exact hp.proposal_start_supported_at hpI hR hci hcall hd hti hib hy hcy hes hjb

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
