module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.PivotAnchor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteParent
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalPasses
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.PivotSourceVotes

public section

/-! # Viable proposal suffixes under growing faults -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A held block above every pre-slot high origin reaches the proposal reader's floor. -/
theorem proposal_floor_above_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} (hci : tr.projAC.CallAt p i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state p i).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O B) :
    (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h := by
  have ht := hp.run.time_nonneg i
  have hj : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hp.run.time_mono hq.le
  have hreach := fg_reachable_at hp.run ht hj hpH
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot_at hR
  have hBh := Outcome.high_of_anc_at hp.run hp.noColl ho₀ ht hj hpH hB
    (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb)
  have hnc := Outcome.no_high_contest_at hp hpH hib
  by_contra hle
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state p i).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state p i).fg.headHeightFloor = (tr.state p i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ := Healing.entry_at_height hreach hC
    (h := (tr.state p i).fg.hmax - 1) (by omega) (by omega)
  have hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults (tr.time i) ht hib
    have hn := sp.toParams.hn
    change 3 * (H (tr.time i))ᶜ.ncard ≤ sp.toParams.n - 1 at h3
    change (H (tr.time i))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  obtain ⟨_, _, _, _, v, _, d, hdj, _, _, r, hrd, l, O, ho, hEO⟩ :=
    Outcome.left_entry_origin_at (g := g) hp.run hp.noColl ht hj hpH hq hE hET
      (by omega) hEC (by omega)
  have hlu := hp.origin_label_lt_at_proposal_at hpH hci hcall hti hib (by omega : r < i) ho
  obtain ⟨CV, ellw, D, _, hf, _⟩ := ho.2.2.1
  have hrt := Outcome.fastLock_time_lt_at hp.run hf hlu (by
    rw [← hti]
    have := hp.run.time_mono (show r ≤ i by omega)
    have := sp.toParams.hΔ
    linarith)
  have hEB := hEO.trans (hBold v r l O ho hrt
    ((hp.run.time_mono (show r ≤ i by omega)).trans hib))
  have hh := Healing.h_le_of_store_anc hreach
    (store_anc_of_honest_anc_at hp.run hp.noColl ht hj hpH hEB hB)
  omega

/-- The proposal suffix above all pre-slot high origins consists of viable heads. -/
theorem reset_suffix_viable_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (hDt : D ∈ ell.frame.tree)
    (hsD : ell.frame.Anc d.start D)
    (hDold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O D) :
    ∀ X, ell.frame.Anc D X → ell.frame.Anc X d.head → X ∈ ell.frame.viableHeads :=
  proposal_suffix_viable_of_floor (Outcome.frame_realized hp.run hpH hci)
    (Outcome.frame_tree_subset hp.run hpH hci) (Outcome.frame_of_call hp.run hpH hci) hd hDt hsD
    fun _ hX hDX => hp.proposal_floor_above_old_at hpH hR hci hcall hti hib hX
      fun x r l O ho hrt hrb => (hDold x r l O ho hrt hrb).trans hDX

/-- Pivot construction with the independently supplied proposal-start support. -/
theorem reset_pivot_of_start_supported_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts u + Regimes.Growing.hold sp))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root)
    (hstart : ∀ y j elly e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j elly e →
      e.msg.slot = u → tr.time j ≤ b →
      Anc (tr.HonestBlocksAt H) d.start
        (SA.getHead sp e.readPoint elly.frame (tr.time j)
          (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
          (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1))) :
    ∃ D, ellp.frame.Anc d.start D ∧ ellp.frame.Anc D d.head ∧
      (∀ X, ellp.frame.Anc D X → ellp.frame.Anc X d.head → X ∈ ellp.frame.viableHeads) ∧
      ∀ y j elly e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j elly e → e.msg.slot = u →
        tr.time j ≤ b →
        (∀ x j' e', x ∈ H (tr.time j') → j' < j → SA.VoteAt tr.projAC x j' e' →
          e'.msg.slot = u → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ellp.frame.Anc D X ∧ ellp.frame.Anc X d.head)) ∧
          elly.frame.Anc (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) X ∧
          elly.frame.Anc X (SA.getHead sp e.readPoint elly.frame (tr.time j)
            (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
            (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  have hpI : p ∈ H (tr.time i) := hp.run.antitone
    (by rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hr :=
    (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hPhi := Outcome.frame_realized hp.run hpI hci
  have hPhiU := Outcome.frame_tree_subset hp.run hpI hci
  have hkt : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hactual.2.2
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
  refine (proposal_pivot_of_supports (tr := tr) (u := u) hr.coherent hPhi hPhiU hd hPQ
    {O | ∃ x r l, HighOrigin tr H g x r l O ∧ tr.time r < sp.ts u}
    (fun y j elly e => y ∈ H (tr.time j) ∧ SA.CastAt tr.projAC y j elly e ∧ e.msg.slot = u ∧
      tr.time j ≤ b ∧ ∀ x j' e', x ∈ H (tr.time j') → j' < j → SA.VoteAt tr.projAC x j' e' →
        e'.msg.slot = u → e'.msg.head = P.root)
    (hp.reset_proposal_passes_at hc hpI hR hci hcall hd hti hib)
    (fun D hDt hsD hDold => hp.reset_suffix_viable_at hpI hR hci hcall hd hti hib D hDt hsD
      fun x r l O ho hrt _ => hDold O ⟨x, r, l, ho, hrt⟩)
    (fun _ _ _ _ h => ⟨Outcome.frame_realized hp.run h.1 h.2.1.1,
      Outcome.frame_tree_subset hp.run h.1 h.2.1.1⟩)
    (fun _ j _ _ h => h.2.2.1 ▸ (SA.castAt_spec (hr.upTo (hp.run.time_nonneg j)) h.1
      (SA.upTo_castAt.mpr ⟨le_rfl, h.2.1⟩)).2.2.2)
    (fun y j elly e h => hstart y j elly e h.1 h.2.1 h.2.2.1 h.2.2.2.1)
    (fun O ⟨x, r, l, ho, hrt⟩ y j elly e ⟨hy, hcy, hes, hjb, _⟩ => by
      have hri : r < i :=
        lt_of_not_ge fun h => (hp.run.time_mono h).not_gt (hrt.trans_eq hti.symm)
      have hlu := hp.origin_label_lt_at_proposal_at hpI hci hcall hti hib hri ho
      exact hp.high_origin_votes_before_at j hjb x r l O ho
        ((hp.run.time_mono hri.le).trans hib) y elly e hy hcy (by omega))
    (fun D hDU hQU hDQ hDold y j elly e ⟨hy, hcy, hes, hjb, hE⟩ =>
      hp.reset_vote_anchor_at hPU hR hPQ hQU hDQ hDU
        (fun x r l O ho hrt _ => hDold O ⟨x, r, l, ho, hrt⟩) hy hcy hes hjb hE
        fun l hl hne hlive L hL hLr => ProposalImpl.vote_old_live_lock_below_parent_at hp hc
          hpI hR hci hcall hd hti hib hy hcy hes hjb hl hne hlive hL hLr)).imp
    fun D ⟨hsD, hDQ, hV, h⟩ =>
      ⟨hsD, hDQ, hV, fun y j elly e hy hcy hes hjb hE => h y j elly e ⟨hy, hcy, hes, hjb, hE⟩⟩

open Regimes.Growing (hold)

/-- The deepest old-source pivot is viable and supported at every honest cast. -/
theorem reset_pivot_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts u + hold sp))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root) :
    ∃ D, ellp.frame.Anc d.start D ∧ ellp.frame.Anc D d.head ∧
      (∀ X, ellp.frame.Anc D X → ellp.frame.Anc X d.head → X ∈ ellp.frame.viableHeads) ∧
      ∀ y j elly e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j elly e → e.msg.slot = u →
        tr.time j ≤ b →
        (∀ x j' e', x ∈ H (tr.time j') → j' < j → SA.VoteAt tr.projAC x j' e' →
          e'.msg.slot = u → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ellp.frame.Anc D X ∧ ellp.frame.Anc X d.head)) ∧
          elly.frame.Anc (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) X ∧
          elly.frame.Anc X (SA.getHead sp e.readPoint elly.frame (tr.time j)
            (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
            (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  refine hp.reset_pivot_of_start_supported_at hc hpH hactual hPs hR hci hcall hd hti hib hPQ ?_
  intro y j elly e hy hcy hes hjb
  have hpI : p ∈ H (tr.time i) := hp.run.antitone
    (by rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  exact hp.proposal_start_supported_at hc hpI hR hci hcall hd hti hib hy hcy hes hjb

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
