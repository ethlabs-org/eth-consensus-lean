module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
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
    ∀ X, ell.frame.Anc D X → ell.frame.Anc X d.head → X ∈ ell.frame.viableHeads := by
  intro X hDX _
  have hPhi := Outcome.frame_realized hp.run hpH hci
  have hPhiU := Outcome.frame_tree_subset hp.run hpH hci
  have hXt : X ∈ ell.frame.tree := Compose.mem_of_anc_left hDX hDt
  have hDXU := hDX.mono hPhiU
  obtain ⟨A, _, hstart, _⟩ := Compose.acProposal_walk hd
  have hfX : ell.frame.Anc ell.frame.fcRoot X := by
    rw [hstart] at hsD
    exact ((SA.fcRoot_anc_getAnchor hPhi A (tr.time i)).trans hsD).trans hDX
  rw [Outcome.frame_of_call hp.run hpH hci] at hXt hfX ⊢
  obtain ⟨hXs, hFX⟩ := hXt
  exact ⟨hXs, hFX, hfX.mono (fun _ h => h.1),
    hp.proposal_floor_above_old_at hpH hR hci hcall hti hib hXs
      (fun x r l O ho hrt hrb => (hDold x r l O ho hrt hrb).trans hDXU)⟩

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
  have hU := hr.coherent
  have hPhi := Outcome.frame_realized hp.run hpI hci
  have hPhiU := Outcome.frame_tree_subset hp.run hpI hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := Compose.mem_of_anc_left hsQ hst
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
  have hpass := hp.reset_proposal_passes_at hc hpI hR hci hcall hd hti hib
  let old : Set (SA.Blk sp.n (List (FG.Att sp.n))) :=
    {O | ∃ x r l, HighOrigin tr H g x r l O ∧ tr.time r < sp.ts u}
  obtain ⟨D, hD⟩ := SA.exists_deepest hPhi (S := {X | X ∈ ellp.frame.tree ∧
      ellp.frame.Anc d.start X ∧ ellp.frame.Anc X d.head ∧ (X = d.start ∨ X ∈ old)})
    (fun X hX => hX.1) ⟨d.start, hst, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hPhi (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hPhi.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O ∈ old, Anc (tr.HonestBlocksAt H) O D := by
    intro O hO
    have hOQ := hpass O hO
    rcases Anc.total hU hOQ (Anc.mono hPhiU hsQ) with h | h
    · exact h.trans (Anc.mono hPhiU hsD)
    have hOt := Compose.mem_between hU hPhi hPhiU hst hQt h hOQ
    exact Anc.mono hPhiU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hPhi hPhiU hst h hOt,
      SA.anc_tree_of_anc_U hU hPhi hPhiU hOt hOQ hQt, Or.inr hO⟩)
  have hDold' : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O D :=
    fun x r l O ho hrt _ => hDold O ⟨x, r, l, ho, hrt⟩
  refine ⟨D, hsD, hDQ,
    hp.reset_suffix_viable_at hpI hR hci hcall hd hti hib D hDt hsD hDold', ?_⟩
  intro y j elly e hy hcy hes hjb hE
  have hPsi := Outcome.frame_realized hp.run hy hcy.1
  have hPsiU := Outcome.frame_tree_subset hp.run hy hcy.1
  have hrj := hr.upTo (hp.run.time_nonneg j)
  have hcj := SA.upTo_castAt.mpr (And.intro le_rfl hcy)
  have hhead := (SA.castAt_spec hrj hy hcj).2.2.2
  rw [hes] at hhead
  have hat := Compose.anchor_tree hPsi e.readPoint (tr.time j)
  have hah : elly.frame.Anc (SA.getAnchor sp e.readPoint elly.frame (tr.time j))
      (SA.getHead sp e.readPoint elly.frame (tr.time j)
        (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
        (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) :=
    SA.anc_ghost (fun B hB => SA.voteDomain_subset_tree hB.1) _ hat
  have hht := Compose.mem_of_anc_left hah hat
  have hDh : Anc (tr.HonestBlocksAt H) D (SA.getHead sp e.readPoint elly.frame (tr.time j)
      (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
      (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
    rcases hDk with rfl | ⟨x, r, l, ho, hrt⟩
    · exact hstart y j elly e hy hcy hes hjb
    have hri : r < i := by
      by_contra hn
      have ht := hp.run.time_mono (Nat.le_of_not_gt hn)
      rw [hti] at ht
      exact (not_lt_of_ge ht) hrt
    have hlu := hp.origin_label_lt_at_proposal_at hpI hci hcall hti hib hri ho
    obtain ⟨Hd, hHd, hHdr, hDHd⟩ := hp.high_origin_votes_before_at j hjb x r l D ho
      ((hp.run.time_mono hri.le).trans hib) y elly e hy hcy (by omega)
    rwa [hU.1 hHd (hPsiU hht) (hHdr.trans hhead)] at hDHd
  rcases hp.reset_vote_anchor_at hPU hR hPQ (hPhiU hQt) (Anc.mono hPhiU hDQ) (hPhiU hDt)
      hDold' hy hcy hes hjb hE (fun l hl hne hlive L hL hLr =>
        ProposalImpl.vote_old_live_lock_below_parent_at hp hc hpI hR hci hcall hd hti hib
          hy hcy hes hjb hl hne hlive hL hLr) with haD | ⟨hDa, haP⟩
  · have hDt' := Compose.mem_between hU hPsi hPsiU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hPsi hPsiU hat haD hDt',
      SA.anc_tree_of_anc_U hU hPsi hPsiU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint elly.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := Compose.anc_parent hU haP haPe hPQ (hPhiU hQt)
  have hat' := Compose.mem_between hU hPhi hPhiU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hPhi hPhiU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hPhi hPhiU hat' haQ hQt⟩, .refl, hah⟩

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
