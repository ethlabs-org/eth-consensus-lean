module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedC4

public section

/-! # C4 of the healed window under growing faults: no reorg of honest proposals

The growing form of `Obligations/HealedC4` and of the window-facing C4 wrappers of
`Obligations/HealedUpTo`, with each proposer honest through its own slot's `t_s + hold`:

* `proposesAt_of_honestProposalRun_at`: an honest proposal run is made operationally;
  `honestProposalRun_slot_at`, `accept_of_proposesAt_at` (the static `accept_of_proposesAt` on the
  prefix through the proposal cut), `proposer_mem_of_proposesAt_at`, `proposal_held_at`: its
  slot, its proposer's honesty at the proposal cut, the acceptance and the holding after it;
* `UpTo.operational_proposal_below_next_parent_at`: under the finite reset premises and
  Catch(2Δ), a post-drain operational proposal of slot `u` is an honest ancestor of the duty head
  of every honest proposal call at `t_{u+1}`;
* `honest_proposal_child_at`: an honest proposal is the child of the duty head of its call. -/

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **An honest proposal run is made operationally**: its proposer proposes it at some cut. -/
theorem proposesAt_of_honestProposalRun_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) :
    ∃ k, tr.ProposesAt (proposer s) k P := by
  obtain ⟨hpH, -, -, -, -, -, -, -, -, -, -, hPp, -, j, -, hacc, htj⟩ := hP
  change tr.time j = sp.ts s at htj
  have hd := hrun.time_nonneg j
  have hl := (hrun.upTo hd).toLocalRun
  have hp : proposer s ∈ H (tr.time j) := hrun.antitone (by
    rw [htj]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hacc' : (tr.upTo (tr.time j)).projAC.AcceptAt (proposer s) j P := by
    obtain ⟨ℓ, hc, hb⟩ := hacc
    rw [RunTrace.upTo_projAC]
    exact ⟨ℓ, (Trace.upTo_callAt_of_le _ le_rfl).mpr hc, hb⟩
  obtain ⟨j₀, -, ha, -⟩ := Healing.fg_accept_before hl hp hacc'
  obtain ⟨j', -, ⟨acc, hc⟩, hpos⟩ := hl.block_unforgeable _ hp j₀ P ⟨true, ha⟩ (hPp ▸ hp)
  rw [hPp] at hc
  rcases Compose.blockCall_cases hl hp hc with hg | ⟨j₁, x, rfl, -, hpr, d', pay', -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  · have hs : P.slot = sp.toParams.slotOf (tr.time (j₁ + 2)) := by rw [hB]; rfl
    have hown : (tr.upTo (tr.time j)).OwnBlockAt (proposer s) (j₁ + 2) P := ⟨⟨acc, hc⟩, hpos⟩
    exact ⟨j₁ + 2, ((RunTrace.upTo_ownBlockAt _).mp hown).2, hPp, hs ▸ hpr.2.1⟩

/-- The block of an honest proposal run of slot `s` has slot `s`. -/
theorem honestProposalRun_slot_at {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) : P.slot = s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hs, -⟩ := hP
  exact hs

/-- **A proposal of a node honest at its proposal cut is accepted there**, with the block in its
tree after the cut (the static `accept_of_proposesAt` on the prefix through the cut's time). -/
theorem accept_of_proposesAt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hp : p ∈ H (tr.time k)) (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
  have hd := hrun.time_nonneg k
  have hb : ∀ m < k + 1, tr.time m ≤ tr.time k := fun _ hm => hrun.time_mono (by omega)
  have hW' : (tr.upTo (tr.time k)).ProposesAt p k W :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hW.1⟩, hW.2.1, hW.2.2⟩
  obtain ⟨ha, hmem, hpost⟩ := Healing.accept_of_proposesAt (hrun.upTo hd)
    (hnc.upTo (tr.time k)) hp hW'
  rw [Trace.upTo_state _ _ hb] at hmem hpost
  exact ⟨((RunTrace.upTo_acceptAt _).mp ha).2, hmem, hpost⟩

/-- The proposer of an honest anchor is honest at its proposal cut. -/
theorem proposer_mem_of_proposesAt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) {k : Nat}
    (hk : tr.ProposesAt (proposer s) k P) : proposer s ∈ H (tr.time k) := by
  have hsl := honestProposalRun_slot_at hP
  have ht : tr.time k = sp.ts s := by
    rw [hk.2.2, ← hsl, sp.slotTime_eq]; rfl
  refine hrun.antitone ?_ hP.1
  rw [ht]
  exact le_add_of_nonneg_right sp.toParams.hΔ.le

/-- **An honest proposal is held by its proposer**: proposed at a cut `k` where the proposer is
honest, and held after it, at cut `k + 1`, which is at the same time. -/
theorem proposal_held_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) :
    ∃ k, tr.ProposesAt (proposer s) k P ∧ proposer s ∈ H (tr.time k) ∧
      tr.time (k + 1) = tr.time k ∧ P ∈ (tr.state (proposer s) (k + 1)).fg.tree := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun_at hrun hP
  have hm := proposer_mem_of_proposesAt_at hrun hP hk
  obtain ⟨ha, hP', -⟩ := accept_of_proposesAt_at hrun hnc hm hk
  obtain ⟨-, -, -, ht⟩ := accept_next_at hrun hm ha
  exact ⟨k, hk, hm, ht, hP'⟩

/-- **No reorg one slot on, finite horizon**, under growing faults. A post-drain operational
proposal `P` of slot `u`, by its proposer honest through `t_u + hold`, is an honest ancestor of the
duty head of every proposal call at `t_{u+1}` of a node honest at that call. -/
theorem UpTo.operational_proposal_below_next_parent_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + Regimes.Growing.hold sp)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (u + 1 : Nat)) :
    Anc (tr.HonestBlocksAt H) P d.head := by
  sorry

/-- The honest proposal `P'` of `s'` is the child of the duty head of its proposal call. -/
theorem honest_proposal_child_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {s' : Nat} {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP' : Healing.Growing.HonestProposalRun tr H proposer s' P')
    (hPd : ∀ {i ell} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay},
      tr.projAC.CallAt (proposer s') i ell → ell.call = .proposal →
      (SA.acProposal sp (tr.projAC.state (proposer s') i) ell.frame (tr.time i)).2 =
        some (d, pay) → tr.time i = sp.ts s' → Anc (tr.HonestBlocksAt H) P d.head) :
    Anc (tr.HonestBlocksAt H) P P' := by
  have hBU : P' ∈ tr.HonestBlocksAt H := by
    obtain ⟨k, -, hm, ht, hXm⟩ := proposal_held_at hp.run hp.noColl hP'
    exact ⟨_, k + 1, tr.time k, hp.run.time_nonneg k,
      fun _ hq => hp.run.time_mono (by omega), hm, hXm⟩
  obtain ⟨hy, i, ell, d, pay, hci, hcall, hd, hti, hpar, -⟩ := hP'
  change tr.time i = sp.ts s' at hti
  have h0 := hp.run.time_nonneg i
  have hyi : proposer s' ∈ H (tr.time i) := hp.run.antitone (by
    rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hy
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hp.run.upTo h0) (hp.noColl.upTo _)).localRun
  have hci' : (tr.upTo (tr.time i)).projAC.CallAt (proposer s') i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hci
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hyi hci'
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ell.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hQU : d.head ∈ tr.HonestBlocksAt H :=
    RunTrace.honestBlocks_upTo_subset hp.run.time_mono h0 (hPhiU hQt)
  exact (hPd hci hcall hd hti).trans (.single ⟨hQU, hBU, hpar⟩)

end Consensus.Goldilocks.Obligations.Growing

end
