module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RowSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RawReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Domain
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRowSources
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The proposal domain of a clean source, under growing faults

The growing form of `Healing.ResetPremisesUpTo.clean_source_proposal_domain_before`. The source's
writer is honest at its write, the proposer at its call. The source block is held by the writer;
the held-target domain (`held_target_proposal_domain_before_at`) needs it held by the proposer
when the proposer's finalized block is below it (`raw_writer_held_at_slot_start_at`), compatible
with a reset seed written before the proposal and with every high origin written before the call
(`protected_source_compatible_high_origin_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A clean protected source, written by a node honest at its write, is below the frame root of
every later proposal call of a node honest at it, or viable in its frame. -/
theorem clean_source_proposal_domain_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x p : Fin sp.n} {r s i u : Nat}
    (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s < u) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hm := hp.run.time_mono
  have hxU : (tr.state x r).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, r, tr.time r, hp.run.time_nonneg r, fun _ hq => hm hq.le, hx, h⟩
  have evidence : ∃ C CV, (SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV) ∧
      Anc (tr.HonestBlocksAt H) B C ∧ B ∈ (tr.state x r).fg.tree := by
    rcases hsource with ⟨CV, hf⟩ | hsl
    · refine ⟨B, CV, Or.inr hf, .refl, ?_⟩
      rcases hf with ⟨ellX, C, hupd, _, hdeep, _⟩ | ⟨ellX, A, hpt, _, hsel, _⟩
      · exact (frame_tree_subset_at hp.run hp.noColl hx hupd.1).2 (SA.deepest_mem hdeep).1.1.1
      · unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact (frame_tree_subset_at hp.run hp.noColl hx hpt.1).2 (SA.deepest_mem hsel).1.1
    · obtain ⟨ellX, C, hupd, hconf, hdeep⟩ := hsl
      have hB := (SA.deepest_mem hdeep).1.1
      have hsub := (frame_tree_subset_at hp.run hp.noColl hx hupd.1).2
      exact ⟨C, _, Or.inl ⟨ellX, hupd, hconf, rfl⟩, hB.2.2.mono (hsub.trans hxU), hsub hB.1⟩
  obtain ⟨C, CV, hw, hBC, hBx⟩ := evidence
  have hcut := hp.clean_window_timing_at hs s (by have := sp.two_le_k; clear * - this; omega)
  have htiming : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have hz := Healing.lt_cutZ sp g
    have := sp.toParams.hΔ
    linarith only [hcut, hz, this]
  obtain ⟨v, q, m, S, hS, hqa, -⟩ := hp.reset_seed_at
  have hqt : tr.time q < sp.ts u := by
    have hau : sp.slot a < u := by
      rw [drainTime_eq] at hR
      have := (SA.ts_le_iff sp).mp hR
      clear * - this; omega
    by_contra h
    have ha0 : 0 ≤ a := (hp.run.time_nonneg q).trans hqa
    have := (SA.ts_le_iff_le_slot sp ha0 u).mp ((not_lt.mp h).trans hqa)
    clear * - this hau; omega
  refine ProposalImpl.held_target_proposal_domain_before_at hp hx hpH hBx hci hcall hd hti hib
    ?_ ?_ ?_
  · exact ProposalImpl.raw_writer_held_at_slot_start_at hp hc hx hpH hw hBC htiming hsu hci hti hib
  · exact ⟨v, q, m, S, hS, hqt,
      ProposalImpl.protected_source_compatible_high_origin_at hp hc hx hsource hs hrb hS
        (hqa.trans hp.reset_le)⟩
  · intro v q m O hqi ho
    exact ProposalImpl.protected_source_compatible_high_origin_at hp hc hx hsource hs hrb ho
      ((hm hqi.le).trans hib)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
