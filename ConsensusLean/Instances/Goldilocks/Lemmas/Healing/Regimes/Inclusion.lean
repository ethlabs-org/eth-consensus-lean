module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks milestone Regimes: R.2 run facts under `Sleepy`

Two facts of the run for the sleepy rows: a proposer ready at its slot start proposes
(`ready_proposer_proposes`: its tick's `ac_proposal` returns a proposal since it is joined, and
C0.3 accepts the own block); the point after all events at `t` is between two events of every
node (`cutAfter_boundary`).

The file is in the Healing layer for the tick facts of `Healing/Projection/Run`. -/

namespace Consensus.Goldilocks.Regimes

open AC (ACParams ReplayOrder Payload)
open Compose

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-! ## Open steps -/

/-- **A proposer ready at its slot start proposes** (node-level: its tick at `t_s` runs
the proposal step, `ac_proposal` returns a proposal since it is joined, and C0.3 accepts the own
block). -/
theorem ready_proposer_proposes {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {s : Nat} (hs : 0 < s) (hready : ReadyAt tr H (catchUp sp) (proposer s) (sp.ts s)) :
    ∃ k P, tr.ProposesAt (proposer s) k P ∧ tr.time k = sp.ts s := by
  have hΔ := sp.toParams.hΔ
  set p := proposer s
  have hp := hready.1
  have ht0 : 0 ≤ sp.ts s := by simp only [ACParams.ts]; positivity
  have hslot : sp.toParams.slotOf (sp.ts s) = s :=
    AC.slot_of_mem sp s le_rfl (by simp only [ACParams.ts]; push_cast; linarith)
  have hpub : sp.toParams.IsPublic (sp.ts s) := ⟨4 * s, by simp only [ACParams.ts]; ring⟩
  have hc : (8 : Time) * sp.Δ ≤ catchUp sp + 1 := by simp only [catchUp]; linarith
  have hJ := ready_implies_joined_of hrun hp ht0 hc hready.2
  obtain ⟨j, x, fgDue, hg⟩ := hrun.tick_of_awake p hp _ ht0 hpub hJ.1
  have hP : Node.Proposes proposer p (sp.ts s) :=
    ⟨by rw [hslot]; exact hs, by rw [hslot, sp.slotTime_eq]; simp only [ACParams.ts],
      by rw [hslot]⟩
  obtain ⟨hc₀, ht₀⟩ := Healing.tick_first_cut hg
  have hj : AC.joined sp (tr.state p j).ac (sp.ts s) :=
    ((joined_projection_from hrun hp _).2.1 j ⟨_, hc₀⟩
      (fun ⟨ℓ, hc', hr⟩ => by
        have := Option.some.inj (hc₀.2.symm.trans hc'.2)
        simp only [Node.acCall, Cut.ac.injEq] at this
        rw [← this] at hr
        cases hr) ht₀).1 hJ.2
  -- `ac_proposal` after the tick's `ac_on_tick` returns a proposal: the tick keeps `restart_time`
  have hj' : AC.joined sp (Node.tickStep proposer dg p (tr.state p j) (sp.ts s) x .acTick).1.ac
      (sp.ts s) := by
    change AC.joined sp ((goldilocksNode sp ro).step p (tr.state p j).ac
      (Node.frame (tr.state p j)) (sp.ts s) .tick).1 (sp.ts s)
    unfold AC.joined at hj ⊢
    rw [AC.step_restartTime p _ _ _ .tick (by simp)]
    exact hj
  obtain ⟨d, pay, hr⟩ : ∃ d pay,
      (Node.acProposal (Node.tickStep proposer dg p (tr.state p j) (sp.ts s) x .acTick).1
        (sp.ts s)).2.2 = some (d, pay) := by
    cases hpr : (Node.acProposal (Node.tickStep proposer dg p (tr.state p j) (sp.ts s) x .acTick).1
        (sp.ts s)).2.2 with
    | none =>
      exfalso
      change (AC.acProposal sp _ _ (sp.ts s)).2 = none at hpr
      unfold AC.acProposal at hpr
      simp [hj'] at hpr
    | some dp => exact ⟨dp.1, dp.2, rfl⟩
  obtain ⟨hacc, ht₂⟩ := Healing.own_block_accepted hrun.toLocalRun
    (requirements_from sp ro (hrun.vstart p)) hrun.genesis_root_ok hnc hp hg hP hr
  refine ⟨j + 2, _, ⟨⟨⟨true, hacc⟩, ?_⟩, rfl, ?_⟩, ht₂⟩
  · -- the own block is the third cut of the tick, so not the first of a group
    have hlen : 2 <
        (Node.exec proposer dg p (tr.state p j) (sp.ts s) (.tick x fgDue)).2.length := by
      have h1 : (Node.tickStep proposer dg p (tr.state p j) (sp.ts s) x .acTick).2.length = 1 := rfl
      change 2 < (Node.onTick proposer dg p (tr.state p j) (sp.ts s) x fgDue).2.length
      rw [Healing.onTick_eq, Healing.proposal_cuts_some hP hr]
      simp only [List.length_append, List.length_cons, Node.onBlock, Node.mkBlock, lt_irrefl,
        ↓reduceIte]
      split <;> simp <;> omega
    obtain ⟨j₀, e, k, hg₀, hjk, hk⟩ := call_in_group hrun.toLocalRun hp hacc
    intro h0
    have hk' := (List.getElem?_eq_some_iff.1 hk).1
    have hpos := (hg₀.2.1 k hk').2.2.2.1
    rw [← hjk, h0] at hpos
    subst hpos
    simp only [Nat.add_zero] at hjk
    subst hjk
    exact absurd (group_start hg hg₀ (by omega) (by omega)) (by omega)
  · rw [ht₂]
    simp only [Node.mkBlock]
    rw [hslot, sp.slotTime_eq]
    rfl

/-! ## Reads after all events -/

/-- The point after all events at `t` is between two events of every node. -/
theorem cutAfter_boundary {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {t : Time} (hj : CutAfter tr j t) : Boundary tr y j := by
  rintro ⟨c, hc⟩
  obtain ⟨j₀, e, k, hg, rfl, -⟩ := call_in_group hrun.toLocalRun hy hc
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1
  · exfalso
    have h₀ := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.1
    simp only [Nat.add_zero] at h₀
    have := hj.1 j₀ (by omega)
    linarith [hj.2]

/-! ## R.2 -/

end Consensus.Goldilocks.Regimes

end
