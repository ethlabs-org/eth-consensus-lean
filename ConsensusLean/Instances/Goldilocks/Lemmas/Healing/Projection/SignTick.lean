module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The `ac_to_fg` cuts of a signing tick

A tick that runs the FG update (`fgDue = true`) executes an `ac_to_fg` call at its own time, after
its AC tick and its proposal cuts (`toFG_call_of_signing_tick`). When the node does not propose
then, as at an update deadline `t_u + 6Δ` (`not_proposes_update_time`), that call is the cut right
after the AC tick, at the tick's frame (`toFG_second_cut_of_signing_tick`). These are trace facts:
the frame equality reads only the cut law at the two cuts, so static and growing runs share them.
-/

namespace Consensus.Goldilocks.Healing

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {tr : RunTrace A} {proposer : Nat → Fin P.n}

/-- A signing tick executes an `ac_to_fg` call at its own time (its proposal cuts may come
first). -/
theorem toFG_call_of_signing_tick {y : Fin P.n} {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt proposer dg y j t (.tick x true)) :
    ∃ k ell, tr.projAC.CallAt y (j + k) ell ∧ ell.call = .toFG ∧ tr.time (j + k) = t := by
  obtain ⟨ell₀, pc, uc, _, hcuts, _, huc⟩ :=
    @Compose.tick_order P A proposer dg y (tr.state y j) t x true
  simp only [↓reduceIte] at huc
  obtain ⟨ell, hcall, huc⟩ := huc
  have hmem : Cut.ac ell ∈ uc := by
    rcases huc with h | ⟨C, h⟩ | ⟨C, att, h⟩ <;> rw [h] <;> simp
  have hmem' : Cut.ac ell ∈ (exec proposer dg y (tr.state y j) t (.tick x true)).2 := by
    simp only [exec]
    rw [hcuts]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ hmem)
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem hmem'
  obtain ⟨hn, htime, _, _, hl⟩ := hg.2.1 k hk
  rw [he] at hl
  exact ⟨k, ell, Compose.projAC_callAt.2 ⟨hn, hl⟩, hcall, htime⟩

/-- **The adjacent tick and `ac_to_fg` cuts.** At a time the node does not propose, the cut after a
signing tick's AC tick is its `ac_to_fg` call, at the same time and, by the cut law at both cuts,
at the tick's frame. -/
theorem toFG_second_cut_of_signing_tick {y : Fin P.n} {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt proposer dg y j t (.tick x true)) (hnP : ¬ Proposes proposer y t)
    (hlaw : ∀ i c, tr.CallAt y i c → tr.time i = t →
      CutStep y (tr.time i) (tr.state y i) c (tr.post i)) :
    ∃ ell ell' : ACLabel A, tr.projAC.CallAt y j ell ∧ ell.call = .tick ∧ tr.time j = t ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧ tr.time (j + 1) = t ∧
      ell'.frame = ell.frame := by
  obtain ⟨hcj, htj⟩ := tick_first_cut hg
  have h1 : (exec proposer dg y (tr.state y j) t (.tick x true)).2[1]? =
      some (acToFG (tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.1 := by
    change (onTick proposer dg y (tr.state y j) t x true).2[1]? = _
    rw [onTick_eq]
    simp only [tickStep, hnP, ↓reduceIte]
    split <;> simp [acToFG, acCall]
  obtain ⟨hk', hlabel⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 1 hk'
  obtain ⟨ell', hcj1, hcall', htj1⟩ : ∃ ell' : ACLabel A,
      tr.CallAt y (j + 1) (.ac ell') ∧ ell'.call = .toFG ∧ tr.time (j + 1) = t :=
    ⟨_, ⟨hn, hl.trans (congrArg some hlabel)⟩, rfl, ht⟩
  obtain ⟨ell, hcjAC, hcall⟩ : ∃ ell : ACLabel A, tr.CallAt y j (.ac ell) ∧ ell.call = .tick :=
    ⟨_, hcj, rfl⟩
  refine ⟨ell, ell', Compose.projAC_callAt.2 hcjAC, hcall, htj, Compose.projAC_callAt.2 hcj1,
    hcall', htj1, ?_⟩
  have hl0 := hlaw j _ hcjAC htj
  rw [(hlaw (j + 1) _ hcj1 htj1).1, hl0.1, tr.state_succ_of_call hcjAC]
  unfold frame
  rw [hl0.2.2.1]

/-- No node proposes at an update deadline `t_u + 6Δ`, which lies strictly inside slot `u + 1`. -/
theorem not_proposes_update_time {sp : AC.ACParams} {proposer : Nat → Fin sp.n} (y : Fin sp.n)
    (u : Nat) : ¬ Proposes proposer y (sp.ts u + 6 * sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
    AC.slot_of_mem sp (u + 1) (by simp only [AC.ACParams.ts]; push_cast; linarith)
      (by simp only [AC.ACParams.ts]; push_cast; linarith)
  rintro ⟨-, h, -⟩
  rw [show sp.toParams.slotOf (sp.ts u + 6 * sp.Δ) = u + 1 from hslot, sp.slotTime_eq] at h
  simp only [AC.ACParams.ts] at h
  push_cast at h
  linarith

end Consensus.Goldilocks.Healing

end
