module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.5: the shared facts of the consumption step

Facts that the steps of HS.5's consumption shared; the steps themselves are removed with HS.4 and
HR.3 (retired, owner decision):

* blocks: an honest proposal is accepted by its proposer at its cut (`accept_of_proposesAt`), and
  ancestry does not raise the slot (`slot_le_of_anc`);
* sources: an `ac_to_fg` return is held (`toFG_mem_tree`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

/-! ## Cuts -/

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF : Time}
  {proposer : Nat → Fin sp.n}

/-! ## Blocks -/

/-- **An honest proposal is accepted by its proposer at its cut**, so it is held after it: for any
AC, from the proposer's AC start `ini p` at which the AC meets the requirements. -/
theorem accept_of_proposesAt_from {P : Params} {A : NodeAC P}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
    {tr : RunTrace A} {proposer : Nat → Fin P.n} {ini : Fin P.n → A.State}
    (h : Node.LocalRun proposer dg H sg tr ini)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg) (hnc : Compose.NoCollRun dg tr)
    {p : Fin P.n} (hp : p ∈ H) (hq : ({ A with initial := ini p } : NodeAC P).Requirements)
    {k : Nat} {W : A.Blk} (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hW
  rcases Compose.blockCall_cases h hp hc with hg |
    ⟨j, x, fgDue, rfl, hg, hpr, d, p', hdp, rfl, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨hacc, -⟩ := own_block_accepted h hq hroot hnc hp hg hpr hdp
  have he := hc.2.symm.trans hacc.2
  simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at he
  obtain rfl := he.2
  refine ⟨hc, ?_, (tr.state_succ_of_call hc).symm⟩
  have hlaw := h.cutLaw p hp _ _ hc
  rw [tr.state_succ_of_call hc, (Goldilocks.Store.tree_grows _ _ _ _
    (Compose.fg_reachable h hp _)).1 _ _ hlaw.2.1]
  exact Set.mem_insert _ _

/-- **An honest proposal is accepted by its proposer at its cut** (`accept_of_proposesAt_from`
at the Goldilocks requirements from the run's starts). -/
theorem accept_of_proposesAt {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) :=
  accept_of_proposesAt_from hrun.toLocalRun hrun.genesis_root_ok hnc hp
    (Compose.requirements_from sp (hrun.vstart p)) hW

/-- The right end of an ancestry inside `S` is in `S` when the left end is. -/
theorem mem_of_anc_right {n : Nat} {FGP ACP : Type} {S : Set (Block n FGP ACP)}
    {A B : Block n FGP ACP} (h : Anc S A B) (hA : A ∈ S) : B ∈ S := by
  induction h with
  | refl => exact hA
  | tail _ hst _ => exact hst.2.1

/-- Ancestry inside a coherent set does not raise the slot. -/
theorem slot_le_of_anc {S : Set (AC.Blk sp.n (List (FG.Att sp.n)))} (hS : Coherent S)
    {A B : AC.Blk sp.n (List (FG.Att sp.n))} (h : Anc S A B) : A.slot ≤ B.slot := by
  induction h with
  | refl => exact le_rfl
  | tail _ hst ih => exact ih.trans (hS.2 _ hst.1 _ hst.2.1 hst.2.2).le

/-! ## Sources and votes -/

/-- The block that `ac_to_fg` returns is in the frame of the call. -/
theorem toFG_mem_frame {FGP : Type} {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    {t : Time} {C : AC.Blk sp.n FGP} (h : (AC.acToFG sp A Φ t).2 = some C) : C ∈ Φ.tree :=
  (AC.toFG_source h).1.1

/-- A source of an honest node is in its FG tree. -/
theorem toFG_mem_tree {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hto : AC.ToFGAt tr.projAC y k ℓ C) : C ∈ (tr.state y k).fg.tree :=
  mem_tree_of_frame hrun hy hto.1 (toFG_mem_frame hto.2.2)

end Consensus.Goldilocks.Healing

end
