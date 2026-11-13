module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RoleBinding
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox

public section

/-! # The committee dictionary of an outage query

The query's vote role `Q.voteRole` (its binding's), the dictionary `Q.K` of the keys the run
selects for each slot's vote role, and the fact that `Q.K` binds that selection
(`Q.bindsSel`). Each committee has `committeeSize` members (`Q.hsize`, from the admissible
selection), so it is nonempty (`Q.K_nonempty`), and the committee of the slot of a time `t ≥ 0`
is the selection the outage premise reads at `t` (`Q.mem_K_iff_selected`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape

variable {S : BoundSetup} {A : ContractAssumptions S.toSetup} {V : Type} [Fintype V] [DecidableEq V]

namespace OutageQueryAt

/-- The vote role of the query's binding. -/
abbrev voteRole (_Q : OutageQueryAt S A V) := S.vote.voteRole

/-- The committee dictionary of the query: the keys selected for each slot's vote role. -/
def K (Q : OutageQueryAt S A V) : SA.CommitteeDict (Fintype.card V) :=
  ⟨fun s => {k | k ∈ Q.run.2.sel (Q.voteRole s)}⟩

/-- `Q.K` binds the run's selection for `Q.voteRole`. -/
theorem bindsSel (Q : OutageQueryAt S A V) : Q.K.BindsSel Q.run.2 Q.voteRole :=
  (Q.K.bindsSel_iff _ _).2 fun _ _ => Iff.rfl

/-- **The committee size**: the run's selection for a vote role is admissible
(`SelValid`), so it has `committeeSize` keys (all keys without a participation kind). -/
theorem hsize (Q : OutageQueryAt S A V) (s : Nat) :
    (Q.K.committee s).ncard = Q.params.committeeSize := by
  have hsel := (Q.valid : Q.run.2.ExecutionValid).selValid (Q.voteRole s)
  change (↑(Q.run.2.sel (Q.voteRole s)) : Set (Fin (Fintype.card V))).ncard =
    S.vote.committeeSize (Model.pubOf Q.run.1)
  rw [Set.ncard_coe_finset]
  unfold VoteBinding.committeeSize
  revert hsel
  unfold OutageQueryAt.voteRole VoteBinding.voteRole
  rcases S.vote.participationKind with _ | k
  · intro _
    dsimp only
    exact (congrArg Finset.card (selValid_poll S Q.run.2
      (Q.valid : Q.run.2.ExecutionValid).selValid)).trans
      (by rw [Finset.card_univ, Fintype.card_fin])
  · intro hsel
    dsimp only at hsel ⊢
    change (S.vote.kindSel (Model.pubOf Q.run.1) k).Admits _ at hsel
    split
    · rename_i m hm
      rw [hm] at hsel
      exact hsel
    · rename_i T hT
      rw [hT] at hsel
      change _ = T at hsel
      rw [hsel]

/-- Every slot committee of the query is nonempty (`BoundSetup.committeeSize_pos`). -/
theorem K_nonempty (Q : OutageQueryAt S A V) (s : Nat) : (Q.K.committee s).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by
    rw [Q.hsize s]; exact (S.committeeSize_pos (Model.pubOf Q.run.1) Q.hn).ne')

/-- **The committee of the slot of `t ≥ 0` is the selection the outage premise reads at `t`**:
the participation role at `t` is the vote role of the slot of `t` (the shape grid's slot is the
protocol slot from time `0` on), and without a participation kind both select every key. -/
theorem mem_K_iff_selected (Q : OutageQueryAt S A V) {t : Time} (ht : 0 ≤ t)
    {x : Fin (Fintype.card V)} :
    x ∈ Q.K.committee (Q.params.slot t) ↔
      Q.run.2.key x ∈ (shapeProgress (goldilocksWith S) V).toExternal.selected
        Q.run.2.point.env ((shapeProgress (goldilocksWith S) V).toExternal.ext Q.run) t := by
  have hslot : (t / (4 * Q.params.Δ)).toNat = Q.params.slot t := by
    have h := SA.slot_eq Q.params ht
    omega
  have hrole : (Model.protoOf (compiled (goldilocksWith S)) Q.run.2.point.env).participationRole t =
      S.vote.participationKind.map (fun k => ShapeRole.duty (Q.params.slot t) k) := by
    rw [← hslot]; rfl
  unfold shapeProgress
  dsimp only [Model.sysExternal]
  rw [hrole]
  change x ∈ Q.run.2.sel (S.vote.voteRole (Q.params.slot t)) ↔ _
  unfold VoteBinding.voteRole
  rcases S.vote.participationKind with _ | k
  · simp only [Option.map_none, Finset.mem_univ, iff_true]
    exact (Finset.ext_iff.1 (selValid_poll S Q.run.2
      (Q.valid : Q.run.2.ExecutionValid).selValid) x).2 (Finset.mem_univ x)
  · simp

end OutageQueryAt

end Consensus.Goldilocks.Obligations.Growing

end
