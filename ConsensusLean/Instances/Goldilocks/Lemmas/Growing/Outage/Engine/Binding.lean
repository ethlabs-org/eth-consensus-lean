module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.CommitteeSelection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox

public section

/-! # The committee dictionary of a run

The dictionary `voteK S rho` of the keys a run selects for each slot's vote role, and the fact
that it binds that selection (`voteK_bindsSel`). In a valid run each committee has
`committeeSize` members (`voteK_ncard`, from the admissible selection), so it is nonempty
(`voteK_nonempty`), and the committee of the slot of a time `t ≥ 0` is the selection the
participation premises read at `t` (`mem_voteK_iff_selected`).

An outage query's committee dictionary `Q.K` is the `voteK` of its run. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape

variable {V : Type} [Fintype V] [DecidableEq V]

section Run

variable (S : Setup) {E : Env V} (rho : Model.Run (compiled (goldilocks S)) E)

/-- The committee dictionary of a run: the keys selected for each slot's vote role. -/
def voteK : SA.CommitteeDict (Fintype.card V) :=
  NodeAsChainShape.CanonicalTrace.voteK (rho.sel ∘ S.vote.voteRole)

omit [DecidableEq V] in
/-- `voteK S rho` binds the run's selection for the binding's vote role. -/
theorem voteK_bindsSel : (voteK S rho).BindsSel rho S.vote.voteRole :=
  NodeAsChainShape.CanonicalTrace.voteK_bindsSel rho S.vote.voteRole

omit [DecidableEq V] in
private theorem voteRole_size (hn : 1 ≤ Fintype.card V) (s : Nat) :
    (match (goldilocks S (Model.pubOf E)).skel.selSpec (S.vote.voteRole s) with
    | .fixed T => T.card
    | .sized m => min m (Fintype.card V)) = (S.params (Model.pubOf E) hn).committeeSize := by
  change (match (skeleton (Model.pubOf E) S.vote).selSpec (S.vote.voteRole s) with
    | .fixed T => T.card
    | .sized m => min m (Fintype.card V)) = S.vote.committeeSize (Model.pubOf E)
  unfold VoteBinding.voteRole VoteBinding.committeeSize
  cases S.vote.participationKind with
  | none => exact Finset.card_univ.trans (Fintype.card_fin _)
  | some k =>
    dsimp only [Skeleton.selSpec, skeleton]
    cases S.vote.kindSel (Model.pubOf E) k <;> rfl

/-- **The committee size**: the selection of a valid run for a vote role is admissible
(`SelValid`), so it has `committeeSize` keys (all keys without a participation kind). -/
theorem voteK_ncard (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (s : Nat) :
    ((voteK S rho).committee s).ncard = (S.params (Model.pubOf E) hn).committeeSize := by
  exact (NodeAsChainShape.CanonicalTrace.voteK_ncard rho S.vote.voteRole hv.selValid s).trans
    (voteRole_size (E := E) S hn s)

/-- Every slot committee of a valid run is nonempty (`Setup.committeeSize_pos`). -/
theorem voteK_nonempty (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (s : Nat) :
    ((voteK S rho).committee s).Nonempty :=
  NodeAsChainShape.CanonicalTrace.voteK_nonempty rho S.vote.voteRole hv.selValid s (by
    exact Nat.lt_of_lt_of_eq (S.committeeSize_pos (Model.pubOf E) hn)
      (voteRole_size (E := E) S hn s).symm)

/-- **The committee of the slot of `t ≥ 0` is the selection the participation premises read at
`t`**: the participation role at `t` is the vote role of the slot of `t` (the shape grid's slot is
the protocol slot from time `0` on), and without a participation kind both select every key. -/
theorem mem_voteK_iff_selected (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) {t : Time}
    (ht : 0 ≤ t) {x : Fin (Fintype.card V)} :
    x ∈ (voteK S rho).committee ((S.params (Model.pubOf E) hn).slot t) ↔
      rho.key x ∈ (shapeProgress (goldilocks S) V).toExternal.selected
        rho.point.env ((shapeProgress (goldilocks S) V).toExternal.ext ⟨E, rho⟩) t := by
  have hslot : (t / (4 * (S.params (Model.pubOf E) hn).Δ)).toNat =
      (S.params (Model.pubOf E) hn).slot t := by
    have h := SA.slot_eq (S.params (Model.pubOf E) hn) ht
    omega
  have hrole : (Model.protoOf (compiled (goldilocks S)) rho.point.env).participationRole t =
      S.vote.participationKind.map
        (fun k => ShapeRole.duty ((S.params (Model.pubOf E) hn).slot t) k) := by
    rw [← hslot]; rfl
  unfold shapeProgress
  dsimp only [Model.sysExternal]
  rw [hrole]
  rw [(voteK S rho).bindsSel_iff rho S.vote.voteRole |>.1 (voteK_bindsSel S rho)]
  unfold VoteBinding.voteRole
  rcases S.vote.participationKind with _ | k
  · simp only [Option.map_none, Finset.mem_univ, iff_true]
    exact (Finset.ext_iff.1 (selValid_poll S rho hv.selValid) x).2 (Finset.mem_univ x)
  · simp

end Run

variable {S : Setup} {A : ContractAssumptions S}

/-- The committee dictionary of an outage query: the run's `voteK`. -/
abbrev OutageQueryAt.K (Q : OutageQueryAt S A V) : SA.CommitteeDict (Fintype.card V) :=
  voteK S Q.run.2

end Consensus.Goldilocks.Obligations.Growing

end
