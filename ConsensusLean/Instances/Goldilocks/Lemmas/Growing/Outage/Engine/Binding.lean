module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RoleBinding
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

variable (S : BoundSetup) {E : Env V} (rho : Model.Run (compiled (goldilocksWith S)) E)

/-- The committee dictionary of a run: the keys selected for each slot's vote role. -/
def voteK : SA.CommitteeDict (Fintype.card V) :=
  ⟨fun s => {k | k ∈ rho.sel (S.vote.voteRole s)}⟩

omit [DecidableEq V] in
/-- `voteK S rho` binds the run's selection for the binding's vote role. -/
theorem voteK_bindsSel : (voteK S rho).BindsSel rho S.vote.voteRole :=
  ((voteK S rho).bindsSel_iff _ _).2 fun _ _ => Iff.rfl

/-- **The committee size**: the selection of a valid run for a vote role is admissible
(`SelValid`), so it has `committeeSize` keys (all keys without a participation kind). -/
theorem voteK_ncard (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (s : Nat) :
    ((voteK S rho).committee s).ncard = (S.params (Model.pubOf E) hn).committeeSize := by
  have hsel := hv.selValid (S.vote.voteRole s)
  change (↑(rho.sel (S.vote.voteRole s)) : Set (Fin (Fintype.card V))).ncard =
    S.vote.committeeSize (Model.pubOf E)
  rw [Set.ncard_coe_finset]
  unfold VoteBinding.committeeSize
  revert hsel
  unfold VoteBinding.voteRole
  rcases S.vote.participationKind with _ | k
  · intro _
    dsimp only
    exact (congrArg Finset.card (selValid_poll S rho hv.selValid)).trans
      (by rw [Finset.card_univ, Fintype.card_fin])
  · intro hsel
    dsimp only at hsel ⊢
    change (S.vote.kindSel (Model.pubOf E) k).Admits _ at hsel
    split
    · rename_i m hm
      rw [hm] at hsel
      exact hsel
    · rename_i T hT
      rw [hT] at hsel
      change _ = T at hsel
      rw [hsel]

/-- Every slot committee of a valid run is nonempty (`BoundSetup.committeeSize_pos`). -/
theorem voteK_nonempty (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (s : Nat) :
    ((voteK S rho).committee s).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by
    rw [voteK_ncard S rho hn hv s]; exact (S.committeeSize_pos (Model.pubOf E) hn).ne')

/-- **The committee of the slot of `t ≥ 0` is the selection the participation premises read at
`t`**: the participation role at `t` is the vote role of the slot of `t` (the shape grid's slot is
the protocol slot from time `0` on), and without a participation kind both select every key. -/
theorem mem_voteK_iff_selected (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) {t : Time}
    (ht : 0 ≤ t) {x : Fin (Fintype.card V)} :
    x ∈ (voteK S rho).committee ((S.params (Model.pubOf E) hn).slot t) ↔
      rho.key x ∈ (shapeProgress (goldilocksWith S) V).toExternal.selected
        rho.point.env ((shapeProgress (goldilocksWith S) V).toExternal.ext ⟨E, rho⟩) t := by
  have hslot : (t / (4 * (S.params (Model.pubOf E) hn).Δ)).toNat =
      (S.params (Model.pubOf E) hn).slot t := by
    have h := SA.slot_eq (S.params (Model.pubOf E) hn) ht
    omega
  have hrole : (Model.protoOf (compiled (goldilocksWith S)) rho.point.env).participationRole t =
      S.vote.participationKind.map
        (fun k => ShapeRole.duty ((S.params (Model.pubOf E) hn).slot t) k) := by
    rw [← hslot]; rfl
  unfold shapeProgress
  dsimp only [Model.sysExternal]
  rw [hrole]
  change x ∈ rho.sel (S.vote.voteRole ((S.params (Model.pubOf E) hn).slot t)) ↔ _
  unfold VoteBinding.voteRole
  rcases S.vote.participationKind with _ | k
  · simp only [Option.map_none, Finset.mem_univ, iff_true]
    exact (Finset.ext_iff.1 (selValid_poll S rho hv.selValid) x).2 (Finset.mem_univ x)
  · simp

end Run

variable {S : BoundSetup} {A : ContractAssumptions S.toSetup}

/-- The committee dictionary of an outage query: the run's `voteK`. -/
abbrev OutageQueryAt.K (Q : OutageQueryAt S A V) : SA.CommitteeDict (Fintype.card V) :=
  voteK S Q.run.2

end Consensus.Goldilocks.Obligations.Growing

end
