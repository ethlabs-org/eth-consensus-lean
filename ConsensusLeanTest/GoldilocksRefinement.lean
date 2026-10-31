module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement
@[expose] public section

/-! # Witnesses for the Goldilocks refinement statements

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `selValid_proposer`: in a run admitted by the engine (`SelValid`, part of
  `ExecutionValid`), the proposer role of every slot selects exactly the setup's proposer of
  that slot, the spec node's own `proposer`: the skeleton's per-slot `proposerSel` is the fixed
  singleton `{proposer s}` (for `n ≥ 1`). This is the schedule hypothesis `SelIs` of the earlier
  statements, now a consequence of validity rather than a premise.
* (b) `selValid_exists`: a valid selection exists (the schedule with everyone polling), so
  `SelValid` is satisfiable. -/

namespace Consensus.Goldilocks.Refinement.Test

open Shape
open Consensus.Model (pubOf SelSpec)

variable {V : Type} [Fintype V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The skeleton's proposer selection at slot `s` is the singleton of the setup's proposer. -/
theorem skeleton_proposerSel (s : Nat) :
    (family S (pubOf E)).skel.proposerSel s =
      .fixed {(S.params (pubOf E) hn).toParams.proposer s} := by
  change SelSpec.fixed _ = _
  congr 1
  ext k
  constructor
  · intro hk
    exact Finset.mem_singleton.mpr (Fin.ext (Finset.mem_filter.mp hk).2)
  · intro hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, congrArg Fin.val (Finset.mem_singleton.mp hk)⟩

/-- In an admitted run, the proposer role of slot `s` selects exactly the setup's proposer. -/
theorem selValid_proposer (hsel : rho.SelValid) (s : Nat) :
    rho.sel (.proposer s) = {(S.params (pubOf E) hn).toParams.proposer s} := by
  have h := hsel (.proposer s)
  change ((family S (pubOf E)).skel.proposerSel s).Admits _ at h
  rw [skeleton_proposerSel S hn s] at h
  exact h

include hn in
/-- The schedule with everyone polling is an admissible selection. -/
theorem selValid_exists :
    ∃ sel : (Model.protoOf (compiled (family S)) E).Role → Finset (Fin (Fintype.card V)),
      (Model.protoOf (compiled (family S)) E).SelAdmits sel := by
  refine ⟨fun r => match r with
    | .proposer s => {(S.params (pubOf E) hn).toParams.proposer s}
    | .duty _ k => k.elim
    | .poll => Finset.univ, ?_⟩
  intro r
  cases r with
  | proposer s =>
    change ((family S (pubOf E)).skel.proposerSel s).Admits _
    rw [skeleton_proposerSel S hn s]
    rfl
  | duty _ k => exact k.elim
  | poll => rfl

variable [DecidableEq V]

/-- Exact-time release cannot be satisfied solely by a later send, even at the horizon. -/
theorem released_requires_same_time (v : V)
    (o : (Model.protoOf (compiled (family S)) E).Object) (τ : Time)
    (h : ReleasedFrom S rho v o τ) : rho.releases v o τ := h

/-- An admission at the horizon still requires a relay at that same time. -/
theorem relayed_at_horizon (v : V) (o : (Model.protoOf (compiled (family S)) E).Object)
    (h : RelayedFrom S rho v o rho.horizon) :
    ∃ cs, o ∈ cs ∧ rho.releases v (.mk .none (.data .relay) cs) rho.horizon := h

end Consensus.Goldilocks.Refinement.Test
