module
public import ConsensusLeanTest.Goldilocks.FG.Faulty
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Client
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
@[expose] public section

/-! # Witnesses for `Aggregation` (G0.10), both branches of its `if`

At `n = 4` (`gp4`), the entry state `σe` of chain A (`chainA`, blocks `1, 2, 3` signed by validators
`0, 1, 2`) is at height `4`, entered by block `3`, with its previous height justified by
`J = 2` (a block, not genesis) at `h_j = 3`. Two client records, each reached by an honest client
run from the empty record on entry states of accepted chains (`EntryInputs`), meet the premises of
`Aggregation` at `σe` together. Labelled by kind (CONTRIBUTING "Statements"):

* (a) `permitting_premises`: validator `0` attested on the entry states of chain A's prefixes of one
  and two blocks (its own attestations in blocks `2` and `3`); its record permits `(3, 2)`. The
  client computes the target `(4, 3, target; (3, 2))` (`permitting_createAtt`), which is what
  `aggregation` gives (`permitting_aggregation`).
* (a) `nonpermitting_premises`: validator `3` attested on the entry state of chain A's first prefix
  and on the entry state of a fork whose block `22` entered height `3`, so its target at height `3`
  names `22`; its record does not permit `(3, 2)`. The client computes the target
  `(4, 3, target; none)`, not a timeout (`nonpermitting_createAtt`), which is what `aggregation`
  gives (`nonpermitting_aggregation`). -/

namespace Consensus.Goldilocks.AggregationWitness

open FG FaultyWitness

/-- The chain state of a chain that `gp4` accepts. -/
def stateOf (c : List (FGBlock 4)) (h : (gp4.chainState c).isSome) : ChainState 4 :=
  (gp4.chainState c).get h

theorem chainState_stateOf (c : List (FGBlock 4)) (h : (gp4.chainState c).isSome) :
    gp4.chainState c = some (stateOf c h) :=
  (Option.some_get h).symm

/-- A fork of chain A after block `1`: block `22` carries the height-`2` target quorum of
validators `0, 1, 2` for block `1` (as block `2` does) and enters height `3`. -/
def fork : List (FGBlock 4) := chainA.take 1 ++ [⟨22, 2, 0, tvs [0, 1, 2] 2 1 (some (1, 0))⟩]

/-- The entry state of chain A: height `4`, entered by block `3`. -/
def σe : ChainState 4 := stateOf chainA (by decide +kernel)

/-- The entry state of chain A's first block: height `2`, entered by block `1`. -/
def σ₁ : ChainState 4 := stateOf (chainA.take 1) (by decide +kernel)

/-- The entry state of chain A's second block: height `3`, entered by block `2`. -/
def σ₂ : ChainState 4 := stateOf (chainA.take 2) (by decide +kernel)

/-- The entry state of the fork: height `3`, entered by block `22`. -/
def σ₂' : ChainState 4 := stateOf fork (by decide +kernel)

theorem chainState_chainA : gp4.chainState chainA = some σe := chainState_stateOf _ _

theorem chainState_inputs :
    gp4.chainState (chainA.take 1) = some σ₁ ∧ gp4.chainState (chainA.take 2) = some σ₂ ∧
      gp4.chainState fork = some σ₂' :=
  ⟨chainState_stateOf _ _, chainState_stateOf _ _, chainState_stateOf _ _⟩

/-- The entry state `σe`: height `4` entered by block `3` (slot `3`), its previous height `3`
justified by block `2` (not genesis), block `1` finalized at height `2`, `(3, 2)` pending. -/
theorem σe_eq :
    σe.h = 4 ∧ σe.Th = 3 ∧ σe.hj = 3 ∧ σe.J = 2 ∧
      (σe.L, σe.s, σe.ThSlot, σe.F, σe.hF) = (3, 3, 3, 1, 2) ∧ σe.pending = [(3, 2)] ∧
      σe.target = ∅ ∧ σe.prog = ∅ ∧ σe.previousHeightJustified ∧ σe.J ≠ gp4.genesis := by
  decide +kernel

/-- The client's inputs: `(h, T_h, h_j, J)` of the three entry states. -/
theorem inputs_eq :
    (σ₁.h, σ₁.Th, σ₁.hj, σ₁.J) = (2, 1, 1, 0) ∧ (σ₂.h, σ₂.Th, σ₂.hj, σ₂.J) = (3, 2, 2, 1) ∧
      (σ₂'.h, σ₂'.Th, σ₂'.hj, σ₂'.J) = (3, 22, 2, 1) := by
  decide +kernel

/-! ## The permitting record -/

/-- Validator `0`'s inputs: the entry states of chain A's prefixes. -/
def insP : List (ChainState gp4.n) := [σ₁, σ₂]

/-- Validator `0`'s record after attesting on `insP`. -/
def Λp : Record := (Record.run 0 Record.empty insP).1

/-- The honest run: the inputs are entry states, the attestations sent are validator `0`'s
attestations of chain A's blocks `2` and `3`, and the record holds targets `1, 2` at heights
`2, 3` and locks `0, 1` at heights `1, 2`, no timeout. -/
theorem insP_run :
    EntryInputs gp4 insP ∧
      (Record.run 0 Record.empty insP).2 = [tv 0 2 1 (some (1, 0)), tv 0 3 2 (some (2, 1))] ∧
      Λp.sent = [(2, 1, false, some (1, 0)), (3, 2, false, some (2, 1))] ∧
      Λp.target 2 = some 1 ∧ Λp.target 3 = some 2 ∧ Λp.lock 1 = some 0 ∧ Λp.lock 2 = some 1 ∧
      Λp.lock 3 = none ∧ Λp.timeout 2 = ∅ ∧ Λp.timeout 3 = ∅ := by
  unfold EntryInputs
  decide +kernel

/-- (a) The premises of `Aggregation` at `σe` hold together for `Λp`, and `Λp` permits the
predecessor `(h_j, J) = (3, 2)`. -/
theorem permitting_premises :
    σe.previousHeightJustified ∧ (Λp.lock σe.h = none ∨ Λp.lock σe.h = some σe.Th) ∧
      Λp.timeout σe.h = ∅ ∧ Λp.target σe.h = none ∧ (∀ b ∈ Λp.sent, b.1 ≠ σe.h) ∧
      Λp.permits σe.hj σe.J := by
  decide +kernel

/-- The client's attestation at `σe`, computed: the target `(4, 3)` with the finality pair
`(h_j, J) = (3, 2)`. -/
theorem permitting_createAtt :
    (Λp.createAtt 0 σe).map Prod.fst = some ⟨0, 4, 3, false, some (3, 2)⟩ ∧
      (Λp.createAtt 0 σe).map (fun r => r.1.content) =
        some (σe.h, σe.Th, false, some (σe.hj, σe.J)) := by
  decide +kernel

/-- `aggregation` at `σe` and `Λp`, its `if` reduced: the content `(4, 3, target; (3, 2))`. -/
theorem permitting_aggregation :
    ∃ a Λ', Λp.createAtt 0 σe = some (a, Λ') ∧ a.content = (4, 3, false, some (3, 2)) := by
  obtain ⟨hb, hl, hto, htg, hs, hp⟩ := permitting_premises
  obtain ⟨a, Λ', hc, ha⟩ := aggregation gp4 σe Λp 0 hb hl hto htg hs
  rw [ite_eq_left hp] at ha
  obtain ⟨hh, hTh, hhj, hJ, -⟩ := σe_eq
  exact ⟨a, Λ', hc, by rw [ha, hh, hTh, hhj, hJ]⟩

/-! ## The non-permitting record -/

/-- Validator `3`'s inputs: the entry state of chain A's first block, then the fork's. -/
def insN : List (ChainState gp4.n) := [σ₁, σ₂']

/-- Validator `3`'s record after attesting on `insN`. -/
def Λn : Record := (Record.run 3 Record.empty insN).1

/-- The honest run: the inputs are entry states, and the record holds targets `1, 22` at
heights `2, 3` and locks `0, 1` at heights `1, 2`, no timeout. -/
theorem insN_run :
    EntryInputs gp4 insN ∧
      (Record.run 3 Record.empty insN).2 = [tv 3 2 1 (some (1, 0)), tv 3 3 22 (some (2, 1))] ∧
      Λn.sent = [(2, 1, false, some (1, 0)), (3, 22, false, some (2, 1))] ∧
      Λn.target 2 = some 1 ∧ Λn.target 3 = some 22 ∧ Λn.lock 1 = some 0 ∧ Λn.lock 2 = some 1 ∧
      Λn.lock 3 = none ∧ Λn.timeout 2 = ∅ ∧ Λn.timeout 3 = ∅ := by
  unfold EntryInputs
  decide +kernel

/-- (a) The premises of `Aggregation` at `σe` hold together for `Λn`, and `Λn` does not permit
the predecessor `(h_j, J) = (3, 2)`: its target at height `3` names `22`. -/
theorem nonpermitting_premises :
    σe.previousHeightJustified ∧ (Λn.lock σe.h = none ∨ Λn.lock σe.h = some σe.Th) ∧
      Λn.timeout σe.h = ∅ ∧ Λn.target σe.h = none ∧ (∀ b ∈ Λn.sent, b.1 ≠ σe.h) ∧
      ¬ Λn.permits σe.hj σe.J := by
  decide +kernel

/-- The client's attestation at `σe`, computed: the target `(4, 3)` (not a timeout) with no
finality pair. -/
theorem nonpermitting_createAtt :
    (Λn.createAtt 3 σe).map Prod.fst = some ⟨3, 4, 3, false, none⟩ ∧
      (Λn.createAtt 3 σe).map (fun r => r.1.content) = some (σe.h, σe.Th, false, none) := by
  decide +kernel

/-- `aggregation` at `σe` and `Λn`, its `if` reduced: the content `(4, 3, target; none)`. -/
theorem nonpermitting_aggregation :
    ∃ a Λ', Λn.createAtt 3 σe = some (a, Λ') ∧ a.content = (4, 3, false, none) := by
  obtain ⟨hb, hl, hto, htg, hs, hp⟩ := nonpermitting_premises
  obtain ⟨a, Λ', hc, ha⟩ := aggregation gp4 σe Λn 3 hb hl hto htg hs
  rw [ite_eq_right hp] at ha
  obtain ⟨hh, hTh, -⟩ := σe_eq
  exact ⟨a, Λ', hc, by rw [ha, hh, hTh]⟩

end Consensus.Goldilocks.AggregationWitness

end
