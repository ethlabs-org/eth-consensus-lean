module
public import AvailableChainGridCO.Proofs.Map

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic
open AvailableChain.Statements.Generic

/-- The state just before the public release tick of label `r`. -/
def releaseInput {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (v : V) : State p.n :=
  Run.stateBeforeTime (gridCO p) rho (releaseTime p r) v

/-- The release tick precedes the next would-be HEAD, including at a sleeper. -/
def nextHeadState {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (v : V) : State p.n :=
  clock p (releaseInput p rho r v) (releaseTime p r)

/-- A genuine gate reads all deliveries strictly before its gate time. -/
def gateInput {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (v : V) : State p.n :=
  Run.stateBeforeTime (gridCO p) rho (gateTime p r) v

/-- The ordinary next HEAD walk from the state after the release tick. -/
def nextHead (p : Params) {n : Nat} (st : State n) (r : Slot) : Block :=
  forkChoice st (voterTree p st (r + 1))
    (voterView p st (r + 1)) (voterSupportView p st (r + 1)) (r + 1)

/-- Same-label compatibility from seat alignment. Cross-view receipt
and reverse equivocation relay supply the alignment premises. -/
theorem same_label_of_seat_alignment {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (r : Slot) (u v : V)
    (B C : Block) (ZB ZC : Finset (Fin p.n))
    (hB : confirmation p (gateInput p rho r u) r = some B)
    (hC : confirmation p (gateInput p rho r v) r = some C)
    (hcardB : ZB.card = prefixSupport p (gateInput p rho r u) r B)
    (hcardC : ZC.card = prefixSupport p (gateInput p rho r v) r C)
    (hcrossB : ZB ∪ ZC ⊆ lateSeats p (gateInput p rho r u) r)
    (hcrossC : ZB ∪ ZC ⊆ lateSeats p (gateInput p rho r v) r)
    (hdisjoint : Block.compatible B C = false → Disjoint ZB ZC) :
    Block.compatible B C = true := by
  exact same_label_compatible_in_run p rho r u v B C ZB ZC
    hB hC hcardB hcardC hcrossB hcrossC hdisjoint

/-- The genuine surviving seat sets fit in
both late pools, and conflicting prefixes have disjoint support.
Discharged by `sameLabelSeatAlignment_from_engine` in `CrossView.lean`. -/
def SameLabelSeatAlignment {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (r : Slot) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ B C,
    confirmation p (gateInput p rho r u) r = some B →
    confirmation p (gateInput p rho r v) r = some C →
    ∃ ZB ZC : Finset (Fin p.n),
      ZB.card = prefixSupport p (gateInput p rho r u) r B ∧
      ZC.card = prefixSupport p (gateInput p rho r v) r C ∧
      ZB ∪ ZC ⊆ lateSeats p (gateInput p rho r u) r ∧
      ZB ∪ ZC ⊆ lateSeats p (gateInput p rho r v) r ∧
      (Block.compatible B C = false → Disjoint ZB ZC)

theorem same_label_from_alignment {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (r : Slot)
    (halign : SameLabelSeatAlignment p rho r) :
    ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ B C,
      confirmation p (gateInput p rho r u) r = some B →
      confirmation p (gateInput p rho r v) r = some C →
      Block.compatible B C = true := by
  intro u hu v hv B C hB hC
  obtain ⟨ZB, ZC, hcardB, hcardC, hcrossB, hcrossC, hdisjoint⟩ :=
    halign u hu v hv B C hB hC
  exact same_label_of_seat_alignment p rho r u v B C ZB ZC
    hB hC hcardB hcardC hcrossB hcrossC hdisjoint

/-- The engine's conditional snapshot argument. Receipt includes path
resolution; reverse relay excludes a second copy at the reader. -/
theorem snapshot_of_receipts (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) (Z : Finset (Fin n))
    (hreceipts : ∀ i ∈ Z, ∃ o,
      o ∈ votesAt st r ∧
      resolvedBefore st o (releaseTime p r) = true ∧
      headSeat? o = some i ∧
      (match headTarget? o with
       | some target => !Block.compatible target B
       | none => false) = true)
    (hnoEquivocation : ∀ i ∈ Z,
      equivocates (votesAt st r) i = false) :
    Z.card ≤ releaseCount p st r B := by
  exact snapshot_count_of_relayed_seats p st r B Z hreceipts hnoEquivocation

/-- Path resolution and reverse equivocation relay. A source support set
is counted at each reader as resolved conflict seats. Discharged by
`snapshotSeatAlignment_from_engine` in `Snapshot.lean`. -/
def SnapshotSeatAlignment {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (r : Slot) : Prop :=
  ∀ source ∈ rho.honest, ∀ reader ∈ rho.honest, ∀ B C,
    confirmation p (gateInput p rho r source) r = some C →
    Block.preceq B C = true → ∀ K,
      Block.compatible K B = false →
      ∃ Z : Finset (Fin p.n),
        Z.card = prefixSupport p (gateInput p rho r source) r B ∧
        (∀ i ∈ Z, ∃ o,
          o ∈ votesAt (releaseInput p rho r reader) r ∧
          resolvedBefore (releaseInput p rho r reader) o
            (releaseTime p r) = true ∧
          headSeat? o = some i ∧
          (match headTarget? o with
           | some target => !Block.compatible target K
           | none => false) = true) ∧
        (∀ i ∈ Z, equivocates
          (votesAt (releaseInput p rho r reader) r) i = false)

theorem snapshot_from_alignment {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (r : Slot)
    (halign : SnapshotSeatAlignment p rho r) :
    ∀ source ∈ rho.honest, ∀ reader ∈ rho.honest, ∀ B C,
      confirmation p (gateInput p rho r source) r = some C →
      Block.preceq B C = true → ∀ K,
        Block.compatible K B = false →
        prefixSupport p (gateInput p rho r source) r B ≤
          releaseCount p (releaseInput p rho r reader) r K := by
  intro source hs reader hr B C hresult hprefix K hconflict
  obtain ⟨Z, hcard, hreceipts, hnoEquivocation⟩ :=
    halign source hs reader hr B C hresult hprefix K hconflict
  rw [← hcard]
  exact snapshot_of_receipts p (releaseInput p rho r reader) r K Z
    hreceipts hnoEquivocation

/-- Relay is available early enough to merge the previous frozen views
before this proposal. Synchrony starting at the proposal itself is too
late: old accepted objects can arrive only after the proposer has acted.
The healthy-prefix alternative uses the contract's existing relay field. -/
def ProposalRelayReady {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (s : Slot) : Prop :=
  (E.t_GST + E.Δ ≤ proposalTime p s ∧ PartialSynchrony (gridCO p) E rho) ∨
    ∃ cut, proposalTime p s ≤ cut ∧ HealthyPrefixDelivery (gridCO p) E rho cut

/-- A complete label is synchronous either in the suffix after GST or in
a declared healthy prefix. Receipt relay is explicit in both cases.
The awake majority is the source's honest batch premise. The gate must
lie within the run horizon; a future label has no delivery guarantee. -/
def SynchronousLabel {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (r : Slot) : Prop :=
  ExecutionValid (gridCO p) E rho ∧
  AwakeMajority E rho (voteTime p r) ∧
  gateTime p r ≤ rho.horizon ∧
  ((E.t_GST ≤ proposalTime p r ∧
      PartialSynchrony (gridCO p) E rho) ∨
    ∃ cut, gateTime p r ≤ cut ∧
      HealthyPrefixDelivery (gridCO p) E rho cut)

/-- Every label from genesis through `r` has its complete synchronous
premises. Coverage of an old stable read needs this clean prefix. -/
def CleanThroughLabel {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (r : Slot) : Prop :=
  ∀ s, s ≤ r → SynchronousLabel p E rho s

end AvailableChain.GridCO
end
