module
public import AvailableChainSimplexFG.Client
public import AvailableChainSimplexFG.Frame

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- The three record guards hold at each height at or above h0.
DC: ValidatorClient/W4FKChainFinalityRows.lean:124–128 (guard consumer).
INTENTIONAL: quantify the guard over the inclusive high cut; record
TS blueprint/22-finality.md:735–741,770–773. -/
def HighRecord (h0 : Height)
    (entry : Height → BlockId) (Λ : Record) : Prop :=
  ∀ h, h0 ≤ h →
    (Λ.target h = none ∨ Λ.target h = some (entry h)) ∧
    Λ.timeout h = false ∧
    (Λ.lock h = none ∨ Λ.lock h = some (entry h))

/-- The complete inclusive record guard.
DC: ValidatorClient/W4FKChainFinalityRows.lean:124–128; the high-cut extension
is intentional (TS blueprint/22-finality.md:735–741,770–773). -/
theorem HighRecord_def (h0 : Height)
    (entry : Height → BlockId) (Λ : Record) :
    HighRecord h0 entry Λ =
      (∀ h, h0 ≤ h →
        (Λ.target h = none ∨ Λ.target h = some (entry h)) ∧
        Λ.timeout h = false ∧
        (Λ.lock h = none ∨ Λ.lock h = some (entry h))) := by rfl

/-- One record write keeps the high entries and emits only high targets.
DC: ValidatorClient/W4FKChainFinalityRows.lean:115–129 (guard consumer).
INTENTIONAL: H1 and the record induction supply the guard; record
TS blueprint/22-finality.md:770–773. The source and finality entries are inputs.
H.13 uses h0 = μ+1 (TS blueprint/21-healing.md:2563–2575);
FF2 uses h0 = M+1 (TS blueprint/22-finality.md:735–741). -/
def RecordHighStatement : Prop :=
  ∀ {V : Type} (h0 : Height)
    (entry : Height → BlockId) (Λ : Record) (signer : V)
    (fields : Option (Height × BlockId)) (hd : HeadFields),
    HighRecord h0 entry Λ →
    (∀ h T, fields = some (h, T) →
      h0 ≤ h → T = entry h) →
    (∀ fp, finality_pair Λ hd = some fp →
      h0 ≤ fp.height → fp.target = entry fp.height) →
    let a : Row V :=
      ⟨signer, height_pair Λ fields (finality_pair Λ hd),
        finality_pair Λ hd⟩
    HighRecord h0 entry (record_row Λ a) ∧
    (∀ h T timeout,
      a.height_pair = .vote h T timeout →
      h0 ≤ h →
      T = entry h ∧ timeout = false)

/-- One record write keeps the high entries and emits only high targets.
DC: ValidatorClient/W4FKChainFinalityRows.lean:115–129 (guard consumer).
INTENTIONAL: H1 and the record induction supply the guard; record
TS blueprint/22-finality.md:770–773. The source and finality entries are inputs.
H.13 uses h0 = μ+1 (TS blueprint/21-healing.md:2563–2575);
FF2 uses h0 = M+1 (TS blueprint/22-finality.md:735–741). -/
theorem RecordHighStatement_def :
    RecordHighStatement =
      (∀ {V : Type} (h0 : Height)
        (entry : Height → BlockId) (Λ : Record) (signer : V)
        (fields : Option (Height × BlockId)) (hd : HeadFields),
        HighRecord h0 entry Λ →
        (∀ h T, fields = some (h, T) →
          h0 ≤ h → T = entry h) →
        (∀ fp, finality_pair Λ hd = some fp →
          h0 ≤ fp.height →
          fp.target = entry fp.height) →
        let a : Row V :=
          ⟨signer, height_pair Λ fields (finality_pair Λ hd),
            finality_pair Λ hd⟩
        HighRecord h0 entry (record_row Λ a) ∧
        (∀ h T timeout,
          a.height_pair = .vote h T timeout →
          h0 ≤ h →
          T = entry h ∧ timeout = false)) := by rfl

/-- A contest cannot exceed the inclusive high-row cut.
DC: none; INTENTIONAL addition: FJ contest replaces DC's NJ case; record
TS blueprint/21-healing.md:2579–2581. Only a quorum honest-member bound is needed.
H.13 gives H ≤ μ+1: in a contest H = j+1, so this excludes j > μ.
FF2 gives H ≤ M+1, exactly TS blueprint/22-finality.md:775–779. -/
def NoHighContestStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig)
    (h0 : Height)
    (entry : Height → BlockId)
    (faulty : Finset V) (A : Finset (Row V))
    (F : FGBlock V) (vw : View V),
    ViewRootInj vw →
    E.weightOf faulty < E.q →
    (∀ W ∈ vw, chainRows W ⊆ A) →
    (∀ a ∈ A, a.signer ∉ faulty →
      ∀ h T timeout, a.height_pair = .vote h T timeout →
      h0 ≤ h →
      T = entry h ∧ timeout = false) →
    (fjControls E cfg F vw).contest = true →
    (fjControls E cfg F vw).H ≤ h0

/-- A contest cannot exceed the inclusive high-row cut.
DC: none; INTENTIONAL addition: FJ contest replaces DC's NJ case; record
TS blueprint/21-healing.md:2579–2581. Only a quorum honest-member bound is needed.
H.13 gives H ≤ μ+1: in a contest H = j+1, so this excludes j > μ.
FF2 gives H ≤ M+1, exactly TS blueprint/22-finality.md:775–779. -/
theorem NoHighContestStatement_def :
    NoHighContestStatement =
      (∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
        (E : Electorate V) (cfg : FGConfig)
        (h0 : Height)
        (entry : Height → BlockId)
        (faulty : Finset V) (A : Finset (Row V))
        (F : FGBlock V) (vw : View V),
    ViewRootInj vw →
        E.weightOf faulty < E.q →
        (∀ W ∈ vw, chainRows W ⊆ A) →
        (∀ a ∈ A, a.signer ∉ faulty →
          ∀ h T timeout, a.height_pair = .vote h T timeout →
          h0 ≤ h →
          T = entry h ∧ timeout = false) →
        (fjControls E cfg F vw).contest = true →
        (fjControls E cfg F vw).H ≤ h0) := by rfl

end AvailableChain.KitFG
end
