module
public import AvailableChainSimplexFG.Client

@[expose] public section

namespace AvailableChain.SimplexFG

/-! The send-once client of `fgsa-protocol-bf46ae7f.tex`, Fig. `alg:client`.
The record belongs to one signer and persists through sleep and restart.
Only a released row changes the record. There is no pending finality pair. -/

/-- The full two-pair content. The record owner supplies the fixed signer. -/
def Row.onceKey {V : Type} (a : Row V) : NamedHeightPair × Option FinalityPair :=
  (a.height_pair, a.finality_pair)

/-- Full signed content under a fixed label and a fixed validator-to-seat
bijection: authentication fields and both pairs. This is pure content, not
an FGSA wire adapter. -/
def Row.onceSignedContent {V S L : Type} (seatOf : V ≃ S) (label : L) (a : Row V) :
    (L × S) × (NamedHeightPair × Option FinalityPair) :=
  ((label, seatOf a.signer), a.onceKey)

/-- Durable state of one signer. Keep every released two-pair content. -/
structure RecordOnce extends Record where
  sent : List (NamedHeightPair × Option FinalityPair)

/-- No pair history and no released content. -/
def RecordOnce.initial : RecordOnce := ⟨Record.initial, []⟩

/-- Record both pair history and full content before release. -/
def record_row_once {V : Type} (Λ : RecordOnce) (a : Row V) : RecordOnce :=
  ⟨record_row Λ.toRecord a, a.onceKey :: Λ.sent⟩

/-- A prior row blocks a same-height target or a repeat entry timeout.
This guard is separate from the full-content membership test. -/
def sameHeightOnce (Λ : RecordOnce) (h : Height) (T : BlockId) (timeout : Bool) : Bool :=
  Λ.sent.any fun b =>
    NamedHeightPair.casesOn (motive := fun _ => Bool) b.1 false
      (fun g U _ => decide (g = h) && (!timeout || decide (U = T)))

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Compute the provisional finality lock, then the height pair. Reject an
empty pair or a blocked same-height repeat. Keep finality only below the
height pair. Reject full-content repeats, then record and release the row. -/
def createRowOnce (E : Electorate V) (cfg : FGConfig) (Λ : RecordOnce) (signer : V)
    (source : Option (FGBlock V)) (hd : HeadFields) : Option (Row V) × RecordOnce :=
  let fp := finality_pair Λ.toRecord hd
  let hp := height_pair Λ.toRecord
    (source.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) fp
  match hp with
  | .empty => (none, Λ)
  | .vote h T timeout =>
      if sameHeightOnce Λ h T timeout then (none, Λ)
      else
        let a : Row V := ⟨signer, hp, fp.filter (fun p => decide (p.height < h))⟩
        if a.onceKey ∈ Λ.sent then (none, Λ)
        else (some a, record_row_once Λ a)

/-- The client rule through the public height-pair eliminator. Proof modules
can use this equation without exporting a generated matcher. -/
theorem createRowOnce_def (E : Electorate V) (cfg : FGConfig) (Λ : RecordOnce) (signer : V)
    (source : Option (FGBlock V)) (hd : HeadFields) :
    createRowOnce E cfg Λ signer source hd =
      let fp := finality_pair Λ.toRecord hd
      let hp := height_pair Λ.toRecord
        (source.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) fp
      NamedHeightPair.casesOn (motive := fun _ => Option (Row V) × RecordOnce) hp
        (none, Λ) (fun h T timeout =>
          if sameHeightOnce Λ h T timeout then (none, Λ)
          else
            let a : Row V := ⟨signer, hp, fp.filter (fun p => decide (p.height < h))⟩
            if a.onceKey ∈ Λ.sent then (none, Λ)
            else (some a, record_row_once Λ a)) := by
  unfold createRowOnce
  dsimp only
  generalize hp : height_pair Λ.toRecord
    (source.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root))
    (finality_pair Λ.toRecord hd) = pair
  cases pair <;> rfl

/-- Fold the client over action inputs. Omit actions with no released row. -/
def clientRunOnce (E : Electorate V) (cfg : FGConfig) (signer : V) :
    RecordOnce → List (Option (FGBlock V) × HeadFields) → List (Row V)
  | _, [] => []
  | Λ, (src, hd) :: rest =>
      let step := createRowOnce E cfg Λ signer src hd
      match step.1 with
      | none => clientRunOnce E cfg signer step.2 rest
      | some a => a :: clientRunOnce E cfg signer step.2 rest

/-- The durable record after the input list. Use this same record when the
client resumes after sleep or restart. -/
def clientRecordOnce (E : Electorate V) (cfg : FGConfig) (signer : V) :
    RecordOnce → List (Option (FGBlock V) × HeadFields) → RecordOnce
  | Λ, [] => Λ
  | Λ, (src, hd) :: rest =>
      clientRecordOnce E cfg signer (createRowOnce E cfg Λ signer src hd).2 rest

end AvailableChain.SimplexFG
end
