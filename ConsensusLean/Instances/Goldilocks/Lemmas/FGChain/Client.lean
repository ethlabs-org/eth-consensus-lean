module
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety

public section

/-! # Goldilocks FG: the validator client (G0.5, G0.10)

Client safety (G0.5) from a record invariant over the attestations sent so far: each target
is the recorded target at its height, each timeout's root is in the recorded timeout set at
its height, and each finality pair is the lock at its height and stays permitted. The
invariant holds for the empty record and `createAtt` keeps it when the entry state's pairs
are below its height; at the end it rules out E1 (the permitted pair meets every row at its
height) and E2 (one recorded target per height). Aggregation (G0.10) unfolds `createAtt`. -/

namespace Consensus.Goldilocks.FG

namespace Record

variable {n : Nat}

/-- The record invariant of a client run over the attestations `atts` sent so far. -/
private def Tracks (Λ : Record) (atts : List (Att n)) : Prop :=
  ∀ a ∈ atts, (a.timeout = true → a.T ∈ Λ.timeout a.h) ∧
    (a.timeout = false → Λ.target a.h = some a.T) ∧
    ∀ p ∈ a.fin.toList, Λ.lock p.1 = some p.2 ∧ Λ.permits p.1 p.2

private theorem tracks_empty : Tracks empty ([] : List (Att n)) := by
  sorry

/-- `createAtt` keeps the invariant when the entry state's pairs are below its height. -/
private theorem tracks_createAtt {Λ Λ' : Record} {atts : List (Att n)} {v : Fin n}
    {σe : ChainState n} {a : Att n} (hΛ : Tracks Λ atts)
    (hσ : σe.hj < σe.h ∧ ∀ p ∈ σe.pending, p.1 < σe.h)
    (h : Λ.createAtt v σe = some (a, Λ')) : Tracks Λ' (a :: atts) := by
  sorry

/-- A tracked set of attestations has no slashable pair. -/
private theorem not_slashable_of_tracks {Λ : Record} {atts : List (Att n)} (hΛ : Tracks Λ atts)
    {a b : Att n} (ha : a ∈ atts) (hb : b ∈ atts) : ¬ slashable a b := by
  sorry

end Record

/-- **G0.10.** -/
theorem aggregation (gp : FGParams) : Aggregation gp := by
  sorry

/-- **G0.5.** -/
theorem client_safety (gp : FGParams) : ClientSafety gp := by
  sorry

end Consensus.Goldilocks.FG

end
