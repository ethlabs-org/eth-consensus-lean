module
public import ConsensusLean.Lemmas.Model.Candidates

public section

namespace Consensus.Model.Run

variable {V : Type} [Fintype V] {O : OutputSchema} {F : ProtocolFamily O} {E : Env V}

/-- Run the second duty list from the final state of the first, appending their releases. -/
theorem runDuties_append (rho : Run F E) (v : V) (nd : Node (protoOf F E))
    (ds es : List (protoOf F E).Duty) :
    rho.runDuties v nd (ds ++ es) =
      let r := rho.runDuties v nd ds
      let r' := rho.runDuties v r.1 es
      (r'.1, r.2 ++ r'.2) := by
  induction ds generalizing nd with
  | nil => simp only [List.nil_append, rho.runDuties_nil]
  | cons d ds ih =>
    simp only [List.cons_append, rho.runDuties_cons, ih, List.append_assoc]

/-- The two successive folds agree with the concatenated fold on the final node. -/
theorem runDuties_append_fst (rho : Run F E) (v : V) (nd : Node (protoOf F E))
    (ds es : List (protoOf F E).Duty) :
    (rho.runDuties v nd (ds ++ es)).1 = (rho.runDuties v (rho.runDuties v nd ds).1 es).1 := by
  rw [rho.runDuties_append]

end Consensus.Model.Run
