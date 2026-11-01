module
public import AvailableChainFGSARun.Proofs.Excludes -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Restore -- shake: keep (re-export)
public import AvailableChainKitV2.DutyClockLaws -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.RetainedClock -- shake: keep (re-export)
public import AvailableChainGeneric.Statements.V2.Duty.Reads -- shake: keep (re-export)

public section

/-! The base clock and the restore premises for FG-SA (plan T7.4). -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In)

/-- [P3 r3.5.6 F0.2] An ancestor of F stays an ancestor through each local step. -/
theorem fgsa_monoAlong_preceq_F (X : FGBlock (Fin p.n)) :
    Gen.V2.Duty.MonoAlong (P := fgsa p c) (fun nd => FGBlock.Preceq X nd.st.fg.F) := by
  rw [Gen.V2.Duty.MonoAlong_def]
  refine ⟨?_, ?_, ?_⟩
  · intro nd t h
    change FGBlock.Preceq X (clock p nd.st t).fg.F
    rwa [clock_F_eq]
  · intro nd o h
    exact KitFG.preceq_trans h (process_F_mono p nd.st (toWire p o))
  · intro nd o h
    exact h

/-- A predicate preserved by retained-store restart holds after restore. -/
theorem fgsa_hrestore_retained (Q : FGSA.State p.n → Prop)
    (hQ : ∀ st w, Q st → Q (acRestart p st w)) :
    ∀ (nd : Node p) w, Q nd.st →
      Q ((fgsa p c).restore ((fgsa p c).durable nd) w).st := by
  intro nd w h
  exact hQ nd.st w h

/-- A retained list field has no new members after restore. -/
theorem fgsa_hrestore_field_retained {α : Type} (field : FGSA.State p.n → List α)
    (hfield : ∀ st w, field (acRestart p st w) ⊆ field st) :
    ∀ (nd : Node p) w x, x ∈ field ((fgsa p c).restore ((fgsa p c).durable nd) w).st →
      x ∈ field nd.st := by
  intro nd w x hx
  exact hfield nd.st w hx

end AvailableChain.FGSA.Run

end
