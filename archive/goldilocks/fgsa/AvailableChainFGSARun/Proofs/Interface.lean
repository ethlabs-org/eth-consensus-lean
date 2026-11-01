module
public import AvailableChainFGSARun.Statements.Interface

public section

namespace AvailableChain.FGSA.Run

theorem fgsaDelay_row {p : Params} (Δ ΔF : Time) (a : RowWire p.n) :
    fgsaDelay Δ ΔF (ofRow p a) = ΔF := rfl

theorem fgsaDelay_nonrow {p : Params} (Δ ΔF : Time) (o : Obj p)
    (h : ¬ isRowObject o) : fgsaDelay Δ ΔF o = Δ := by
  cases o with
  | mk a m =>
    cases m with
    | head => rfl
    | proposal => rfl
    | row => exact (h trivial).elim

theorem fgsaDelay_self {p : Params} (Δ : Time) :
    fgsaDelay (p := p) Δ Δ = fun _ => Δ := by
  funext o
  cases o with
  | mk a m => cases m <;> rfl



/-- Distinct slots have distinct proposal duties. -/
theorem propLabel_injective (p : Params) {In : Type} (c : AppCodec In) :
    Function.Injective (fgsaInterface p c).propLabel :=
  (fgsaInterface p c).propLabel_injective

/-- The proposal duty has the SA proposal time. -/
theorem proposalTime_fgsa (p : Params) {In : Type} (c : AppCodec In) (s : Slot) :
    V2.D.proposalTime (fgsaInterface p c) s = SA.proposalTime p.toParams s := rfl

end AvailableChain.FGSA.Run

end
