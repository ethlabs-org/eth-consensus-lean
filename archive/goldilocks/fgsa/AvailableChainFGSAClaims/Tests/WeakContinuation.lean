module
public import AvailableChainFGSAClaims.Statements.WeakContinuation -- shake: keep (test examples)

public section

namespace AvailableChain.FGSA.Run.Tests.WeakContinuation

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]

-- Opus WCCheck2.wc_self_cont: the continuation domain contains the source.
example {E : Generic.Env V} {source : V2.D.Run V (fgsa p c)} {G ΔF : Time}
    (h : StrongRecoverySearchPrefix₂ p c E source G ΔF) :
    CleanContinuation₂ p c E source E source ΔF where
  base := h.base
  agrees :=
    { honest := rfl, gst := rfl, delta := rfl, seats := rfl
      inputs := fun _ _ _ => rfl, awake := fun _ _ _ => rfl
      events := by simp
      suffixTime := by intro e he; simp at he }
  covered := le_rfl
  sync := h.sync
  deltaF := h.deltaF
  participation := fun _ h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

-- Opus WCCheck2.wc_prefix_iff: no additional recovery premise is hidden.
example {E : Generic.Env V} {source : V2.D.Run V (fgsa p c)} {G ΔF : Time} :
    StrongRecoverySearchPrefix₂ p c E source G ΔF ↔
      RecoverySleep₂ p c E source G ΔF ∧ LivenessBoundW p ΔF ∧
        source.horizon = recoveryStart p E + B_HF p ΔF G := by
  constructor
  · intro h
    exact ⟨h.toRecoverySleep₂, h.liveness, h.endpoint⟩
  · rintro ⟨r, l, e⟩
    exact ⟨r, l, e⟩

-- Agreement has an unconditional self witness for any run and row delay.
example (E : Generic.Env V) (source : V2.D.Run V (fgsa p c)) (ΔF : Time) :
    AgreesThrough₂ p c E source E source ΔF where
  honest := rfl
  gst := rfl
  delta := rfl
  seats := rfl
  inputs := fun _ _ _ => rfl
  awake := fun _ _ _ => rfl
  events := by simp
  suffixTime := by intro e he; simp at he

-- A Recovery₂ witness needs only the stated liveness bound and endpoint.
-- This is conditional non-vacuity; it does not construct an execution.
example {E : Generic.Env V} {source : V2.D.Run V (fgsa p c)} {G ΔF : Time}
    (r : RecoverySleep₂ p c E source G ΔF) (l : LivenessBoundW p ΔF)
    (e : source.horizon = recoveryStart p E + B_HF p ΔF G) :
    StrongRecoverySearchPrefix₂ p c E source G ΔF :=
  ⟨r, l, e⟩

-- The permitted network equality follows from the two Base₂ records.
example {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}
    (s : Base₂ p c E source) (r : Base₂ p c E' rho) : E'.Δ = E.Δ :=
  r.delta.trans s.delta.symm

-- Opus WCCheck2.wc_inPrefix_redundant: a completed cut cannot exceed the run.
example (source : V2.D.Run V (fgsa p c)) (t : Time) :
    afterTicksIdx source t ≤ source.events.length :=
  List.length_filter_le _ _

end AvailableChain.FGSA.Run.Tests.WeakContinuation
end
