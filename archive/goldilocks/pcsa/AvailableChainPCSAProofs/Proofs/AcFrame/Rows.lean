module
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAClaims.Statements.Regimes

public section

/-! The AC-only instance emits no FG rows (pcsa34-r4.3 §5.0). -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- No FG signing duty has a payload in AC-only mode. -/
theorem pcsa_ac_no_row_emission (E : Generic.Env V) (rho : V2.D.Run V (pcsaAC p c))
    (x : V) (i : Fin p.n) (a : RowPayload) (t : Time) :
    ¬ V2.D.Run.emits E rho x (⟨.seat (.base .fg) i, .row a⟩ : Obj p) t := by
  rintro ⟨k, hk, ho⟩
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, _, ha⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.base .fg) i (.row a)).mp ho
  cases d with
  | headAction s =>
    change RunLabel.base (.head s) = .base .fg at hl
    cases RunLabel.base.inj hl
  | propAction s => contradiction
  | ackAction s =>
    change RunLabel.base (.ack s) = .base .fg at hl
    cases RunLabel.base.inj hl
  | fgAction r =>
    change none = some (.row a : Msg p.n) at ha
    contradiction

/-- An authentic carried FG row has a faulty holder in AC-only mode. -/
theorem pcsa_ac_carried_row_faulty (E : Generic.Env V) (rho : V2.D.Run V (pcsaAC p c))
    (hv : V2.D.UnforgeableSignatures E rho) (x : V) (o : Obj p) (t : Time)
    (hp : V2.D.Run.processes rho x o t) (i : Fin p.n) (a : RowPayload)
    (hc : (pcsaAC p c).carries o (⟨.seat (.base .fg) i, .row a⟩ : Obj p)) :
    rho.seatOf (.base .fg) i ∉ rho.honest := by
  intro hh
  obtain ⟨t', _, he⟩ := hv.carried x o t hp _ hc _ hh rfl
  exact pcsa_ac_no_row_emission E rho _ i a t' he

/-- A directly delivered FG row also has a faulty holder. -/
theorem pcsa_ac_delivered_row_faulty (E : Generic.Env V) (rho : V2.D.Run V (pcsaAC p c))
    (hv : V2.D.UnforgeableSignatures E rho) (x : V) (i : Fin p.n)
    (a : RowPayload) (t : Time)
    (hp : V2.D.Run.processes rho x (⟨.seat (.base .fg) i, .row a⟩ : Obj p) t) :
    rho.seatOf (.base .fg) i ∉ rho.honest := by
  intro hh
  obtain ⟨t', _, he⟩ := hv.unforgeable x _ t hp _ hh rfl
  exact pcsa_ac_no_row_emission E rho _ i a t' he

end AvailableChain.PCSA.Run
end
