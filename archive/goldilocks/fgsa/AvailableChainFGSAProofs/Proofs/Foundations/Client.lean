module
public import AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSARun.Proofs.EmissionWellFormed

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- bp.clientSafety.v1: T7.9 A, including runs with restarts.
The claim type is applied only at the Foundations export boundary (L42). -/
theorem fgsa_clientSafeAll (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x :=
  fgsa_bridge_clientSafeAll p c E rho hL

set_option linter.unusedFintypeInType false in
/-- BaseSet supplies authenticity to the validator-attribution adapters.
The retained Fintype instance is unused; BaseSet has the frozen instance binder. -/
theorem fgsa_unforgeable_of_base [Fintype V] (hb : BaseSet p c E rho) :
    V2.D.UnforgeableSignatures E rho :=
  hb.valid.toUnforgeableSignatures

private theorem row_at_seat (hv : V2.D.ExecutionValid E rho)
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    ∃ i body, a = ⟨.seat .fg i, body⟩ ∧
      rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      rho.seatOf (.base .fg) i = x ∧
      ofRow p a ∈ V2.D.Run.emitsAt E rho j := by
  obtain ⟨i, hi⟩ := honestRow_auth p c rho E hv ha
  obtain ⟨_, hj, hem⟩ := ha
  rcases a with ⟨auth, body⟩
  dsimp only at hi
  subst auth
  exact ⟨i, body, rfl, hj, ((fgsa_emitsAt_row E rho j x _ hj i body).mp hem).2.1, hem⟩

-- The frozen BaseSet package takes Fintype, although its fields do not use it.
set_option linter.unusedFintypeInType false in
/-- P3 §6, 22 §1: at most one signed row per honest identity and action.
Tick uniqueness and the deterministic optional attest read give uniqueness.
The retained Fintype instance is unused; BaseSet has the frozen instance binder. -/
theorem honest_at_most_one_row_per_action [Fintype V] (hb : BaseSet p c E rho) :
    ∀ x ∈ rho.honest, ∀ r : Nat,
      ∀ (j j' : Nat) (a a' : RowWire p.n), HonestRowAt p c E rho j x r a →
        HonestRowAt p c E rho j' x r a' → j = j' ∧ a = a' := by
  intro x _ r j j' a a' ha ha'
  obtain ⟨i, body, rfl, hj, hi, hem⟩ := row_at_seat p c E rho hb.valid ha
  obtain ⟨i', body', rfl, hj', hi', hem'⟩ := row_at_seat p c E rho hb.valid ha'
  have hii : i' = i := (hb.linked.toCStar (.base .fg) trivial).1 (hi'.trans hi.symm)
  subst i'
  have hjj' := fgsa_tick_unique E rho hb.valid.toScheduleWellFormed hj hj'
  subst j'
  obtain ⟨_, _, _, _, hbody⟩ := (fgsa_emitsAt_row E rho j x _ hj i body).mp hem
  obtain ⟨_, _, _, _, hbody'⟩ := (fgsa_emitsAt_row E rho j x _ hj i body').mp hem'
  exact ⟨rfl, congrArg (fun b => (⟨.seat .fg i, b⟩ : RowWire p.n))
    (Option.some.inj (hbody.symm.trans hbody'))⟩

set_option linter.unusedFintypeInType false in
/-- A successful attest read at an awake honest action emits a complete row.
The retained Fintype instance is unused; BaseSet has the frozen instance binder. -/
theorem honest_row_of_attest_some [Fintype V] (hb : BaseSet p c E rho)
    (x : V) (hx : x ∈ rho.honest) (r j : Nat)
    (hj : rho.events[j]? = some (.tick x (p.actionTime r)))
    (hawake : E.awake x (p.actionTime r) = true) (body : RowPayload)
    (hattest : (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho j x).st
      (p.actionTime r)) (V2.D.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1 = some body) :
    ∃ a : RowWire p.n, HonestRowAt p c E rho j x r a ∧ RowComplete p c rho x a := by
  obtain ⟨i, hi⟩ := (hb.linked.toCStar (.base .fg) trivial).2 x
  let a : RowWire p.n := ⟨.seat .fg i, body⟩
  have hem : ofRow p a ∈ V2.D.Run.emitsAt E rho j :=
    (fgsa_emitsAt_row E rho j x _ hj i body).mpr ⟨hawake, hi, r, rfl, hattest⟩
  have hv := honest_emit_wellFormed E rho hb.valid.toDeliveryWellFormed
    hb.valid.toScheduleWellFormed j x _ hj hx hawake (ofRow p a) hem
  exact ⟨a, ⟨hx, hj, hem⟩, hv, i, rfl, hi⟩

/-- The durable sent set identifies both the event and action of an honest row. -/
theorem honest_emit_unique (hv : V2.D.ExecutionValid E rho)
    {j k : Nat} {y : V} {r r' : Nat} {a : RowWire p.n}
    (he : HonestRowAt p c E rho j y r a) (he' : HonestRowAt p c E rho k y r' a) :
    j = k ∧ r = r' := by
  obtain ⟨i, body, rfl, hj, hi, hem⟩ := row_at_seat p c E rho hv he
  have h := Gen.V2.Duty.emit_duty_unique_of_emitOnce E rho (.base .fg)
    (fgsa_emitOnceUnder E rho hv) i (hi.symm ▸ he.1) (.row body) j k
    (.fgAction r) (.fgAction r') rfl rfl (fgsa_dutiesInjectiveAt _)
    (hi.symm ▸ hj) (hi.symm ▸ he'.2.1) hem he'.2.2
  exact ⟨h.1, RunDuty.fgAction.inj h.2⟩

end AvailableChain.FGSA.Run
end
