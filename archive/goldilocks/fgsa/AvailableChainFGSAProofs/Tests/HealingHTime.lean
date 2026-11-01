module
public import AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival -- shake: keep (HTIME tests)

public section

/-! Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W2–W4.
DC: SAME HTimeClaim and its original run package, with named recovery producers. -/

namespace AvailableChain.FGSA.Run.Tests.HealingHTime

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W3.
DC: SAME claim type with only the statement producer as a hypothetical input. -/
example (p : Params) (hTime : ∀ G ΔF, HTimeStatement p G ΔF) : HTimeClaim p :=
  healing_hTimeClaim_of_statement p hTime

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W3.
DC: SAME witness and chained bound after the package is applied to a run. -/
example (p : Params) (hTime : ∀ G ΔF, HTimeStatement p G ΔF)
    (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim_of_statement p hTime G ΔF hClock c E rho () h

#check healing_hTimeClaim_of_statement
#print axioms healing_hTimeClaim_of_statement

section OpenInputs
variable (p : Params)
    (stepRL : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetRawStep p c E rho w i)
    (hcone : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      PostResetRetainedCone p c E rho w)

include stepRL stepLease stepRaw hcone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W2.
DC: SAME full reset statement with the four future producers as hypotheses. -/
example (G ΔF : Time) : ResetArrivalFullStatement p G ΔF :=
  healing_resetArrivalFull_of_open p stepRL stepLease stepRaw hcone G ΔF

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W4.
DC: SAME literal HTimeClaim conclusion with only the four open inputs. -/
example : HTimeClaim p :=
  healing_hTimeClaim_of_open p stepRL stepLease stepRaw hcone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W4.
DC: SAME witness and both time bounds after W4 is applied to a healing run. -/
example (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim_of_open p stepRL stepLease stepRaw hcone G ΔF hClock c E rho () h

end OpenInputs

#check healing_resetArrivalFull_of_open
#check healing_hTimeClaim_of_open
#print axioms healing_hTimeClaim_of_open

/-- Blueprint 21 H.17:2958–3012; plan S5 CONE-2 T.
DC: SAME cone step after the Assembly producer is applied to a healing run. -/
example (p : Params) {V In : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) : ∀ i, PostResetConeStep p c E rho w i :=
  healing_postReset_coneStep_of_set p c E rho hset h0r

#check healing_postReset_coneStep_of_set
#print axioms healing_postReset_coneStep_of_set

section OpenInputs₂
variable (p : Params)
    (stepRL : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetRawStep p c E rho w i)
    (stepCone : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetConeStep p c E rho w i)

include stepRL stepLease stepRaw stepCone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 T/W2.
DC: SAME full reset statement with the four future producers as hypotheses. -/
example (G ΔF : Time) : ResetArrivalFullStatement p G ΔF :=
  healing_resetArrivalFull_of_open₂ p stepRL stepLease stepRaw stepCone G ΔF

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 T/W4.
DC: SAME literal HTimeClaim conclusion with only the four open inputs. -/
example : HTimeClaim p :=
  healing_hTimeClaim_of_open₂ p stepRL stepLease stepRaw stepCone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 T/W4.
DC: SAME witness and both time bounds after W4 is applied to a healing run. -/
example (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim_of_open₂ p stepRL stepLease stepRaw stepCone G ΔF hClock c E rho () h

end OpenInputs₂

#check healing_resetArrivalFull_of_open₂
#check healing_hTimeClaim_of_open₂
#print axioms healing_resetArrivalFull_of_open₂
#print axioms healing_hTimeClaim_of_open₂

end AvailableChain.FGSA.Run.Tests.HealingHTime
end

namespace AvailableChain.FGSA.Run.Tests.HealingHTime

section Steps
variable (p : Params)
    (stepRL : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetRawStep p c E rho w i)

include stepRL stepLease stepRaw

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 CONE-3 R3.
DC: SAME HTimeClaim with the three exact step inputs and the cone supplied. -/
example : HTimeClaim p :=
  healing_hTimeClaim_of_steps p stepRL stepLease stepRaw

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 CONE-3 R3.
DC: SAME witness and both time bounds after the claim is applied to a run. -/
example (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim_of_steps p stepRL stepLease stepRaw G ΔF hClock c E rho () h

end Steps

#check healing_hTimeClaim_of_steps
#print axioms healing_hTimeClaim_of_steps

end AvailableChain.FGSA.Run.Tests.HealingHTime

namespace AvailableChain.FGSA.Run.Tests.HealingHTime

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE T/H2.
DC: SAME HTimeClaim with only the explicit Params binder. -/
example (p : Params) : HTimeClaim p := healing_hTimeClaim p

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE T/H2 all parameters.
DC: SAME claim for each Params value. -/
example : ∀ p, HTimeClaim p := healing_hTimeClaim_all

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE T/H2 run application.
DC: SAME witness and both time bounds under HealingTimePrem. -/
example (p : Params) (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim p G ΔF hClock c E rho () h

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE T/H3.
DC: SAME full reset arrival with p, G and ΔF explicit. -/
example (p : Params) (G ΔF : Time) : ResetArrivalFullStatement p G ΔF :=
  healing_resetArrivalFull p G ΔF

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE T/H4.
DC: SAME HealingInputClaim with only the explicit Params binder. -/
example (p : Params) : HealingInputClaim p := healing_healingInputClaim p

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE T/H4 run application.
DC: SAME input package for the supplied witness and its local horizon. -/
example (p : Params) (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtW)
    (h : HealingInputPrem p c G ΔF E rho pt) : HealingInput p c E rho pt.w ΔF :=
  healing_healingInputClaim p G ΔF hClock c E rho pt h

#check healing_postReset_resetLeaseStep_of_set
#check healing_postReset_leaseStep_of_set
#check healing_postReset_rawStep_of_set
#check healing_hTimeClaim
#check healing_hTimeClaim_all
#check healing_resetArrivalFull
#check healing_healingInputClaim
#print axioms healing_hTimeClaim
#print axioms healing_hTimeClaim_all
#print axioms healing_resetArrivalFull
#print axioms healing_healingInputClaim

end AvailableChain.FGSA.Run.Tests.HealingHTime

namespace AvailableChain.FGSA.Run.Tests.HealingHTime

/-- The named time producers apply to this run and its selected witness. -/
public theorem selectedTime (p : Params) {V In : Type}
    [DecidableEq V] [Fintype V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    (hClock : p.δt = 2 * p.R)
    (hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon) :
    HTimeConcl p c E rho G ΔF :=
  assembly_hTime_at p c E rho hset hbound hClock hhor

/-- The local input result keeps the selected witness's own horizon. -/
private theorem selectedInput (p : Params) {V In : Type}
    [DecidableEq V] [Fintype V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF)
    (hClock : p.δt = 2 * p.R) (w : HealingWitness) (h0 : H0 p c E rho w)
    (hhor : tstar p w ≤ rho.horizon) : HealingInput p c E rho w ΔF :=
  assembly_healingInput_at p c E rho hset hClock w h0 hhor

/-- The named recovery producer supplies the selected joint invariant. -/
private theorem selectedInv (p : Params) {V In : Type}
    [DecidableEq V] [Fintype V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0 : H0 p c E rho w) (hhor : tstar p w ≤ rho.horizon) : HealingInput p c E rho w ΔF :=
  assembly_healingInput_of_inv p c E rho hset h0 hhor

#print axioms selectedTime
#print axioms selectedInput
#print axioms selectedInv

end AvailableChain.FGSA.Run.Tests.HealingHTime
