module
public import AvailableChainFGSAClaims.Statements.Packages.Healing
public import AvailableChainFGSAClaims.Statements.Packages.Outage
public import AvailableChainFGSAClaims.Statements.Packages.Inclusion


@[expose] public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure (ServedOn MonoOn)

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.exactProposal.v2; 00:985–997; 03 §4:332–394; P3:3234.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: this local adoption
contract gives admitted proposals and exact HEADs, used to prove inclusion.
The receipt and deterministic HEAD clauses apply to joined readers.
The silence clause applies to every honest node that is asleep.
Clause 3 restates inclusion_sleep_silence, proved from fgsa_tick_asleep
and V2.D.tick_asleep. -/
def ExactProposalAt (pt : PtSP) : Prop :=
  (∀ x ∈ rho.honest,
    joinedAt p E rho x pt.s (SA.voteTime p.toParams pt.s) → ∃ o i t,
    (fgsaInterface p c).block o.payload = some pt.P ∧
    t < SA.voteTime p.toParams pt.s ∧ V2.D.Run.acceptsAt E rho i x o t) ∧
  (∀ x ∈ rho.honest,
    joinedAt p E rho x pt.s (SA.voteTime p.toParams pt.s) →
    FGSA.headVote p
      ((fgsa p c).clock (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams pt.s) x)
        (SA.voteTime p.toParams pt.s)).st pt.s = pt.P) ∧
  (∀ x ∈ rho.honest, E.awake x (SA.voteTime p.toParams pt.s) = false →
    ∀ o, ¬ V2.D.Run.emits E rho x o (SA.voteTime p.toParams pt.s))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.exactProposal.v2; 00:985–997; 03 §4; P3:3914.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast: INTENTIONAL: exact local HEAD
adoption is the FG-SA producer of the generic inclusion property. -/
def ExactProposalClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSP) (ΔF : Time),
    ExactProposalPrem p c E rho pt ΔF → ExactProposalAt p c E rho pt

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.cleanInclusion.v2; 03:397–431; P3:3234–3240; S3a Q12:3454.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: the event-prefix post-gate read and monotonicity supply the
inclusive public read after same-time deliveries (S3a Q12). -/
def InclusionPostGateAt (pt : PtSP) : Prop :=
  ScopedServed (fun x i => confirmedReaderAtIdx p c E rho x i
      (SA.gateTime p.toParams pt.s))
    (S_at p c E rho) pt.P
    (fun i => i = afterTicksIdx rho (SA.gateTime p.toParams pt.s)) ∧
  ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho)
    (· ≤ rho.events.length)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.cleanInclusion.v2; 00:999–1007; 03:397–400; P3:3234–3240.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: a supplied honest proposal and all later finite-horizon reads,
with confirmed-reader scope, replace DC's deadline read (03 §5). -/
def InclusionAt (pt : PtSP) : Prop :=
  ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ScopedServed (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t) pt.P
      (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.cleanInclusion.v2; S3a Q12:3454–3458; 03 §5.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: expose the post-gate
read plus event monotonicity before deriving the public-read form (O13). -/
def CleanInclusionPostGateClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSP) (ΔF : Time),
    CleanInclusionPrem p c E rho pt ΔF → InclusionPostGateAt p c E rho pt

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.cleanInclusion.v2; 00:999–1007; S3a Q12:3454–3458; P3:3234–3240.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast: INTENTIONAL: the public-read
corollary covers each later read within the Clean horizon (03 §5).
Its proof is deferred; the post-gate claim and monotonicity are its route. -/
def CleanInclusionClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSP) (ΔF : Time),
    CleanInclusionPrem p c E rho pt ΔF → InclusionAt p c E rho pt

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.fastP1.v2 / bp.slowP1.v2; 00:1031–1054; S3a FS8:2010–2032.
DC Generic/Claims.lean:79–80 Consensus.stableAsynchronyResilient:
INTENTIONAL: FG-SA also protects emitted HEADs and proposal parents;
these are separate from the persistence predicate (00:875–878). -/
def DutiesExtendOn (B : Block) (b₀ b₁ : Time) : Prop :=
  ∀ x t o, x ∈ rho.honest → b₀ ≤ t → t < b₁ → V2.D.Run.emits E rho x o t →
    (∀ H, HeadTargetAtEmission p c E rho x o t H → Block.Preceq B H) ∧
    (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.outageCompatibility.v2; 00:1009–1029; S3a FS8:2020–2022.
DC Generic/Claims Consensus.stableAsynchronyResilient: INTENTIONAL:
FG-SA must also control its finalized state during the outage (03 §§6–8). -/
def FCompatBefore (B : Block) (b₁ : Time) : Prop :=
  ∀ t x, 0 ≤ t → t < b₁ → x ∈ rho.honest →
    Block.Compatible B (V2.D.outputAt E rho finalizedOut x t)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.fastP1.v2 / bp.slowP1.v2; 00:1031–1054; P3:3234–3240; S3a FS8.
DC Generic/Properties:124–129 PersistsFrom, Generic/Claims:79–80:
INTENTIONAL: ServedOn is restricted to [b₀,b₁), and separate duty and
F-compatibility clauses implement the blueprint's finite outage contract. -/
def P1Concl (fast : Bool) (pt : PtOut) : Prop :=
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho g x pt.T) →
      ScopedServed (outageConfirmedReader p c E rho fast pt.b₀ pt.b₁)
        (fun t y => V2.D.outputAt E rho g y t) B
        (fun t => pt.b₀ ≤ t ∧ t < pt.b₁)) ∧
  (∀ x B, confirmedReader p c E rho x pt.T →
    Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
    DutiesExtendScoped p c E rho fast B pt.b₀ pt.b₁ ∧
    FCompatBefore p c E rho B pt.b₁)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.outageCompatibility.v2 / bp.slowP1.v2; 00:1009–1029, 1043–1054;
03 §§6–8; S3a FS8. DC Generic/Claims.lean:79–80:
INTENTIONAL: the FG-SA lease starts at the pending gate, not the outage
cut; it preserves B in the full domain or below Z until F covers B. -/
def LeaseOrFFrom (G : Finset V) (B : Block) (d b₁ : Time) : Prop :=
  ∀ t y, d ≤ t → t < b₁ → y ∈ G →
    let st := storeAt p c E rho (timeIdx rho t) y
    Block.Preceq B (eraseFG st.fg.F) ∨
      ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧ d + L p ≤ dl ∧
        ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
          Block.Preceq B (eraseFG (FGSA.controls p st).Z))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.outageCompatibility.v2; 00:1009–1029; S3a FS8:2027–2031.
DC Generic/Claims.lean:79–80: INTENTIONAL: the finite outage carries a
pending-gate lease guarantee in addition to DC's persistence (03 §§6–8). -/
def OutageCompatAt (fast : Bool) (pt : PtOut) : Prop :=
  P1Concl p c E rho fast pt ∧
  ∀ x B, confirmedReader p c E rho x pt.T →
    Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
    B ≠ .genesis →
    LeaseOrFFrom p c E rho (coveredNodes p E rho fast pt.b₀) B
      (SA.gateTime p.toParams (coverLabel p pt.b₀)) pt.b₁

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.outageCompatibility.v2; 00:1009–1029; P3:3914–3930; S3a FS8.
DC Generic/Claims.lean:79–80: INTENTIONAL: both finite OutageSet alternatives
carry the additional duty, F, and pending-gate lease clauses (03 §§6–8). -/
def OutageCompatClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (pt : PtOut) (ΔF : Time),
    OutagePrem p c fast E rho pt ΔF → OutageCompatAt p c E rho fast pt

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.fastP1.v2; 00:1031–1041; 03 §9.1; P3:3929–3930.
DC Generic/Claims.lean:79–80 Consensus.stableAsynchronyResilient:
INTENTIONAL: fast OutageSet fixes lag 4Δ and the high participation
premise; P1Concl adds the blueprint's duty and F clauses. -/
def FastP1Claim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtOut) (ΔF : Time),
    OutagePrem p c true E rho pt ΔF → P1Concl p c E rho true pt

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.slowP1.v2; 00:1043–1054; 03 §9.2; P3:3929–3930.
DC Generic/Claims.lean:79–80 Consensus.stableAsynchronyResilient:
INTENTIONAL: slow OutageSet fixes lag L−3Δ without fast participation,
and includes the pending-gate lease guarantee of 00:887–889. -/
def SlowP1Claim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtOut) (ΔF : Time),
    OutagePrem p c false E rho pt ΔF → OutageCompatAt p c E rho false pt

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Blueprint 21 H.22; DC available/stableIncludedFast: INTENTIONAL.
Healed event safety and persistent public inclusion after the recovery bound. -/
def AvailableFromConcl (t₀ : Time) : Prop :=
  Healed p c E rho t₀ ∧
  ∀ pt : PtSP,
    t₀ ≤ V2.D.proposalTime (fgsaInterface p c) pt.s →
    HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
    SA.gateTime p.toParams pt.s ≤ rho.horizon →
    InclusionAt p c E rho pt

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC confirmedLive/stableLive: SAME joint strict-prefix growth conclusion.
The trigger and deadline have independent confirmed-reader scopes. -/
def AvailableGrowthConcl (t d : Time) : Prop :=
  ∃ s B,
    t < V2.D.proposalTime (fgsaInterface p c) s ∧
    HonestProposal E rho (fgsaInterface p c) s B ∧
    ∀ g ∈ [(fgsaInterface p c).stable,
           (fgsaInterface p c).confirmed],
      (∀ x, confirmedReader p c E rho x t →
        Block.Prec (V2.D.outputAt E rho g x t) B) ∧
      (∀ x, confirmedReader p c E rho x d →
        Block.Preceq B (V2.D.outputAt E rho g x d))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Blueprint 21 H.20–H.22; DC available/stableIncludedFast: INTENTIONAL GST output.
Recovery is a premise; the healing witness is an output. Scope: the premise is continued
Recovery₂ (awake and `gap` up to the horizon); DC `available` uses SleepyRegime + RecoveredBy
(recurrence only in the bounded recovery prefix). The weaker scope is the weak-continuation
companion's. -/
def AvailableGSTClaim (p : Params) : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)),
    HealingTimePrem p c G ΔF E rho () →
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G ∧
      AvailableFromConcl p c E rho
        (recoveryStart p E + B_HF p ΔF G)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC confirmedLive/stableLive: INTENTIONAL recovery contract.
CONTRACT: stage 5 must supply the proposal-existence and causal-slot bridges. Scope: the
premise is continued Recovery₂ (awake and `gap` up to the horizon); DC uses SleepyRegime +
RecoveredBy (recurrence only in the bounded recovery prefix). The weaker scope is the
weak-continuation companion's. -/
def AvailableGrowthGSTClaim (p : Params) : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (t : Time),
    HealingTimePrem p c G ΔF E rho () →
    recoveryStart p E + B_HF p ΔF G ≤ t →
    t + G + 6 * p.Δ ≤ rho.horizon →
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < recoveryStart p E + B_HF p ΔF G ∧
      AvailableGrowthConcl p c E rho t
        (t + G + 6 * p.Δ)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC confirmedLive/stableLive under LiveSleepyRegime (Generic/Claims.lean:68–71;
Generic/Regimes.lean:106–111): SAME shape; INTENTIONAL: the awake-proposer condition.
Clean case from time 0 (Clean₂, GST = 0). CONTRACT: stage 5 proves it from CleanInclusion and the
recurrence (DC liveFrom_of_includedFrom route).
The trigger is at or after 0 (DC LiveFrom t₀ ≤ t; ruling B32). -/
def CleanGrowthClaim (p : Params) : Prop :=
  ∀ (G ΔF : Time)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (t : Time),
    CleanSet p c E rho ΔF →
    AwakeProposerRecurrenceFrom p c E rho 0 G →
    4 * p.Δ ≤ G →
    0 ≤ t → t + G + 6 * p.Δ ≤ rho.horizon →
    AvailableGrowthConcl p c E rho t (t + G + 6 * p.Δ)

end AvailableChain.FGSA.Run
end
