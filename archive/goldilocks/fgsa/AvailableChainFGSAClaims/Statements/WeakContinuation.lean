module
public import AvailableChainFGSAClaims.Statements.Regimes

@[expose] public section

/-!
Additive bounded weak-continuation statement (G-F0b companion).
No existing declaration changes. DC counterparts are cited on each record.
The source horizon is the bounded search endpoint; the chosen gate can be earlier.
-/
namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- DC StrongRecoveryPrefix
(DecoupledConsensusStatements/Assumptions/Regimes.lean:22-35).
Finite Recovery₂ fields, with horizon exactly GST+B_HF. Thus no strong duty
is imposed on a continuation. INTENTIONAL: FG-SA uses its own bound, gap,
and family delays (blueprint 23:34-100); LivenessBoundW supplies κ≤R.
-/
structure StrongRecoverySearchPrefix₂ (E : Generic.Env V)
    (source : V2.D.Run V (fgsa p c)) (G ΔF : Time) : Prop
    extends RecoverySleep₂ p c E source G ΔF where
  liveness : LivenessBoundW p ΔF
  endpoint : source.horizon = recoveryStart p E + B_HF p ΔF G

/-- DC AgreesUntil
(DecoupledConsensusStatements/Assumptions/PrefixAgreement.lean:18-22).
INTENTIONAL: an exact global event prefix replaces per-node agreement.
FG-SA's replay reads
seatOf/input/awake (EngineV2/Engine/Duty/Run:28-55), so preserve those too.
Static corruption fixes honest identities (blueprint 23:69-83; contract:25-27).
No honest-set shrink is admitted. Exact global agreement follows this choice.
Seat maps remain fixed as in DC's fixed setup; input and awake may change
strictly after the endpoint. Inclusive endpoint: blueprint 23:103-124.
The fixed full seat map is INTENTIONAL: DC fixes Setup (WC-02).
The Δ equality is SAME: same network; DC fixes Setup.
The explicit ΔF index records the common row delay; this record adds no delay bound.
-/
structure AgreesThrough₂ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c))
    (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) : Prop where
  honest : rho.honest = source.honest
  gst : E'.t_GST = E.t_GST
  delta : E'.Δ = E.Δ
  seats : rho.seatOf = source.seatOf
  inputs : ∀ v t, t ≤ source.horizon → rho.input v t = source.input v t
  awake : ∀ v t, t ≤ source.horizon → E'.awake v t = E.awake v t
  events : rho.events.take source.events.length = source.events
  suffixTime : ∀ e ∈ rho.events.drop source.events.length, source.horizon < e.time

/-- DC WeakContinuation
(DecoupledConsensusStatements/Assumptions/Regimes.lean:44-53).
The weak rule is Clean's a<h at every later time (blueprint 23:69-83),
not SG windows (INTENTIONAL). Family-indexed synchrony CONTINUES; it includes broadcast
and acceptance relay, including obligations triggered before the cut.
Rows use the same ΔF as the source; other objects use Δ (INTENTIONAL,
blueprint 23:111-116). Pending obligations keep their original triggers.
All honest receivers, including sleepers, remain covered. No proposal gap,
all-awake, HealingInput, SeedClosed, or suffix safety premise occurs here.
INTENTIONAL: coverage needs only the source endpoint, rather than DC's later healing boundary:
FG-SA uses the completed gate below that endpoint (blueprint 23:103-124).
INTENTIONAL: no separate SlashableBound is needed: static identities preserve the source
fault bound, and Base₂ keeps Linked and authentication (blueprint 23:57-83; L41).
-/
structure CleanContinuation₂ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c))
    (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) : Prop where
  base : Base₂ p c E' rho
  agrees : AgreesThrough₂ p c E source E' rho ΔF
  covered : source.horizon ≤ rho.horizon
  sync : Gen.V2.Duty.PartialSynchronyBy E' rho (fgsaDelay E'.Δ ΔF)
  deltaF : E'.Δ ≤ ΔF
  participation : ∀ t, source.horizon < t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (Gen.V2.Duty.awakeHonest E' rho t).card

/-- DC's bounded m and actual named P (NamedVoteConsumers:58-59).
INTENTIONAL: FG-SA uses a completed gate and an actual emitted honest proposal, as in
H0.proposal and H4's cut equality (Witness:90-96; Healed:75-82).
The ΔF index is shared with the source and adds no condition.
These are CONCLUSIONS of recovery, never continuation premises.
INTENTIONAL: the refresh is stated on the source. Exact prefix replay transfers it to each
continuation, where DC states it (SafetyRegimes:86-88; Opus WCCheck2.wc_refreshed_transfer).
-/
structure BoundedHealingCut₂ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c))
    (u : Slot) (Q : Block) (iStar : Nat) (ΔF : Time) : Prop where
  afterGST : E.t_GST ≤ SA.gateTime p.toParams u
  beforeEnd : SA.gateTime p.toParams u < source.horizon
  cut : iStar = afterTicksIdx source (SA.gateTime p.toParams u)
  actualProposal : HonestProposal E source (fgsaInterface p c) u Q
  refreshed : ∀ x ∈ source.honest, S_at p c E source iStar x = Q

/-- DC PhaseShiftSafety / UserConfirmationAfterHealing
(Legacy/Definitions/SafetyRegimes:85-127), restricted to the required
S-safety companion. Blueprint 23:145-160 gives the FG-SA output shape.
F_x <= S_y is at the SAME event prefix; S compatibility is cross-time.
The range starts at d_u, not at DC's search start n (SafetyRegimes:38-51,106-110).
This divergence is INTENTIONAL (blueprint 23:103-160).
Safety-only is INTENTIONAL (blueprint 02:25-30; 23:145-160; Claims/Clean:90-95).
This is the safety projection of blueprint 23:133-160.
Future proposal service and finality liveness remain separate claims.
The ΔF index adds no safety condition. F_at and S_at use the post-J4
window store through Statements/Reads:68-73.
Public-time reads use timeIdx ≥ iStar; this includes t ≥ d_u for a valid
continuation and its completed cut. As in CleanSafetyAt, both outputs are covered.
-/
structure SSafeFromCut₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (iStar : Nat) (Q : Block) (ΔF : Time) : Prop where
  compatible : ScopedCompat (confirmedReaderIdx p c E rho) (S_at p c E rho)
    (fun i => iStar ≤ i ∧ i ≤ rho.events.length)
  monotone : ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho)
    (fun i => iStar ≤ i ∧ i ≤ rho.events.length)
  seed : ScopedServed (confirmedReaderIdx p c E rho) (S_at p c E rho) Q
    (fun i => iStar ≤ i ∧ i ≤ rho.events.length)
  finalBelow : ∀ i x y, iStar ≤ i → i ≤ rho.events.length →
    x ∈ rho.honest → confirmedReaderIdx p c E rho y i →
    Block.Preceq (F_at p c E rho i x) (S_at p c E rho i y)
  outputs : ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ScopedCompat (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
      (fun t => iStar ≤ timeIdx rho t) ∧
    ScopedMono (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
      (fun t => iStar ≤ timeIdx rho t)

structure CleanContinuationSleep₂ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c))
    (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) : Prop
    extends CleanContinuation₂ p c E source E' rho ΔF where
  joinedParticipation : ∀ t, source.horizon < t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E' rho t).card

/-- DC Statements.BoundedSafetyRecovery (NamedVoteConsumers:56-61).
The actual proposal, completed cut, and Q are chosen ONCE before all
continuations. Finite endpoint = GST+B_HF, not an assumed infinite strong
run. Companion only; Recovery₂ and HealingInput stay unchanged.
The safety-only scope is INTENTIONAL (blueprint 02:25-30; 23:145-160;
Claims/Clean:90-95). Participation may drop after the endpoint (WC-01).
Coverage note (argument, not a Lean proof): a run with the required strong
premises through T = GST+B_HF can be truncated at time ≤ T to form its source.
Schedule validity, delivery validity, authentication and synchrony restrict
to this prefix by replay; awake and gap restrict to [GST,T]. Thus inclusive
agreement loses no such run. Witness uniformity is over this fixed prefix.
-/
def BoundedSafetyRecovery₂ (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R →
  ∀ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c)),
    StrongRecoverySearchPrefix₂ p c E source G ΔF →
    ∃ (u : Slot) (Q : Block) (iStar : Nat),
      BoundedHealingCut₂ p c E source u Q iStar ΔF ∧
      ∀ (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        CleanContinuationSleep₂ p c E source E' rho ΔF →
        SSafeFromCut₂ p c E' rho iStar Q ΔF

end AvailableChain.FGSA.Run
end
