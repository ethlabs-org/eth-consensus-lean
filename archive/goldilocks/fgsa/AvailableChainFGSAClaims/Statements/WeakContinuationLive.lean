module
public import AvailableChainFGSAClaims.Statements.WeakContinuation
public import AvailableChainFGSAClaims.Statements.OutputReads

@[expose] public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- bp.weakContinuationAvailable.v2 = safety + inclusion (blueprint 23:126–192);
growth: paper proof in 23 §17 (bp.weakContinuationGrowth.v2).
DC Legacy/Definitions/NamedVoteConsumers.lean:56–61 BoundedSafetyRecovery: SAME
safety role; DC Legacy/Liveness.lean:29–71: SAME inclusion and growth roles.
INTENTIONAL: all three results use one completed gate, and each field has
the finite-horizon guard required by B31. An absent gate imposes no result.
Growth quantifies its own continuation gap G' (B33). -/
structure WeakContinuationLiveAt₂
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (u : Slot) (Q : Block) (iStar : Nat) (ΔF : Time) : Prop where
  /-- Blueprint 23:145–160; DC SafetyRegimes:85–127: SAME safety role.
  INTENTIONAL: retain the exact SSafeFromCut₂ result from the chosen gate. -/
  safety :
    SA.gateTime p.toParams u ≤ rho.horizon →
    SSafeFromCut₂ p c E rho iStar Q ΔF
  /-- Blueprint 23:162–181; DC HonestProposalConfirmation:29–37:
  INTENTIONAL: u + 2 ≤ pt.s replaces DC's u < s. Only proposals at
  s ≥ j+2 extend a gate result (Transfers S2; H5RawTransfer clause 3).
  Slot u+1 is proposed before d_u. Require an actual proposal and a covered
  proposal gate; ServedFromGateAt covers every later read in the horizon. -/
  inclusion :
    SA.gateTime p.toParams u ≤ rho.horizon →
    ∀ pt : PtSP,
      u + 2 ≤ pt.s →
      HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon →
      ServedFromGateAt p c E rho pt
  /-- Growth: paper proof in 23 §17 (bp.weakContinuationGrowth.v2).
  DC AvailableChainGrowth.afterGST:46–51:
  SAME universal continuation-gap order (B33); SingleProposerRecurrence
  is Generic/Conditions.lean:207–211.
  INTENTIONAL: FG-SA requires an awake proposer, 4Δ ≤ G', and a covered
  t+G'+6Δ deadline. This is available-chain growth. -/
  growth :
    SA.gateTime p.toParams u ≤ rho.horizon →
    ∀ G' : Time, 4 * p.Δ ≤ G' →
      AwakeProposerRecurrenceFrom p c E rho (SA.gateTime p.toParams u) G' →
    ∀ t : Time,
      SA.gateTime p.toParams u ≤ t →
      t + G' + 6 * p.Δ ≤ rho.horizon →
      JointGrowthAt p c E rho t (t + G' + 6 * p.Δ)

/-- Blueprint 23:103–192 (safety + inclusion);
growth: paper proof in 23 §17 (bp.weakContinuationGrowth.v2).
DC NamedVoteConsumers:56–61:
SAME source-witness-before-continuation order.
INTENTIONAL: choose one joint cut for safety, inclusion, and growth; DC
selects an existential m for each property. RecoveredBy t₀ uses recoveryEnd.
FG-SA uses its completed gate below the source endpoint GST+B_HF.
The source gap G does not fix the continuation gap G' (B33).
Reuse the source and continuation premises without an extra suffix premise. -/
def BoundedSafetyLivenessRecovery₂ (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R →
  ∀ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c)),
    StrongRecoverySearchPrefix₂ p c E source G ΔF →
    ∃ (u : Slot) (Q : Block) (iStar : Nat),
      BoundedHealingCut₂ p c E source u Q iStar ΔF ∧
      ∀ (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        CleanContinuationSleep₂ p c E source E' rho ΔF →
        WeakContinuationLiveAt₂ p c E' rho u Q iStar ΔF

-- Equation export required by BUILD §7.2 B3a.
theorem BoundedSafetyLivenessRecovery₂_def (G ΔF : Time) :
    BoundedSafetyLivenessRecovery₂ p (V := V) c G ΔF =
      (p.δt = 2 * p.R →
      ∀ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c)),
        StrongRecoverySearchPrefix₂ p c E source G ΔF →
        ∃ (u : Slot) (Q : Block) (iStar : Nat),
          BoundedHealingCut₂ p c E source u Q iStar ΔF ∧
          ∀ (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
            CleanContinuationSleep₂ p c E source E' rho ΔF →
            WeakContinuationLiveAt₂ p c E' rho u Q iStar ΔF) := by
  rw [BoundedSafetyLivenessRecovery₂]

end AvailableChain.FGSA.Run
end
