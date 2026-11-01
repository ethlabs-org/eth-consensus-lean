module
public import AvailableChainGeneric.Statements.Pure.Props -- shake: keep (open ServedOn)
public import AvailableChainFGSAClaims.Statements.Packages.Safety

@[expose] public section

namespace AvailableChain.FGSA.Run

open Gen.Pure (ServedOn)

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- bp.cleanInclusion.v2; blueprint 00:999–1007; 03:397–400; 23:162–181.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: an actual proposal and every later read within the horizon,
including asleep readers, replace DC's existential deadline read.
SAME body as InclusionAt, with a neutral Statements home. -/
def ServedFromGateAt (pt : PtSP) : Prop :=
  ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ScopedServed (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t) pt.P
      (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon)

-- Equation export required by BUILD §7.2 B3a.
theorem ServedFromGateAt_def (pt : PtSP) :
    ServedFromGateAt p c E rho pt =
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ScopedServed (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t) pt.P
      (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon)) := by
  rfl

/-- Growth: paper proof in 23 §17 (bp.weakContinuationGrowth.v2).
Blueprint 23 §17.2, step 5 for "both accessors expose S".
DC Generic/Properties.lean:104–110 LiveFrom: SAME joint strict-prefix growth body
as AvailableGrowthConcl.
INTENTIONAL: one actual proposal extends both outputs at t and is in both
outputs at the shared deadline d. Both FG-SA accessors expose S. -/
def JointGrowthAt (t d : Time) : Prop :=
  ∃ s B,
    t < V2.D.proposalTime (fgsaInterface p c) s ∧
    HonestProposal E rho (fgsaInterface p c) s B ∧
    ∀ g ∈ [(fgsaInterface p c).stable,
           (fgsaInterface p c).confirmed],
      (∀ x, confirmedReader p c E rho x t →
        Block.Prec (V2.D.outputAt E rho g x t) B) ∧
      (∀ x, confirmedReader p c E rho x d →
        Block.Preceq B (V2.D.outputAt E rho g x d))

-- Equation export required by BUILD §7.2 B3a.
theorem JointGrowthAt_def (t d : Time) :
    JointGrowthAt p c E rho t d =
  (∃ s B,
    t < V2.D.proposalTime (fgsaInterface p c) s ∧
    HonestProposal E rho (fgsaInterface p c) s B ∧
    ∀ g ∈ [(fgsaInterface p c).stable,
           (fgsaInterface p c).confirmed],
      (∀ x, confirmedReader p c E rho x t →
        Block.Prec (V2.D.outputAt E rho g x t) B) ∧
      (∀ x, confirmedReader p c E rho x d →
        Block.Preceq B (V2.D.outputAt E rho g x d))) := by
  rfl

end AvailableChain.FGSA.Run
end
