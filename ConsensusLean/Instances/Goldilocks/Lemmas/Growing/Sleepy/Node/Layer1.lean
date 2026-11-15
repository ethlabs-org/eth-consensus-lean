module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.SleepyLayer1
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.GoldilocksBridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Induction

public section

/-! # Goldilocks event and read adapters

Open proof targets over the existing sleepy invariant, not a second induction.
Committee facts and slot constancy remain explicit; these heads do not supply an
unconditional instance of the generic event-safety contract.
-/

namespace Consensus.Goldilocks.Generic.SleepyLayer1

open SA (SAParams ReplayOrder)

/-- Updates, including vetoed results, and optimistic locks are confirmation events. -/
def goldilocksEvents (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    Data (goldilocksNode sp ro) where
  ConfirmedEvent tr x k s B :=
    ∃ CV, SA.ResultAt tr.projAC x k s B CV ∨ SA.OptimisticLockAt tr.projAC x k s B CV

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- Output provenance at the reader's actual evaluation time. -/
def GoldilocksOutputProvenance : Prop :=
  ∀ cm proposer dg H tr b,
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y i t, HonestReadPoint tr H b y i t → ReadBoundary tr y i →
      confirmedRead tr y i t ∈ (tr.state y i).fg.tree ∧
      (Anchored (goldilocksEvents sp ro) tr H b t (confirmedRead tr y i t) ∨
        Anc (tr.HonestBlocksAt H) (confirmedRead tr y i t) (tr.state y i).fg.F)

/-- A report's source is an ancestor of a same-reporter event, possibly at the same cut. -/
def GoldilocksSourceProvenance : Prop :=
  ∀ cm proposer dg H tr b,
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y i B, y ∈ H (tr.time i) → tr.time i ≤ b → ReportAt tr y i B →
    B.root = sp.genesisRoot ∨ ∃ k s B', k ≤ i ∧ y ∈ H (tr.time k) ∧ tr.time k ≤ b ∧
      (goldilocksEvents sp ro).ConfirmedEvent tr y k s B' ∧ Anc (tr.HonestBlocksAt H) B B'

/-- Numerical data only; no local correctness supplier is assumed by these adapters. -/
def GoldilocksWindowPremises (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (p : EnvPoint (Fin sp.n)) (cm : Time → Finset (Fin sp.n))
    (c look committeeLook ΔF b : Time) : Prop :=
  RunPointBinding tr H p ∧ b ≤ p.horizon ∧
  Regimes.catchUp sp ≤ c ∧ 5 * sp.Δ ≤ look ∧ 5 * sp.Δ ≤ committeeLook ∧
  (∀ s, cm (sp.ts s + sp.Δ) = cm (sp.ts s)) ∧
  tr.SleepyPrefixAt H ΔF look b ∧
  (∀ t d, 0 ≤ t → t ≤ d → d ≤ min b (p.lookAhead committeeLook t) →
    (cm t).Nonempty →
    let q := p.retain d
    (1 / 2 : ℚ) * (((q.readyAt c t ∩ cm t).card +
      (q.faultyAt t ∩ cm t).card : Nat) : ℚ) < ((q.readyAt c t ∩ cm t).card : ℚ)) ∧
  (∀ t d, 0 ≤ t → t ≤ d → d ≤ min b (p.lookAhead look t) →
    (p.retain d).ReadyAbove (1 / 2) c t)

/-- Adapt the two count windows to `sleepy_invariant_at`; keep the existing induction. -/
def GoldilocksInvariantAdapter : Prop :=
  ∀ cm proposer dg H tr p c look committeeLook ΔF b,
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm) →
    GoldilocksWindowPremises tr H p cm c look committeeLook ΔF b →
    Compose.Growing.SleepyInvariantUpTo tr H b

/-- Event compatibility on the actual run, not on arbitrary frame sequences. -/
def GoldilocksEventSafety : Prop :=
  ∀ cm proposer dg H tr p c look committeeLook ΔF b,
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm) →
    GoldilocksWindowPremises tr H p cm c look committeeLook ΔF b →
    AnchoredFrames (goldilocksEvents sp ro) tr H b →
    ∀ B B', EventWithin (goldilocksEvents sp ro) tr H b b B →
      EventWithin (goldilocksEvents sp ro) tr H b b B' → Compatible (tr.HonestBlocksAt H) B B'

/-- Same-reader extension is a separate obligation, not a consequence of compatibility. -/
def GoldilocksExtension : Prop :=
  ∀ cm proposer dg H tr p c look committeeLook ΔF b,
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm) →
    GoldilocksWindowPremises tr H p cm c look committeeLook ΔF b →
    AnchoredFrames (goldilocksEvents sp ro) tr H b →
    ∀ y i j t u, ReadyReadPoint tr H b c y i t → ReadyReadPoint tr H b c y j u →
      ReadBoundary tr y i → ReadBoundary tr y j → i ≤ j → t ≤ u →
      Anc (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr y j u)

/-- Serviced proposal ancestry at the actual bounded read. The source route is
`sleepy_serviced_proposal_coverage_at` / `include_sleepy_at`; the committee facts
remain explicit as in the other adapters. Catch-up and hold dominate the concrete
durations, and the margin covers six delays. No proposal witness is selected here. -/
def GoldilocksProposalCoverage : Prop :=
  ∀ cm proposer dg H tr p c look committeeLook ΔF b hold margin,
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm) →
    GoldilocksWindowPremises tr H p cm c look committeeLook ΔF b →
    sp.Δ ≤ hold → 6 * sp.Δ ≤ margin →
    AnchoredFrames (goldilocksEvents sp ro) tr H b →
    ∀ B k y j t, ReadyProposal tr H c hold B k → 0 ≤ tr.time k →
    tr.time k + hold ≤ b → tr.time k ≤ b → tr.time k + margin ≤ t →
    ReadyReadPoint tr H b c y j t → ReadBoundary tr y j → t < tr.time j →
      Anc (tr.HonestBlocksAt H) B (confirmedRead tr y j t)

end Consensus.Goldilocks.Generic.SleepyLayer1

end
