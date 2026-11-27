module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowSigned

public section

/-! # Proposal report follow over the shadow run (interface)

The stock suppliers `proposal_report_follow_at` (`FollowEndpoint`) and
`proposal_report_follow_delayed_at` (`FollowSigned`), restated over `Growing.GoldilocksRun'` and
`Healing.FrameWindow' … M isTop J`. Their proofs compose `CandidateReport` (`Deep`), the
early-witness family (`WitnessFamily`) and the regular and optimistic later-head suppliers
(`FollowHeads`, `FollowWrite`, `RegularLater`); until those are restated the statements below have
no proof and are unresolved.

The signing calendar of a shadow run is read through the shadow tick groups
(`RunTrace.GroupAt'`), not the stock ones: `SignCalendarAt'` is the stock `SignCalendarAt` with
`GroupAt'`. The signing gap `SignGapAt` reads only the calendar and is reused. -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- **The signing calendar of a shadow run** (`SignCalendarAt` over the shadow groups): each tick
of a node honest at its time runs the FG update exactly when the calendar allows it then. -/
def SignCalendarAt' (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sign : Fin P.n → Time → Bool) : Prop :=
  ∀ y j t x fgDue, y ∈ H t → tr.GroupAt' proposer dg y j t (.tick x fgDue) → fgDue = sign y t

theorem signCalendarAt'_iff {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sign : Fin P.n → Time → Bool} :
    tr.SignCalendarAt' proposer dg H sign ↔
      ∀ y j t x fgDue, y ∈ H t → tr.GroupAt' proposer dg y j t (.tick x fgDue) →
        fgDue = sign y t :=
  Iff.rfl

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {hold : Time}

/-- **The fresh candidate yields an actual report**, followed by later honest proposal heads
(`proposal_report_follow_at` over the shadow run). -/
theorem proposal_report_follow_at'
    {g ΔF b : Time} {s₀ u N M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ))
    (hsign : sign y (sp.ts (u + 1 : Nat) + 2 * sp.Δ) = true)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ AC.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (AC.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  sorry

/-- **The delayed report follow** at signing gap `G` (`proposal_report_follow_delayed_at` over the
shadow run). -/
theorem proposal_report_follow_delayed_at'
    {g ΔF b t₀ : Time} {s₀ u N M G : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀)
      (max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ))
      M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N)
    (hmb : max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ) ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign G t₀) (ht₀ : t₀ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ))
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ AC.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 + (G + 3) / 4 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (AC.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  sorry

end Consensus.Goldilocks.Shadow.PU.Growing

end
