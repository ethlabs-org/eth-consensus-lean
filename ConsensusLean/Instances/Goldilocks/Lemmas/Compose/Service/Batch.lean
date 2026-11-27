module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Restarts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.BatchWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.CommitteeRun
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the honest batch at an update

`honest_vote_at_update_early`: honest votes reach a joined updater of slot `s` using service through
`t_s + 2Δ` only, so the update itself may be after the horizon; it is the windowed form of
`Compose/Service/BatchWindow` at `a = κ = 0`. The restarts of a joined updater
(`update_restarts`) are in `Compose/Service/Restarts`. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload)

/-! ### One honest updater over an AC trace -/

section Node

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (AC.Blk sp.n FGP)} {T : AC.GTrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- Honest votes reach a joined updater using service through `t_s + 2Δ` only: every delivery
the update counts has its deadline by then, so the update itself may be after `b` (the windowed
form at `a = κ = 0`). -/
theorem honest_vote_at_update_early {ini} (hrun : AC.ACRun proposer T H U ini)
    {b : Time} {k₀ : Nat}
    {s : Nat} (hsync : AC.ServiceBefore H U b T) (hsb : sp.ts s + 2 * sp.Δ ≤ b) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)} (hu : AC.UpdateAt T y k₀ s ℓ)
    {P : AC.Blk sp.n FGP} (hPU : P ∈ U) (hFP : Anc U ℓ.frame.F P)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : AC.Em sp FGP} (hv : AC.VoteAt T x j e)
    (hes : e.msg.slot = s) (hhead : e.msg.head = P.root) :
    P ∈ ℓ.frame.tree ∧ e.msg ∈ (T.state y k₀).pool s ∧
      AC.resolutionTime (T.state y k₀) ℓ.frame e.msg < AC.ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  exact honest_vote_at_update_window (κ := 0) (b' := T.time k₀) hrun hsync
    ⟨fun _ _ k _ _ hk => absurd hk (not_lt.2 (hrun.localRun.time_nonneg k))⟩
    (by simp only [ACParams.ts]; positivity) (by simp only [ACParams.ts]; positivity) hsb le_rfl
    hy hu hPU hFP hx hv hes hhead

end Node

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}

end Consensus.Goldilocks.Compose

end
