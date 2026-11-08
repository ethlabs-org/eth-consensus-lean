module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Restarts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.BatchWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
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

When every honest slot-`s` vote names a block `P` of a joined updater's frame,
the honest slot-`s` votes reach the updater of slot `s`, held and resolved before `t_s + 2Δ`
(the update analogue of `honest_batch_carry`). The whole-history forms here are instances of the
windowed forms of `Compose/Service/BatchWindow`, imported privately; the restarts of a joined
updater (`update_restarts`) are in `Compose/Service/Restarts`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

/-! ### One honest updater over an SA trace -/

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- Honest votes reach a joined updater using service through `t_s + 2Δ` only: every delivery
the update counts has its deadline by then, so the update itself may be after `b` (the windowed
form at `a = κ = 0`). -/
theorem honest_vote_at_update_early (hrun : SA.ACRun proposer T H U) {b : Time} {k₀ : Nat}
    {s : Nat} (hsync : SA.ServiceBefore H U b T) (hsb : sp.ts s + 2 * sp.Δ ≤ b) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt T y k₀ s ℓ)
    {P : SA.Blk sp.n FGP} (hPU : P ∈ U) (hFP : Anc U ℓ.frame.F P)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = s) (hhead : e.msg.head = P.root) :
    P ∈ ℓ.frame.tree ∧ e.msg ∈ (T.state y k₀).pool s ∧
      SA.resolutionTime (T.state y k₀) ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  exact honest_vote_at_update_window (κ := 0) (b' := T.time k₀) hrun hsync
    ⟨fun _ _ k _ _ hk => absurd hk (not_lt.2 (hrun.localRun.time_nonneg k))⟩
    (by simp only [SAParams.ts]; positivity) (by simp only [SAParams.ts]; positivity) hsb le_rfl
    hy hu hPU hFP hx hv hes hhead

/-- Honest votes reach a joined updater using service through the update's time. -/
theorem honest_vote_at_update_before (hrun : SA.ACRun proposer T H U) {b : Time} {k₀ : Nat}
    (hsync : SA.ServiceBefore H U b T) (hb : T.time k₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    {s : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt T y k₀ s ℓ)
    {P : SA.Blk sp.n FGP} (hPU : P ∈ U) (hFP : Anc U ℓ.frame.F P)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = s) (hhead : e.msg.head = P.root) :
    P ∈ ℓ.frame.tree ∧ e.msg ∈ (T.state y k₀).pool s ∧
      SA.resolutionTime (T.state y k₀) ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  have ht : T.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  exact honest_vote_at_update_early hrun hsync (by linarith) hy hu hPU hFP hx hv hes hhead

/-- Whole-run service specializes the same updater argument. -/
theorem honest_vote_at_update (hrun : SA.ACRun proposer T H U) {a₀ : Time} {k₀ : Nat}
    (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a₀ (T.time k₀) T) {y : Fin sp.n} (hy : y ∈ H)
    {s : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt T y k₀ s ℓ)
    (ha₀ : a₀ ≤ sp.ts s) {P : SA.Blk sp.n FGP} (hPU : P ∈ U) (hFP : Anc U ℓ.frame.F P)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = s) (hhead : e.msg.head = P.root)
    (hPa : ∀ kx, T.AcceptAt x kx P → a₀ ≤ T.time kx) :
    P ∈ ℓ.frame.tree ∧ e.msg ∈ (T.state y k₀).pool s ∧
      SA.resolutionTime (T.state y k₀) ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) :=
  honest_vote_at_update_of_sync hrun (Or.inl ⟨hsync, hPa⟩) hy hu ha₀ hPU hFP hx hv hes hhead

end Node

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}

/-- The honest batch reaches the updater using only service through the bounded horizon. -/
theorem honest_batch_at_update_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {b : Time}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k₀ s ℓ)
    (hb : tr.time k₀ ≤ b) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ℓ.frame.tree)
    (hall : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      e.msg ∈ (tr.projAC.state y k₀).pool s ∧
        SA.resolutionTime (tr.projAC.state y k₀) ℓ.frame e.msg <
          SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  intro x hx j e hv hes
  have hr := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr.localRun hy hu.1
  exact (honest_vote_at_update_before hr hsync hb hy hu (hΦU hPt)
    (Anc.mono hΦU (hΦ.rooted.2 P hPt)) hx hv hes (hall x hx j e hv hes)).2

end Consensus.Goldilocks.Compose

end
