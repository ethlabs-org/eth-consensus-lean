module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.StatementsBundle
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
import ConsensusLean.Lemmas.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-! # Generic healing assembly edges

The assembly edges over any node AC, from the generic healing leaves (`HealingLeaves` and
`HealingRounds`). Every edge is a theorem.

`highCanonical` is proved over any `ACHealing`: by the horizon of a premised reset, honest stores
have no high contest (leaf 13), high signings come from high origins (leaf 12), and self-entries of
equal height below two high origins are equal (leaf 14, `high_entry_eq_at_of_healing`).

`premises_truncH` assembles the bundled premises on the honest sets truncated after `b` from the
premises for `H` with restarts bounded only up to `b` (`NoRestartUpTo`). With
`ACRun.run_truncH`, `HZ_truncH` and `isReset_truncH_iff` (`HealingLeaves`) it lets a finite-horizon
consumer apply the bundled leaves on the truncation.
-/

namespace Consensus.Goldilocks.Generic

open AC (gbar)
open Healing (cutZ FirstCutAfter riseLen)
open Healing.Growing (HZ IsReset CatchRun)

/-! ## Four-delay grid timing -/

private theorem grid_span {P : Params} (hgrid : ∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ))
    (s d : Nat) : P.slotTime (s + d) = P.slotTime s + 4 * P.Δ * (d : Time) := by
  rw [hgrid, hgrid]
  push_cast
  ring

/-- On the four-delay grid `t_s = s · 4Δ`, the timeout inequality at every slot is the numerical
bound `6Δ + ΔF ≤ 4Δ · δt`. -/
theorem timeout_grid_equation {P : Params} (ΔF : Time)
    (hgrid : ∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) :
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) ↔
      6 * P.Δ + ΔF ≤ 4 * P.Δ * (P.δt : Time) := by
  constructor
  · intro h
    linarith [h 0, grid_span hgrid 0 P.δt]
  · intro h s
    linarith [grid_span hgrid s P.δt]

/-- On the four-delay grid every slot is `4Δ` long. -/
theorem slotLen_of_grid {P : Params} (hgrid : ∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) :
    ∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1) := fun s => by
  have h := grid_span hgrid s 1
  push_cast at h
  linarith

section Edges

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

/-- Canonical high entries by the horizon of a premised reset, field by field from leaves 13, 12
and 14 over the supplier `O`. -/
theorem highCanonical {hold : Time} (O : ACHealing A sg runs hold) :
    ∀ {cm βK tr H proposer dg g ΔF b a}, βK ≤ 1 / 2 →
      runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold →
      IsReset tr H g a → a ≤ b → HighCanonical O.Origin tr H g b := by
  intro cm βK tr H proposer dg g ΔF b a hβ hrun hP hr hab
  refine ⟨fun _ _ hp hib => no_high_contest_at_of_healing O hβ hrun hP hr hab hp hib,
    fun _ _ _ hy hs hkb hh => ?_, ?_⟩
  · obtain ⟨r, hrk, l, Og, ⟨hyr, hO, hOh⟩, E, hE, hEO, hEr, hEh, hET⟩ :=
      high_row_source_at_of_healing O hβ hrun hP hr hab hy hkb hs hh
    exact ⟨r, hrk, l, Og, hO, hyr, hOh, E, hE, hEO, hEr, hEh, hET⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx hO hib hBh hx' hO' hi'b hB'h h₁ h₂ ht₁ hle₁ hy₁
      ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂
    exact high_entry_eq_at_of_healing O hβ hrun hP hr hab ⟨hx, hO, hBh⟩ hib ⟨hx', hO', hB'h⟩
      hi'b h₁ h₂ ht₁ hle₁ hy₁ ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂

/-! ## Truncation after the horizon -/

private theorem committeeFaultsUpTo_truncH {βK : ℚ} {cm : Time → Finset (Fin P.n)}
    {H : Time → Set (Fin P.n)} {g b : Time} (hcom : CommitteeFaultsUpTo βK cm H g b) :
    CommitteeFaultsUpTo βK cm (truncH H b) g b :=
  fun t d ht htb hd hdb hne => by rw [truncH_eq_of_le hdb]; exact hcom t d ht htb hd hdb hne

private theorem faults_truncH {H : Time → Set (Fin P.n)} {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) :
    ∀ t, 0 ≤ t → t ≤ b → 3 * (truncH H b t)ᶜ.ncard ≤ P.n - 1 :=
  fun t ht htb => by rw [truncH_eq_of_le htb]; exact hf t ht htb

/-- Service is read only at honest cuts, which the truncation projects; relay ancestry over the
truncated honest blocks is ancestry over `H`'s. -/
private theorem service_truncH {tr : RunTrace A} {H : Time → Set (Fin P.n)} {g ΔF b' hold : Time}
    (hs : Service tr H g ΔF b' hold) (b : Time) : Service tr (truncH H b) g ΔF b' hold where
  deltaF := hs.deltaF
  message x i m hx hm y j hy := hs.message x i m hx.1 hm y j hy.1
  block x i B hx hB y j hy := hs.block x i B hx.1 hB y j hy.1
  relay x i B hx hB hg y j hy hj hd hF :=
    hs.relay x i B hx.1 hB hg y j hy.1 hj hd (Anc.mono (honestBlocksAt_truncH_subset b) hF)
  signedRow x i att hx hsg hxh y j hy :=
    hs.signedRow x i att hx.1 hsg (fun k hk hs' ht h0 => (hxh k hk hs' ht h0).1) y j hy.1
  hold_le := hs.hold_le

/-- **The premises on the honest sets truncated after `b`**, with restarts bounded only up to
`b`. Committee faults, faults, service, wakefulness and catch-up read honesty up to `b`, or only
in hypotheses, where the truncation is `H` or a subset of it; a restart honest on the truncation
is at a time `≤ b`, so `NoRestartUpTo` bounds it. The run on the truncation is
`ACRun.run_truncH`. -/
theorem premises_truncH {cm : Time → Finset (Fin P.n)} {βK : ℚ} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {tr : RunTrace A} {H : Time → Set (Fin P.n)}
    {g ΔF b hold : Time} (hcom : CommitteeFaultsUpTo βK cm H g b) (hnc : Compose.NoCollRun dg tr)
    (hsvc : Service tr H g ΔF b hold) (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) (hcatch : CatchRun tr H g (2 * P.Δ))
    (hnr : NoRestartUpTo A tr H (gbar g) b)
    (htd : ∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt))
    (hsl : ∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1))
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) (hH : (H b).Nonempty) :
    Premises tr (truncH H b) cm βK proposer dg sg g ΔF b hold where
  committee := committeeFaultsUpTo_truncH hcom
  noColl := hnc
  sync := service_truncH hsvc b
  awake y t hy := hawake y t hy.1
  faults := faults_truncH hf
  catchUp := catchRun_truncH hcatch b
  noRestart y k hy hk := hnr y k hy.1 hk hy.2
  timeoutDelay := htd
  slotLen := hsl
  snapshot := hsnap
  nonempty := hH.mono fun _ hy => ⟨hy, le_rfl⟩

/-- The premises at `b` restrict to the honest sets truncated after `b` (`premises_truncH`): every
field reads the truncation where it reads `H` up to `b`, and its restarts are bounded by the
whole-run bound. -/
theorem premises_restrict_truncH {cm : Time → Finset (Fin P.n)} {βK : ℚ}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload} {tr : RunTrace A}
    {H : Time → Set (Fin P.n)} {g ΔF b hold : Time}
    (h : Premises tr H cm βK proposer dg sg g ΔF b hold) :
    Premises tr (truncH H b) cm βK proposer dg sg g ΔF b hold :=
  premises_truncH h.committee h.noColl h.sync h.awake h.faults h.catchUp
    (fun y k hy hk _ => h.noRestart y k hy hk) h.timeoutDelay h.slotLen h.snapshot h.nonempty

end Edges

end Consensus.Goldilocks.Generic

end
