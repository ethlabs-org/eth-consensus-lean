module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Restart is a bulk stamp

The restart retains locks, the latest confirmation and voting permission, and stamps the
non-genesis tree roots independently of the deep-source and optimistic switches.
-/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} (sp : ACParams)

/-- A node whose latest restart is at `t ≥ 0` is not joined at `t`. -/
theorem not_joined_of_restartTime {A : ACState sp.n} {t : Time} (ht : 0 ≤ t)
    (h : A.restartTime = (t : WithBot Time)) : ¬ joined sp A t := by
  simp only [joined, h, WithBot.coe_le_coe]
  have h₁ := (ts_le_iff_le_slot sp ht (sp.slot t)).mpr le_rfl
  have h₂ : sp.ts ((sp.slot t : Int) - 1) < sp.ts (sp.slot t) := (ts_lt_iff sp).mpr (by omega)
  intro h₃
  exact absurd (lt_of_lt_of_le h₂ h₁) (not_lt.mpr h₃)

/-- The order-free restart result, including all reset and retained fields. -/
noncomputable def restartStamp (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n := by
  classical
  exact { ACState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed,
    restartTime := (t : WithBot Time), mayVote := A.mayVote,
    blockStamp := fun q => if q = sp.genesisRoot then ⊥
      else if InTree Φ q then ETime.of t else ⊤ }

open Classical in
/-- The retained fields, reset fields and stamps of the bulk restart. -/
theorem restartStamp_eq (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    restartStamp sp A Φ t =
      { ACState.initial sp.genesisRoot with
        locks := A.locks, latestConfirmed := A.latestConfirmed,
        restartTime := (t : WithBot Time), mayVote := A.mayVote,
        blockStamp := fun q => if q = sp.genesisRoot then ⊥
          else if InTree Φ q then ETime.of t else ⊤ } := by
  rfl

set_option linter.unusedVariables false in
/-- At every well-formed nonnegative restart, for any input state,
the result is the bulk stamp and emits nothing. No reachability or deep-depth premise is needed. -/
theorem acRestart_eq_stamp (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (hΦ : FrameOK Φ) (ht : 0 ≤ t) :
    acRestart sp self A Φ t = (restartStamp sp A Φ t, []) := by
  rw [restartStamp_eq]
  rfl

end Consensus.Goldilocks.AC

end
