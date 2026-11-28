module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Committee
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: post-reset source and transport foundations

The objects of the post-reset argument (with HS.2)
after the reset `a = a_z`, stated over the run, for every consumer
(C1.2 here, H.3 (c)'s `Inv` half), not specialized to C1.2's entries.
With `b = slot(a) + 3` (`cleanLabel`) and `R = t_{b+2k+2}` (`drainTime`, the `R_z` of C1.2):

* **RN, stored ancestry is irreversible**: every lock stored at a later cut sits below a
  stored lock of its slot at an earlier cut, or below a fresh write between them
  (`stored_lock_below`, `AC.lock_provenance_fromU` on the AC projection). **RU** is
  `AC.unlock_compatible`: unlocking against a view with at least `n/2` validators whose slot-`s`
  support votes extend `B`, or that equivocate, moves every lock of a slot below `s` to a block
  compatible with `B`.
* **The drain** (HS.2 (3)): from `R` on, every live lock has a label at least `b + k + 2`, so
  every lock with a label before `b` or a slow window straddling `b` has expired
  (`drain_live_locks`).
* **Clean fast transfer** (`clean_fast_transfer`, HS.2 (1)): the stored block of a fast lock of
  label `≥ b` written by an honest joined node is extended by every honest vote of a later slot,
  and is in the voter's viable voter block tree or at or below its `fc_root` there (HR.4 (R3)
  when it is high; inherited from a high seed when it is a low ancestor of one).

`Outcome.Pivot` consumes these source facts. The downstream `Outcome.Supplier` retains
the report-cover suppliers; this separation lets
those suppliers use the pivot without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}

/-- The first clean evidence label `b = slot(a) + 3` after the reset `a`. -/
def cleanLabel (sp : ACParams) (a : Time) : Nat := sp.slot a + 3

/-- The drain time `R = t_{b+2k+2} = t_{slot(a)+2k+5}` (C1.2's `R_z`). -/
def drainTime (sp : ACParams) (a : Time) : Time := sp.ts (sp.slot a + 2 * sp.k + 5 : Nat)

theorem cleanLabel_eq (a : Time) : cleanLabel sp a = sp.slot a + 3 := by rfl

theorem drainTime_eq (a : Time) : drainTime sp a = sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) := by
  rfl

/-- A time `a ≥ 0` is before its drain time. -/
theorem lt_drainTime {a : Time} (ha0 : 0 ≤ a) : a < drainTime sp a := by
  have ha : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hle : sp.ts ((sp.slot a : Int) + 1) ≤ drainTime sp a :=
    (AC.ts_le_iff sp).2 (by push_cast; omega)
  exact ha.trans_le hle

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF a : Time}

/-- **The drain** (HS.2 (3)): at a time `t ≥ R`, every live lock of an honest node has a
label at least `b + k + 2`; every lock of a label before `b`, and every slow lock whose window
straddles `b`, has expired. The locks are those of a run (`LocksWF`: every expiry is at most
`k` slots after the label), as every honest node's are (`AC.locksWF_state`). -/
theorem drain_live_locks {Φ : AC.Frm sp.n (List (FG.Att sp.n))} {L : Set AC.Lock} {t : Time}
    (hwf : AC.LocksWF sp L) (ht : drainTime sp a ≤ t) :
    ∀ l ∈ AC.liveLocks sp L Φ t, cleanLabel sp a + sp.k + 2 ≤ l.slot := by
  intro l hl
  have hk := hwf.slot_le_of_live hl
  have h0 : 0 ≤ t := le_trans (by
    rw [drainTime_eq]
    simp only [ACParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (Int.natCast_nonneg _)) ht
  rw [drainTime_eq] at ht
  have hs := (AC.ts_le_iff_le_slot sp h0 _).1 ht
  rw [cleanLabel_eq]
  omega

/-- A stored lock that is live by time after the drain has a clean label. This requires
neither normalized `liveLocks` membership nor a later `addLocks` call. -/
theorem drain_stored_lock_label {l : AC.Lock} {t : Time}
    (ht : drainTime sp a ≤ t) (hlive : sp.slot t ≤ l.slot + sp.k) :
    cleanLabel sp a + sp.k + 2 ≤ l.slot := by
  have h0 : 0 ≤ t := le_trans (by
    rw [drainTime_eq]
    simp only [ACParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (Int.natCast_nonneg _)) ht
  rw [drainTime_eq] at ht
  have hs := (AC.ts_le_iff_le_slot sp h0 _).1 ht
  rw [cleanLabel_eq]
  omega

end Consensus.Goldilocks.Healing

end
