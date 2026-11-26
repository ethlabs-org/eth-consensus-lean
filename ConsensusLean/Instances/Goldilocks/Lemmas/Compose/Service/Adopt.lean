module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Strict
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Confirmation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the record after an update

`acOnTick_update_record`: after a joined tick at `t_s + 6Δ` whose update of slot `s` has a result
`C` that no live lock vetoes, the record is the old one when `C` is below it in the tree, and `C`
otherwise. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

open Classical in
/-- The record after a joined tick at `t_s + 6Δ` whose update of slot `s` has a result `C` that
no live lock vetoes: the old record when `C` is below it in the tree, else `C`. -/
theorem acOnTick_update_record (self : Fin sp.n) {A : AC.ACState sp.n}
    {Φ : AC.Frm sp.n (List (FG.Att sp.n))} {s : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    {t : Time} (ht : t = sp.ts s + 6 * sp.Δ) (hj : AC.joined sp A t)
    (hC : AC.getConfirmation sp A Φ s = some C) (hv : ¬ AC.conflictsWithLock sp A.locks Φ t C) :
    (AC.acOnTick sp self A Φ t).1.latestConfirmed =
      if AC.AncR Φ C A.latestConfirmed then A.latestConfirmed else C.root := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h6 : t = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ := ht.trans (AC.slot_arithmetic sp s).2.2
  have hsl : sp.slot t = s + 1 := by
    have := (AC.slot_arithmetic sp (s + 1)).1 2 (by omega)
    rw [h6]
    simpa using this
  have hne : ¬ t = sp.ts ((s + 1 : Nat) : Int) + sp.Δ := by rw [h6]; intro h; linarith
  unfold AC.acOnTick
  rw [ite_eq_right (not_not.2 hj)]
  simp only [hsl]
  rw [ite_eq_right hne, ite_eq_left ⟨h6, Nat.succ_pos s⟩, Nat.add_sub_cancel]
  simp only [AC.updateConfirmation, hC]
  rw [ite_eq_right hv]
  simp only [AC.updateLatestConfirmed]
  split_ifs <;> rfl

end Consensus.Goldilocks.Compose

end
