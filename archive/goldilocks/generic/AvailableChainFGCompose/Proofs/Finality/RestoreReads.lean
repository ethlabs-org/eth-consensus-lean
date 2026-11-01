module
public import AvailableChainFGCompose.Statements.FinalityReceipts
public import AvailableChainFGCompose.Statements.Finality
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import AvailableChainKitFG.Ancestry

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

/-- Finalized ancestry survives restore because F is durable.
DC: SAME durable finality; the restore equation is the protocol's leaf. -/
theorem finality_restore_preceq_F (F : FGFinalityDurableLaws R) (X : FGBlock (Fin n)) :
    ∀ nd t, FGBlock.Preceq X (R.core nd).fg.F →
      FGBlock.Preceq X (R.core (P.restore (P.durable nd) t)).fg.F := by
  intro nd t h
  rw [F.restore]
  exact h

/-- A strict-before index witness gives acceptance across sleep and restore.
DC: SAME strict deadline read. -/
theorem finality_acceptsFinalBefore_of_idx (F : FGFinalityDurableLaws R)
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X : FGBlock (Fin n)} {d : Time}
    (h : ∃ i ≤ rho.events.length,
      (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
      FGBlock.Preceq X (R.core (V2.D.Run.stateBefore E rho i x)).fg.F) :
    AcceptsFinalBefore R E rho x X d :=
  (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs (F.mono X)
    (finality_restore_preceq_F R F X)).mpr h

/-- A later deadline preserves acceptance of durable finality.
DC: SAME monotone deadline. -/
theorem finality_acceptsFinalBefore_mono_deadline (F : FGFinalityDurableLaws R)
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X : FGBlock (Fin n)}
    {d d' : Time} (hdd : d ≤ d') (h : AcceptsFinalBefore R E rho x X d) :
    AcceptsFinalBefore R E rho x X d' := by
  obtain ⟨i, hi, hbefore, hX⟩ :=
    (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs (F.mono X)
      (finality_restore_preceq_F R F X)).mp h
  apply finality_acceptsFinalBefore_of_idx R E rho F hs
  refine ⟨i, hi, ?_, hX⟩
  intro k hk
  obtain ⟨e, he, ht⟩ := hbefore k hk
  exact ⟨e, he, ht.trans_le hdd⟩

/-- Acceptance of a descendant also accepts its ancestor at a later deadline.
DC: SAME prefix closure of finality. -/
theorem finality_acceptsFinalBefore_mono_ancestor (F : FGFinalityDurableLaws R)
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X U : FGBlock (Fin n)}
    {d d' : Time} (hXU : FGBlock.Preceq X U) (hdd : d ≤ d')
    (h : AcceptsFinalBefore R E rho x U d) : AcceptsFinalBefore R E rho x X d' := by
  have hU := finality_acceptsFinalBefore_mono_deadline R E rho F hs hdd h
  revert hU
  delta AcceptsFinalBefore Gen.V2.Duty.HoldsBefore
  exact fun hU => KitFG.preceq_trans hXU hU

/-- Durable rows remain held at a later proposal read across restore.
The held-row durability along indices and across the clock are the protocol's leaves.
DC: SAME cumulative row storage. -/
theorem finality_heldBefore_at_proposal (I : V2.D.Interface P)
    (blockWireRows : P.State → List Wire) (hs : V2.D.ScheduleWellFormed E rho)
    (durable : ∀ i j x a, i ≤ j →
      rowHeld R blockWireRows (V2.D.Run.stateBefore E rho i x) a →
      rowHeld R blockWireRows (V2.D.Run.stateBefore E rho j x) a)
    (clock : ∀ nd t a, rowHeld R blockWireRows nd a →
      rowHeld R blockWireRows (P.clock nd t) a)
    {s : Slot} {a : Wire} {d : Time} {st : P.State}
    (hst : proposalStateAt E rho I s = some st)
    (hheld : HeldBefore R E rho blockWireRows (V2.D.proposerOf rho I s) a d)
    (hd : d ≤ V2.D.proposalTime I s) : heldAtProposal R E rho I blockWireRows s a := by
  refine ⟨st, hst, ?_⟩
  have hst' : postClock E rho (V2.D.proposerOf rho I s) (V2.D.proposalTime I s) = some st :=
    hst
  rw [postClock_def, preTick_def] at hst'
  cases hj : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho I s) (V2.D.proposalTime I s) with
  | none => rw [hj] at hst'; cases hst'
  | some k =>
    rw [hj] at hst'
    have hk := V2.D.Run.tickIdx?_spec hj
    have hst'' : P.clock (V2.D.Run.stateBefore E rho k (V2.D.proposerOf rho I s))
        (V2.D.proposalTime I s) = st := Option.some.inj hst'
    have hik : V2.D.Run.idxBefore rho d ≤ k := by
      by_contra hn
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk d).mp (Nat.lt_of_not_ge hn)
      exact (not_lt.mpr hd) ht
    revert hheld
    delta HeldBefore Gen.V2.Duty.HoldsBefore
    intro hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
    rw [← hst'']
    exact clock _ _ a (durable _ _ _ a hik hheld)

end AvailableChain.FGCompose
end
