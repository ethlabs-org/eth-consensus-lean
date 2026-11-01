module
public import AvailableChainFGSARun.Model.Protocol
public import AvailableChainFGSA.Proofs.Reconcile
public import AvailableChainFGSA.Proofs.Restart
public import AvailableChainKitV2.DutyClockLaws
public import AvailableChainKitV2.DutyStable

public section

/-! [Sleep v6; P3, P24] Restore keeps durable fields and sets the wake clock. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In)

private theorem restoreClock_fold {α β : Type} (f : α → β → α)
    (now : α → Time) (xs : List β) (st : α)
    (hf : ∀ st x, now (f st x) = now st) :
    now (xs.foldl f st) = now st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

private theorem restoreClock_vote (st : GridCO.State p.n .root)
    (o : GridCO.Wire p.n .root) :
    (GridCO.admitVote p.toParams.engine st o).now = st.now := by
  dsimp only [GridCO.admitVote]
  cases o.auth <;> cases o.payload <;> dsimp only
  split <;> rfl

private theorem restoreClock_proposal (st : GridCO.State p.n .root)
    (o : GridCO.Wire p.n .root) (b : Block) (raw : List (GridCO.HeadWire p.n .root)) :
    (GridCO.admitProposal p.toParams.engine st o b raw).now = st.now := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · rfl
  · exact restoreClock_fold _ GridCO.State.now _ _
      (fun acc row => restoreClock_vote p acc (GridCO.fromHead row))

private theorem restoreClock_row (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base = st.base := by
  rcases admitRow_eq p st a with h | h <;> rw [h]

private theorem restoreClock_rows (rows : List (RowWire p.n)) (st : State p.n) :
    (rows.foldl (admitRow p) st).base = st.base := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih => rw [List.foldl_cons, ih, restoreClock_row]

private theorem restoreClock_process (st : State p.n) (o : Wire p.n) :
    (FGSA.process p st o).base.now = st.base.now := by
  dsimp only [FGSA.process]
  rcases h : o.decode with _ | (⟨s, i, b⟩ | ⟨i, body⟩ | ⟨s, N⟩)
  · rfl
  · exact restoreClock_vote p _ _
  · rw [restoreClock_row]
  · dsimp only [admitBlock]
    split
    · rfl
    · cases parentFG st N.erase <;> dsimp only
      split
      · rw [restoreClock_rows]
        split_ifs
        · exact restoreClock_proposal p _ _ _ _
        · rw [(reconcile_frame _).2.2.2.2.2.2.2.2.1]
          exact restoreClock_proposal p _ _ _ _
      · rfl

private theorem restoreClock_gate (st : State p.n) (s : Slot) :
    (gateStep p st s).base.now = st.base.now := by
  have hg (v : GridCO.State p.n .root) (a : Block) :
      (SA.Root.gateFrom p.toParams a v s).now = v.now := by
    dsimp only [SA.Root.gateFrom, GridCO.gateFrom]
    cases GridCO.confirmationFrom p.engine a v s <;> dsimp only
    split
    · rfl
    · exact restoreClock_fold _ GridCO.State.now _ _ (fun acc _ =>
        restoreClock_fold _ GridCO.State.now _ _ (fun _ _ => rfl))
  unfold gateStep normalizeS
  dsimp only
  split_ifs <;> first | rfl | exact hg _ _

private theorem restoreClock_clock (st : State p.n) (t : Time) :
    (FGSA.clock p st t).base.now = t := by
  have hc : (clockPre p st t).base.now = t := by
    unfold clockPre
    dsimp only
    split_ifs <;> rfl
  unfold FGSA.clock
  dsimp only
  split
  · rw [restoreClock_gate]; exact hc
  · exact hc

/-- The run clock is the store's base clock. -/
def fgsaClock : V2.D.Engine.ClockLaws (fgsa p c) where
  now nd := nd.st.base.now
  init := rfl
  clock nd t := restoreClock_clock p nd.st t
  process nd o := restoreClock_process p nd.st (toWire p o)
  recordOwn_now _ _ := rfl

/-- The clock projection is the base store clock. -/
theorem fgsa_clock_now (nd : Node p) : (fgsaClock p c).now nd = nd.st.base.now := by
  change nd.st.base.now = nd.st.base.now
  rfl

/-- The restarted node uses the retained-store restart. -/
theorem restore_st (d : State p.n × RecordOnce) (w : Time) :
    ((fgsa p c).restore d w).st = acRestart p d.1 w := rfl

/-- The restarted node keeps Λ. -/
theorem restore_rec (d : State p.n × RecordOnce) (w : Time) :
    ((fgsa p c).restore d w).record = d.2 := rfl

/-- Restore sets the clock to the supplied wake time. -/
theorem fgsaRestoreTimeLaw : V2.D.Engine.RestoreTimeLaw (fgsaClock p c) where
  restore_now d w := acRestart_now p d.1 w

/-- The restored clock is the exact wake time. -/
theorem fgsa_restore_now (d : State p.n × RecordOnce) (w : Time) :
    (fgsaClock p c).now ((fgsa p c).restore d w) = w :=
  (fgsaRestoreTimeLaw p c).restore_now d w

/-- The store records the supplied wake time. -/
theorem fgsa_restore_restartTime (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.restartTime = some w :=
  acRestart_restartTime p nd.st w

/-- Restore keeps the client record Λ. -/
theorem fgsa_restore_record (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).record = nd.record := rfl

/-- Restore keeps the complete FG store, including F. -/
theorem fgsa_restore_fg (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.fg = nd.st.fg :=
  acRestart_fg p nd.st w

/-- Restore keeps the signed row pool. -/
theorem fgsa_restore_rowPool (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.rowPool = nd.st.rowPool :=
  acRestart_rowPool p nd.st w

/-- Restore keeps the exact proposal wires in admission order. -/
theorem fgsa_restore_proposals (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.proposals = nd.st.proposals :=
  acRestart_proposals p nd.st w

/-- Restore keeps the named bodies derived from the proposal wires. -/
theorem fgsa_restore_namedBodies (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.namedBodies = nd.st.namedBodies := by
  unfold State.namedBodies
  rw [fgsa_restore_proposals]

/-- Restore keeps cumulative blocks. -/
theorem fgsa_restore_blocks (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.base.blocks = nd.st.base.blocks :=
  acRestart_blocks p nd.st w

/-- Restore keeps locks with their original deadlines. -/
theorem fgsa_restore_obligations (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.base.obligations =
      nd.st.base.obligations :=
  acRestart_obligations p nd.st w

/-- Restore keeps the stable record. -/
theorem fgsa_restore_stableRecord (nd : Node p) (w : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) w).st.base.stableRecord =
      nd.st.base.stableRecord :=
  acRestart_stableRecord p nd.st w

/-- Restore preserves local reachability using the retained pre-restart store. -/
theorem fgsa_restore_reachable (nd : Node p) (w : Time) (h : Reachable p nd.st) :
    Reachable p ((fgsa p c).restore ((fgsa p c).durable nd) w).st :=
  reachable_acRestart p nd.st w h

/-- Indexed stores stay reachable across clocks, deliveries and retained-store restarts. -/
theorem fgsa_reachable_stateBefore {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (i : Nat) (v : V) :
    Reachable p (V2.D.Run.stateBefore E rho i v).st := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => Reachable p nd.st) (Nat.zero_le i) v ?_ Reachable.init
  intro k e _ _ _ hv hk
  cases e with
  | restart u w =>
      change u = v at hv; subst u
      simpa only [V2.D.World.step, Function.update_self] using
        fgsa_restore_reachable p c _ w hk
  | tick u t =>
      change u = v at hv; subst u
      simpa only [V2.D.World.step, Function.update_self] using
        V2.D.Engine.tick_preserve E rho (fun nd : Node p => Reachable p nd.st)
          (fun _ _ h => h) (Reachable.tick t hk)
  | deliver u o t =>
      change u = v at hv; subst u
      simp only [V2.D.World.step, Function.update_self]
      exact Reachable.deliver (toWire p o) hk

end AvailableChain.FGSA.Run
end
