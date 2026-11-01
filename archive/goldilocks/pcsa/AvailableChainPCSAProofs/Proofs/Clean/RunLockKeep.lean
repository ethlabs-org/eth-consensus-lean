module
public import AvailableChainPCSAProofs.Proofs.Clean.ProcessLockRetention
public import AvailableChainPCSAProofs.Proofs.Clean.GateLockRetention
public import AvailableChainPCSAProofs.Proofs.Clean.StorePCInputs
public import AvailableChainPCSAProofs.Proofs.Clean.ReleaseCount
public import AvailableChainPCSAProofs.Proofs.Clean.RootSources
public import AvailableChainPCSAProofs.Proofs.Clean.RelayOrigin

public section

/-! C6 RunLockKeep: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A release before the next vote has a strictly earlier label. -/
theorem pcsa_release_label_before_vote (p : Params) (r j : Slot)
    (ht : SA.releaseTime p.toParams r < SA.voteTime p.toParams (j + 1)) : r < j := by
  by_contra hn
  have hr : (j : Int) ≤ (r : Int) := Int.ofNat_le.mpr (Nat.le_of_not_gt hn)
  change 4 * p.Δ * (r : Int) + 5 * p.Δ <
    4 * p.Δ * ((j + 1 : Nat) : Int) + p.Δ at ht
  push_cast at ht
  have hp : (0 : Int) < p.Δ := p.deltaPos
  nlinarith
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- Earlier-result HEAD coverage and ack/result compatibility preserve every bounded live lock. -/
theorem pcsa_lock_keep_of_chain (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) (j : Slot)
    (hpast : ∀ r, r ≤ j → ∀ z H, HonestHeadAt p c E rho z r H →
      ∀ y ∈ rho.honest, ∀ i X, i < r →
        gateResultAt p c E rho y i = some (some X) → Block.Preceq X H)
    (hcompat : ∀ s, s ≤ j → ∀ z B, HonestAckAt p c E rho z s B →
      ∀ i, i ≤ j → ∀ y ∈ rho.honest, ∀ X,
        gateResultAt p c E rho y i = some (some X) → Block.Compatible B X)
    (x : V) (hx : x ∈ rho.honest) (k : Nat) (e : V2.Event V (Obj p))
    (he : rho.events[k]? = some e) (ht : e.time < SA.voteTime p.toParams (j + 1))
    (row : Block × Nat × Time) (hr : row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations)
    (hlive : e.time < row.2.2) :
    ∃ row' ∈ (V2.D.Run.stateBefore E rho (k + 1) x).st.base.obligations, row'.1 = row.1 := by
  have hidx : k + 1 ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams (j + 1)) :=
    Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he _).mpr
      ht)
  by_cases hn : e.node = x
  · cases e with
    | restart y t => exact (h.noRestart k y t he).elim
    | tick y t =>
      change y = x at hn
      subst y
      have hclock : (V2.D.Run.stateBefore E rho (k + 1) x).st =
          clock p (V2.D.Run.stateBefore E rho k x).st t := by
        rw [V2.D.Run.stateBefore_succ E rho he]
        change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
        rw [Function.update_self]
        exact pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
      rw [hclock]
      apply pcsa_clock_keep_lock_target p _ t row hr hlive
      intro r hrelease
      have hrj := pcsa_release_label_before_vote p r j (by rw [← hrelease]; exact ht)
      have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime h.valid.toScheduleWellFormed
        h.noRestart he
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.valid.toScheduleWellFormed] at hpre
      have hrow := hr
      rw [hpre] at hrow
      obtain ⟨a, ha, i, X, hai, hX, hrowX, hlevel⟩ :=
        pcsa_lock_stateBefore_origin E rho h _ x row hrow
      have hgate := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hai t).mp ha
      have htime : SA.releaseTime p.toParams r = SA.voteTime p.toParams (r + 1) := by
        change 4 * p.Δ * (r : Int) + 5 * p.Δ = 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
        push_cast
        ring
      have hir := pcsa_gate_label_lt_next_vote p i r (by rw [← htime, ← hrelease]; exact hgate)
      have hheads : ∀ z H, HonestHeadAt p c E rho z r H → Block.Compatible H row.1 := by
        intro z H hH
        exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_trans hrowX
          (hpast r hrj.le z H hH x hx i X hir hX)))
      have hcount := pcsa_release_count_fault_bound E rho h hF k x hx t r row.1 hheads
      rw [hlevel]
      exact hcount.trans_lt hFault
    | deliver y o t =>
      change y = x at hn
      subst y
      have hpost := pcsa_clean_deliver_succ E rho he
      have hf := (hF x hx (k + 1)).1
      rw [hpost] at hf
      obtain ⟨a, ha, i, X, hai, hX, hrowX, _⟩ := pcsa_lock_stateBefore_origin E rho h k x row hr
      have hgate := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hai _).mp
        (ha.trans_le ((Nat.le_succ k).trans hidx))
      have hij := (pcsa_gate_label_lt_next_vote p i j hgate).le
      have down (B : Block) (hc : Block.Compatible B X) : Block.Compatible B row.1 := by
        rcases Bool.or_eq_true_iff.mp hc with hBX | hXB
        · exact Gen.Pure.block_compatible_of_common hBX hrowX
        · exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_trans hrowX hXB))
      rw [hpost]
      refine ⟨row, pcsa_process_keep_lock p _ (toWire p o) row hr hf ?_ ?_, rfl⟩
      · intro C hC
        rw [← hpost] at hC
        obtain ⟨hs, z, hAck⟩ := pcsa_pc_index_ack_slot E rho h hFault j (k + 1) x hx hidx C hC
        exact down C.target (hcompat C.slot hs z C.target hAck i hij x hx X hX)
      · intro s C hC
        rw [← hpost] at hC
        obtain ⟨hs, z, hAck⟩ := pcsa_carriedPC_index_ack_slot E rho h hFault j (k + 1) x hx hidx s
          C hC
        exact down C.target (hcompat C.slot hs z C.target hAck i hij x hx X hX)
  · rw [V2.D.Run.stateBefore_succ E rho he,
      V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hn]
    exact ⟨row, hr, rfl⟩
end AvailableChain.PCSA.Run

end
