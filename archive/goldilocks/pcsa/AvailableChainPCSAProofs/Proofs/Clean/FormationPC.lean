module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRetention
public import AvailableChainPCSAProofs.Proofs.Shared.GateReceipt
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun

public section

/-! Formation step 4 with named C3 store inputs (pcsa34-r4.3 §5.3).
F1 uses a max deadline, so HealthyPrefixDeliveryBy cannot be used directly.
The remaining C3 hypotheses are hAckAdmit, hPCCollect, and hFreezeKeep.
FormationRetention closes hAckPoolMono from NoRestart.
hPCCollect must assemble the full proposal target, not only a block with
the same root. FormationAck supplies the emitted quorum from honest acks.
The participating-ack variant uses only the nodes counted by F2. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- F1 delivers an honest early ack strictly before the freeze. -/
theorem pcsa_formation_ack_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (i : Fin p.n) (y : V)
    (hi : rho.seatOf (.base (.ack s)) i ∈ rho.honest) (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i)
      (ackObj p s i N.erase.root) (SA.earlyTime p.toParams s)) :
    ∃ t, SA.earlyTime p.toParams s ≤ t ∧ t < SA.freezeTime p.toParams s ∧
      ∃ j, V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t := by
  have hs : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt h.slotPos))
  have hprev : SA.freezeTime p.toParams (s - 1) ≤ SA.earlyTime p.toParams s := by
    have hd := p.deltaPos
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    nlinarith
  have hdl : max (SA.earlyTime p.toParams s) (SA.freezeTime p.toParams (s - 1)) + E.Δ =
      SA.freezeTime p.toParams s := by
    rw [max_eq_left hprev, h.base.delta]
    change (4 * p.Δ * (s : Int) + 2 * p.Δ) + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hh := h.delivery.broadcast _ hi (ackObj p s i N.erase.root)
    (show IsNonRow (ackObj p s i N.erase.root) from True.intro) _ he y hy
    (by rw [hdl])
    (pcsa_ack_not_excluded _ s i N.erase.root)
  simpa only [hdl] using hh

/-- Strict F1 receipt and the remaining C3 store inputs give the stamped Formation PC. -/
theorem pcsa_formation_pc_of_store_facts (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hAck : ∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
      HonestAckAt p c E rho y s N.erase)
    (hAckAdmit : ∀ y ∈ rho.honest, ∀ (i : Fin p.n) j t,
      rho.seatOf (.base (.ack s)) i ∈ rho.honest →
      SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t →
      (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool)
    (hPCCollect : ∀ y ∈ rho.honest, ∀ Q : Finset (Fin p.n),
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card →
      ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = N.erase)
    (hFreezeKeep : ∀ y ∈ rho.honest,
      (collectPCs (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).pcs ⊆
        (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs) :
    ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase := by
  obtain ⟨Q, hQ, hAckEmits⟩ := pcsa_formation_ack_quorum E rho s N ΔF h hAck
  intro y hy
  have hp : ∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.ackPool := by
    intro i hi
    obtain ⟨t, het, htz, j, hh⟩ := pcsa_formation_ack_receipt E rho s N ΔF h i y
      (hAckEmits i hi).1 hy (hAckEmits i hi).2
    have ha := hAckAdmit y hy i j t (hAckEmits i hi).1 het htz hh
    obtain ⟨parent, hj, _⟩ := hh
    have hjz : j < V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed hj _).mpr htz
    have hm := pcsa_formation_run_ackPool_mono E rho h.base.noRestart y (j + 1) _
      (Nat.succ_le_of_lt hjz) ha
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.base.valid.toScheduleWellFormed] at hm
    exact hm
  obtain ⟨C, hC, hs, ht⟩ := hPCCollect y hy Q hp hQ
  exact ⟨C, hFreezeKeep y hy hC, hs, ht⟩

/-- F1 and the three C3 facts stamp the PC from participating acks.
A node that wakes only at e_s need not ack for this PC conclusion. -/
theorem pcsa_formation_pc_of_participating_acks (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hAck : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
      E.awake y (SA.earlyTime p.toParams s) = true → HonestAckAt p c E rho y s N.erase)
    (hAckAdmit : ∀ y ∈ rho.honest, ∀ (i : Fin p.n) j t,
      rho.seatOf (.base (.ack s)) i ∈ rho.honest →
      SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t →
      (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool)
    (hPCCollect : ∀ y ∈ rho.honest, ∀ Q : Finset (Fin p.n),
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card →
      ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = N.erase)
    (hFreezeKeep : ∀ y ∈ rho.honest,
      (collectPCs (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).pcs ⊆
        (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs) :
    ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase := by
  obtain ⟨Q, hQ, hAckEmits⟩ := pcsa_formation_participating_ack_quorum E rho s N ΔF h hAck
  intro y hy
  have hp : ∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.ackPool := by
    intro i hi
    obtain ⟨t, het, htz, j, hh⟩ := pcsa_formation_ack_receipt E rho s N ΔF h i y
      (hAckEmits i hi).1 hy (hAckEmits i hi).2
    have ha := hAckAdmit y hy i j t (hAckEmits i hi).1 het htz hh
    obtain ⟨parent, hj, _⟩ := hh
    have hjz : j < V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed hj _).mpr htz
    have hm := pcsa_formation_run_ackPool_mono E rho h.base.noRestart y (j + 1) _
      (Nat.succ_le_of_lt hjz) ha
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.base.valid.toScheduleWellFormed] at hm
    exact hm
  obtain ⟨C, hC, hs, ht⟩ := hPCCollect y hy Q hp hQ
  exact ⟨C, hFreezeKeep y hy hC, hs, ht⟩

/-- A stamped Formation PC is in the complete snapshot frozen at z_s. -/
theorem pcsa_formation_snapshot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (hy : y ∈ rho.honest)
    (hPC : PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) :
    ∃ C ∈ pcSnapshotAt (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)) s,
      C.slot = s ∧ C.target = N.erase := by
  rw [snapshot_afterTicks E rho h.base.valid.toScheduleWellFormed h.base.delta y hy s
    h.horizon]
  exact hPC

end AvailableChain.PCSA.Run
end
