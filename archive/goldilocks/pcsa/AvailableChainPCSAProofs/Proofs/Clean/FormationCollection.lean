module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSourceRetention
public import AvailableChainFGSA.Proofs.HeadResolution
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun

public section

/-! Formation collection from the required early N counts. A passing count
resolves the full target body. NoRestart retains it until the freeze. Shared
CollectClosed supplies its PC key from pooled quorum acks. The two PC
consumers need hAckAdmit and the early N-count conclusion of C7; they no
longer need hPCCollect. The early N-count producer remains open. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA
variable {n : Nat}
/-- Shared collection closure installs the full stored quorum target. -/
theorem pcsa_formation_collect_of_target (st : State n) (s : Slot) (B : Block)
    (hClosed : CollectClosed st) (hF : st.fg.F = .genesis)
    (hs : 0 < s) (hB : B ∈ st.base.blocks) (hslot : B.slot = s)
    (Q : Finset (Fin n))
    (hpool : ∀ i ∈ Q, (⟨.seat (.ack s) i, B.root⟩ : AckWire n) ∈ st.ackPool)
    (hQ : pcQuorum n ≤ Q.card) :
    ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = B := by
  classical
  let C : PC n := ⟨s, B, Q.toList.map (fun i => ⟨.seat (.ack s) i, B.root⟩)⟩
  have hgen : B ≠ .genesis := by
    intro he
    rw [he] at hslot
    change 0 = s at hslot
    exact (Nat.ne_of_gt hs) hslot.symm
  have hseats : C.seats = Q.toList := by
    change ((Q.toList.map (fun i =>
      (⟨.seat (.ack s) i, B.root⟩ : AckWire n))).filterMap AckWire.seat?).dedup = _
    have he : (Q.toList.map (fun i =>
        (⟨.seat (.ack s) i, B.root⟩ : AckWire n))).filterMap AckWire.seat? = Q.toList := by
      rw [List.filterMap_map]
      change Q.toList.filterMap (fun i => some i) = Q.toList
      simp only [List.filterMap_some]
    rw [he, List.dedup_eq_self.mpr Q.nodup_toList]
  have hw : C.wellFormed = true := by
    apply pcsa_pc_wellFormed_of C hs hgen hslot
    · change pcQuorum n ≤ (Q.toList.map _).length
      simpa only [List.length_map, Finset.length_toList] using hQ
    · rw [hseats]
      exact (List.length_map _).symm
    · intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact ⟨i, rfl⟩
  have hf : activeCompatible st B = true := by
    change Block.compatible B (eraseFG st.fg.F) = true
    rw [hF]
    exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq B))
  obtain ⟨D, hd⟩ := pcsa_assemblePC_of_pool st C hw (by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hpool i (Finset.mem_toList.mp hi)) hB hf
  obtain ⟨A, ha, has, hab⟩ := (KeyHeld_def _ _ _).mp
    ((CollectClosed_def st).mp hClosed s B D hB hd)
  exact ⟨A, collectPCs_pcs_mono st ha, has, hab⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}
omit [Fintype V] in
/-- An early N count supplies the full target before the freeze. -/
theorem pcsa_formation_target_before_freeze_of_n_count (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho) (y : V)
    (s : Slot) (P : Block) (nd : Node p)
    (hr : pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd)
    (hN : holdsN p (actView nd.st) s P = true) :
    P ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.base.blocks := by
  obtain ⟨o, _, ho⟩ := pcsa_formation_n_witness p (actView nd.st) s P hN
  have hb := FGSA.resolvedHead_mem (actView nd.st) o ho
  change P ∈ nd.st.base.blocks.filter (activeCompatible nd.st) at hb
  have hb' := (List.mem_filter.mp hb).1
  have hread := pcsa_formation_read_afterTicks E rho hBase.valid.toScheduleWellFormed y _ nd hr
  rw [← hread] at hb'
  change P ∈ (FGSA.Run.afterTicks E rho (SA.earlyTime p.toParams s) y).st.base.blocks at hb'
  rw [FGSA.Run.afterTicks_eq_stateBefore E rho hBase.valid.toScheduleWellFormed] at hb'
  have htz : SA.earlyTime p.toParams s < SA.freezeTime p.toParams s := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
    nlinarith
  have hle : FGSA.Run.afterTicksIdx rho (SA.earlyTime p.toParams s) ≤
      V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) := by
    apply le_trans (FGSA.Run.preIdx_le_afterTicksIdx E rho hBase.valid.toScheduleWellFormed _).2
    rw [V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    exact decide_eq_true ((of_decide_eq_true he).trans_lt htz)
  have hm := pcsa_formation_run_blocks_mono E rho hBase.noRestart y _ _ hle hb'
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hBase.valid.toScheduleWellFormed] at hm
  exact hm

/-- C7 early N counts discharge hPCCollect at every honest receiver. -/
theorem pcsa_formation_pcCollect_of_n_counts (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hN : ∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
      holdsN p (actView nd.st) s N.erase = true) :
    ∀ y ∈ rho.honest, ∀ Q : Finset (Fin p.n),
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card → ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = N.erase := by
  obtain ⟨src, _, hslot, _, _⟩ := pcsa_formation_base_below_parent E rho s N ΔF h
  intro y hy Q
  dsimp only
  intro hp hq
  obtain ⟨nd, hr, hn⟩ := hN y hy
  have hc := pcsa_collectClosed_stateBefore E rho h.base y hy
    (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s))
  have hf := (h.frame y hy (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s))).1
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.base.valid.toScheduleWellFormed] at hc hf
  exact pcsa_formation_collect_of_target _ s N.erase hc hf h.slotPos
    (pcsa_formation_target_before_freeze_of_n_count E rho h.base y s N.erase nd hr hn) hslot Q hp hq
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}
/-- Early N counts replace hPCCollect in the all-early PC consumer. -/
theorem pcsa_formation_pc_of_n_counts (E : Generic.Env V)
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
    (hN : ∀ y ∈ rho.honest, ∃ nd,
      pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
        holdsN p (actView nd.st) s N.erase = true) :
    ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase := by
  exact pcsa_formation_pc_of_store_facts_retained E rho s N ΔF h hAck hAckAdmit
    (pcsa_formation_pcCollect_of_n_counts E rho s N ΔF h hN)

/-- Early N counts replace hPCCollect in the participating-ack consumer. -/
theorem pcsa_formation_pc_of_participating_acks_n_counts (E : Generic.Env V)
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
    (hN : ∀ y ∈ rho.honest, ∃ nd,
      pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
        holdsN p (actView nd.st) s N.erase = true) :
    ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase := by
  exact pcsa_formation_pc_of_participating_acks_retained E rho s N ΔF h hAck hAckAdmit
    (pcsa_formation_pcCollect_of_n_counts E rho s N ΔF h hN)

end AvailableChain.PCSA.Run

end
