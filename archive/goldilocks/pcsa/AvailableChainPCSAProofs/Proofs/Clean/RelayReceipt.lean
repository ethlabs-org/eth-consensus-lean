module
public import AvailableChainPCSAProofs.Proofs.Clean.RelayOrigin
public import AvailableChainPCSAProofs.Proofs.Clean.RelayPersistence
public import AvailableChainPCSAProofs.Proofs.Clean.AckDecisions
public import AvailableChainPCSAProofs.Proofs.Clean.BodyRelayTime
public import AvailableChainPCSAProofs.Proofs.Shared.Count

public section

/-! C6 RelayReceipt: concrete receipt and count support. -/
namespace AvailableChain.PCSA.CleanPCRelay
variable {n : Nat}
private theorem relay_ack_decode_eq (a : AckWire n) (s : Slot) (i : Fin n) (r : BlockId)
    (hd : a.decode? = some (s, i, r)) : a = ⟨.seat (.ack s) i, r⟩ := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => cases hd
  | proposer k => cases hd
  | seat l j =>
    cases l <;> dsimp only [AckWire.decode?, Label.ackSlot?] at hd <;> simp at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    rfl
end AvailableChain.PCSA.CleanPCRelay

namespace AvailableChain.PCSA.Run
open AvailableChain.PCSA.CleanPCRelay
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- C3 assembly recovers a received certificate key once all acks and the target body are held. -/
theorem pcsa_clean_pc_from_pool (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (k : Nat) (y : V) (hy : y ∈ rho.honest)
    (C : PC p.n) (hw : C.wellFormed = true)
    (hB : C.target ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks)
    (hpool : ∀ a ∈ C.acks, a ∈ (V2.D.Run.stateBefore E rho k y).st.ackPool) :
    KeyHeld (V2.D.Run.stateBefore E rho k y).st C.slot C.target := by
  classical
  obtain ⟨hs, _, hslot, hq, hlen, hdecode⟩ := pcsa_pc_wellFormed_parts C hw
  let Q := (C.acks.filterMap AckWire.seat?).toFinset
  have hQ : pcQuorum p.n ≤ Q.card := by
    rw [← pcsa_pc_seats_card, hlen]
    exact hq
  have hp : ∀ i ∈ Q, (⟨.seat (.ack C.slot) i, C.target.root⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBefore E rho k y).st.ackPool := by
    intro i hi
    obtain ⟨a, ha, hseat⟩ := (pcsa_ack_count_witness C.acks i).mp hi
    obtain ⟨j, hj⟩ := hdecode a ha
    have hji : j = i := by
      change a.decode?.map (fun x => x.2.1) = some i at hseat
      rw [hj] at hseat
      exact Option.some.inj hseat
    subst j
    rw [← relay_ack_decode_eq a C.slot i C.target.root hj]
    exact hpool a ha
  have hh := pcsa_collect_held_target E rho h hF k y hy C.slot C.target hs hslot hB Q hQ hp
  rw [pcsa_collectPCs_eq_of_saturated _ (pcsa_saturated_stateBefore E rho k y)] at hh
  rw [KeyHeld_def]
  exact hh
/-- In the delivery window: A held PC before a public cut is relayed by key to every later honest
read within Delta. -/
theorem pcsa_pc_before_public_cut_relay_win [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (bound : Time) (hpub : V2.PublicTime E bound) (hz : 0 ≤ bound)
    (ha : a ≤ V2.D.Run.idxBefore rho bound)
    (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k) (hT : T₀ ≤ bound) (hc : bound + E.Δ ≤ cut)
    (D : PC p.n) (hDmem : D ∈ (V2.D.Run.stateBefore E rho a x).st.pcs) :
    ∃ C ∈ (V2.D.Run.stateBefore E rho k y).st.pcs, C.slot = D.slot ∧ C.target = D.target := by
  obtain ⟨i, hi, C, t, hCs, hCt, hCm, hacc⟩ := pcsa_clean_keyHeld_accepted E rho h hF x hx
    D.slot D.target a ((KeyHeld_def _ _ _).mpr ⟨D, hDmem, rfl, rfl⟩)
  obtain ⟨o, he, _⟩ := hacc.1
  have ht : t < bound := (Gen.V2.Duty.index_lt_idxBefore_iff
    h.valid.toScheduleWellFormed he bound).mp (hi.trans_le ha)
  have hiCut : i + 1 ≤ V2.D.Run.idxBefore rho bound := Nat.succ_le_of_lt (hi.trans_le ha)
  have hw := (pcsa_pc_honest_ack_before E rho h hFault (i + 1) x hx bound hiCut C hCm).1
  have hbody : C.target ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks := by
    rw [hCt]
    exact pcsa_pc_targets_held p _ (pcsa_reachable_stateBefore E rho a x) D hDmem
  have hg : C.target ≠ .genesis := (pcsa_pc_wellFormed_parts C hw).2.1
  have hs := pcsa_body_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed h.noRestart
    a x C.target bound ha hg hbody
  have hrecv := (pcsa_body_before_public_cut_relay_win E rho h hF hD (hT := hT) a k x y hx hy
      C.target bound
    hpub hz hc hk hg hbody hs).1
  have hiK : i + 1 ≤ k := by
    apply le_trans _ hk
    apply Nat.succ_le_of_lt
    apply (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he _).mpr
    exact ht.trans (lt_add_of_pos_right bound E.Δ_pos)
  have finish (hm : KeyHeld (V2.D.Run.stateBefore E rho k y).st C.slot C.target) :
      ∃ C ∈ (V2.D.Run.stateBefore E rho k y).st.pcs, C.slot = D.slot ∧ C.target = D.target := by
    rw [hCs, hCt, KeyHeld_def] at hm
    exact hm
  cases hprocessed : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (i + 1) y)
      (⟨.none, .pc C⟩ : Obj p) with
  | true =>
    apply finish
    exact pcsa_keyHeld_mono (pcsa_clean_pc_indices_mono E rho h.noRestart hF y hy
      (i + 1) k hiK) ((pcsa_clean_processed_pc _ C).mp hprocessed)
  | false =>
    obtain ⟨d, _, hdle, _, hrel⟩ := pcsa_strict_relay_from E rho hD
      (⟨.none, .pc C⟩ : Obj p) (by intro body heq; cases heq) x i t hx hacc
    have hdb : d ≤ bound + E.Δ := hdle.trans (Int.add_le_add_right (max_le ht.le hT) E.Δ)
    obtain ⟨u, _, hu, j, parent, hj, hh⟩ := hrel y hy hprocessed (hdb.trans hc) rfl
    have hjK : j + 1 ≤ k := by
      apply le_trans _ hk
      apply Nat.succ_le_of_lt
      apply (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hj _).mpr
      exact lt_of_lt_of_le hu hdb
    apply finish
    rcases pcsa_handles_pc_store _ parent C hw hh with hkey | hpool
    · rw [← pcsa_clean_deliver_succ E rho hj] at hkey
      exact pcsa_keyHeld_mono (pcsa_clean_pc_indices_mono E rho h.noRestart hF y hy
        (j + 1) k hjK) hkey
    · rw [← pcsa_clean_deliver_succ E rho hj] at hpool
      apply pcsa_clean_pc_from_pool E rho h hF k y hy C hw hrecv
      intro ack hack
      exact pcsa_ackPool_stateBefore_mono E rho h.noRestart y hjK (hpool ack hack)
/-- A held PC before a public cut is relayed by key to every later honest read within Delta. -/
theorem pcsa_pc_before_public_cut_relay [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (bound : Time) (hpub : V2.PublicTime E bound) (hz : 0 ≤ bound)
    (ha : a ≤ V2.D.Run.idxBefore rho bound)
    (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k) (hc : bound + E.Δ ≤ cut)
    (D : PC p.n) (hDmem : D ∈ (V2.D.Run.stateBefore E rho a x).st.pcs) :
    ∃ C ∈ (V2.D.Run.stateBefore E rho k y).st.pcs, C.slot = D.slot ∧ C.target = D.target :=
  pcsa_pc_before_public_cut_relay_win E rho h hF hFault (pcsa_strictFrom_of_healthy E rho hD 0) a
    k x y hx hy bound hpub hz ha hk hz hc D hDmem
end AvailableChain.PCSA.Run

end
