module
public import AvailableChainPCSAProofs.Proofs.Clean.AckDecisions
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalReceipt

public section

/-! C6 CarriedPCs: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem carried_ack_exact (a : AckWire p.n) (s : Slot) (i : Fin p.n) (r : BlockId)
    (hd : a.decode? = some (s, i, r)) : ofAck p a = ackObj p s i r := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => cases hd
  | proposer k => cases hd
  | seat l j =>
    cases l <;> dsimp only [AckWire.decode?, Label.ackSlot?] at hd <;> simp at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    rfl
private theorem carried_proposal_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) : o.payload = .proposal N := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
  | seat l i =>
    cases l with
    | prop k =>
      cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
      exact congrArg Msg.proposal h.2
    | base l => cases l <;> cases payload <;>
      dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h
/-- A carried well-formed certificate cannot precede its honest ack duty. -/
theorem pcsa_carried_pc_early_le [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (j : Nat) (x : V) (o : Obj p) (t : Time)
    (he : rho.events[j]? = some (.deliver x o t)) (C : PC p.n)
    (hw : C.wellFormed = true) (hcar : ∀ a ∈ C.acks, carriesS p o (ofAck p a)) :
    SA.earlyTime p.toParams C.slot ≤ t := by
  obtain ⟨i, hi, a, ha, hd⟩ := pcsa_pc_honest_ack rho h.cstar hFault C hw
  have hc := hcar a ha
  rw [carried_ack_exact a C.slot i C.target.root hd] at hc
  obtain ⟨t', hle, hem⟩ := h.valid.carried x o t ⟨j, he⟩ _ hc _ hi rfl
  obtain ⟨ht, _, _, _⟩ := pcsa_honest_ack_of_emission E rho h.valid.nodup _ hi
    C.slot i C.target.root t' hem
  exact ht ▸ hle
/-- A PC selected from stored proposal metadata has an earlier carrying delivery. -/
theorem pcsa_carriedPC_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) (s : Slot) (C : PC p.n)
    (hC : C ∈ carriedPCs (V2.D.Run.stateBefore E rho k x).st s) :
    C.wellFormed = true ∧ ∃ j < k, ∃ o t,
      rho.events[j]? = some (.deliver x o t) ∧ ∀ a ∈ C.acks, carriesS p o (ofAck p a) := by
  obtain ⟨hm, hv⟩ := List.mem_filter.mp hC
  have hw : C.wellFormed = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1
  refine ⟨hw, ?_⟩
  obtain ⟨w, hw, hpc⟩ := List.mem_filterMap.mp hm
  cases hd : w.decode with
  | none => rw [hd] at hpc; cases hpc
  | some msg => cases msg with
    | vote t i r => rw [hd] at hpc; cases hpc
    | row i body => rw [hd] at hpc; cases hpc
    | ack t i r => rw [hd] at hpc; cases hpc
    | pc D => rw [hd] at hpc; cases hpc
    | block t N =>
      rw [hd] at hpc
      change (if N.slot = s then N.pc else none) = some C at hpc
      split at hpc
      · obtain ⟨j, hj, t', o, u, M, P, he, hdecode, hwire, _⟩ :=
          pcsa_proposal_receipt_origin E rho k x w hw
        rw [hwire] at hd
        change some (Input.block u M) = some (Input.block t N) at hd
        have hMN : M = N := (Input.block.inj (Option.some.inj hd)).2
        subst M
        refine ⟨j, hj, o, t', he, ?_⟩
        intro a ha
        have haN : a ∈ N.pcAcks := by
          delta NamedProposal.pcAcks
          rw [hpc]
          exact ha
        delta carriesS
        left
        rw [carried_proposal_payload o u N hdecode]
        exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨a, haN, rfl⟩)))
      · cases hpc
/-- A valid carried PC has an honest ack on its exact scoped target. -/
theorem pcsa_carriedPC_honest_ack_before [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (bound : Time) (hk : k ≤ V2.D.Run.idxBefore rho bound) (C : PC p.n)
    (hC : C ∈ carriedPCs (V2.D.Run.stateBefore E rho k x).st s) :
    ∃ y, HonestAckAt p c E rho y C.slot C.target ∧
      SA.earlyTime p.toParams C.slot < bound := by
  obtain ⟨hw, j, hj, o, t, he, hcar⟩ := pcsa_carriedPC_origin E rho k x s C hC
  obtain ⟨i, hi, a, ha, hd⟩ := pcsa_pc_honest_ack rho h.cstar hFault C hw
  have hc := hcar a ha
  rw [carried_ack_exact a C.slot i C.target.root hd] at hc
  obtain ⟨t', hle, hem⟩ := h.valid.carried x o t ⟨j, he⟩ _ hc _ hi rfl
  obtain ⟨ht, B, hAck, hroot⟩ := pcsa_honest_ack_of_emission E rho h.valid.nodup _ hi
    C.slot i C.target.root t' hem
  have hvalid := (List.mem_filter.mp hC).2
  have hmem : C.target ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hvalid).1).2
  have hBs := pcsa_honestAck_body_scope E rho _ C.slot B hAck
  have hCs := pcsa_body_scope E rho k x hx C.target hmem
  have hBC := pcsa_scoped_root_eq E rho h.idealization B C.target hBs hCs hroot
  have htime : t < bound :=
    (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he bound).mp
      (lt_of_lt_of_le hj hk)
  exact ⟨_, hBC ▸ hAck, ht ▸ (hle.trans_lt htime)⟩
/-- A carried PC visible before a cut has its ack duty strictly before that cut. -/
theorem pcsa_carriedPC_early_before [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V) (s : Slot) (bound : Time)
    (hk : k ≤ V2.D.Run.idxBefore rho bound) (C : PC p.n)
    (hC : C ∈ carriedPCs (V2.D.Run.stateBefore E rho k x).st s) :
    C.wellFormed = true ∧ SA.earlyTime p.toParams C.slot < bound := by
  obtain ⟨hw, j, hj, o, t, he, hcar⟩ := pcsa_carriedPC_origin E rho k x s C hC
  have ht : t < bound :=
    (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he bound).mp
      (lt_of_lt_of_le hj hk)
  exact ⟨hw, lt_of_le_of_lt (pcsa_carried_pc_early_le E rho h hFault j x o t he C hw hcar) ht⟩
/-- No proposal-carried PC is visible before the first gate. -/
theorem pcsa_carriedPCs_before_first_gate_empty [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V) (s : Slot)
    (hk : k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams 0)) :
    carriedPCs (V2.D.Run.stateBefore E rho k x).st s = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro C hC
  obtain ⟨hw, ht⟩ := pcsa_carriedPC_early_before E rho h hFault k x s _ hk C hC
  have hpos : 0 < C.slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1).1).1).1
  have hs : (1 : Int) ≤ (C.slot : Int) := by exact_mod_cast hpos
  have hp := p.deltaPos
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * p.Δ by positivity)
  change 4 * p.Δ * (C.slot : Int) + 2 * p.Δ < 4 * p.Δ * (0 : Int) + 6 * p.Δ at ht
  nlinarith
end AvailableChain.PCSA.Run

end
