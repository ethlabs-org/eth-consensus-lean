module
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainGeneric.Proofs.Pure.PCQuorum

public section

/-! HEAD uniqueness and the support of an ack (pcsa34-r4.3 §5.1; proof plan C1). -/

namespace AvailableChain.PCSA.Run

/-- Only the HEAD duty uses the HEAD signing label of a slot. -/
theorem signLabel_head_iff (d : RunDuty) (s : Slot) :
    d.signLabel = .base (.head s) ↔ d = .headAction s := by
  cases d <;> dsimp only [RunDuty.signLabel] <;> simp

/-- The HEAD label fixes both its duty and its emission time. -/
theorem head_emission_duty (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (t : Time) (k : Nat)
    (hk : rho.events[k]? = some (.tick x t))
    (ho : (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) ∈ V2.D.Run.emitsAt E rho k) :
    t = SA.voteTime p.toParams s ∧
      actWith m p c ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k x) t)
        (.headAction s) (rho.input x t) = some (.head r) := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, ht, ha⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.base (.head s)) i (.head r)).mp ho
  have hd := (signLabel_head_iff d s).mp hl
  subst d
  exact ⟨ht.symm, ha⟩

/-- One tick and one HEAD duty give one root per slot and seat. -/
theorem head_emission_unique (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hnd : rho.events.Nodup)
    (x : V) (s : Slot) (i : Fin p.n) (r r' : BlockId) (t t' : Time)
    (h : V2.D.Run.emits E rho x (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t)
    (h' : V2.D.Run.emits E rho x (⟨.seat (.base (.head s)) i, .head r'⟩ : Obj p) t') :
    r = r' ∧ t = t' ∧ t = SA.voteTime p.toParams s := by
  obtain ⟨k, hk, ho⟩ := h
  obtain ⟨k', hk', ho'⟩ := h'
  obtain ⟨ht, ha⟩ := head_emission_duty p c m E rho x s i r t k hk ho
  obtain ⟨ht', ha'⟩ := head_emission_duty p c m E rho x s i r' t' k' hk' ho'
  have he : t = t' := ht.trans ht'.symm
  cases he
  have hklt := (List.getElem?_eq_some_iff.mp hk).1
  have heq : k = k' := (List.Nodup.getElem?_inj hklt hnd).mp (hk.trans hk'.symm)
  subst k'
  have hr : some (Msg.head r : Msg p.n) = some (Msg.head r') := ha.symm.trans ha'
  exact ⟨by simpa only [Option.some.injEq, Msg.head.injEq] using hr, rfl, ht⟩


/-- An emitted ack has an N target in the state read by its duty. -/
theorem ack_emission_nTarget (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (t : Time) (k : Nat)
    (hk : rho.events[k]? = some (.tick x t))
    (ho : ackObj p s i r ∈ V2.D.Run.emitsAt E rho k) :
    ∃ b, b.root = r ∧ nTarget? p
      (clock p (V2.D.Run.stateBefore E rho k x).st t) s = some b := by
  obtain ⟨_, ha⟩ := ack_emission_duty p c m E rho x s i r t k hk ho
  have heq := actWith_def m p c
    ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k x) t)
    (.ackAction s) (rho.input x t)
  rw [heq] at ha
  change (ackFor p (clock p (V2.D.Run.stateBefore E rho k x).st t) s).map
    (fun b => Msg.ack b.root) = some (.ack r) at ha
  obtain ⟨b, hb, hr⟩ := Option.map_eq_some_iff.mp ha
  exact ⟨b, Msg.ack.inj hr, (Option.filter_eq_some_iff.mp hb).1⟩


/-- An N target has q_N distinct exact HEAD seats in the cumulative vote pool. -/
theorem nTarget_support (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (hb : nTarget? p st s = some b) :
    ∃ S : Finset (Fin p.n), Gen.Pure.qN p.n ≤ S.card ∧ ∀ i ∈ S,
      (⟨.seat s i, .head b.root⟩ : GridCO.Wire p.n .root) ∈ st.base.votes := by
  classical
  have hn := List.find?_some hb
  have hcount : nQuorum p.n ≤ nCount p (actView st) s b :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hn).2
  let votes := (timelyHeads p (actView st) s).filter
    (fun o => GridCO.resolvedHead? (actView st) o == some b)
  let S := (GridCO.seats p.n votes).toFinset
  refine ⟨S, ?_, ?_⟩
  · change Gen.Pure.qN p.n ≤ (GridCO.seats p.n votes).toFinset.card
    rw [List.toFinset_card_of_nodup
      (show (GridCO.seats p.n votes).Nodup from List.nodup_dedup _)]
    exact hcount
  · intro i hi
    have hi' : i ∈ votes.filterMap GridCO.headSeat? := by
      simpa only [S, GridCO.seats, List.mem_toFinset, List.mem_dedup] using hi
    obtain ⟨o, ho, hseat⟩ := List.mem_filterMap.mp hi'
    have hres : GridCO.resolvedHead? (actView st) o = some b :=
      beq_iff_eq.mp (List.mem_filter.mp ho).2
    have ht := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
    have hv := (List.mem_filter.mp ht).1
    have hlabel : GridCO.headLabel? o = some s := beq_iff_eq.mp (List.mem_filter.mp hv).2
    have hmem : o ∈ st.base.votes := (List.mem_filter.mp hv).1
    have hshape : ∃ r, o = ⟨.seat s i, .head r⟩ := by
      rcases o with ⟨auth, payload⟩
      cases auth <;> cases payload <;>
        dsimp only [GridCO.headSeat?, GridCO.headLabel?] at hseat hlabel <;>
        simp at hseat hlabel
      obtain rfl := hseat
      obtain rfl := hlabel
      exact ⟨_, rfl⟩
    obtain ⟨r, rfl⟩ := hshape
    change ((Block.findByRoot? (GridCO.resolutionTree (actView st)) r).bind
      (fun B => if B ∈ (actView st).blocks then some B else none)) = some b at hres
    obtain ⟨B, hB, hr⟩ := Option.bind_eq_some_iff.mp hres
    split at hr
    · have he : B = b := Option.some.inj hr
      subst B
      have he := Block.findByRoot?_root hB
      rwa [he]
    · contradiction

end AvailableChain.PCSA.Run
end
