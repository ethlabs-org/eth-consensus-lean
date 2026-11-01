module
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAProofs.Proofs.Shared.GateReceipt
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAProofs.Proofs.Shared.Clock
public import AvailableChainPCSAProofs.Proofs.Clean.Saturation
public import AvailableChainPCSAProofs.Proofs.Shared.BodyScope
public import AvailableChainPCSAProofs.Proofs.Clean.AckEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.AckStore
public import AvailableChainFGSA.Proofs.HeadResolution

public section

/-! C3 honest ack admission and Formation hAckAdmit. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

theorem pcsa_seat_roots (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.ExecutionValid E rho) (j : Nat) (y : V) (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.ack s)) i ∈ rho.honest) (r : BlockId) (t : Time)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r) t) :
    ∀ r' ∈ seatAcks (V2.D.Run.stateBefore E rho j y).st s i, r' = r := by
  intro r' hr
  change r' ∈ (_ : List BlockId).eraseDups at hr
  obtain ⟨a, ha, hd⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp hr)
  cases hdec : a.decode? with
  | none => rw [hdec] at hd; cases hd
  | some v =>
    rcases v with ⟨s', i', r''⟩
    rw [hdec] at hd
    dsimp only at hd
    split at hd
    · rename_i hh
      have hx : s' = s ∧ i' = i := by simpa only [Bool.and_eq_true, beq_iff_eq] using hh
      obtain ⟨rfl, rfl⟩ := hx
      obtain rfl := Option.some.inj hd
      obtain ⟨t', ht'⟩ := pcsa_pool_honest_emits E rho hv.toUnforgeableSignatures
        j y a ha s' i' r'' hdec hi
      exact (ack_emission_unique p c m E rho hv.nodup _ s' i' r'' r t' t ht' he).1
    · cases hd

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA
/-- Admission passes when every old root for the seat is the offered root. -/
theorem pcsa_poolAck_one_root (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n)
    (r : BlockId) (hs : s ≤ st.slot p) (hr : ackSlotOK st s r = true)
    (hroots : ∀ r' ∈ seatAcks st s i, r' = r) :
    (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈
      (admitAck p st (⟨.seat (.ack s) i, r⟩ : AckWire p.n)).ackPool := by
  change _ ∈ (collectPCs (poolAck p st _)).ackPool
  rw [(collectPCs_frame _).2.2.1]
  delta poolAck
  change _ ∈ (if st.slot p < s || !ackSlotOK st s r ||
      decide ((⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈ st.ackPool) then st else
    if 2 ≤ (seatAcks st s i).length && !decide (r ∈ seatAcks st s i) then st else
      { st with ackPool := st.ackPool ++ [(⟨.seat (.ack s) i, r⟩ : AckWire p.n)] }).ackPool
  simp only [show ¬st.slot p < s from Nat.not_lt.mpr hs, decide_false, hr,
    Bool.not_true, Bool.false_or]
  split
  · exact of_decide_eq_true ‹_›
  · split
    · rename_i h
      have hlen : 2 ≤ (seatAcks st s i).length :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
      have hnot : r ∉ seatAcks st s i := by
        simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using
          (Bool.and_eq_true_iff.mp h).2
      have hempty : seatAcks st s i = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro r' hm
        exact hnot (hroots r' hm ▸ hm)
      rw [hempty, List.length_nil] at hlen
      omega
    · exact List.mem_append_right _ (by simp)
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem pcsa_ofAck_exact (a : AckWire p.n) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : ofAck p a = ackObj p s i r) : a = ⟨.seat (.ack s) i, r⟩ := by
  have he : (⟨a.auth, .ack a.payload⟩ : Wire p.n) = ⟨.seat (.ack s) i, .ack r⟩ :=
    (toWireEquiv p).symm.injective h
  have ha := congrArg (fun w : Wire p.n => w.auth) he
  have hr := Msg.ack.inj (congrArg (fun w : Wire p.n => w.payload) he)
  cases a
  cases ha
  cases hr
  rfl
private theorem pcsa_raw_mem (st : State p.n) (as : List (AckWire p.n)) (a : AckWire p.n)
    (ha : a ∈ as) (hd : ∃ s i r, a.decode? = some (s, i, r)) :
    a ∈ (as.foldl poolAckRaw st).ackPool := by
  induction as generalizing st with
  | nil => cases ha
  | cons b bs ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with he | ha
    · subst b
      obtain ⟨s, i, r, hh⟩ := hd
      exact pcsa_fold_poolAckRaw_mono _ _ (poolAckRaw_mem st a s i r hh)
    · exact ih _ ha

theorem pcsa_handled_ack_pool (st : State p.n) (o : Obj p) (s : Slot) (i : Fin p.n)
    (r : BlockId) (hw : (pcsaWith m p c).wellFormed o = true)
    (hh : (pcsaWith m p c).handles ⟨st, SimplexFG.RecordOnce.initial⟩ o (ackObj p s i r))
    (hs : s ≤ st.slot p) (hr : ackSlotOK st s r = true)
    (hroots : ∀ r' ∈ seatAcks st s i, r' = r) :
    (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈ (process p st (toWire p o)).ackPool := by
  change handlesS p st o (ackObj p s i r) at hh
  delta handlesS at hh
  rcases hh with he | hh | hh
  · subst o
    exact pcsa_poolAck_one_root p st s i r hs hr hroots
  · cases hd : (toWire p o).decode with
    | none => rw [hd] at hh; cases hh
    | some msg => cases msg with
      | vote t j root => rw [hd] at hh; cases hh
      | row j body => rw [hd] at hh; cases hh
      | ack t j root => rw [hd] at hh; cases hh
      | pc C =>
        rw [hd] at hh
        obtain ⟨a, ha, he⟩ := List.mem_map.mp hh
        obtain rfl := pcsa_ofAck_exact a s i r he
        have hC : C.wellFormed = true := by
          change wellFormed p (toWire p o) = true at hw
          delta wellFormed at hw
          rwa [hd] at hw
        delta process
        rw [hd]
        dsimp only
        delta admitPC
        rw [hC]
        simp only [ite_true]
        rw [(collectPCs_frame _).2.2.1]
        exact pcsa_raw_mem st C.acks _ ha ⟨s, i, r, rfl⟩
      | block t N =>
        rw [hd] at hh
        obtain ⟨⟨hn, P, hp, hb⟩, hh⟩ := hh
        rcases hh with hh | hh | hh
        · obtain ⟨a, _, he⟩ := List.mem_map.mp hh
          have he' := congrArg (fun o : Obj p => o.payload) he
          change Msg.head _ = Msg.ack _ at he'
          cases he'
        · obtain ⟨a, _, he⟩ := List.mem_map.mp hh
          have he' := congrArg (fun o : Obj p => o.payload) he
          change Msg.row _ = Msg.ack _ at he'
          cases he'
        · obtain ⟨a, ha, he⟩ := List.mem_map.mp hh
          obtain rfl := pcsa_ofAck_exact a s i r he
          delta process
          rw [hd]
          dsimp only
          have hrw (acc : State p.n) (as : List (RowWire p.n)) :
              (as.foldl (admitRow p) acc).ackPool = acc.ackPool := by
            apply List.foldlRecOn (motive := fun st : State p.n => st.ackPool = acc.ackPool)
            · rfl
            · intro st hh a _
              delta admitRow
              cases a.decode? <;> dsimp only <;> first | exact hh | split <;> exact hh
          delta admitBlock
          split
          · rename_i hdeny
            rw [hn] at hdeny
            contradiction
          · cases hparent : parentFG st N.erase with
            | none => rw [hparent] at hp; cases hp
            | some Q =>
              rw [hparent] at hp
              have hQP : Q = P := Option.some.inj hp
              subst Q
              dsimp only
              split
              · cases N.pc <;> dsimp only
                all_goals rw [hrw, (collectPCs_frame _).2.2.1]
                all_goals exact pcsa_raw_mem _ N.pcAcks _ ha ⟨s, i, r, rfl⟩
              · exact (‹¬ blockAccepted p st t N P = true› hb).elim
  · obtain ⟨_, C, he, _, _⟩ := hh
    have hp := congrArg (fun o : Obj p => o.payload) he
    cases hp

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem pcsa_decoded_payloads_ack (o : Obj p) :
    (∀ s N, (toWire p o).decode = some (.block s N) → o.payload = .proposal N) ∧
    (∀ C, (toWire p o).decode = some (.pc C) → o.payload = .pc C) := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] <;> simp
  | seat l j =>
    cases l with
    | prop k => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] <;> simp
    | base l => cases l <;> cases payload <;>
      dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] <;> simp
/-- Every handled child is the delivered object or a carried object. -/
theorem pcsa_handles_carried (st : State p.n) (o child : Obj p)
    (hh : handlesS p st o child) : child = o ∨ carriesS p o child := by
  delta handlesS at hh
  rcases hh with hh | hh | hh
  · exact Or.inl hh.symm
  · right
    cases hd : (toWire p o).decode with
    | none => rw [hd] at hh; cases hh
    | some msg => cases msg with
      | vote s i r => rw [hd] at hh; cases hh
      | ack s i r => rw [hd] at hh; cases hh
      | row i body => rw [hd] at hh; cases hh
      | pc C =>
        rw [hd] at hh
        delta carriesS
        left
        rw [(pcsa_decoded_payloads_ack o).2 C hd]
        exact hh
      | block s N =>
        rw [hd] at hh
        delta carriesS
        left
        rw [(pcsa_decoded_payloads_ack o).1 s N hd]
        rcases hh.2 with hh | hh | hh
        · exact Or.inl hh
        · exact Or.inr (Or.inr (Or.inl hh))
        · exact Or.inr (Or.inr (Or.inr hh))
  · exact Or.inr hh.1
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- An ack emission names an N target in the duty state. -/
theorem pcsa_ack_emission_nTarget (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (t : Time) (k : Nat)
    (hk : rho.events[k]? = some (.tick x t))
    (ho : ackObj p s i r ∈ V2.D.Run.emitsAt E rho k) :
    ∃ B, B.root = r ∧ nTarget? p
      (clock p (V2.D.Run.stateBefore E rho k x).st t) s = some B := by
  obtain ⟨_, ha⟩ := ack_emission_duty p c m E rho x s i r t k hk ho
  have heq := actWith_def m p c
    ((pcsaWith m p c).clock (V2.D.Run.stateBefore E rho k x) t)
    (.ackAction s) (rho.input x t)
  rw [heq] at ha
  change (ackFor p (clock p (V2.D.Run.stateBefore E rho k x).st t) s).map
    (fun B => Msg.ack B.root) = some (.ack r) at ha
  obtain ⟨B, hb, hr⟩ := Option.map_eq_some_iff.mp ha
  exact ⟨B, Msg.ack.inj hr, (Option.filter_eq_some_iff.mp hb).1⟩

theorem pcsa_ack_root_slotOK (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (t : Time) (j : Nat)
    (he : V2.D.Run.emits E rho x (ackObj p s i r) t) :
    ackSlotOK (V2.D.Run.stateBefore E rho j y).st s r = true := by
  obtain ⟨k, hk, ho⟩ := he
  obtain ⟨B, hroot, hn⟩ := pcsa_ack_emission_nTarget p c m E rho x s i r t k hk ho
  have hslot : B.slot = s := by
    have hh := List.find?_some hn
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hh).1
  have hmem : B ∈ (clock p (V2.D.Run.stateBefore E rho k x).st t).base.blocks := by
    obtain ⟨o, _, hb⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some hn)
    exact (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hb)).1
  have hB := pcsa_clock_body_scope p (RootBlockInRun p c E rho)
    (V2.D.Run.stateBefore E rho k x).st t (pcsa_body_scope E rho k x hx) B hmem
  have hdst := pcsa_body_scope E rho j y hy
  delta ackSlotOK
  cases hf : (V2.D.Run.stateBefore E rho j y).st.base.blocks.find? (fun b => b.root == r) with
  | none => rfl
  | some D =>
    dsimp only
    have hD := hdst D (List.mem_of_find?_eq_some hf)
    have hr' : (D.root == r) = true := List.find?_some (p := fun b : Block => b.root == r) hf
    have hr : D.root = B.root := (beq_iff_eq.mp hr').trans hroot.symm
    rw [pcsa_scoped_root_eq E rho h.idealization D B hD hB hr, hslot]
    exact BEq.rfl

theorem pcsa_ack_receiver_slot (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (j : Nat) (y : V) (o : Obj p) (t : Time) (s : Slot)
    (hj : rho.events[j]? = some (.deliver y o t))
    (ht : SA.earlyTime p.toParams s ≤ t) :
    s ≤ (V2.D.Run.stateBefore E rho j y).st.slot p := by
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = ((4 * s + 2 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hzero : 0 ≤ SA.earlyTime p.toParams s := by
    have := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  have hn := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho
    h.valid.toScheduleWellFormed h.noRestart hj hpub hzero ht
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j y)] at hn
  change SA.earlyTime p.toParams s ≤ (V2.D.Run.stateBefore E rho j y).st.base.now at hn
  change s ≤ ((V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ)).toNat
  have hd := p.deltaPos
  have hle : 4 * p.Δ * (s : Int) ≤ (V2.D.Run.stateBefore E rho j y).st.base.now := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ _ at hn
    linarith
  have hi : (s : Int) ≤ (V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ) := by
    exact (Int.le_ediv_iff_mul_le (by positivity)).mpr (by nlinarith [hle])
  exact_mod_cast (le_trans hi (Int.self_le_toNat _))
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every handled honest ack is admitted, including carried receipt. -/
theorem pcsa_honest_ack_admitted (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (y : V) (hy : y ∈ rho.honest) (s : Slot) (i : Fin p.n) (r : BlockId)
    (j : Nat) (t : Time) (hi : rho.seatOf (.base (.ack s)) i ∈ rho.honest)
    (ht : SA.earlyTime p.toParams s ≤ t)
    (hh : V2.D.Run.handlesAt E rho j y (ackObj p s i r) t) :
    (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool := by
  obtain ⟨parent, hj, hh⟩ := hh
  have hem : ∃ tt, V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i)
      (ackObj p s i r) tt := by
    rcases pcsa_handles_carried _ parent _ hh with hdir | hcar
    · have hp : V2.D.Run.processes rho y (ackObj p s i r) t := by
        rw [hdir]
        exact ⟨j, hj⟩
      obtain ⟨tt, _, he⟩ := h.valid.unforgeable y _ t hp _ hi rfl
      exact ⟨tt, he⟩
    · obtain ⟨tt, _, he⟩ := h.valid.carried y parent t ⟨j, hj⟩ _ hcar _ hi rfl
      exact ⟨tt, he⟩
  obtain ⟨tt, he⟩ := hem
  have hs := pcsa_ack_receiver_slot E rho h j y parent t s hj ht
  have hr := pcsa_ack_root_slotOK E rho h _ y hi hy s i r tt j he
  have hroots := pcsa_seat_roots E rho h.valid j y s i hi r tt he
  rw [V2.D.Run.stateBefore_succ E rho hj]
  change _ ∈ (Function.update (V2.D.Run.stateBefore E rho j) y _ y).st.ackPool
  rw [Function.update_self]
  exact pcsa_handled_ack_pool _ parent s i r (h.valid.wire j y parent t hj) hh hs hr hroots
/-- Formation's exact hAckAdmit interface. -/
theorem pcsa_formation_ack_admit [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF) :
    ∀ y ∈ rho.honest, ∀ (i : Fin p.n) j t,
      rho.seatOf (.base (.ack s)) i ∈ rho.honest →
      SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t →
      (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool := by
  intro y hy i j t hi het _htz hh
  exact pcsa_honest_ack_admitted E rho h.base y hy s i N.erase.root j t hi het hh

/-- The exact hFreezeKeep interface for formation. -/
theorem pcsa_clean_freeze_keep [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF) :
    ∀ y ∈ rho.honest,
      (collectPCs (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).pcs ⊆
        (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs := by
  intro y hy
  exact pcsa_collectPCs_after_freeze E rho h.base.valid.toScheduleWellFormed
    h.base.noRestart h.base.delta y hy s
    ((le_of_lt (pcsa_freeze_lt_gate p s)).trans h.horizon)

end AvailableChain.PCSA.Run

end
