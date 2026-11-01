module
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures

public section

/-! Tick output by duty, in both FG modes (FG finality safety, step P6).
Each duty has its own signing label. Only the FG label is self-visible.
Mode `.idle` gives no FG row. -/

namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- A HEAD label has exactly its HEAD duty. -/
theorem pcsa_head_singleDuty (m : FGMode) (s : Slot) :
    Gen.V2.Duty.SingleDuty (pcsaWith m p c) (.base (.head s)) := by
  refine ⟨.headAction s, rfl, ?_⟩
  intro d hd
  change RunDuty.signLabel d = _ at hd
  cases d <;> cases hd
  rfl

/-- A proposal label has exactly its proposal duty. -/
theorem pcsa_prop_singleDuty (m : FGMode) (s : Slot) :
    Gen.V2.Duty.SingleDuty (pcsaWith m p c) (.prop s) := by
  refine ⟨.propAction s, rfl, ?_⟩
  intro d hd
  change RunDuty.signLabel d = _ at hd
  cases d <;> cases hd
  rfl

/-- An ack label has exactly its ack duty. -/
theorem pcsa_ack_singleDuty (m : FGMode) (s : Slot) :
    Gen.V2.Duty.SingleDuty (pcsaWith m p c) (.base (.ack s)) :=
  ⟨.ackAction s, rfl, fun d hd => (signLabel_ack_iff d s).mp hd⟩

/-- Only an FG duty uses the FG signing label. -/
theorem signLabel_fg_iff (d : RunDuty) :
    d.signLabel = .base .fg ↔ ∃ r, d = .fgAction r := by
  constructor
  · intro hd
    cases d <;> cases hd
    exact ⟨_, rfl⟩
  · rintro ⟨r, rfl⟩
    rfl

/-- Exact HEAD emission at a tick, in both modes. -/
theorem pcsa_emits_head (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (nd : Node p) (v : V) (t : Time) (s : Slot)
    (j : Fin p.n) (b : BlockId) :
    (⟨.seat (.base (.head s)) j, .head b⟩ : Obj p) ∈ (V2.D.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ SA.voteTime p.toParams s = t ∧
      rho.seatOf (.base (.head s)) j = v ∧
      b = (headVote p (PCSA.clock p nd.st t) s).root := by
  refine (Gen.V2.Duty.mem_tick_singleDuty_iff (P := pcsaWith m p c) E rho nd v t
    (.base (.head s)) (pcsa_head_singleDuty m s) (.headAction s) rfl j (.head b)).trans ?_
  have ha : (pcsaWith m p c).act ((pcsaWith m p c).clock nd t) (.headAction s)
      (rho.input v t) = some (.head b) ↔
        b = (headVote p (PCSA.clock p nd.st t) s).root := by
    cases m <;> exact ⟨fun h => (Msg.head.inj (Option.some.inj h)).symm, fun h => h ▸ rfl⟩
  exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ha

/-- Exact FG row emission at a tick. Only mode `.on` signs a row. -/
theorem pcsa_emits_row (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (nd : Node p) (v : V) (t : Time)
    (j : Fin p.n) (body : RowPayload) :
    ofRow p ⟨.seat .fg j, body⟩ ∈ (V2.D.tick E rho nd v t).2 ↔
      m = .on ∧ E.awake v t = true ∧ rho.seatOf (.base .fg) j = v ∧
      ∃ r, p.actionTime r = t ∧
        (attest p (PCSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1 = some body := by
  change (⟨.seat (.base .fg) j, .row body⟩ : Obj p) ∈ _ ↔ _
  refine (mem_tick_seat_iff (P := pcsaWith m p c) E rho nd v t (.base .fg) j
    (.row body)).trans ?_
  have hact : ∀ r, (pcsaWith m p c).act ((pcsaWith m p c).clock nd t) (.fgAction r)
      (rho.input v t) = some (.row body) ↔
        m = .on ∧ (attest p (PCSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1 = some body := by
    intro r
    cases m with
    | idle =>
        change (none : Option (Msg p.n)) = _ ↔ _
        constructor
        · intro h
          cases h
        · rintro ⟨h, -⟩
          cases h
    | on =>
        change (attest p (PCSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1.map Msg.row =
          some (.row body) ↔ _
        rw [Option.map_eq_some_iff]
        constructor
        · rintro ⟨a, ha, he⟩
          cases Msg.row.inj he
          exact ⟨rfl, ha⟩
        · rintro ⟨-, ha⟩
          exact ⟨body, ha, rfl⟩
  constructor
  · rintro ⟨hw, hi, d, hl, ht, ha⟩
    obtain ⟨r, rfl⟩ := (signLabel_fg_iff d).mp hl
    obtain ⟨hm, hb⟩ := (hact r).mp ha
    exact ⟨hm, hw, hi, r, ht, hb⟩
  · rintro ⟨hm, hw, hi, r, ht, hb⟩
    exact ⟨hw, hi, .fgAction r, rfl, ht, (hact r).mpr ⟨hm, hb⟩⟩

/-- Exact row emission at a tick event. -/
theorem pcsa_emitsAt_row (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (v : V) (t : Time)
    (hk : rho.events[k]? = some (.tick v t)) (j : Fin p.n) (body : RowPayload) :
    ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho k ↔
      m = .on ∧ E.awake v t = true ∧ rho.seatOf (.base .fg) j = v ∧
      ∃ r, p.actionTime r = t ∧
        (attest p (PCSA.clock p (V2.D.Run.stateBefore E rho k v).st t)
          (V2.D.Run.stateBefore E rho k v).record ⟨0, p.nPos⟩).1 = some body := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2]
  exact pcsa_emits_row m E rho _ v t j body

/-- Exact proposal emission at a tick, in both modes. -/
theorem pcsa_emits_proposal (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (nd : Node p) (v : V) (t : Time) (s : Slot)
    (msg : Msg p.n) :
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, msg⟩ : Obj p) ∈ (V2.D.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ SA.proposalTime p.toParams s = t ∧
      rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = v ∧
      (propose p (PCSA.clock p nd.st t) s).map (withApp p (c.app (rho.input v t))) =
        some msg := by
  refine (Gen.V2.Duty.mem_tick_singleDuty_iff (P := pcsaWith m p c) E rho nd v t
    (.prop s) (pcsa_prop_singleDuty m s) (.propAction s) rfl ⟨0, Nat.one_pos⟩ msg).trans ?_
  have ha : (pcsaWith m p c).act ((pcsaWith m p c).clock nd t) (.propAction s)
      (rho.input v t) =
        (propose p (PCSA.clock p nd.st t) s).map (withApp p (c.app (rho.input v t))) := by
    cases m <;> rfl
  rw [ha]
  rfl

/-- Exact ack emission at a tick, in both modes. -/
theorem pcsa_emits_ack (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (nd : Node p) (v : V) (t : Time) (s : Slot)
    (j : Fin p.n) (b : BlockId) :
    ackObj p s j b ∈ (V2.D.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ SA.earlyTime p.toParams s = t ∧
      rho.seatOf (.base (.ack s)) j = v ∧
      ∃ B, ackFor p (PCSA.clock p nd.st t) s = some B ∧ B.root = b := by
  refine (Gen.V2.Duty.mem_tick_singleDuty_iff (P := pcsaWith m p c) E rho nd v t
    (.base (.ack s)) (pcsa_ack_singleDuty m s) (.ackAction s) rfl j (.ack b)).trans ?_
  have hm : ∀ x : Option Block, x.map (fun B => Msg.ack B.root) = some (Msg.ack b : Msg p.n) ↔
      ∃ B, x = some B ∧ B.root = b := by
    intro x
    cases x <;> simp
  have ha : (pcsaWith m p c).act ((pcsaWith m p c).clock nd t) (.ackAction s)
      (rho.input v t) = some (.ack b) ↔
        ∃ B, ackFor p (PCSA.clock p nd.st t) s = some B ∧ B.root = b := by
    cases m <;> exact hm _
  exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ha

/-- Sleep releases no object and keeps the record. -/
theorem pcsa_tick_asleep (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (nd : Node p) (v : V) (t : Time)
    (h : E.awake v t = false) :
    (V2.D.tick E rho nd v t).2 = [] ∧ (V2.D.tick E rho nd v t).1.record = nd.record := by
  rw [V2.D.tick_asleep E rho nd h]
  exact ⟨rfl, rfl⟩

/-- The complete self-visible output of a tick: in mode `.on`, zero or one FG
row at an awake action tick; in mode `.idle`, nothing. -/
theorem pcsa_tick_rows_of_seats (m : FGMode) (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c))
    (e : Fin p.n ≃ V) (he : ∀ j, rho.seatOf (.base .fg) j = e j)
    (nd : Node p) (v : V) (t : Time) :
    ((V2.D.tick E rho nd v t).2.filter (pcsaWith m p c).objSelfVisible) =
      if E.awake v t = true ∧ m = .on ∧ p.actionTime ((p.slotOf t - 1) / p.R) = t then
        (attest p (PCSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1.toList.map
          (fun body => ofRow p ⟨.seat .fg (e.symm v), body⟩)
      else [] := by
  let nd' : Node p := ⟨PCSA.clock p nd.st t, nd.record⟩
  let out : RunDuty → List (Obj p) := fun d =>
    (rho.ownSeats (RunDuty.signLabel d) v).filterMap (fun j =>
      (actWith m p c nd' d (rho.input v t)).map
        (fun q => (⟨.seat (RunDuty.signLabel d) j, q⟩ : Obj p)))
  -- Read visibility on `Obj p`, the element type of `out`.
  obtain ⟨vis, hvis⟩ : ∃ vis : Obj p → Bool,
      ∀ o : Obj p, vis o = (pcsaWith m p c).objSelfVisible o := ⟨_, fun _ => rfl⟩
  have hvs : ∀ (ℓ : RunLabel) (j : Fin (RunLabel.seats p ℓ)) (q : Msg p.n),
      vis ⟨.seat ℓ j, q⟩ = RunLabel.selfVisible ℓ := fun ℓ j q => hvis _
  refine (List.filter_congr (fun o _ => (hvis o).symm)).trans ?_
  have ht : @Eq (List (Obj p)) (V2.D.tick E rho nd v t).2
      (if E.awake v t then (duties p t).flatMap out ++ [] else []) := rfl
  have hnil : ∀ d, RunLabel.selfVisible d.signLabel = false →
      List.filter vis (out d) = [] := by
    intro d hd
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp ha
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hj
    rw [hvs, hd]
    exact Bool.false_ne_true
  have hseats : rho.ownSeats (RunLabel.base .fg) v = [e.symm v] :=
    ownSeats_bijSeat rho (ℓ := .base .fg) e he v
  have hfgvis : RunLabel.selfVisible (.base .fg) = true := rfl
  have hfg : ∀ r, List.filter vis (out (.fgAction r)) =
      if m = .on then
        (attest p (PCSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1.toList.map
          (fun body => ofRow p ⟨.seat .fg (e.symm v), body⟩)
      else [] := by
    intro r
    change List.filter vis ((rho.ownSeats (RunLabel.base .fg) v).filterMap (fun j =>
      (actWith m p c nd' (.fgAction r) (rho.input v t)).map
        (fun q => (⟨.seat (RunLabel.base .fg) j, q⟩ : Obj p)))) = _
    rw [hseats]
    cases m with
    | idle => rfl
    | on =>
        change List.filter vis ([e.symm v].filterMap (fun j =>
          ((attest p (PCSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1.map Msg.row).map
            (fun q => (⟨.seat (RunLabel.base .fg) j, q⟩ : Obj p)))) = _
        cases (attest p (PCSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1 with
        | none => rfl
        | some body =>
            change List.filter vis [(⟨.seat (RunLabel.base .fg) (e.symm v), .row body⟩ : Obj p)] =
              [(⟨.seat (RunLabel.base .fg) (e.symm v), .row body⟩ : Obj p)]
            have hv := hvs (.base .fg) (e.symm v) (.row body)
            rw [List.filter_cons, hv, hfgvis, ite_eq_left rfl, List.filter_nil]
  have hprop : ∀ s, List.filter vis (out (.propAction s)) = [] := fun s => hnil _ rfl
  have hhead : ∀ s, List.filter vis (out (.headAction s)) = [] := fun s => hnil _ rfl
  have hack : ∀ s, List.filter vis (out (.ackAction s)) = [] := fun s => hnil _ rfl
  rw [ht]
  clear ht
  by_cases hw : E.awake v t = true
  · rw [ite_eq_left hw, List.append_nil, List.filter_flatMap]
    dsimp only [duties]
    simp only [List.flatMap_append]
    split_ifs <;>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
        hprop, hhead, hack, hfg] <;>
      by_cases hm : m = .on <;> simp_all
  · rw [ite_eq_right hw, ite_eq_right (fun h => hw h.1)]
    rfl

end AvailableChain.PCSA.Run
end
