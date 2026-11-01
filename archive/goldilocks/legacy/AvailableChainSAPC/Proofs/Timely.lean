module
public import AvailableChainSAPC.Proofs.ReceiptTimes
public import AvailableChainSAPC.Proofs.Quorum

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The actual clock phase immediately before `saveTimely`. This names
the existing transition; it adds no protocol action or premise. -/
def timelyInput (p : Params) {n : Nat} (st : State n) (t : Time) : State n :=
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    { st with base := GridCO.freeze p.engine st.base fSlot,
              frozenPC := if st.frozenPC.any (fun row => row.1 == fSlot)
                then st.frozenPC else st.frozenPC ++ [(fSlot, st.bestPC)] }
    else st
  let r := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  { st with base := { st.base with early := st.base.early ++
    [(r, GridCO.earlyVotes p.engine st.base r)] } }

theorem timelyInput_timely (p : Params) {n : Nat} (st : State n) (t : Time) :
    (timelyInput p st t).timely = st.timely := by
  unfold timelyInput
  dsimp only
  split_ifs <;> rfl

theorem timelyInput_archive (p : Params) {n : Nat} (st : State n) (t : Time) :
    (timelyInput p st t).receivedHeads = st.receivedHeads := by
  unfold timelyInput
  dsimp only
  split_ifs <;> rfl

theorem clock_timely (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).timely =
      let r := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
      if 0 ≤ t - 2 * p.Δ && t == earlyTime p r then
        (saveTimely p (timelyInput p st t) r).timely else st.timely := by
  unfold clock timelyInput
  dsimp only
  split_ifs <;> simp only [gate]

theorem process_timely (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).timely = st.timely := by
  have hhead (st : State n) (h : HeadWire n) : (receiveHead p st h).timely = st.timely := by
    unfold receiveHead
    split
    · dsimp only; split <;> (try split_ifs) <;> rfl
    · rfl
  have hcollect (st : State n) : (collectPCs p st).timely = st.timely :=
    collectPCs_field p State.timely (by intros; rfl) st
  have hfold (xs : List (HeadWire n)) (st : State n) :
      (xs.foldl (receiveHead p) st).timely = st.timely :=
    fold_field State.timely _ hhead xs st
  unfold process
  split
  · simp only [admitHead, hcollect, hhead]
  · unfold admitProposal
    split <;> simp only [hcollect, hfold]
  · split <;> simp only [hcollect, installPC, hfold]
  · rfl

theorem saveTimely_prefix (p : Params) {n : Nat} (st : State n) (r : Slot) :
    st.timely <+: (saveTimely p st r).timely := by
  unfold saveTimely
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem clock_timely_prefix (p : Params) {n : Nat} (st : State n) (t : Time) :
    st.timely <+: (clock p st t).timely := by
  rw [clock_timely]
  dsimp only
  split
  · simpa only [timelyInput_timely] using saveTimely_prefix p (timelyInput p st t) _
  · exact List.prefix_refl _

/-- A newly saved row has an exact early tick, and its value is the
candidate search at that tick. Empty results have the same origin. -/
theorem clock_timely_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (r : Slot) (value : Option Block) (hm : (r, value) ∈ (clock p st t).timely) :
    (r, value) ∈ st.timely ∨
      t = earlyTime p r ∧
      value = ((timelyInput p st t).receivedHeads.map (fun o => o.payload.target)).find?
        (timelyCandidate p (timelyInput p st t) r) := by
  rw [clock_timely] at hm
  dsimp only at hm
  split at hm
  · rename_i htime
    unfold saveTimely at hm
    split at hm
    · exact Or.inl (by simpa only [timelyInput_timely] using hm)
    · rcases List.mem_append.mp hm with hold | hnew
      · exact Or.inl (by simpa only [timelyInput_timely] using hold)
      · have he := List.mem_singleton.mp hnew
        have hr := congrArg Prod.fst he
        have hv := congrArg Prod.snd he
        dsimp only at hr hv
        right
        constructor
        · simpa only [← hr, beq_iff_eq] using (Bool.and_eq_true_iff.mp htime).2
        · simpa only [← hr] using hv
  · exact Or.inl hm

theorem stateBefore_timely_prefix {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (sapc p) rho i v).timely <+:
      (Run.stateBefore (sapc p) rho j v).timely := by
  set_option backward.isDefEq.respectTransparency false in
  exact stateBefore_field_prefix (P := sapc p) State.timely (clock_timely_prefix p)
    (fun st o => by rw [show (sapc p).process = process p from rfl, process_timely])
    rho hij v

/-- A completed save is immutable at every later engine input. -/
theorem savedTimely_at_later_input {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) (r : Slot)
    (value : Option Block) (h : savedTimely (Run.stateBefore (sapc p) rho i v) r = some value) :
    savedTimely (Run.stateBefore (sapc p) rho j v) r = some value := by
  obtain ⟨suffix, he⟩ := stateBefore_timely_prefix p rho hij v
  unfold savedTimely at h ⊢
  rw [← he, List.find?_append]
  cases hf : (Run.stateBefore (sapc p) rho i v).timely.find? (fun row => row.1 == r) with
  | none => simp [hf] at h
  | some row => simpa [hf] using h

/-- Every saved value comes from the actual early phase of a prior local
tick. There is no synchrony or fault-cap premise. -/
theorem timely_origin_before {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (v : V) (r : Slot) (value : Option Block)
    (hm : (r, value) ∈ (Run.stateBefore (sapc p) rho index v).timely) :
    ∃ j < index,
      rho.events[j]? = some (.tick v (earlyTime p r)) ∧
      value = ((timelyInput p (Run.stateBefore (sapc p) rho j v) (earlyTime p r)).receivedHeads.map
        (fun o => o.payload.target)).find?
          (timelyCandidate p
            (timelyInput p (Run.stateBefore (sapc p) rho j v) (earlyTime p r)) r) := by
  obtain ⟨j, hj, t, ht, htime, hvalue⟩ := clock_field_origin
    (P := sapc p) State.timely rfl (process_timely p)
    (fun st t row => t = earlyTime p row.1 ∧
      row.2 = ((timelyInput p st t).receivedHeads.map (fun o => o.payload.target)).find?
        (timelyCandidate p (timelyInput p st t) row.1))
    (fun st t row hm => clock_timely_origin p st t row.1 row.2 hm)
    rho index v (r, value) hm
  subst t
  exact ⟨j, hj, ht, hvalue⟩

/-- A successful save identifies a qualifying N in its original early
input, rather than a candidate formed by later receipts. -/
theorem savedTimely_origin_before {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (v : V) (r : Slot) (b : Block)
    (h : savedTimely (Run.stateBefore (sapc p) rho index v) r = some (some b)) :
    ∃ j < index, rho.events[j]? = some (.tick v (earlyTime p r)) ∧
      timelyCandidate p
        (timelyInput p (Run.stateBefore (sapc p) rho j v) (earlyTime p r)) r b = true := by
  obtain ⟨row, hr, hb⟩ := Option.map_eq_some_iff.mp h
  have hlabel : row.1 = r := by simpa using List.find?_some hr
  have hrow : row = (r, some b) := Prod.ext hlabel hb
  have hm := List.mem_of_find?_eq_some hr
  rw [hrow] at hm
  obtain ⟨j, hj, ht, hfind⟩ := timely_origin_before p rho index v r (some b) hm
  exact ⟨j, hj, ht, List.find?_some hfind.symm⟩

/-- A saved N contains an honest exact preparation when q exceeds the
fault count. No one-third cap or synchrony premise is needed here. -/
theorem savedTimely_honest_preparation {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hauth : UnforgeableSignatures (sapc p) E rho)
    (ha : (faulty rho).card < pcQuorum p) (index : Nat) (v : V) (r : Slot) (b : Block)
    (h : savedTimely (Run.stateBefore (sapc p) rho index v) r = some (some b)) :
    ∃ i data, rho.seatOf r i ∈ rho.honest ∧ data.target = b ∧
      Run.emits (sapc p) E rho (rho.seatOf r i)
        (fromHead ⟨.seat r i, data⟩) (voteTime p r) := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨j, _, _, hc⟩ := savedTimely_origin_before p rho index v r b h
  obtain ⟨i, data, honest, hm, ht⟩ := timelyCandidate_honest_witness p rho _ r b hc ha
  rw [timelyInput_archive] at hm
  exact ⟨i, data, honest, ht,
    archive_authenticated_before p E rho hauth j v r i data hm honest⟩

/-- Successful saves at different readers select the same target under
the cap, even if the saves have different receipt orders. -/
theorem savedTimely_unique {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i j : Nat) (u v : V) (r : Slot) (a b : Block)
    (ha : savedTimely (Run.stateBefore (sapc p) rho i u) r = some (some a))
    (hb : savedTimely (Run.stateBefore (sapc p) rho j v) r = some (some b)) : a = b := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨ia, _, _, hca⟩ := savedTimely_origin_before p rho i u r a ha
  obtain ⟨ib, _, _, hcb⟩ := savedTimely_origin_before p rho j v r b hb
  apply timelyCandidate_unique p E rho hx.toScheduleWellFormed hcap _ _ ?_ ?_ r a b hca hcb
  all_goals
    simpa only [ArchiveAuthenticated, timelyInput_archive] using!
      (archive_authenticated_before p E rho hx.toUnforgeableSignatures _ _)

/-- Before the scheduled early tick, no save for its label exists.
This uses tick uniqueness, not an assumed clean start. -/
theorem savedTimely_none_before_early {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) (r : Slot)
    (hi : rho.events[index]? = some (.tick v (earlyTime p r))) :
    savedTimely (Run.stateBefore (sapc p) rho index v) r = none := by
  unfold savedTimely
  cases hf : (Run.stateBefore (sapc p) rho index v).timely.find? (fun row => row.1 == r) with
  | none => rfl
  | some row =>
      have hr : row.1 = r := by simpa using List.find?_some hf
      obtain ⟨j, hj, htick, _⟩ := timely_origin_before p rho index v row.1 row.2
        (List.mem_of_find?_eq_some hf)
      rw [hr] at htick
      have hlen := (List.getElem?_eq_some_iff.mp hi).1
      have heq : index = j := (List.Nodup.getElem?_inj hlen hs.nodup).mp (hi.trans htick.symm)
      exact (Nat.ne_of_lt hj heq.symm).elim

theorem saveTimely_result (p : Params) {n : Nat} (st : State n) (r : Slot)
    (hnone : savedTimely st r = none) :
    savedTimely (saveTimely p st r) r = some
      ((st.receivedHeads.map (fun o => o.payload.target)).find? (timelyCandidate p st r)) := by
  have hf : st.timely.find? (fun row => row.1 == r) = none := by
    cases he : st.timely.find? (fun row => row.1 == r) with
    | none => rfl
    | some row => simp [savedTimely, he] at hnone
  simp [saveTimely, savedTimely, List.find?_append, hf]

/-- A qualifying target is selected when candidates are unique. The
uniqueness premise can be supplied by the capped quorum proof. -/
theorem saveTimely_of_unique_candidate (p : Params) {n : Nat} (st : State n)
    (r : Slot) (b : Block) (hnone : savedTimely st r = none)
    (hc : timelyCandidate p st r b = true)
    (hunique : ∀ c, timelyCandidate p st r c = true → c = b) :
    savedTimely (saveTimely p st r) r = some (some b) := by
  rw [saveTimely_result p st r hnone]
  have hq := timelySeats_quorum p st r b hc
  have hpos : 0 < (timelySeats p st r b).card := lt_of_lt_of_le (quorum_bounds p).1 hq
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨data, hm, ht, _⟩ := timelySeats_witness p st r b i hi
  have hb : b ∈ st.receivedHeads.map (fun o => o.payload.target) :=
    List.mem_map.mpr ⟨⟨.seat r i, data⟩, hm, ht⟩
  cases hf : (st.receivedHeads.map (fun o => o.payload.target)).find?
      (timelyCandidate p st r) with
  | none => exact (List.find?_eq_none.mp hf b hb hc).elim
  | some c => rw [hunique c (List.find?_some hf)]

theorem clock_timely_at_early (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (clock p st (earlyTime p r)).timely =
      (saveTimely p (timelyInput p st (earlyTime p r)) r).timely := by
  rw [clock_timely]
  have ht : earlyTime p r - 2 * p.Δ = 4 * p.Δ * (r : Time) := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ - 2 * p.Δ = _
    ring
  have hd : 4 * p.Δ ≠ 0 := ne_of_gt (by linarith [p.deltaPos])
  simp [ht, hd, mul_nonneg (show 0 ≤ 4 * p.Δ by linarith [p.deltaPos])
    (Int.natCast_nonneg r)]

/-- At its actual early tick, a capped reader saves every qualifying
target. Later inputs retain that result. Receipt and path completeness
are the remaining inputs to the local candidate test. -/
theorem timely_saved_at_early {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (index : Nat) (v : V) (r : Slot) (b : Block)
    (hi : rho.events[index]? = some (.tick v (earlyTime p r)))
    (hc : timelyCandidate p
      (timelyInput p (Run.stateBefore (sapc p) rho index v) (earlyTime p r)) r b = true) :
    savedTimely (Run.stateBefore (sapc p) rho (index + 1) v) r = some (some b) := by
  set_option backward.isDefEq.respectTransparency false in
  rw [stateBefore_succ_event hi]
  simp only [World.step, Function.update_self, sapc, savedTimely, clock_timely_at_early]
  refine saveTimely_of_unique_candidate p _ r b ?_ hc ?_
  · simpa only [savedTimely, timelyInput_timely] using!
      savedTimely_none_before_early p E rho hx.toScheduleWellFormed index v r hi
  · intro c hcc
    have hauth : ArchiveAuthenticated p E rho
        (timelyInput p (Run.stateBefore (sapc p) rho index v) (earlyTime p r)) := by
      simpa only [ArchiveAuthenticated, timelyInput_archive] using!
        archive_authenticated_before p E rho hx.toUnforgeableSignatures index v
    exact timelyCandidate_unique p E rho hx.toScheduleWellFormed hcap _ _
      hauth hauth r c b hcc hc

/-- Ack fields name the preceding label and an actual immutable save. -/
theorem ackFor_saved {n : Nat} (st : State n) (r s : Slot) (target b : Block)
    (h : ackFor st r target = some (s, b)) :
    r = s + 1 ∧ savedTimely st s = some (some b) ∧ Block.Preceq b target := by
  unfold ackFor at h
  split at h
  · simp at h
  · rename_i hn
    have hr : r ≠ 0 := by simpa using hn
    split at h
    next value candidate hs =>
      split at h
      · rename_i hext
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hlabel, rfl⟩
        refine ⟨?_, ?_, hext⟩
        · rw [← hlabel]
          exact (Nat.sub_add_cancel (Nat.pos_of_ne_zero hr)).symm
        · simpa only [hlabel] using hs
      · simp at h
    next => simp at h

theorem voteTime_ne_earlyTime (p : Params) (r s : Slot) : voteTime p r ≠ earlyTime p s := by
  intro he
  change 4 * p.Δ * (r : Time) + p.Δ = 4 * p.Δ * (s : Time) + 2 * p.Δ at he
  have hmul : (4 * (r : Time) + 1) * p.Δ = (4 * (s : Time) + 2) * p.Δ := by
    nlinarith
  have h := mul_right_cancel₀ (ne_of_gt p.deltaPos) hmul
  have hm := congrArg (fun x : Int => x % 4) h
  norm_num [Int.add_emod, Int.mul_emod] at hm

theorem clock_timely_at_vote (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (clock p st (voteTime p r)).timely = st.timely := by
  rw [clock_timely]
  dsimp only
  split
  · rename_i ht
    exact (voteTime_ne_earlyTime p r _ (by simpa using (Bool.and_eq_true_iff.mp ht).2)).elim
  · rfl

/-- An emitted ack comes from a successful save at the emitter's prior
early tick, and its actual emitted HEAD extends that saved target. -/
theorem emitted_ack_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (v : V) (r s : Slot) (i : Fin p.n)
    (data : HeadData) (b : Block)
    (hem : Run.emits (sapc p) E rho v (fromHead ⟨.seat r i, data⟩) (voteTime p r))
    (hack : data.ack = some (s, b)) :
    r = s + 1 ∧ Block.Preceq b data.target ∧
      ∃ j k, j < k ∧ rho.events[j]? = some (.tick v (earlyTime p s)) ∧
        rho.events[k]? = some (.tick v (voteTime p r)) ∧
        timelyCandidate p
          (timelyInput p (Run.stateBefore (sapc p) rho j v) (earlyTime p s)) s b = true := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨index, htick, he⟩ := hem
  have hact := (emittedAt_seat_action (sapc p) E rho index v (voteTime p r)
    r i (.head data) he).2
  change some (Msg.head _) = some (Msg.head data) at hact
  have hd := Msg.head.inj (Option.some.inj hact)
  have ha : ackFor (clock p (Run.stateBefore (sapc p) rho index v) (voteTime p r)) r
      data.target = some (s, b) := by
    rw [← hd]
    exact (congrArg HeadData.ack hd).trans hack
  obtain ⟨hr, hs, hb⟩ := ackFor_saved _ r s data.target b ha
  simp only [savedTimely, clock_timely_at_vote] at hs
  obtain ⟨j, hj, ht, hc⟩ := savedTimely_origin_before p rho index v s b hs
  exact ⟨hr, hb, j, index, hj, ht, htick, hc⟩

/-- A valid PC in an authentic archive has an earlier honest exact
preparation, not just an honest ack. This uses q>a, without the cap. -/
theorem pc_honest_preparation {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hauth : UnforgeableSignatures (sapc p) E rho) (st : State p.n)
    (harchive : ArchiveAuthenticated p E rho st) (c : PC p.n)
    (hc : pcValid p st c = true) (ha : (faulty rho).card < pcQuorum p) :
    ∃ i data, rho.seatOf c.slot i ∈ rho.honest ∧ data.target = c.target ∧
      Run.emits (sapc p) E rho (rho.seatOf c.slot i)
        (fromHead ⟨.seat c.slot i, data⟩) (voteTime p c.slot) := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨ackSeat, ack, honest, hm, hack, _⟩ := pc_honest_witness p rho st c hc ha
  have hem := harchive (c.slot + 1) ackSeat ack hm honest
  obtain ⟨_, _, j, _, _, _, _, hn⟩ := emitted_ack_origin p E rho
    (rho.seatOf (c.slot + 1) ackSeat) (c.slot + 1) c.slot ackSeat ack c.target hem hack
  obtain ⟨i, data, honestPrep, hmPrep, ht⟩ :=
    timelyCandidate_honest_witness p rho _ c.slot c.target hn ha
  rw [timelyInput_archive] at hmPrep
  exact ⟨i, data, honestPrep, ht, archive_authenticated_before p E rho hauth j _
    c.slot i data hmPrep honestPrep⟩

end AvailableChain.SAPC
end
