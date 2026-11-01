module
public import AvailableChainSAPC.Proofs.Handling
public import AvailableChainKit.Engine.EngineClock

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

theorem gateWithPC_now (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (c : Option (PC n)) : (gateWithPC p st r c).now = st.now := by
  cases c with
  | none => exact @GridCO.gate_now GridCO.slowLeasePolicy p.engine n st r
  | some cert =>
      cases hc : SA.confirmation p st r with
      | none => simp [gateWithPC, hc]
      | some b =>
          simp only [gateWithPC, hc]
          split
          · rfl
          · rw [fold_field GridCO.State.now _ (by
              intro acc b
              exact fold_field GridCO.State.now _ (by intros; rfl) _ _)]
            split <;> rfl

theorem clock_now (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).base.now = t := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, gateWithPC_now, saveTimely]
  all_goals (try split_ifs) <;> rfl

theorem process_now (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).base.now = st.base.now := by
  unfold process
  split
  · simp only [admitHead, collectPCs_base, receiveHead_now]
  · unfold admitProposal
    split
    · simp only [collectPCs_base, receiveHeads_now, proposalBase_now]
    · rfl
  · split
    · simp only [collectPCs_base, installPC, receiveHeads_now]
    · rfl
  · rfl

def engineClock (p : Params) : AvailableChain.Engine.ClockLaws (sapc p) where
  now := fun st => st.base.now
  init := rfl
  clock := clock_now p
  process := process_now p

theorem stateBefore_now_le_event {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V (sapc p).Object}
    (hi : rho.events[i]? = some e) (v : V) :
    (Run.stateBefore (sapc p) rho i v).base.now ≤ e.time :=
  AvailableChain.Engine.stateBefore_now_le_event (engineClock p) E rho hs hi v

theorem stateBefore_now_mono {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (sapc p) rho i v).base.now ≤
      (Run.stateBefore (sapc p) rho j v).base.now :=
  AvailableChain.Engine.stateBefore_now_mono (engineClock p) E rho hs hij v

theorem delivery_now_ge_public {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {v : V} {o : Wire p.n} {a t : Time}
    (hi : rho.events[i]? = some (.deliver v o t))
    (ha : PublicTime E a) (ha0 : 0 ≤ a) (hat : a ≤ t) :
    a ≤ (Run.stateBefore (sapc p) rho i v).base.now :=
  AvailableChain.Engine.delivery_now_ge_public (engineClock p) E rho hs hi ha ha0 hat

/-- Before the early cutoff, the receipt clock names the HEAD label. -/
theorem head_delivery_current_label {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) {index : Nat} {reader : V} {parent : Wire p.n}
    {r : Slot} {t : Time}
    (hi : rho.events[index]? = some (.deliver reader parent t))
    (hlo : voteTime p r ≤ t) (hhi : t < earlyTime p r) :
    ((Run.stateBefore (sapc p) rho index reader).base.now / (4 * p.Δ)).toNat = r := by
  have hpub : PublicTime E (voteTime p r) := by
    refine ⟨4 * r + 1, ?_⟩
    simp only [voteTime, SA.voteTime, GridCO.voteTime, GridCO.proposalTime,
      SA.Params.engine, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have hnonneg : 0 ≤ voteTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + p.Δ
    have := p.deltaPos
    positivity
  have hl := delivery_now_ge_public p E rho hs hi hpub hnonneg hlo
  have hh := (stateBefore_now_le_event p E rho hs hi reader).trans_lt hhi
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hdiv : (Run.stateBefore (sapc p) rho index reader).base.now / (4 * p.Δ) =
      (r : Int) := by
    apply (Int.ediv_eq_iff_of_pos hd).mpr
    change 4 * p.Δ * (r : Time) + p.Δ ≤ _ at hl
    change _ < 4 * p.Δ * (r : Time) + 2 * p.Δ at hh
    constructor <;> nlinarith [p.deltaPos]
  rw [hdiv]
  simp

/-- Actual HEAD calls before the early cutoff pass raw admission. -/
theorem early_handled_head_archived {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (index : Nat) (reader : V) (r : Slot) (i : Fin p.n)
    (data : HeadData) (t : Time) (hlo : voteTime p r ≤ t) (hhi : t < earlyTime p r)
    (hh : Run.handlesAt (sapc p) rho index reader (fromHead ⟨.seat r i, data⟩) t) :
    (⟨.seat r i, data⟩ : HeadWire p.n) ∈
      (Run.stateBefore (sapc p) rho (index + 1) reader).receivedHeads := by
  obtain ⟨parent, hp, hcall⟩ := hh
  have hlabel := head_delivery_current_label p E rho hs hΔ hp hlo hhi
  rw [AvailableChain.Engine.stateBefore_succ_event hp]
  simpa only [World.step, Function.update_self, sapc] using
    handled_head_archived p (Run.stateBefore (sapc p) rho index reader) parent r i data
      (by rw [hlabel]) hcall

end AvailableChain.SAPC
end
