module
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp -- shake: keep (source declarations)

public section

namespace AvailableChain.FGSA.Run
open V2 (Event)
open V2.D.Engine

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- The tick and strict-time reads agree if this node does not restart at that time. -/
theorem finality_tick_read (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t))
    (hNoRestart : V2.Event.restart v t ∉ rho.events) :
    V2.D.Run.stateBefore E rho i v = V2.D.Run.stateBeforeTime E rho t v := by
  let q := fun e : V2.Event V (fgsa p c).Object => decide (e.time < t)
  have hf := filter_eq_take hs q (fun e f hk hf => decide_eq_true
    ((time_le_of_key_le e f hk).trans_lt (of_decide_eq_true hf)))
  have hni : (rho.events.filter q).length ≤ i := by
    by_contra hc
    have hlt : i < (rho.events.filter q).length := by omega
    have hm : Event.tick v t ∈ rho.events.filter q := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have ht := of_decide_eq_true (List.mem_filter.mp hm).2
    exact lt_irrefl t ht
  change _ = ((rho.events.filter q).foldl (V2.D.World.step E rho) V2.D.World.init) v
  rw [hf]
  apply stateBefore_other_node E rho hni
  intro j e hj hji hget hnode
  have hl : t ≤ e.time := by
    have := filter_false_of_index_ge hs q (fun e f hk hf => decide_eq_true
    ((time_le_of_key_le e f hk).trans_lt (of_decide_eq_true hf))) hj hget
    simpa [q] using this
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk : e.key ≤ (Event.tick v t : V2.Event V (fgsa p c).Object).key := by
    simpa [hje, hie] using (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  have ht : e.time = t := le_antisymm (time_le_of_key_le _ _ hk) hl
  have he : e = .tick v t := by
    cases e with
    | restart u t' =>
        dsimp only [Event.node] at hnode
        subst hnode
        change t' = t at ht
        subst t'
        exact (hNoRestart (List.mem_of_getElem? hget)).elim
    | tick u t' => dsimp only [Event.node] at hnode; dsimp only [Event.time] at ht; rw [hnode, ht]
    | deliver u o t' =>
        dsimp only [Event.time] at ht
        subst t'
        dsimp only [Event.key, Event.time, Event.phase] at hk
        simp [Prod.Lex.toLex_le_toLex] at hk
  have : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, he])
  omega

/-- The joined HEAD guard excludes a receiver restart at the exact vote time. -/
theorem finality_joined_tick_read (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.voteTime p.toParams s)))
    (hJ : joinedAt p E rho v s (SA.voteTime p.toParams s)) :
    V2.D.Run.stateBefore E rho i v =
      V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s) v := by
  apply finality_tick_read p c E rho hs hi
  intro hr
  have ht : 0 ≤ SA.voteTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have hb := hJ.2.2 _ ht le_rfl hr
  change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s : Int) - 1) at hb
  nlinarith [p.deltaPos]

end AvailableChain.FGSA.Run
end
