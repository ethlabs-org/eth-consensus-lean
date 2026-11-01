module
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotKeys
public import AvailableChainKitV2.DutyEngineClock
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

/-! The first freeze in a valid run (pcsa34-r4.3 §3.3; proof plan §5). -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every stored freeze label comes from a prior tick at its freeze time. -/
theorem snapshot_key_origin (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (i : Nat) (v : V) (s : Slot)
    (h : s ∈ (V2.D.Run.stateBefore E rho i v).st.pcSnapshot.map Prod.fst) :
    ∃ j < i, rho.events[j]? = some (.tick v (SA.freezeTime p.toParams s)) := by
  obtain ⟨j, hj, t, he, ht⟩ := V2.D.Engine.clock_field_origin
    (P := pcsaWith m p c) (fun nd : Node p => nd.st.pcSnapshot.map Prod.fst)
    rfl (fun nd o => process_snapshot_keys p nd.st (toWire p o))
    (fun _ _ _ h => h) (by intro nd s h; exact False.elim (List.not_mem_nil h))
    (fun _ t s => t = SA.freezeTime p.toParams s)
    (fun nd t s h => clock_snapshot_origin p nd.st t s h) E rho i v s h
  exact ⟨j, hj, ht ▸ he⟩

/-- Before a node's freeze tick, that freeze label is absent. -/
theorem snapshot_absent_before_tick (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hnd : rho.events.Nodup) (i : Nat) (v : V) (s : Slot)
    (hi : rho.events[i]? = some (.tick v (SA.freezeTime p.toParams s))) :
    (V2.D.Run.stateBefore E rho i v).st.pcSnapshot.find? (fun row => row.1 == s) = none := by
  cases he : (V2.D.Run.stateBefore E rho i v).st.pcSnapshot.find? (fun row => row.1 == s) with
  | none => rfl
  | some row =>
    have hs : row.1 = s := by simpa using List.find?_some he
    have hm : s ∈ (V2.D.Run.stateBefore E rho i v).st.pcSnapshot.map Prod.fst :=
      List.mem_map.mpr ⟨row, List.mem_of_find?_eq_some he, hs⟩
    obtain ⟨j, hj, hje⟩ := snapshot_key_origin E rho i v s hm
    have hji : j = i := (List.Nodup.getElem?_inj
      (List.getElem?_eq_some_iff.mp hje).1 hnd).mp (hje.trans hi.symm)
    omega

/-- After the freeze tick, the snapshot equals the held PC set. -/
theorem snapshot_afterTicks (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (v : V) (hh : v ∈ rho.honest) (s : Slot)
    (hhor : SA.freezeTime p.toParams s ≤ rho.horizon) :
    pcSnapshotAt (storeAfterTicks p c E rho v (SA.freezeTime p.toParams s)) s =
      (storeAfterTicks p c E rho v (SA.freezeTime p.toParams s)).pcs := by
  have hpublic : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [hΔ]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = ((4 * s + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.freezeTime p.toParams s := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    positivity
  have hm := hv.tick_total v hh _ hpublic hz hhor
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hread : storeAfterTicks p c E rho v (SA.freezeTime p.toParams s) =
      clock p (V2.D.Run.stateBefore E rho i v).st (SA.freezeTime p.toParams s) := by
    change (FGSA.Run.afterTicks E rho (SA.freezeTime p.toParams s) v).st = _
    rw [FGSA.Run.afterTicks_node E rho hv hi]
    exact pcsa_tick_st E rho _ _ _
  rw [hread]
  exact clock_freeze_snapshot p _ s (snapshot_absent_before_tick E rho hv.nodup i v s hi)

end AvailableChain.PCSA.Run
end
