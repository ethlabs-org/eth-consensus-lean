module
public import AvailableChainPCSAProofs.Proofs.Foundations.Stamps
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun

public section

/-! The separate stamp bridge for held PCs (pcsa34-r4.3 §3.3). -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Before a positive local tick, all held PCs have stamps below its time. -/
theorem stampBound_before_tick (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.ScheduleWellFormed E rho) (i : Nat) (v : V) (t : Time) (ht : 0 < t)
    (hi : rho.events[i]? = some (.tick v t)) :
    StampBound t (V2.D.Run.stateBefore E rho i v).st := by
  have hz : StampBound t (initial p.n) := by
    rw [StampBound_def]
    dsimp only [initial]
    exact ⟨ht, by simp, by simp⟩
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => StampBound t nd.st) (Nat.zero_le i) v ?_ hz
  intro k e _ hki he hn h
  cases e with
  | restart u a =>
    change u = v at hn
    subst u
    change StampBound t (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact hz
  | tick u a =>
    change u = v at hn
    subst u
    have hlt : a < t := by
      obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      have hk := (List.pairwise_iff_getElem.mp hv.sorted) k i hkl hil hki
      rw [hke, hie] at hk
      have hle : a ≤ t := V2.D.Engine.time_le_of_key_le _ _ hk
      have hne : a ≠ t := by
        intro hat
        subst a
        have hEq : k = i := (List.Nodup.getElem?_inj hkl hv.nodup).mp (he.trans hi.symm)
        omega
      exact lt_of_le_of_ne hle hne
    change StampBound t (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    have heq := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k v) v a
    rw [heq]
    exact clock_stampBound p t a _ hlt h
  | deliver u o a =>
    change u = v at hn
    subst u
    change StampBound t (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact process_stampBound p t _ (toWire p o) h

/-- For a PC held after the freeze tick, its stamp is below that tick exactly
when the PC is in the pre-tick store. Stamps alone do not imply membership. -/
theorem pcStamp_before_freeze_iff (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (v : V) (s : Slot)
    (hi : rho.events[i]? = some (.tick v (SA.freezeTime p.toParams s)))
    (d : PC p.n) (held : d ∈ (storeAfterTicks p c E rho v (SA.freezeTime p.toParams s)).pcs) :
    (∃ a < SA.freezeTime p.toParams s,
      pcStamp? (storeAfterTicks p c E rho v (SA.freezeTime p.toParams s)) d = some a) ↔
      d ∈ (V2.D.Run.stateBefore E rho i v).st.pcs := by
  have hread : storeAfterTicks p c E rho v (SA.freezeTime p.toParams s) =
      clockPre p (V2.D.Run.stateBefore E rho i v).st (SA.freezeTime p.toParams s) := by
    change (FGSA.Run.afterTicks E rho (SA.freezeTime p.toParams s) v).st = _
    rw [FGSA.Run.afterTicks_node E rho hv hi]
    exact (pcsa_tick_st E rho _ _ _).trans (clock_freeze p _ s)
  rw [hread, clockPre_pcs] at held
  constructor
  · intro _
    exact held
  · intro hd
    have ht : 0 < SA.freezeTime p.toParams s := by
      have hp : (0 : Int) < p.Δ := p.deltaPos
      change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
      positivity
    obtain ⟨a, ha, hs⟩ := held_pcStamp _ _ (stampBound_before_tick E rho hv i v _ ht hi) d hd
    exact ⟨a, ha, by simpa only [hread, pcStamp?_def, clockPre_pcStamps] using hs⟩

end AvailableChain.PCSA.Run
end
