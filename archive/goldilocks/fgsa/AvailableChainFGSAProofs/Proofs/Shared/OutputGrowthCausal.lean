module
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainFGSAClaims.Statements.Reads

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Plan A5: the inclusive read clock is bounded by its time. This includes
terminal reads and time zero. The clock source needs no next event. -/
theorem fgsa_timeIdx_now_le (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (t : Time) (ht : 0 ≤ t) (x : V) :
    (V2.D.Run.stateBefore E rho (timeIdx rho t) x).st.base.now ≤ t := by
  rcases V2.D.Engine.stateBefore_now_source_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c)
    E rho (timeIdx rho t) x with hz | ⟨j, hj, he⟩
  · rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (timeIdx rho t) x)] at hz
    exact hz.le.trans ht
  · rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (timeIdx rho t) x)] at he
    rcases he with he | he <;>
      exact (V2.D.Engine.index_lt_read_length_iff hs t he).mp hj

/-- Plan A5: stored prefix closure and the scheduled slot bound exclude
a block whose slot is at least the selected strictly future slot. -/
theorem fgsa_output_noFuture_of_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    {t : Time} (ht : 0 ≤ t) {s : Slot}
    (hfuture : t < V2.D.proposalTime (fgsaInterface p c) s)
    {B : Block} (hslot : s ≤ B.slot)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) (x : V) :
    ¬ Block.Preceq B (V2.D.outputAt E rho g x t) := by
  intro hb
  have hread : V2.D.outputAt E rho g x t =
      (V2.D.Run.stateBefore E rho (timeIdx rho t) x).st.base.stableRecord := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl
  rw [hread] at hb
  have inv := cstoreInv_stateBefore E rho (timeIdx rho t) x
  obtain ⟨S, hS, he⟩ := (inv.baseTree _).mp inv.Smem
  rw [← he] at hb
  obtain ⟨C, hC, hCB⟩ := eraseFG_ancestor_mem inv.fg.closed hS hb
  have hmem := (inv.baseTree B).mpr ⟨C, hC, hCB⟩
  have hbound := (fgsa_stateBefore_bounds E rho hs (timeIdx rho t) x).1 B hmem
  have hnow := fgsa_timeIdx_now_le E rho hs t ht x
  have hle : B.slot ≤ p.slotOf t :=
    hbound.trans (Internal.slotOf_mono hnow)
  have hpos : 0 < 4 * p.Δ := mul_pos (by decide) p.deltaPos
  have hspos : 0 < s := by
    change t < 4 * p.Δ * (s : Time) at hfuture
    apply Nat.pos_of_ne_zero
    intro hz
    simp only [hz, Nat.cast_zero, mul_zero] at hfuture
    exact (not_lt.mpr ht) hfuture
  have hdiv : t / (4 * p.Δ) < (s : Time) := by
    apply (Int.ediv_lt_iff_lt_mul hpos).mpr
    change t < 4 * p.Δ * (s : Time) at hfuture
    simpa only [mul_comm] using hfuture
  have hlt : p.slotOf t < s := by
    unfold Params.slotOf
    exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hspos)).mpr hdiv
  exact (not_lt_of_ge (hslot.trans hle)) hlt

end AvailableChain.FGSA.Run
end
