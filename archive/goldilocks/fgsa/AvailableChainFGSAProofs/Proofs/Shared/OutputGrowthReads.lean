module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAClaims.Statements.Healed

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Both selected getters use the same inclusive event-prefix record. -/
theorem fgsa_outputAt_eq_S_at (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed])
    (x : V) (t : Time) :
    V2.D.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;>
    change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
    rw [S_at_def, V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl

omit [DecidableEq V] in
/-- An inclusive read at or after a healing cut is in its suffix, also
when the trigger equals a gate cut with same-time deliveries. -/
theorem fgsa_healSuffix_timeIdx (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {a t : Time} (hat : a ≤ t) :
    HealSuffix p c rho a (timeIdx rho t) := by
  rw [HealSuffix_def]
  refine ⟨?_, List.length_filter_le _ _⟩
  have hm := V2.D.Engine.read_length_mono (rho := rho) a t hat
  rw [healStart_def]
  split
  · exact (preIdx_le_afterTicksIdx E rho hs a).2.trans hm
  · exact hm

/-- Healed event monotonicity supplies both inclusive public reads. -/
theorem fgsa_healed_output_mono (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {a t D : Time}
    (healed : Healed p c E rho a) (hat : a ≤ t) (htD : t ≤ D)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed])
    (x : V)
    (hreadT : confirmedReaderIdx p c E rho x (timeIdx rho t))
    (hreadD : confirmedReaderIdx p c E rho x (timeIdx rho D)) :
    Block.Preceq (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g x D) := by
  rw [fgsa_outputAt_eq_S_at E rho hs g hg x t, fgsa_outputAt_eq_S_at E rho hs g hg x D]
  exact healed.2.1 _ _ x (fgsa_healSuffix_timeIdx E rho hs hat)
    (fgsa_healSuffix_timeIdx E rho hs (hat.trans htD))
    (V2.D.Engine.read_length_mono _ _ htD) hreadT hreadD

end AvailableChain.FGSA.Run
end
