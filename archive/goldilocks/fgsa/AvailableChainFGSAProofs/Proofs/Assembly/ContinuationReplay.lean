module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export -- shake: keep

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

/-- Matched local ticks read after every same-time restart in each run. -/
theorem assembly_tickReplay_atWake (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    {j : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest) (ht : t ≤ source.horizon)
    (hj : source.events[j]? = some (.tick x t)) :
    ∃ k, rho.events[k]? = some (.tick x t) ∧
      rho.stateBefore E' k x = source.stateBefore E j x :=
  wcg_tickEventReplay ha hs hr hx ht hj

/-- A retained reader keeps the source join guard through the inclusive endpoint. -/
theorem assembly_joinedReplay
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    {x : V} {s : Slot} {t : Time} (hx : x ∈ rho.honest) (ht : t ≤ source.horizon)
    (hj : joinedAt p E source x s t) : joinedAt p E' rho x s t := by
  refine ⟨(ha.awake x hx t ht).trans hj.1, ?_, ?_⟩
  · intro u hu hut hw
    apply hj.2.1 u hu hut
    change E.awake x u = true ∧ E.awake x (u - 1) = false
    change E'.awake x u = true ∧ E'.awake x (u - 1) = false at hw
    rw [← ha.awake x hx u (hut.trans ht),
      ← ha.awake x hx (u - 1) ((sub_le_self _ (by decide)).trans (hut.trans ht))]
    exact hw
  · intro u hu hut he
    exact hj.2.2 u hu hut
      ((wcg_eventReplay ha (.restart x u) hx (hut.trans ht)).mp he)

end AvailableChain.FGSA.Run
end
