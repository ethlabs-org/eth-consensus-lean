module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.CommitteeRun

public section

/-! # Committee facts under growing faults and on prefixes

`CommitteePAt` / `CommitteeTAt` (P and T for a time-indexed honest set) are P and T on the prefix
of the run through each time `t`, with honest set `H t` (`CommitteePAt.upTo`,
`CommitteeTAt.upTo`), and P and T at a constant honest set are their growing forms
(`CommitteeP.at`, `CommitteeT.at`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {K : CommitteeDict sp.n}

/-- P at a constant honest set is P under growing faults. -/
theorem CommitteeP.at {H : Set (Fin sp.n)} (hP : CommitteeP K tr H) :
    CommitteePAt K tr (fun _ => H) :=
  ⟨fun _ y hy i _ s v hv => hP.1 y hy i s v hv,
    fun y i ℓ A hy hpt s v hv => hP.2 y hy i ℓ A hpt s v hv⟩

/-- T at a constant honest set is T under growing faults. -/
theorem CommitteeT.at {H : Set (Fin sp.n)} (hT : CommitteeT K tr H) :
    CommitteeTAt K tr (fun _ => H) :=
  fun y i ℓ e hy hc => hT y hy i ℓ e hc

/-- P under growing faults is P on the prefix through each time `t`, with honest set `H t`, in a
run whose cuts are in time order and whose honest set is antitone. -/
theorem CommitteePAt.upTo {H : Time → Set (Fin sp.n)} (hm : Monotone tr.time)
    (hanti : Antitone H) (hP : CommitteePAt K tr H) (t : Time) :
    CommitteeP K (tr.upTo t) (H t) := by
  refine ⟨fun y hy i s v hv => ?_, fun y hy i ℓ A hpt s v hv => ?_⟩
  · obtain ⟨i₀, -, hb, hst⟩ := Trace.upTo_state_exists (d := t) tr hm y i
    exact hP.1 t y hy i₀ hb s v (hst ▸ hv)
  · obtain ⟨hi, hpt'⟩ := (upTo_optimisticPoint hm).mp hpt
    exact hP.2 y i ℓ A (hanti hi hy) hpt' s v hv

/-- T under growing faults is T on the prefix through each time `t`, with honest set `H t`. -/
theorem CommitteeTAt.upTo {H : Time → Set (Fin sp.n)} (hanti : Antitone H)
    (hT : CommitteeTAt K tr H) (t : Time) : CommitteeT K (tr.upTo t) (H t) := by
  intro y hy i ℓ e hc
  obtain ⟨hi, hc'⟩ := upTo_castAt.mp hc
  exact hT y i ℓ e (hanti hi hy) hc'

end Consensus.Goldilocks.SA

end
