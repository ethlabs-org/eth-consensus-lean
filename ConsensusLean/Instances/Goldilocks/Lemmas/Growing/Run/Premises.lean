module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises

public section

/-! # Growing-fault premises: monotonicity and prefixes

* `FaultBoundAt.mono_right`: a count charged at a later horizon is a stronger premise (the honest
  set only shrinks).
* `SyncOnAt.mono`: `Sync` on a window gives `Sync` on every smaller window.
* `SleepyRunAt.prefix`: `Sleepy` with look-ahead `W` gives its prefix form through every `b ≥ 0`
  (the growing-fault form of `RunTrace.SleepyRun.prefix`). -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Time → Set (Fin P.n)}

/-- **The count is antitone in its horizon.** -/
theorem FaultBoundAt.mono_right (hanti : Antitone H) {t d d' : Time} (hd : d' ≤ d)
    (h : tr.FaultBoundAt H t d) : tr.FaultBoundAt H t d' := by
  have hsub : H d ⊆ H d' := hanti hd
  calc (H d')ᶜ.ncard ≤ (H d)ᶜ.ncard :=
        Set.ncard_le_ncard (Set.compl_subset_compl.mpr hsub) (Set.toFinite _)
    _ < {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard := h
    _ ≤ {y | y ∈ H d' ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard :=
        Set.ncard_le_ncard (fun y hy => ⟨hsub hy.1, hy.2⟩) (Set.toFinite _)

/-- `Sync` on a window gives `Sync` on every smaller window. -/
theorem SyncOnAt.mono {ΔF : Time} {W W' Wr Wr' : Time → Prop} {eff : Time → Time}
    (h : tr.SyncOnAt H ΔF W Wr eff) (hW : ∀ τ, W' τ → W τ) (hWr : ∀ τ, Wr' τ → Wr τ) :
    tr.SyncOnAt H ΔF W' Wr' eff :=
  ⟨h.deltaF, h.delta_le, fun x i m hx hs hw => h.message x i m hx hs (hW _ hw),
    fun x i B hx hs hw => h.block x i B hx hs (hW _ hw),
    fun x i B hx hs hw => h.relay x i B hx hs (hWr _ hw),
    fun x i a hx hs hw => h.attestation x i a hx hs (hW _ hw)⟩

/-- **`Sleepy` with look-ahead `W` gives the prefix premises up to every `b ≥ 0`.** The look-ahead
of each slot point is clamped at `b`, a weaker horizon. -/
theorem SleepyRunAt.prefix (hanti : Antitone H) {ΔF W : Time} (hsl : tr.SleepyRunAt H ΔF W)
    {b : Time} (hb : 0 ≤ b) : tr.SleepyPrefixAt H ΔF W b :=
  ⟨hb, hsl.1.mono (fun _ hw => hw.1) (fun _ hw => hw.1), fun s d hd _ =>
    FaultBoundAt.mono_right hanti (min_le_left _ _) (hsl.2 s d hd)⟩

end Consensus.Goldilocks.RunTrace

end
