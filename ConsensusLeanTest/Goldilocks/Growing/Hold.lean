module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises

@[expose] public section

/-! # The release hold of `SyncOnAt` at `0`

`SyncOnAt` takes a release hold `hold` (default `0`): its attestation clause covers a signing and
the signer's own admission at the signing time only when the signer is honest at `eff + hold`.
`SyncOnAtNoHold` restates the premise as it was before the hold, verbatim. At `hold = 0` the two
agree (`syncOnAt_zero_iff`), and so do `GSTRunAt` and `HealthyRunAt` at their default hold: every
statement that reads them at the default keeps its meaning. -/

namespace Consensus.Goldilocks.Test.Hold

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- `SyncOnAt` as stated before the release hold. -/
structure SyncOnAtNoHold (H : Time → Set (Fin P.n)) (ΔF : Time) (W Wr : Time → Prop)
    (eff : Time → Time) : Prop where
  deltaF : 0 < ΔF
  delta_le : P.Δ ≤ ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m → W (tr.time i) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (eff (tr.time i)) m
  block : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    W (tr.time i) → ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (eff (tr.time i)) B
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → Wr (tr.time i) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (eff (tr.time i)) B
  attestation : ∀ x i a, x ∈ H (tr.time i) → tr.SendOrAdmitAttAt x i a → W (tr.time i) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (eff (tr.time i)) ΔF ≤ tr.time j →
      tr.AttDeliveredBy y j (eff (tr.time i)) ΔF a

/-- **At hold `0`, `SyncOnAt` is the premise before the hold.** -/
theorem syncOnAt_zero_iff {H : Time → Set (Fin P.n)} {ΔF : Time} {W Wr : Time → Prop}
    {eff : Time → Time} : tr.SyncOnAt H ΔF W Wr eff ↔ SyncOnAtNoHold tr H ΔF W Wr eff :=
  ⟨fun ⟨d, l, m, b, r, a, _⟩ => ⟨d, l, m, b, r, fun x i a' hx hs hw =>
      a x i a' hx hs hw fun _ _ _ _ h => (h rfl).elim⟩,
    fun ⟨d, l, m, b, r, a⟩ => ⟨d, l, m, b, r, fun x i a' hx hs hw _ => a x i a' hx hs hw, d.le⟩⟩

/-- `GST(g)` at the default hold is `GST(g)` before the hold. -/
theorem gstRunAt_iff {H : Time → Set (Fin P.n)} {ΔF g : Time} :
    tr.GSTRunAt H ΔF g ↔
      SyncOnAtNoHold tr H ΔF (fun _ => True) (fun τ => g ≤ τ) (fun τ => max τ g) :=
  syncOnAt_zero_iff tr

/-- `Healthy(g)` at the default hold is `Healthy(g)` before the hold. -/
theorem healthyRunAt_iff {H : Time → Set (Fin P.n)} {ΔF g : Time} :
    tr.HealthyRunAt H ΔF g ↔
      SyncOnAtNoHold tr H ΔF (fun _ => True) (fun τ => g ≤ τ) (fun τ => max τ g) ∧
        (∀ y t, max g 0 ≤ t → y ∈ H t → tr.awake y t) ∧ ∀ t, 3 * (H t)ᶜ.ncard ≤ P.n - 1 :=
  and_congr_left' (gstRunAt_iff tr)

end Consensus.Goldilocks.Test.Hold

end
