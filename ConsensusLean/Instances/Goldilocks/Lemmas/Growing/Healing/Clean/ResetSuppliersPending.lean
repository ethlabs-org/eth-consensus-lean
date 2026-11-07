module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool

public section

/-! # Stand-ins for the node and seed layers of the reset-form suppliers

The node-layer and seed-layer facts that `Clean/ResetSuppliers` uses and that are not yet on this
line, stated under their owners' names and statements, implicits in the source's order:

* `Compose.Growing.carryAt_of_delivered`, `Compose.Growing.result_writer_at`
  (`Growing/Sleepy/Node/Transport`);
* `Healing.Growing.fault_bound_late_before_at` (`Growing/Obligations/Healthy/Windows`).

Each theorem here is an open `sorry`; this module is deleted when those modules are on this
line. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro}

/-- **`Carry_y` from deliveries**, for one honest voter over an SA trace. -/
theorem carryAt_of_delivered (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T) {s : Nat}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1)
    {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ τ, sp.ts s ≤ τ ∧ τ < sp.ts s + 2 * sp.Δ ∧
        (T.deadline y i τ ≤ T.time i → SA.MessageServedBefore T y i τ v)) ∧
      ∃ Hv : SA.Blk sp.n FGP, Hv.root = v.head ∧
        ((∃ τ, τ < sp.ts s + 2 * sp.Δ ∧ (T.deadline y i τ ≤ T.time i →
            ∃ k ≤ i, T.AcceptAt y k Hv ∧ T.time k < T.deadline y k τ)) ∨
          SA.AcceptedBefore T y Hv (sp.ts s + 3 * sp.Δ))) :
    SA.CarryAt T U y i e s CV := by
  sorry

end Node

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **What a result's writer did with its counted votes**, for a writer honest at its update. -/
theorem result_writer_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {X : Fin sp.n} {i₀ s : Nat} (hX : X ∈ H (tr.time i₀))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, X ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ tr.HonestBlocksAt H, Hv.root = v.head ∧ Anc (tr.HonestBlocksAt H) C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, X ∈ H (tr.time k) ∧ tr.projAC.AcceptAt X k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ) := by
  sorry

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **The late fault bound**: from the cut on, the faults at any `d ∈ [t, b]` are fewer than the
validators honest at `d` that are awake and joined at `t`. -/
theorem fault_bound_late_before_at {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {t d : Time} (ht : cutZ sp.toParams g ≤ t) (htd : t ≤ d) (hdb : d ≤ b) :
    tr.FaultBoundAt H t d := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end
