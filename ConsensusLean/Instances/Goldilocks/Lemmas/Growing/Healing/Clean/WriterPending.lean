module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing

public section

/-! # Frozen growing interface of the AC writer comparisons

The growing forms of three AC-level writer lemmas that the clean cluster consumes, frozen under
their final names (static name + `_at`) for the AC ports owner. Each node is honest at its own
cut: a writer at its write, a receiver at its cast. The writer's facts come from its own prefix,
and the receiver's from the prefix through its cut. Service is the growing `ServiceWindowBefore`.
The catch-up premise is the static `CatchACWindowBefore` with each node honest at its own cut,
stated inline. No fault count or bound is added to the static statements:

* `SA.Growing.result_result_compatible_window_before_at` and
  `SA.Growing.result_optimistic_compatible_window_before_at` (`Healing/AC/Compat`). The static
  restart bound over all honest nodes is read only for the writers, each at its own cuts;
* `SA.Growing.raw_writer_voterBlockTree_window_before_at` (`Healing/Retention/Relay`).

`first_transfer_stored`, `result_transfer` and `optimistic_transfer_stored` (main) and the
next-transfer statement are reused, not restated. Each theorem here is an open `sorry`; this module
is deleted when the home modules land. -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- Same-slot results of writers honest at their writes are compatible, using only service
through their observation cutoff. -/
theorem result_result_compatible_window_before_at (hrun : ACRun proposer tr H U)
    {a b : Time} {s : Nat} (hsync : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {x x' : Fin sp.n} {i i' : Nat} (hx : x ∈ H (tr.time i)) (hx' : x' ∈ H (tr.time i'))
    {C C' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)}
    (hR : ResultAt tr x i s C CV) (hR' : ResultAt tr x' i' s C' CV')
    (hi : tr.time i ≤ b) (hi' : tr.time i' ≤ b)
    (hreset : ∀ q ≤ i, tr.RestartAt x q → tr.time q ≤ sp.ts s)
    (hreset' : ∀ q ≤ i', tr.RestartAt x' q → tr.time q ≤ sp.ts s) :
    Compatible U C C' := by
  sorry

/-- A result and an optimistic lock of one slot, by writers honest at their writes, agree with
windowed message service. -/
theorem result_optimistic_compatible_window_before_at (hrun : ACRun proposer tr H U)
    {a b : Time} {s : Nat} (hsync : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {x x' : Fin sp.n} {i i' : Nat} (hx : x ∈ H (tr.time i)) (hx' : x' ∈ H (tr.time i'))
    {C O : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)}
    (hR : ResultAt tr x i s C CV) (hO : OptimisticLockAt tr x' i' s O CV')
    (hi : tr.time i ≤ b) (hi' : tr.time i' ≤ b)
    (hreset : ∀ q ≤ i, tr.RestartAt x q → tr.time q ≤ sp.ts s) : Compatible U C O := by
  sorry

/-- An ancestor of a raw writer's block, for a writer honest at its write, is available in the
frozen block tree of a later voter honest at its cast. -/
theorem raw_writer_voterBlockTree_window_before_at
    (hr : Consensus.Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {a b κ : Time} (hsync : ServiceWindowBefore H U a b tr)
    (hcatch : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → tr.time i < a →
      ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → a + κ ≤ tr.time j → tr.time j ≤ b →
        Anc U ℓ.frame.F B → ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < a + κ)
    {x y : Fin sp.n} {j i s : Nat} (hx : x ∈ H (tr.time j)) (hy : y ∈ H (tr.time i))
    {B C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hwriter : ResultAt tr x j s C CV ∨ FastLockAt tr x j s C CV)
    (hBC : Anc U B C) {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : s + 1 ≤ e.msg.slot) (hi : tr.time i ≤ b)
    (hcatchTime : a + κ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ)
    (hF : Anc U ℓ.frame.F B) : B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  sorry

end Consensus.Goldilocks.SA.Growing

end
