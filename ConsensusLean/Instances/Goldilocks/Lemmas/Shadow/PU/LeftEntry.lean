module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore

public section

/-! # Shadow P-U: left-entry provenance

The stock RowSource and LeftEntry arguments instantiated with the proved shadow run cores.
AC-only facts use the stock AC projection inside those cores.
-/

namespace Consensus.Goldilocks.Healing.ShadowLeft

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The stock local RowSource extraction, keeping joinedness as the AC trace predicate. -/
theorem signed_entry_source {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {v : Fin sp.n} (hv : v ∈ H) {d : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt v d att)
    (hfast : ∀ d' ell C, d' < d → AC.ToFGAt tr.projAC v d' ell C →
      att.h ≤ ((tr.state v d').fg.σ C.root).h →
      C ∈ AC.toFGCandidates sp (tr.projAC.state v d') ell.frame (tr.time d')) :
    ∃ r < d, ∃ l O, AC.joined sp (tr.projAC.state v r) (tr.time r) ∧
      (∃ CV, Compose.StoredFastLockAt tr v r l O CV) ∧
      att.h ≤ ((tr.state v r).fg.σ O.root).h ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root := by
  obtain ⟨r, hrd, l, O, -, hstored, rest⟩ :=
    Growing.Outcome.signed_entry_source_core hrun.toStaticCore hnc hv hs hfast
  obtain ⟨CV, ell, D, hc, hfl, hO⟩ := hstored
  have hj := (Healing.joined_of_fastLockAt
    (Compose.goldilocks_ac_projection_from' hrun hnc).localRun hv hfl).1
  exact ⟨r, hrd, l, O, hj, ⟨CV, ell, D, hc, hfl, hO⟩, rest⟩

end Consensus.Goldilocks.Healing.ShadowLeft

namespace Consensus.Goldilocks.Healing.Growing.ShadowLeft

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The stock RowSource wrapper, using the proved shadow deep quarantine. -/
theorem high_row_source_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time} {v : Fin sp.n} {d : Nat}
    {att : FG.Att sp.n} (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d)))
    (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hq : ∀ D, sp.deepDepth = some D → tr.time d ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root :=
  Outcome.high_row_source_at_core hrun.toCore hnc hvz hs hh hsnap hq

theorem signed_row_lock_member {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g a b : Time} {v : Fin sp.n} {d : Nat}
    {att : FG.Att sp.n} (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d)))
    (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧ ∃ r < d, ∃ s C D,
      HealedMemberBefore tr H g a b C s d ∧
      Anc (tr.HonestBlocksAt H) E C ∧ Anc (tr.HonestBlocksAt H) C D ∧
      v ∈ H (tr.time r) ∧
      ((∃ CV, AC.FastLockAt tr.projAC v r s D CV) ∨ AC.SlowLockAt tr.projAC v r s D) :=
  Outcome.signed_row_lock_member_before_at_core hrun.toCore hnc hvz hs hh hsnap hc hdb

end Consensus.Goldilocks.Healing.Growing.ShadowLeft

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {g ΔF a b hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

end Consensus.Goldilocks.Healing.Growing

end
