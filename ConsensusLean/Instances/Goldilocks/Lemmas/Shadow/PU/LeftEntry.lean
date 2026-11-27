module
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

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp}

/-- The stock local RowSource extraction, keeping joinedness as the AC trace predicate. -/
theorem signed_entry_source {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
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

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp}

/-- The stock RowSource wrapper, using the proved shadow deep quarantine. -/
theorem high_row_source_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
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
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
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

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp}
  {g ΔF a b hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- At a time bounded by the reset horizon, deep quarantine or the high-source cover holds. -/
theorem ResetPremisesUpTo'.quarantine_or_cover_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {t : Time} (htb : t ≤ b) :
    (∀ D, sp.deepDepth = some D → t ≤ cutZ sp.toParams g + 4 * D * sp.Δ) ∨
      HighSourceCover tr H g a b :=
  hp.toCore.quarantine_or_cover_at htb

/-- Inside the deep quarantine a left high entry has a prior high origin above it. -/
theorem ResetPremisesUpTo'.left_entry_origin_of_quarantine_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h)
    (hpre : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧
        ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ Anc (tr.HonestBlocksAt H) E O :=
  hp.toCore.left_entry_origin_of_quarantine_at ht hle hy htb hE hET hEh hEC hlt hpre

/-- A left high entry has an earlier high origin, or is covered after the deep quarantine.
This is the stock left-entry contract over the shadow execution. -/
theorem ResetPremisesUpTo'.left_entry_origin_or_covered_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧
        ((∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ Anc (tr.HonestBlocksAt H) E O) ∨
          (v ∈ H (max (cutZ sp.toParams g) t) ∧ CoveredUpTo tr H g a b (sp.slot t) E)) :=
  hp.toCore.left_entry_origin_or_covered_at ht hle hy htb hE hET hEh hEC hlt

end Consensus.Goldilocks.Healing.Growing

end
