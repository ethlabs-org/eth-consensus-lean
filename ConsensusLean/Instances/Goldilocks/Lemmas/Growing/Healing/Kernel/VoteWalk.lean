module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.VoteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Noncurrent voter locks below the proposal parent

The two clean-parent inputs are the clean-source owner's exact contracts, taken
parametrically until their minimal import closure is available on this base.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A noncurrent live voter lock is below the actual parent when the two clean
source parent contracts hold. No source writer is assumed honest at the proposal. -/
theorem vote_old_live_lock_below_parent_of_sources_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    (hparent : ∀ {x r s B}, x ∈ H (tr.time r) →
      ((∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B) →
      cleanLabel sp a + sp.k + 2 ≤ s → s + 2 ≤ u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) B d.head)
    (hoptimistic : ∀ {x r s B CV}, x ∈ H (tr.time r) →
      SA.OptimisticLockAt tr.projAC x r s B CV → cleanLabel sp a + sp.k + 2 ≤ s →
      tr.time r ≤ b → u = s + 1 → Anc (tr.HonestBlocksAt H) B d.head)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ elly.frame.tree) (hLr : L.root = l.block) :
    Anc (tr.HonestBlocksAt H) (elly.frame.viableAncestor L) d.head := by
  obtain ⟨r, D, hrj, hclean, hlu, hyr, hsource, hLD⟩ :=
    vote_old_lock_source_before_at hp hy hcy hes hR hl hne hlive hL hLr
  have hrb := (hp.run.time_mono hrj.le).trans hjb
  apply hLD.trans
  by_cases hgap : l.slot + 2 ≤ u
  · exact hparent hyr hsource hclean hgap hrb
  have he : u = l.slot + 1 := by omega
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
    (tr.upTo (tr.time j)) proposer (hp.run.upTo (hp.run.time_nonneg j))
    (hp.noColl.upTo _)).localRun
  have hcy' : SA.CastAt (tr.upTo (tr.time j)).projAC y j elly e := by
    rw [RunTrace.upTo_projAC]
    exact (SA.upTo_castAt).mpr ⟨le_rfl, hcy⟩
  have htj := (Compose.cast_head_fcRoot hr hy hcy').2
  change tr.time j ≤ sp.ts e.msg.slot + sp.Δ at htj
  rw [hes, he] at htj
  have hrt := hp.run.time_mono hrj.le
  have hts : sp.ts (l.slot + 1 : Nat) = sp.ts l.slot + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hΔ := sp.toParams.hΔ
  rcases hsource with ⟨CV, hfast⟩ | ⟨ellX, C, hupd, _⟩
  · rcases hfast with ⟨ellX, C, hupd, _⟩ | hop
    · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      rw [hts] at htj
      exfalso
      linarith
    · exact hoptimistic hyr hop hclean hrb he
  · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    rw [hts] at htj
    exfalso
    linarith

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
