module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageReader
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageS5.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageGate
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage S5: the early record

An honest update of the
first restored label `r` makes the effective record of its updater a block above `P` at every
later cut (`record_above_of_update_r`):
* when `P ⪯ Σ.F` at the update, the effective record is a block of a later frame, so it extends
  that frame's `Σ.F`, which extends the update's;
* otherwise the gate's result extends `P` (O4's `gate_result_extends` with the cohort majority
  `restored_majority_at_r`), and lock safety's `record_above_from` keeps the record above `P`,
  whether the result is accepted or vetoed. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

variable (D : OutageLockPremises tr H proposer dg)

/-- **The early record** (§9.2(b)–(c)): an actual update at label `r` makes the effective record
`⪰ P` at every later cut. -/
theorem record_above_of_update_r
    (hS : ∀ y ∈ H, ReceiverServiceAfter H (tr.HonestBlocks H) D.b₁ y tr.projAC)
    (hinv : ∀ i, OutageLockInv D i) {w : Fin sp.n} (hw : w ∈ H) {c : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC w c D.r ℓ) :
    ∀ c', c < c' → Anc (tr.HonestBlocks H) D.P
      ((SA.lookup (Node.frame (tr.state w c')) (tr.state w c').ac.latestConfirmed).getD
        (Node.frame (tr.state w c')).F) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hfr : ℓ.frame = Node.frame (tr.state w c) :=
    (D.hrun.cutLaw w hw c _ (projAC_callAt.1 hu.1)).1
  have ht : tr.time c = sp.ts D.r + 6 * sp.Δ := hu.2.2.1
  intro c' hcc'
  by_cases hPF : Anc (tr.HonestBlocks H) D.P (tr.state w c).fg.F
  · -- the effective record is a block of the later frame, above its `Σ.F ⪰ P`
    have hΦ := frameOK_state D.hrun.toLocalRun hw c'
    have hΦU : (Node.frame (tr.state w c')).tree ⊆ tr.HonestBlocks H :=
      fun Z hZ => ⟨w, hw, c', hZ.1⟩
    have hFF := Healing.run_F_mono D.hrun.toLocalRun hw hcc'.le
    have hPF' : Anc (tr.HonestBlocks H) D.P (Node.frame (tr.state w c')).F := hPF.trans hFF
    cases he : SA.lookup (Node.frame (tr.state w c')) (tr.state w c').ac.latestConfirmed with
    | none => exact hPF'
    | some E =>
      obtain ⟨hEt, -⟩ := SA.lookup_eq_some he
      exact hPF'.trans (Anc.mono hΦU (hΦ.rooted.2 E hEt))
  -- otherwise `Σ.F ⪯ P`, and the gate's result extends `P`
  have hFP : Anc (tr.HonestBlocks H) ℓ.frame.F D.P := by
    rw [hfr]
    exact ((hinv c).caches w hw c le_rfl).1.resolve_right hPF
  have hcall : ∃ x ∈ H, ∃ i, tr.IsCall x i ∧ sp.ts D.r + sp.Δ ≤ tr.time i :=
    ⟨w, hw, c, ⟨_, projAC_callAt.1 hu.1⟩, by linarith⟩
  obtain ⟨⟨C, CV, hR⟩, hall⟩ := gate_result_extends D.hrun D.hnc hw (hS w hw) hu D.hr.1
    (restored_majority_at_r D hinv hcall) hFP
  exact record_above_from hinv hw hu hR le_rfl (hall C CV hR) c' hcc'

end Consensus.Goldilocks.Compose

end
