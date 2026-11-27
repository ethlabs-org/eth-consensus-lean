module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Joining from a restart bound over the run core -/

namespace Consensus.Goldilocks.Healing.Growing.Core

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- A restart bound joins a node independently of the finality update and node frame. -/
theorem joined_of_restart_le_at
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {t : Time} {s : Nat} (hy : y ∈ H t)
    (ht : sp.ts s + 4 * sp.Δ ≤ t)
    (hres : ∀ r, tr.time r ≤ t → y ∈ H (tr.time r) → tr.RestartAt y r → tr.time r ≤ sp.ts s)
    {i : Nat} (htime : tr.time i = t) :
    AC.joined sp (tr.projAC.state y i) (tr.time i) := by
  have hΔ := sp.toParams.hΔ
  have hs0 : 0 ≤ sp.ts s := by simp only [ACParams.ts]; positivity
  have ht0 : 0 ≤ t := by linarith
  have hac := (hrun.acRun_upTo hnc ht0).localRun
  have hst : (tr.projAC.upTo t).state y i = tr.projAC.state y i :=
    Trace.upTo_state tr.projAC y (fun q hq => (hrun.time_mono hq.le).trans htime.le)
  rw [← hst]
  unfold AC.joined
  rcases AC.restartTime_stateU hac.toU hrun.vstart hy i with h | ⟨r, _, hrs, h⟩
  · rw [h]; exact bot_le
  · rw [h]
    apply WithBot.coe_le_coe.mpr
    have hrs' : (tr.upTo t).RestartAt y r := by
      apply Compose.projAC_restartAt.mp
      rwa [RunTrace.upTo_projAC]
    obtain ⟨hrt, hrs⟩ := (RunTrace.upTo_restartAt tr).mp hrs'
    have hrestart := hres r hrt (hrun.antitone hrt hy) hrs
    have hs : s + 1 ≤ sp.slot t := by
      apply Int.ofNat_le.mp
      apply (AC.ts_le_iff_le_slot sp ht0 _).1
      have heq : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      rw [heq]
      exact ht
    have hts : sp.ts s ≤ sp.ts ((sp.slot t : Int) - 1) :=
      (AC.ts_le_iff sp).2 (by omega)
    change tr.time r ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
    rw [htime]
    exact hrestart.trans hts

end Consensus.Goldilocks.Healing.Growing.Core

end
