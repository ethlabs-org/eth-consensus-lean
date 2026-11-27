module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupport

public section

/-! # Committee fault bounds from shadow service

This stock counting argument sits below both witness and regular-vote consumers.
-/

namespace Consensus.Goldilocks.Healing.PU

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The stock committee count uses only honesty, awake service and restart bounds. -/
theorem faultBoundK_of_service_at {K : AC.CommitteeDict sp.n} {g b : Time}
    (hK : CommitteeHalfUpTo tr H K g b)
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g)) {s : Nat}
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b)
    {t : Time} (ht0 : 0 ≤ t) (hprev : gbar g ≤ sp.ts ((sp.slot t : Int) - 1)) (htb : t ≤ b) :
    AC.FaultBoundK K s tr.projAC (H t) t := by
  have hts : sp.ts ((sp.slot t : Int) - 1) ≤ t :=
    (AC.ts_le_iff_le_slot sp ht0 _).mpr (by omega)
  have hsub : K.committee s ∩ H t ⊆ K.committee s ∩
      {y | y ∈ H t ∧ tr.projAC.awake y t ∧ AC.JoinedAt tr.projAC y t} := by
    rintro y ⟨hyK, hy⟩
    refine ⟨hyK, hy, hawake y t hy (hprev.trans hts) htb, ?_⟩
    intro k hk hkt
    exact (hnr y k (hrun.antitone hkt hy) (Compose.projAC_restartAt.mp hk)).trans hprev
  have hf := hK.cs2 s hgs hsb t ht0 htb
  have hsplit : (K.committee s ∩ H t).ncard + (K.committee s ∩ (H t)ᶜ).ncard =
      sp.committeeSize := by
    rw [← hK.facts.hsize s]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  unfold AC.FaultBoundK
  exact lt_of_lt_of_le (by omega) (Set.ncard_le_ncard hsub)

end Consensus.Goldilocks.Healing.PU

end
