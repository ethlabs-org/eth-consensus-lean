module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc

public section

/-! # Historical counted supporters of regular writes -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A result has an earlier counted vote signed while its validator was honest.
The writer pool and participation bound are read only at the update cut. -/
theorem result_honest_supporter_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x c s C CV) (hcb : tr.time c ≤ b)
    (hstock : sp.committeeSize = sp.n) :
    ∃ z q, z ∈ H (tr.time q) ∧ q < c ∧ ∃ e, SA.VoteAt tr.projAC z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch
    (hrun.time_nonneg c) hcb hstock
  have hres' := (SA.upTo_resultAt hrun.time_mono).mpr ⟨le_rfl, hres⟩
  obtain ⟨ell, hu, hconf, hCV⟩ := hres'
  have hHV : H (tr.time c) ⊆ SA.voters
      {v | v ∈ ((tr.projAC.upTo (tr.time c)).state x c).pool s} := by
    intro z hz
    exact SA.honest_voter_at_update_before hS
      (fun y hy r hrs => by
        obtain ⟨hrt, hrs⟩ := (ACTrace.upTo_restartAt (tr := tr.projAC)).mp hrs
        exact hnr y r (hrun.antitone hrt hy) (Compose.projAC_restartAt.mp hrs))
      hx hu hm le_rfl hz
  obtain ⟨z, hz, q, hqc, e, he, hmem, hes, R, hR, hroot, hCR⟩ :=
    SA.result_honest_supporter_of_participants sp hS.run hx ⟨ell, hu, hconf, hCV⟩
      (B := C) .refl (by
        have hn : (H (tr.time c)).ncard + (H (tr.time c))ᶜ.ncard = sp.n := by
          rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
        have hcard := Set.ncard_le_ncard hHV
        have hbound := hf _ (hrun.time_nonneg c) hcb
        have hnpos : 0 < sp.n := sp.toParams.hn
        omega)
  obtain ⟨hqt, he⟩ := SA.upTo_voteAt.mp he
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg c)
  exact ⟨z, q, hrun.antitone hqt hz, hqc, e, he, hmem, hes,
    R, hsub hR, hroot, hCR.mono hsub⟩

/-- The fault margin at a healthy observation cut counts validators honest at that cut. -/
theorem faultBound_of_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g)) {t : Time} (ht0 : 0 ≤ t)
    (hprev : gbar g ≤ sp.ts ((sp.slot t : Int) - 1)) (htb : t ≤ b) :
    SA.FaultBoundAt tr.projAC H t t := by
  have hts : sp.ts ((sp.slot t : Int) - 1) ≤ t :=
    (SA.ts_le_iff_le_slot sp ht0 _).mpr (by omega)
  have hsub : H t ⊆ {y | y ∈ H t ∧ tr.projAC.awake y t ∧ SA.JoinedAt tr.projAC y t} := by
    intro y hy
    refine ⟨hy, hawake y t hy (hprev.trans hts) htb, ?_⟩
    intro k hk hkt
    exact (hnr y k (hrun.antitone hkt hy) (Compose.projAC_restartAt.mp hk)).trans hprev
  have hle := Set.ncard_le_ncard hsub
  have hn : (H t).ncard + (H t)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hbound := hf t ht0 htb
  have hnpos : 0 < sp.n := sp.toParams.hn
  change (H t)ᶜ.ncard < {y | y ∈ H t ∧ tr.projAC.awake y t ∧ SA.JoinedAt tr.projAC y t}.ncard
  omega

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
