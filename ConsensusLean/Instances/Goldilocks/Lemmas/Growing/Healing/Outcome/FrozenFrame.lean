module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport

public section

/-! # A voter's pre-freeze block reaches the proposer's frame, under growing faults

`reset_frozen_frame_at`, the growing form of `Healing.ResetPremisesUpTo.reset_frozen_frame`
(`Healing/Outcome/SupplierFrames`): a bounded pre-freeze block of a voter honest at its cast,
above the `Σ.F` of a proposer honest at its proposal call, is in the proposer's frame. The
block's stamp is an acceptance of the voter, honest then, relayed to the proposer. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A bounded pre-freeze block of a voter honest at its cast, above the `Σ.F` of a proposer
honest at its proposal call, is in the proposer's frame. -/
theorem reset_frozen_frame_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {i j s : Nat} (hpH : p ∈ H (tr.time i)) (hy : y ∈ H (tr.time j))
    {ellp elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hcy : SA.CastAt tr.projAC y j elly e) (hib : tr.time i ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ elly.frame.tree)
    (hst : e.readPoint.blockStamp B.root < SA.ETime.of (SA.freeze sp (s + 1)))
    (hF : Anc (tr.HonestBlocksAt H) ellp.frame.F B) : B ∈ ellp.frame.tree := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg j)).localRun
  have hcy' := SA.upTo_castAt.mpr ⟨le_rfl, hcy⟩
  rw [SA.readPoint_blockStamp_eq hr hy hcy'] at hst
  rcases Healing.stamp_origin hr hy j elly hcy'.1 B hB with hgen |
      ⟨q, hqj, ellq, hcq, hBq, hstamp⟩
  · have hri := (hac.upTo (hp.run.time_nonneg i)).localRun
    have hci' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hci⟩
    obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hri hpH i ellp hci'
    obtain rfl : B = G := hac.localRun.coherent.1
      ((SA.frameIn_of_callAt hr hy hcy'.1).2 hB) hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hri hpH hci').1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rw [hstamp] at hst
    have ht : tr.time q < SA.freeze sp (s + 1) :=
      WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
    have hqi : tr.time q + sp.Δ ≤ tr.time i := by
      rw [hti]
      simp only [SA.freeze, SA.SAParams.ts] at ht ⊢
      push_cast at ht ⊢
      linarith only [ht]
    rcases Compose.frame_anc_accepted hr hy q ellq hcq B hBq B .refl with hgen |
        ⟨k, hkq, hak⟩
    · have hri := (hac.upTo (hp.run.time_nonneg i)).localRun
      have hci' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hci⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hri hpH i ellp hci'
      obtain rfl : B = G := hac.localRun.coherent.1
        ((SA.frameIn_of_callAt hr hy hcq).2 hBq) hGU (hgen.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
      · exact he ▸ (SA.frameIn_of_callAt hri hpH hci').1.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    · obtain ⟨ellk, hck, hb⟩ := hak
      obtain ⟨hkt, hck⟩ := (Trace.upTo_callAt tr.projAC).mp hck
      have hyk := hp.run.antitone hkt hy
      obtain ⟨k', rfl, ha, htime⟩ := Obligations.Growing.acBlock_prev_at hp.run hyk
        (Compose.projAC_callAt.mp hck) hb
      exact Outcome.accept_mem_frame hp hc (hp.run.antitone htime.le hyk) hpH ha hci
        hib hg hjoin (by
          rw [htime]
          linarith only [hp.run.time_mono hkq, hqi]) hF

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
