module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionCompatibility
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Strict

public section

/-! # Strict finalization below the unanimous proposal at its update

Compatibility is historical; the finalizer's strict slot bound is read only on
the updating node's prefix. No earlier origin writer must survive to this cut.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

theorem finalized_below_unanimous_at_update_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPU : P ∈ tr.HonestBlocksAt H) (hPs : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) (ha : a ≤ tr.time j) :
    Anc (tr.HonestBlocksAt H) ell.frame.F P := by
  have hm := hp.run.time_mono
  have hd := hp.run.time_nonneg j
  have hle : ∀ k < j, tr.time k ≤ tr.time j := fun k hk => hm hk.le
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hFR := finalized_compatible_before_update_at hp hc hPU hPs hu hun hgu hR hTb hy ha ht.le
  have hreach := fg_reachable_at hp.run hd hle hy
  have hFt := (Store.cache_invariants _ _ _ _ hreach).1
  have hsub : (tr.state y j).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, j, tr.time j, hd, hle, hy, h⟩
  rw [Outcome.frame_of_call hp.run hy hup.1]
  change Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P
  by_cases hg : (tr.state y j).fg.F =
      sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
  · exact ProposalImpl.genesis_root_anc_at hp.run hp.noColl (hsub hFt)
      (by rw [hg]; rfl) hPU
  obtain ⟨B, hBt, _, hFB, hne⟩ := Store.F_lt_finalizer hreach hg
  have hBf : B ∈ ell.frame.tree := by
    rw [Outcome.frame_of_call hp.run hy hup.1]
    exact ⟨hBt, hFB⟩
  have hr := (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer
    hp.run hp.noColl).upTo hd
  have hc' : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hup.1⟩
  have hsl : sp.slot ((tr.projAC.upTo (tr.time j)).time j) = u + 1 := by
    change sp.slot (tr.time j) = u + 1
    rw [ht, (SA.slot_arithmetic sp u).2.2]
    simpa using (SA.slot_arithmetic sp (u + 1)).1 2 (by omega)
  have hBs : B.slot ≤ u + 1 := hsl ▸ SA.frame_slot_le sp hr.localRun hy hc' B hBf
  have hFs : (tr.state y j).fg.F.slot < B.slot :=
    (Anc.slot_le hU (hFB.mono hsub)).2 hne
  rcases hFR with h | hPF
  · exact h
  by_cases he : P = (tr.state y j).fg.F
  · exact he ▸ .refl
  have := (Anc.slot_le hU hPF).2 he
  omega

end Consensus.Goldilocks.Healing.Growing

end
