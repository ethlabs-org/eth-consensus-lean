module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SameSlot
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Origins below the next unanimous slot -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Before the next slot, high origins have either an older label or the unanimous label.
Older origins are tested against a surviving voter, not their possibly compromised writer. -/
theorem high_origins_before_next_slot_below_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) {x : Fin sp.n} {r m : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x r m B)
    (ht : tr.time r < sp.ts (u + 1 : Nat)) (hrb : tr.time r ≤ b) :
    Anc (tr.HonestBlocksAt H) B P := by
  obtain ⟨CV, ell, D, hcall, hfl, hB⟩ := ho.2.2.1
  have hmu : m ≤ u := by
    rcases hfl with ⟨ell', C, hu, _⟩ | ⟨ell', A, _, hs, _⟩
    · have htime : tr.time r = sp.ts m + 6 * sp.Δ := hu.2.2.1
      have hts : sp.ts m < sp.ts (u + 1 : Nat) := by linarith [sp.toParams.hΔ]
      have := (SA.ts_lt_iff sp).1 hts
      omega
    · have hs' : sp.slot (tr.time r) = m := hs
      have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) ((u + 1 : Nat) : Int)).not.mp
        (not_le.mpr ht)
      omega
  rcases lt_or_eq_of_le hmu with hmu | rfl
  · have hT0 : 0 ≤ sp.ts u + sp.Δ := by
      have := SA.gbar_nonneg g
      linarith [sp.toParams.hΔ]
    obtain ⟨w, hw⟩ : (H (sp.ts u + sp.Δ)).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have hf := hp.faults _ hT0 hub
      rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hf
      have := sp.toParams.hn
      change 0 < sp.n at this
      omega
    obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot_at hp hc hgu hR hub w hw
    obtain ⟨ellv, hcast⟩ := hv
    have hwq := hp.run.antitone hq hw
    obtain ⟨Hd, hHd, he, hBH⟩ := hp.high_origin_votes_before_at q (hq.trans hub)
      x r m B ho hrb w ellv e hwq hcast (by omega)
    have heq : Hd = P := (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1 hHd hP
      (he.trans (hun w q e hwq ⟨ellv, hcast⟩ (hq.trans hub) hs))
    exact heq ▸ hBH
  · obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
    obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hc'.2)
    have hac := (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl)
    obtain ⟨hPhi, hsub⟩ : FrameOK ell.frame ∧ ell.frame.tree ⊆ tr.HonestBlocksAt H := by
      rcases hac.localRun.frameLaw x r ell ho.1 hcall with
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.1
    have hBD := (SA.anc_viableAncestor ell.frame D).mono hsub
    rw [← hB] at hBD
    exact hBD.trans (hp.same_slot_source_below_unanimous_at hc ho.1
      (Or.inl ⟨CV, hfl⟩) hrb (hp.cutZ_le_ts_of_highOrigin_at ho hrb) hP hun)

end Consensus.Goldilocks.Healing.Growing

end
