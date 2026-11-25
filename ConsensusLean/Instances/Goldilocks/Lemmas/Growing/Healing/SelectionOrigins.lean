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
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee

public section

/-! # Origins below the next unanimous slot -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- Before the next slot, high origins have either an older label or the unanimous label.
Older origins are tested against a surviving voter, not their possibly compromised writer. -/
theorem high_origins_before_next_slot_below_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) {x : Fin sp.n} {r m : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x r m B)
    (ht : tr.time r < sp.ts (u + 1 : Nat)) (hrb : tr.time r ≤ b) :
    Anc (tr.HonestBlocksAt H) B P := by
  obtain ⟨CV, ell, D, hcall, hfl, hB⟩ := ho.2.2.1
  have hmu : m ≤ u := by
    rcases hfl with ⟨ell', C, hu, _⟩ | ⟨ell', A, _, hs, _⟩
    · have htime : tr.time r = sp.ts m + 6 * sp.Δ := hu.2.2.1
      have hts : sp.ts m < sp.ts (u + 1 : Nat) := by linarith [sp.toParams.hΔ]
      have := (AC.ts_lt_iff sp).1 hts
      omega
    · have hs' : sp.slot (tr.time r) = m := hs
      have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) ((u + 1 : Nat) : Int)).not.mp
        (not_le.mpr ht)
      omega
  rcases lt_or_eq_of_le hmu with hmu | rfl
  · have hT0 : 0 ≤ sp.ts u + sp.Δ := by
      have := AC.gbar_nonneg g
      linarith [sp.toParams.hΔ]
    obtain ⟨w, hwK, hw⟩ := hp.committee_honest_nonempty_at (s := u)
      (by linarith [sp.toParams.hΔ]) (by linarith [sp.toParams.hΔ]) hT0 hub
    obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot_at hp hgu hR hub w hw hwK
    obtain ⟨ellv, hcast⟩ := hv
    have hwq := hp.run.antitone hq hw
    obtain ⟨Hd, hHd, he, hBH⟩ := hp.high_origin_votes_before_at q (hq.trans hub)
      x r m B ho hrb w ellv e hwq hcast (by omega)
    have heq : Hd = P := (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1 hHd hP
      (he.trans (hun w q e hwq ⟨ellv, hcast⟩ (hq.trans hub) hs))
    exact heq ▸ hBH
  · obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
    have hx := hp.run.antitone (le_max_right _ _) ho.1
    obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hc'.2)
    have hac := (Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl)
    obtain ⟨hPhi, hsub⟩ : FrameOK ell.frame ∧ ell.frame.tree ⊆ tr.HonestBlocksAt H := by
      rcases hac.localRun.frameLaw x r ell hx hcall with
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.1
    have hBD := (AC.anc_viableAncestor ell.frame D).mono hsub
    rw [← hB] at hBD
    exact hBD.trans (hp.same_slot_source_below_unanimous_at hx
      (Or.inl ⟨CV, hfl⟩) hrb (hp.cutZ_le_ts_of_highOrigin_at ho) hP hun)

end Consensus.Goldilocks.Healing.Growing

end
