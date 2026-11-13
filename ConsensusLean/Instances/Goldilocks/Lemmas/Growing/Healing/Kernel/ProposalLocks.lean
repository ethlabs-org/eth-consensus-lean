module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Historical sources of proposal locks

Provenance is read on the proposer's prefix. It preserves honesty at the
earlier optimistic write without requiring any other writer to survive.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- At a proposal, a stored high lock comes from an earlier optimistic write of
the previous slot; regular updates and current-slot optimistic writes are too late. -/
theorem proposal_high_lock_source_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {l : SA.Lock} (hl : l ∈ (tr.projAC.state p i).locks) (hlabel : u - 1 ≤ l.slot) :
    ∃ r D CV, r < i ∧ l.slot = u - 1 ∧ p ∈ H (tr.time r) ∧
      SA.OptimisticLockAt tr.projAC p r l.slot D CV ∧
      ∃ L ∈ tr.HonestBlocksAt H, L.root = l.block ∧ Anc (tr.HonestBlocksAt H) L D := by
  have hm := hp.run.time_mono
  have ht0 := hp.run.time_nonneg i
  have hr := hp.run.upTo ht0
  have hac := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i))
    (tr.upTo (tr.time i)) proposer hr (hp.noColl.upTo _)).localRun
  have hs : (tr.upTo (tr.time i)).projAC.state p i = tr.projAC.state p i := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC p fun _ hq => hm hq.le
  obtain ⟨r, hri, D, hw, L, hL, hLr, hLD⟩ := SA.lock_provenance hac hpH i l (hs ▸ hl)
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hm hri.le
  rcases hw with ⟨CV, hop⟩ | ⟨ell', hupd⟩
  · have hop' := hop
    rw [RunTrace.upTo_projAC] at hop'
    have hop₀ := (SA.upTo_optimisticLockAt hm).mp hop' |>.2
    have hle : l.slot ≤ u := by
      obtain ⟨_, _, _, hsl, _⟩ := hop₀
      change sp.slot (tr.time r) = l.slot at hsl
      have hts := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) l.slot).mpr (by omega)
      exact_mod_cast (SA.ts_le_iff sp).mp (hts.trans hrt)
    have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
      have := hp.faults _ ht0 hib
      have hn : 0 < sp.n := sp.toParams.hn
      omega
    have hcp : (tr.upTo (tr.time i)).projAC.CallAt p i ell := by
      rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hci⟩
    have hne : l.slot ≠ u := fun he =>
      Healing.proposal_no_optimistic_of_run hr (hp.noColl.upTo _) hf hpH hcp hcall hti
        hp.stock p hpH r hri D CV (he ▸ hop)
    exact ⟨r, D, CV, hri, by omega, hp.run.antitone (hm hri.le) hpH, hop₀,
      L, RunTrace.honestBlocks_upTo_subset hm ht0 hL, hLr,
      hLD.mono (RunTrace.honestBlocks_upTo_subset hm ht0)⟩
  · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    have hslots := (SA.ts_le_iff sp).mpr (show (u : Int) ≤ l.slot + 1 by omega)
    have hΔ := sp.toParams.hΔ
    have hsucc : sp.ts (l.slot + 1 : Nat) = sp.ts l.slot + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    have hslots' : sp.ts u ≤ sp.ts (l.slot + 1 : Nat) := by exact_mod_cast hslots
    rw [hsucc] at hslots'
    exfalso
    linarith

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
