module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # High-origin labels before an honest proposal

An optimistic write of the proposal's own slot must be at exactly the proposal's
time. Its writer is therefore honest at that time, and the static exclusion applies
on that prefix without assuming survival across a compromise.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalSources

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

theorem origin_label_lt_at_proposal_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {v : Fin sp.n} {r l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u := by
  obtain ⟨hv, -, ⟨CV, ell', D, -, hfl, -⟩, -⟩ := ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ellR, C, ⟨-, -, ht, -⟩, -⟩ | hop
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    exact_mod_cast (SA.ts_lt_iff sp).mp
      (show sp.ts l < sp.ts u by linarith only [ht', hrt, hΔ])
  · obtain ⟨-, -, -, hsl, -⟩ := id hop
    change sp.slot (tr.time r) = l at hsl
    have hts : sp.ts l ≤ tr.time r :=
      (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) l).mpr (by omega)
    have hle : l ≤ u := by
      exact_mod_cast (SA.ts_le_iff sp).mp (hts.trans hrt)
    have hne : l ≠ u := by
      intro he
      rw [he] at hop hts
      have htime : tr.time r = tr.time i := hti.symm ▸ le_antisymm hrt hts
      have hd := hp.run.time_nonneg i
      have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
        have hf₃ := hp.faults _ hd hib
        have hn := sp.toParams.hn
        change 3 * (H (tr.time i))ᶜ.ncard ≤ sp.n - 1 at hf₃
        change 0 < sp.n at hn
        omega
      have hc' : (tr.upTo (tr.time i)).projAC.CallAt p i ell := by
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hci⟩
      have hop' : SA.OptimisticLockAt (tr.upTo (tr.time i)).projAC v r u D CV := by
        rw [RunTrace.upTo_projAC]
        exact (SA.upTo_optimisticLockAt hp.run.time_mono).mpr
          ⟨htime.le, hop⟩
      exact proposal_no_optimistic_of_run (hp.run.upTo hd) (hp.noColl.upTo _) hf hpH
        hc' hcall hti hp.stock v (htime ▸ hv) r hri D CV hop'
    omega

end Consensus.Goldilocks.Healing.Growing.ProposalSources

end
