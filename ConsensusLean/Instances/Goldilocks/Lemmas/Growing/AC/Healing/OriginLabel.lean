module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # High-origin labels before an honest proposal

An optimistic write of the proposal's own slot must be at exactly the proposal's
time. Its writer is therefore honest at that time, and the static exclusion applies
on that prefix without assuming survival across a compromise.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalSources

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

theorem origin_label_lt_at_proposal_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {v : Fin sp.n} {r l : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u := by
  have hcut := hp.cutZ_le_ts_of_highOrigin_at ho
  obtain ⟨hv, -, ⟨CV, ell', D, -, hfl, -⟩, -⟩ := ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ellR, C, ⟨-, -, ht, -⟩, -⟩ | hop
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    exact_mod_cast (AC.ts_lt_iff sp).mp
      (show sp.ts l < sp.ts u by linarith only [ht', hrt, hΔ])
  · obtain ⟨-, -, -, hsl, -⟩ := id hop
    change sp.slot (tr.time r) = l at hsl
    have hts : sp.ts l ≤ tr.time r :=
      (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) l).mpr (by omega)
    have hle : l ≤ u := by
      exact_mod_cast (AC.ts_le_iff sp).mp (hts.trans hrt)
    have hne : l ≠ u := by
      intro he
      rw [he] at hop hts hcut
      have htime : tr.time r = tr.time i := hti.symm ▸ le_antisymm hrt hts
      have hd := hp.run.time_nonneg i
      have hf := hp.committee_cs2_at (s := u) (by have := lt_cutZ sp g; linarith)
        (hti ▸ hib) hd hib
      have hc' : (tr.upTo (tr.time i)).projAC.CallAt p i ell := by
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hci⟩
      have hop' : AC.OptimisticLockAt (tr.upTo (tr.time i)).projAC v r u D CV := by
        rw [RunTrace.upTo_projAC]
        exact (AC.upTo_optimisticLockAt hp.run.time_mono).mpr
          ⟨htime.le, hop⟩
      exact Compose.proposal_no_optimistic_of (hp.run.upTo hd) (hp.noColl.upTo _)
        (by rw [RunTrace.upTo_projAC]
            exact AC.CommitteePAt.upTo hp.run.time_mono hp.run.antitone hp.committeeFacts.hP _)
        hf hpH hc' hcall hti v (htime ▸ hp.run.antitone (le_max_right _ _) hv) r hri D CV hop'
    omega

end Consensus.Goldilocks.Healing.Growing.ProposalSources

end
