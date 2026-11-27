module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.StaticCoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Reset seeds before a post-drain slot in the P-U run -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

namespace Outcome

/-- A held signed row's lock is older than the cast, including optimistic writes. -/
private theorem row_lock_label_lt_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    (hdk : d < k) {r l : Nat} (hrd : r < d) {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hlock : (∃ CV, AC.FastLockAt tr.projAC v r l D CV) ∨ AC.SlowLockAt tr.projAC v r l D) :
    l < e.msg.slot := by
  have hac := hp.run.toCore.acRun_upTo hp.noColl (hp.run.time_nonneg k)
  have hc' := AC.upTo_castAt.mpr (And.intro le_rfl hc)
  have hk : e.msg.slot = sp.slot (tr.time k) :=
    (AC.castAt_specU hac.localRun.toU hy hc').2.1
  have htr : tr.time r ≤ tr.time k := hp.run.time_mono (by omega)
  have hup (ht : tr.time r = sp.ts l + 6 * sp.Δ) : l < e.msg.slot := by
    have h₁ : sp.ts (l + 1 : Nat) ≤ tr.time k := by
      have heq : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      rw [heq]
      linarith [sp.toParams.hΔ]
    have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).mp h₁
    omega
  rcases hlock with ⟨CV, hf⟩ | ⟨ell', C, hu, _⟩
  · rcases hf with ⟨ell', C, hu, _⟩ | hopt
    · exact hup hu.2.2.1
    · have hl : l ≤ e.msg.slot := by
        obtain ⟨_, _, _, hsl, _⟩ := hopt
        rw [hk, ← hsl]
        exact AC.slot_mono sp (hp.run.time_nonneg r) htr
      rcases hl.lt_or_eq with hl | rfl
      · exact hl
      · exact absurd hopt (KernelProof.row_origin_not_current_at hp hy hc hW ha hv hs hrd)
  · exact hup hu.2.2.1

end Outcome

end Consensus.Goldilocks.Healing.Growing

end
