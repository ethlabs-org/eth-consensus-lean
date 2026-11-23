module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Historical acceptance reaches an honest voter's freeze

The sender is honest only at acceptance. The recipient's prefix supplies its
restart and block-stamp laws; the growing service supplies the cross-node relay.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A historical acceptance before `t_s + 2Δ` reaches every later-slot honest vote's freeze. -/
theorem relay_mem_voterBlockTree_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {w y : Fin sp.n} {kw i s : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hw : w ∈ H (tr.time kw)) (hkw : tr.projAC.AcceptAt w kw W)
    (hg : g ≤ tr.time kw) (hkwt : tr.time kw < sp.ts s + 2 * sp.Δ)
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    (hs : s + 1 ≤ e.msg.slot) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F W) :
    W ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg i)).localRun
  have hc' := AC.upTo_castAt.mpr (And.intro le_rfl hc)
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨-, hys, hyj, -⟩ := AC.castAt_spec hr hy hc'
  change e.msg.slot = sp.slot (tr.time i) at hys
  have hslot : sp.ts ((e.msg.slot : Int) - 1) + 4 * sp.Δ = sp.ts e.msg.slot := by
    simp only [ACParams.ts]; ring
  have hti : sp.ts e.msg.slot ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg i) _).2 (by rw [hys])
  have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) :=
    (AC.ts_le_iff sp).2 (by omega)
  have hrsy : ∀ k ≤ i, tr.projAC.RestartAt y k →
      tr.time k ≤ sp.ts ((e.msg.slot : Int) - 1) := by
    have hj' : AC.joined sp ((tr.projAC.upTo (tr.time i)).post i) (tr.time i) := by
      unfold AC.joined
      rw [AC.restartTime_of_castAt hr hy hc']
      exact hyj
    intro k hk hrk
    have := ((AC.joined_awakeU sp) _ ro _ _ _ hr.toU y hy i ell hc'.1 hj').2 k hk
      (ACTrace.upTo_restartAt.mpr ⟨hm hk, hrk⟩)
    change tr.time k ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) at this
    rwa [← hys] at this
  have hdl : ∀ k ≤ i, tr.projAC.deadline y k (tr.time kw) <
      sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
    intro k hk
    have h₁ := Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') (tr.time kw)
    have h₂ := max_lt (show tr.time kw < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith only [hkwt, hsm])
      (show sp.ts ((e.msg.slot : Int) - 1) < sp.ts ((e.msg.slot : Int) - 1) + 2 * sp.Δ by
        linarith only [hΔ])
    change tr.projAC.deadline y k (tr.time kw) ≤
      max (tr.time kw) (sp.ts ((e.msg.slot : Int) - 1)) + sp.Δ at h₁
    linarith only [h₂, h₁]
  obtain ⟨ky, hky, hacc, hkyt⟩ := hp.frame_relay_at hw hkw hg hy hc.1
    (by linarith only [hΔ, hslot, hti, hdl i le_rfl]) hF
  have hkyt' : tr.time ky < AC.freeze sp e.msg.slot := by
    have := hdl ky hky
    unfold AC.freeze
    linarith only [hkyt, this]
  have hfz : AC.freeze sp e.msg.slot ≤ tr.time i := by
    unfold AC.freeze
    linarith only [hΔ, hslot, hti]
  have hacc' := ACTrace.upTo_acceptAt.mpr (And.intro (hm hky) hacc)
  have hWt := AC.mem_tree_of_acceptAt sp hr hy hacc' hky hc'.1 hF
  have hbs := AC.blockStamp_lt_of_acceptedBefore sp hr hp.run.vstart hy hc'.1 hWt
    (Or.inr ⟨ky, hacc', hkyt'⟩)
    (fun k hk hrk => lt_of_le_of_lt (hrsy k hk (ACTrace.upTo_restartAt.mp hrk).2)
      (by unfold AC.freeze; linarith only [hΔ])) (Or.inl hfz)
  have hne : ∀ B, ell.call = .block B → W.root ≠ B.root := by
    intro B₀ hcall hB
    have hB₀ := (AC.accept_new sp hr hy ⟨ell, hc'.1, hcall⟩).1 ell hc'.1
    obtain rfl : B₀ = W := hr.coherent.1 ((AC.frameIn_of_callAt hr hy hc'.1).2 hB₀)
      ((AC.frameIn_of_callAt hr hy hc'.1).2 hWt) hB.symm
    have heq := AC.accept_unique sp hr hy hacc' ⟨ell, hc'.1, hcall⟩
    rw [heq] at hkyt'
    linarith only [hkyt', hfz]
  refine ⟨hWt, Or.inl ?_⟩
  rw [AC.readPoint_blockStampU hr.toU hy hc' hne]
  exact hbs

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
