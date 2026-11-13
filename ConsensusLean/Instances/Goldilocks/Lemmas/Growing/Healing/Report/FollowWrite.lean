module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRoot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLaterBoundary
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Following remapped optimistic writes at later honest proposal calls -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

/-- The stored viable ancestor, rather than the raw selected block, supplies the prefix. -/
theorem FrameWindow.optimistic_write_later_proposal_head_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    {g ΔF b : Time} {s₀ j N floor : Nat} {kindJ : Prop}
    {J R A D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s₀) (hmb : sp.ts N + sp.Δ ≤ b) (hj : s₀ ≤ j)
    {y : Fin sp.n} {a : Nat} (hy : y ∈ H (tr.time a)) {CV : Set (SA.Vote sp.n)}
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt y a ellw)
    (halo : sp.ts s₀ ≤ tr.time a) (hat : tr.time a < sp.ts j + 2 * sp.Δ)
    (hopt : SA.OptimisticLockAt tr.projAC y a j D CV)
    (hRA : Anc (tr.HonestBlocksAt H) R A) (hAD : Anc (tr.HonestBlocksAt H) A D)
    (hsource : ellw.frame.Anc A ellw.frame.fcRoot ∨
      ∃ Q ∈ ellw.frame.tree, floor ≤ ((tr.state y a).fg.σ Q.root).h ∧
        (kindJ → Anc (tr.HonestBlocksAt H) J A) ∧ Anc (tr.HonestBlocksAt H) A Q)
    {r : Nat} (hrlo : j + 1 ≤ r) (hrN : r ≤ N)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z c ell)
    (hcall : ell.call = .proposal) (hti : tr.time c = sp.ts r)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state z c) ell.frame (tr.time c)).2 =
      some (d, pay)) (hstock : sp.committeeSize = sp.n) :
    Anc (tr.HonestBlocksAt H) R d.head := by
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hahi : tr.time a ≤ sp.ts N + sp.Δ := by
    have ht := hts (hrlo.trans hrN)
    have he := SA.ts_succ j (sp := sp)
    linarith only [hat, ht, he, sp.toParams.hΔ]
  have hclo : sp.ts s₀ ≤ tr.time c := by rw [hti]; exact hts (by omega)
  have hchi : tr.time c ≤ sp.ts N + sp.Δ := by
    rw [hti]; linarith only [hts hrN, sp.toParams.hΔ]
  rcases hsource with hroot | ⟨Q, hQ, hh, hJ, hAQ⟩
  · have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
    have hr := hac.upTo (hrun.time_nonneg a)
    have hca := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hcw⟩
    have hrootU := hroot.mono (SA.frameIn_of_callAt hr.localRun hy hca).2
    have he : ellw.frame = Node.frame (tr.state y a) :=
      (hrun.cutLaw y a (.ac ellw) (Compose.projAC_callAt.mp hcw) hy).1
    rw [he] at hrootU
    apply hRA.trans (hrootU.trans ?_)
    exact hframe.fcRoot_anc_proposal_head_at hrun hnc hy hz
      (by
        have hf' := hf (max (tr.time a) (tr.time c))
          ((hrun.time_nonneg a).trans (le_max_left _ _))
          ((max_le hahi hchi).trans hmb)
        exact sp.toParams.fg.faults_lt_quorum_margin hf')
      halo hahi hclo hchi hc hcall hti hd
  · have hsub : FrameWindow tr H (sp.ts j) (sp.ts N + sp.Δ) floor kindJ J :=
      ⟨fun x i hx hlo hhi => hframe.floor_eq x i hx ((hts hj).trans hlo) hhi,
       fun x i hx hlo hhi => hframe.kind_iff x i hx ((hts hj).trans hlo) hhi,
       fun x i hx hlo hhi => hframe.root_eq x i hx ((hts hj).trans hlo) hhi⟩
    exact hRA.trans ((optimistic_later_heads_of_early_witness_at hrun hnc hsvc hawake hf
      hcatch hnr (hm.trans (hts hj)) hmb hsub hy hopt hAD hy hat hcw hQ hh hJ hAQ hstock
      r hrlo hrN).2 z c ell hz hc hcall hti d pay hd)

end Consensus.Goldilocks.Healing.Growing

end
