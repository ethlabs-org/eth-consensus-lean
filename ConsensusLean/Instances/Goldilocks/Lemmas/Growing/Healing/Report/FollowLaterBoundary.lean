module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowInduction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowOptimisticBaseBoundary
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee

public section

/-! # Optimistic propagation across independently honest cuts

From the first-slot bases of `Report/FollowOptimisticBaseBoundary`. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

/-- An early viable witness propagates an optimistic prefix to later honest calls. -/
theorem optimistic_later_heads_of_early_witness_at
    {g ΔF b : Time}
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  intro r hrlo hrN
  have ht : sp.ts (s + 1 : Nat) ≤ sp.ts N :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hrlo.trans hrN)
  have hsub {lo hi : Time} (hl : sp.ts s ≤ lo) (hh' : hi ≤ sp.ts N + sp.Δ) :
      FrameWindow tr H lo hi floor kindJ J :=
    ⟨fun y i hy hlo hhi => hframe.floor_eq y i hy (hl.trans hlo) (hhi.trans hh'),
     fun y i hy hlo hhi => hframe.kind_iff y i hy (hl.trans hlo) (hhi.trans hh'),
     fun y i hy hlo hhi => hframe.root_eq y i hy (hl.trans hlo) (hhi.trans hh')⟩
  have hbase := optimistic_next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch hm
    (by linarith only [hmb, ht]) (hsub le_rfl (by linarith only [ht])) hx hopt hXD hw hat hcw
    hQw hh hJ hXQ hK
  obtain ⟨hvote, hproposal⟩ := later_heads_of_early_witness_at hrun hnc hsvc hawake hf hcatch
    hnr hm hmb hframe hw hat hcw hQw hh hJ hXQ hbase hK r hrlo hrN
  refine ⟨hvote, ?_⟩
  by_cases heq : r = s + 1
  · subst r
    intro y i ell hy hc hcall hti d pay hd
    exact optimistic_next_proposal_of_early_witness_at hrun hnc hsvc hawake hf hcatch hm
      (by linarith only [hmb, ht, sp.toParams.hΔ])
      (hsub le_rfl (by linarith only [ht, sp.toParams.hΔ]))
      hx hopt hXD hw hat hcw hQw hh hJ hXQ hy hc hcall hti hd hK
  · exact hproposal (by omega)

/-- The optimistic writer itself can supply the early viable witness. -/
theorem optimistic_later_heads_of_witness_at
    {g ΔF b : Time}
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s N floor : Nat} (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (AC.Vote sp.n)}
    (hopt : AC.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt x c ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state x c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∧
      (∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) X d.head) := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := hac.upTo (hrun.time_nonneg c)
  have ho := (AC.upTo_optimisticLockAt hrun.time_mono).mpr ⟨le_rfl, hopt⟩
  have ht := (AC.optimisticLockAt_spec hr hx ho K (fun σ v hv =>
    (AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP _).1 x hx _ σ v hv)).1
  exact optimistic_later_heads_of_early_witness_at hrun hnc hsvc hawake hf hcatch hnr
    hm hmb hframe hx hopt hXD hx ht hcw hQw hh hJ hXQ hK

end Consensus.Goldilocks.Healing.Growing

end
