module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.OptimisticWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FullFrameWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Following remapped optimistic writes over the shadow run

`FollowWrite` over the shadow P-U frame: the writer's stored viable ancestor `A` is below its
finalized tip `F`, followed by every later honest proposal head in the window
(`fc_root = F` in the shadow frame), or below a P-U viable head of its frame, followed through
the optimistic early-witness family (`OptimisticWitness`). -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {hold : Time}

/-- The parent of an honest proposal is a P-U viable head of its frame
(`proposal_parent_viable_full_frame_at` over the shadow run). -/
private theorem proposal_parent_viable_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} {c s : Nat} (hz : z ∈ H (tr.time c))
    (hf : (H (tr.time c))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z c ell)
    (hcall : ell.call = .proposal) (hti : tr.time c = sp.ts s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state z c) ell.frame (tr.time c)).2 =
      some (d, pay)) : d.head ∈ ell.frame.viableHeads := by
  have ht := hrun.time_nonneg c
  have hr := hrun.upTo ht
  have hc' : (tr.projAC.upTo (tr.time c)).CallAt z c ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hs := Trace.upTo_state tr.projAC z (d := tr.time c) (i := c)
    (fun k hk => hrun.time_mono hk.le)
  have hfr : ell.frame = Node.frame (tr.state z c) := frame_of_projAC_at hrun hz hc
  obtain ⟨Q, hQ, hv, hroot⟩ := Healing.Growing.Shadow.full_frame_viable_witness_at hrun hnc hz hf
  rw [← hfr] at hQ hv hroot
  have hac := (Compose.goldilocks_ac_projection_from hr (hnc.upTo _)).localRun
  rw [RunTrace.upTo_projAC] at hac
  apply Healing.proposal_head_viable hac hr.vstart hz hc' hcall
    (by rw [Trace.upTo_time, sp.slotTime_eq]; exact hti)
    (by rw [hs, Trace.upTo_time]; exact hd)
  exact ⟨(AC.frameIn_of_callAt hac hz hc').1.fcRoot_mem, .refl, Q, hQ, hv, hroot⟩

/-- A window reader's finalized tip is below every honest proposal head in the window
(`FrameWindow.fcRoot_anc_proposal_head_at` over the shadow frame, where `fc_root = F`). -/
private theorem F_anc_proposal_head_at {lo hi : Time} {M : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i c s : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (max (tr.time i) (tr.time c)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z c ell)
    (hcall : ell.call = .proposal) (hti : tr.time c = sp.ts s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state z c) ell.frame (tr.time c)).2 =
      some (d, pay)) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F d.head := by
  have hfc : (H (tr.time c))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n :=
    lt_of_le_of_lt (Set.ncard_le_ncard (Set.compl_subset_compl.mpr
      (hrun.antitone (le_max_right _ _)))) hf
  have hv := proposal_parent_viable_at hrun hnc hz hfc hc hcall hti hd
  have hwit := early_witness_viable hrun hframe hz hclo hchi hc hv
  have hX : d.head ∈ (tr.state z c).fg.tree := by
    rw [frame_of_projAC_at hrun hz hc, Node.frame_eq, Store.toFrame_viableHeads] at hv
    exact hv.1
  exact hframe.finalized_below_descendant_at hrun hnc hy hz hz hf hilo hihi hX hwit hX .refl

/-- **A remapped optimistic write is followed by later honest proposal heads**
(`FrameWindow.optimistic_write_later_proposal_head_at` over the shadow run). The stock source
premise `A ⪯ fc_root ∨ ∃ Q, floor ≤ σ(Q).h ∧ (kindJ → J ⪯ A) ∧ A ⪯ Q` becomes the shadow frame's
viable-ancestor alternative: `A ⪯ F`, or `A` below a P-U viable head `Q` of the writer's frame
(`early_witness_viable'` gives `Q`'s witness clause inside the window); no `J ⪯ A` is asked. -/
theorem optimistic_write_later_proposal_head_at
    {g ΔF b : Time} {s₀ j N M : Nat} {isTop : Prop}
    {J R A D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) (sp.ts N + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s₀) (hmb : sp.ts N + sp.Δ ≤ b) (hj : s₀ ≤ j)
    {y : Fin sp.n} {a : Nat} (hy : y ∈ H (tr.time a)) {CV : Set (AC.Vote sp.n)}
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt y a ellw)
    (halo : sp.ts s₀ ≤ tr.time a) (hat : tr.time a < sp.ts j + 2 * sp.Δ)
    (hopt : AC.OptimisticLockAt tr.projAC y a j D CV)
    (hRA : Anc (tr.HonestBlocksAt H) R A) (hAD : Anc (tr.HonestBlocksAt H) A D)
    (hsource : ellw.frame.Anc A ellw.frame.F ∨
      ∃ Q ∈ ellw.frame.viableHeads, ellw.frame.Anc A Q)
    {r : Nat} (hrlo : j + 1 ≤ r) (hrN : r ≤ N)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z c ell)
    (hcall : ell.call = .proposal) (hti : tr.time c = sp.ts r)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state z c) ell.frame (tr.time c)).2 =
      some (d, pay)) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) R d.head := by
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hahi : tr.time a ≤ sp.ts N + sp.Δ := by
    have ht := hts (hrlo.trans hrN)
    have he := AC.ts_succ j (sp := sp)
    linarith only [hat, ht, he, sp.toParams.hΔ]
  have hclo : sp.ts s₀ ≤ tr.time c := by rw [hti]; exact hts (by omega)
  have hchi : tr.time c ≤ sp.ts N + sp.Δ := by
    rw [hti]; linarith only [hts hrN, sp.toParams.hΔ]
  have hW := Shadow.PU.frameIn_at hrun hnc hy hcw
  rcases hsource with hroot | ⟨Q, hvQ, hAQ⟩
  · have hFe : ellw.frame.F = (tr.state y a).fg.F := by
      rw [frame_of_projAC_at hrun hy hcw, Node.frame_eq, Store.toFrame_F]
    have hrootU := hroot.mono hW.2
    rw [hFe] at hrootU
    exact hRA.trans (hrootU.trans (F_anc_proposal_head_at hframe hrun hnc hy hz
      (sp.toParams.fg.faults_lt_quorum_margin (hf (max (tr.time a) (tr.time c))
        ((hrun.time_nonneg a).trans (le_max_left _ _)) ((max_le hahi hchi).trans hmb)))
      halo hahi hclo hchi hc hcall hti hd))
  · have hslot : sp.slot (tr.time a) = j := by
      obtain ⟨_, _, _, hs, _⟩ := hopt
      exact hs
    have hjlo : sp.ts j ≤ tr.time a :=
      (AC.ts_le_iff_le_slot sp (hrun.time_nonneg a) _).2 (by rw [hslot])
    have hQw : Q ∈ ellw.frame.tree := by
      have hv := hvQ
      rw [frame_of_projAC_at hrun hy hcw, Node.frame_eq, Store.toFrame_viableHeads] at hv
      rw [frame_of_projAC_at hrun hy hcw, Node.frame_eq, Store.toFrame_tree]
      exact ⟨hv.1, hv.2.1⟩
    exact hRA.trans ((optimistic_later_heads_of_early_witness_at hrun hnc hsvc hawake hf
      hcatch hnr (hm.trans (hts hj)) hmb (hframe.mono (hts hj) le_rfl) hy hopt hAD hy hjlo
      hat hcw hQw hvQ (hAQ.mono hW.2) hK r hrlo hrN).2 z c ell hz hc hcall hti d pay hd)

end Consensus.Goldilocks.Shadow.PU.Growing

end
