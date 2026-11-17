module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowCast
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Full-frame viability through an honest observation

Persistence is local to the receiver. The retained frame window ends at the actual
observation, rather than extending the receiver's honesty beyond that cut.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The actual proposal is viable at a full-frame read after its relay deadline, including the
update itself, from any vote-permitted start: the proposal is relayed to the reader
(`KernelProof.proposal_viable_at_call_at`), so no vote of the reader is used. -/
theorem FrameWindow.proposal_viable_after_votes_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ell)
    (hlo : sp.ts u + 2 * sp.Δ ≤ tr.time k)
    (hhi : tr.time k ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableHeads := by
  have hΔ := sp.toParams.hΔ
  have hshortT : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; linarith
  obtain ⟨hPt, hroot, hv⟩ := KernelProof.proposal_viable_at_call_at hframe hrun hnc hsvc hf hnr
    hgu le_rfl hshortT hTb hz hdes hP hPs hy hc (by linarith) hhi
    (fun h => absurd h (by linarith))
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg k))
    (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hvi : P ∈ ell.frame.viableTree ell.frame.tree := ⟨hPt, hroot, P, hPt, hv, .refl⟩
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  exact ⟨hvi, SA.viableAncestor_self (SA.frameIn_of_callAt hr hy hc').1 hPt (Or.inl hvi), hv⟩

/-- At an actual update the warm unanimous pool forces confirmation and fast
selection, at the slot committees `K` of a run from `K`'s committee start. No
lock-compatibility premise is used to select the raw result. -/
theorem FrameWindow.unanimous_update_selection_at {K : SA.CommitteeDict sp.n}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → SA.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → SA.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      SA.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hkb : tr.time k ≤ b := by rw [hkt, ← hT]; exact hTb
  have hlate : sp.ts u + 2 * sp.Δ ≤ tr.time k := by rw [hkt]; linarith
  obtain ⟨hvi, hva, _⟩ := hframe.proposal_viable_after_votes_at hrun hnc hsvc hf hnr hgu hTb
    hz hdes hP hPs hy hu.1 hlate (by rw [hkt, hT])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, ha, hta⟩ :=
    honestProposalRun_of_proposesAt_at hrun hnc hz hdes hP hPs
  change tr.time a = sp.ts u at hta
  have hza : proposer u ∈ H (tr.time a) := by
    apply hrun.antitone (show tr.time a ≤ sp.ts u + sp.Δ by rw [hta]; linarith)
    exact hdes ▸ hz
  have hpool := unanimous_early_pool_of_acceptance_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hPs hun hza ha hta hy hu.1 hlate hkb hvi.1 hK
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg k))
    (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hPg : P.root ≠ sp.genesisRoot := by
    have hra := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg a))
      (hnc.upTo (tr.time a))).localRun
    rw [RunTrace.upTo_projAC] at hra
    apply SA.accept_ne_genesis sp hra hza
    obtain ⟨ella, hca, hea⟩ := ha
    exact ⟨ella, (Trace.upTo_callAt _).mpr ⟨le_rfl, hca⟩, hea⟩
  have hslots : ∀ v ∈ (tr.projAC.state y k).pool u, v.slot = u := by
    intro v hv
    apply SA.state_pool_slot sp hr hrun.vstart hy k u v
    rwa [hs]
  obtain ⟨hconf, hfast⟩ := SA.confirmation_of_unanimous_early_pool
    (SA.frameIn_of_callAt hr hy hc').1 hvi.1 hPg K (hK.facts.hsize u)
    (fun v hv => hK.facts.hP.1 (tr.time k) y hy k (fun q hq => hrun.time_mono hq.le) u v hv)
    (hK.cs2 u hgu (by linarith) _ (hrun.time_nonneg k) hkb) hslots hpool
  exact ⟨hvi, hconf, hfast, hva⟩

end Consensus.Goldilocks.Healing.Growing

end
