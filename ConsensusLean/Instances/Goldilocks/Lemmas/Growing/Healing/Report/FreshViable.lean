module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowCast
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
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

/-- An earlier viable head persists through the receiver's current honest cut. -/
theorem FrameWindow.viableHead_persists_at {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {a i : Nat}
    (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hai : a ≤ i) (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y a ell)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hv : Q ∈ ell.frame.viableHeads) :
    Q ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot Q ∧
      Q ∈ (Node.frame (tr.state y i)).viableHeads := by
  have hd := hrun.time_nonneg i
  have hr := hrun.upTo hd
  have hfrozen : Healing.FrameWindow (tr := tr.upTo (tr.time i)) (H := H (tr.time i))
      lo (tr.time i) floor kindJ J := by
    constructor
    · intro x hx j hlo hhi
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.floor_eq x j (hrun.antitone hhi hx) hlo (hhi.trans hihi)
    · intro x hx j hlo hhi
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.kind_iff x j (hrun.antitone hhi hx) hlo (hhi.trans hihi)
    · intro x hx j hlo hhi hk
      rw [RunTrace.upTo_state_of_le hrun.time_mono hhi]
      exact hframe.root_eq x j (hrun.antitone hhi hx) hlo (hhi.trans hihi) hk
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt y a ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨hrun.time_mono hai, hc⟩
  have hp := hfrozen.viableHead_persists hr (hnc.upTo (tr.time i)) hf hy hai halo le_rfl hc' hv
  simpa only [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] using hp

/-- The receiver's own earlier vote transports proposal viability to a full-frame
read after the vote-delivery deadline, including the update itself. -/
theorem FrameWindow.proposal_viable_after_votes_at
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hgu : gbar g ≤ sp.ts u) (hu0 : 0 < u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ell)
    (hlo : sp.ts u + 2 * sp.Δ ≤ tr.time k)
    (hhi : tr.time k ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ)
    (hvote : ∃ q e, SA.VoteAt tr.projAC y q e ∧ e.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableHeads := by
  have hΔ := sp.toParams.hΔ
  have hshortT : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; linarith
  have hshort : FrameWindow tr H (sp.ts u) (sp.ts u + sp.Δ) floor kindJ J :=
    ⟨fun x i hx hlo hhi => hframe.floor_eq x i hx hlo (hhi.trans hshortT),
     fun x i hx hlo hhi => hframe.kind_iff x i hx hlo (hhi.trans hshortT),
     fun x i hx hlo hhi => hframe.root_eq x i hx hlo (hhi.trans hshortT)⟩
  obtain ⟨q, e, ⟨ellq, hcq⟩, hes, hqt⟩ := hvote
  have hqk : q ≤ k := by
    by_contra hn
    have := hrun.time_mono (by omega : k ≤ q)
    linarith
  have hyq := hrun.antitone (hrun.time_mono hqk) hy
  have hPv := (KernelProof.proposal_viable_at_cast_at hshort hrun hnc hsvc hawake hf hcatch hnr hgu
    le_rfl hu0 (hshortT.trans hTb) hz hdes hP hPs hyq hcq hes).1
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k))
    (tr.upTo (tr.time k)) proposer (hrun.upTo (hrun.time_nonneg k))
    (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hcq' : SA.CastAt (tr.projAC.upTo (tr.time k)) y q ellq e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨hrun.time_mono hqk, hcq.1⟩, hcq.2⟩
  have hslot : e.msg.slot = sp.slot (tr.time q) := (SA.castAt_spec hr hy hcq').2.1
  have hqlo : sp.ts u ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp (hrun.time_nonneg q) _).2 (by
      rw [← hslot, hes])
  have hmf : (H (tr.time k))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf (tr.time k) (hrun.time_nonneg k) (hhi.trans hTb)
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change (H (tr.time k))ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  obtain ⟨hPt, hroot, hv⟩ := hframe.viableHead_persists_at hrun hnc hy hmf hqk hqlo hhi
    hcq.1 hPv
  have hframeeq : ell.frame = Node.frame (tr.state y k) := by
    have hc' : (tr.upTo (tr.time k)).projAC.CallAt y k ell := by
      rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
    simpa only [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] using
      Compose.frame_of_projAC (hrun.upTo (hrun.time_nonneg k)) hy hc'
  rw [← hframeeq] at hPt hroot hv
  have hvi : P ∈ ell.frame.viableTree ell.frame.tree := ⟨hPt, hroot, P, hPt, hv, .refl⟩
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  exact ⟨hvi, SA.viableAncestor_self (SA.frameIn_of_callAt hr hy hc').1 hPt (Or.inl hvi), hv⟩

/-- At an actual update the warm unanimous pool forces confirmation and fast
selection. No lock-compatibility premise is used to select the raw result. -/
theorem FrameWindow.unanimous_update_selection_at
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
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
    {ell : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k u ell) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      SA.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hu0 : 0 < u := by
    by_contra hn
    have he : u = 0 := by omega
    rw [he] at hmargin
    simp only [SAParams.ts, Nat.cast_zero, mul_zero] at hmargin
    linarith [SA.gbar_nonneg g]
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hkb : tr.time k ≤ b := by rw [hkt, ← hT]; exact hTb
  have hlate : sp.ts u + 2 * sp.Δ ≤ tr.time k := by rw [hkt]; linarith
  have hshort : sp.ts u + sp.Δ ≤ tr.time k := by linarith
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts u + sp.Δ by linarith [SA.gbar_nonneg g]) (hshort.trans hkb)
  have hvotes := honest_votes_of_joined_before_at hS hgu hjoin
  obtain ⟨hvi, hva, _⟩ := hframe.proposal_viable_after_votes_at hrun hnc hsvc hawake hf hcatch
    hnr hgu hu0 hTb hz hdes hP hPs hy hu.1 hlate (by rw [hkt, hT])
    (hvotes y (hrun.antitone hshort hy))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, ha, hta⟩ :=
    honestProposalRun_of_proposesAt_at hrun hnc hz hdes hP hPs
  change tr.time a = sp.ts u at hta
  have hza : proposer u ∈ H (tr.time a) := by
    apply hrun.antitone (show tr.time a ≤ sp.ts u + sp.Δ by rw [hta]; linarith)
    exact hdes ▸ hz
  have hpool := unanimous_early_pool_of_acceptance_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hPs hun hza ha hta hy hu.1 hlate hkb hvi.1
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k))
    (tr.upTo (tr.time k)) proposer (hrun.upTo (hrun.time_nonneg k))
    (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hPg : P.root ≠ sp.genesisRoot := by
    have hra := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time a))
      (tr.upTo (tr.time a)) proposer (hrun.upTo (hrun.time_nonneg a))
      (hnc.upTo (tr.time a))).localRun
    rw [RunTrace.upTo_projAC] at hra
    apply SA.accept_ne_genesis sp hra hza
    obtain ⟨ella, hca, hea⟩ := ha
    exact ⟨ella, (Trace.upTo_callAt _).mpr ⟨le_rfl, hca⟩, hea⟩
  have hslots : ∀ v ∈ (tr.projAC.state y k).pool u, v.slot = u := by
    intro v hv
    apply SA.state_pool_slot sp hr hy k u v
    rwa [hs]
  obtain ⟨hconf, hfast⟩ := SA.confirmation_of_unanimous_early_pool
    (SA.frameIn_of_callAt hr hy hc').1 hvi.1 hPg
    (hf (tr.time k) (hrun.time_nonneg k) hkb) hslots hpool
  exact ⟨hvi, hconf, hfast, hva⟩

end Consensus.Goldilocks.Healing.Growing

end
