module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.GenericReset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ReportFollow
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal viability and height leaves for shadow P-U execution -/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {ACP : Type} {st : Store P ACP}

private theorem full_frame_viable_witness_of_max {acp₀ : ACP}
    (hr : st.Reachable' acp₀)
    (hF : ∀ Q ∈ st.tree, (st.σ Q.root).h = st.hmax → st.Anc st.F Q) :
    ∃ Q ∈ st.toFrame'.tree, Q ∈ st.toFrame'.viableHeads ∧
      st.toFrame'.Anc st.toFrame'.fcRoot Q := by
  obtain ⟨_, _, _, _, _, ⟨Q, hQ, hheight⟩, _⟩ := Store.cache_invariants' hr
  have hFQ := hF Q hQ hheight
  refine ⟨Q, ?_, ?_, ?_⟩
  · rw [Store.toFrame'_tree]
    exact ⟨hQ, hFQ⟩
  · rw [Store.toFrame'_viableHeads]
    exact ⟨hQ, hFQ, (Store.isViable'_iff _ _).2 (Or.inl hheight.ge)⟩
  · change Anc st.toFrame'.tree st.toFrame'.fcRoot Q
    rw [Store.toFrame'_tree, Store.toFrame'_fcRoot]
    exact Anc.restrict .refl hFQ

/-- Transported parent viability bounds the proposal and its top-window ancestry. -/
theorem proposal_viable_of_parent {Q B : NodeBlock P ACP}
    (hv : st.IsViable' Q) (hh : (st.σ Q.root).h ≤ (st.σ B.root).h)
    (hQB : st.Anc Q B) :
    st.hmax - 1 ≤ (st.σ B.root).h ∧
      (st.hmax = st.hj + 1 → (st.σ B.root).h = st.hmax - 1 → st.Anc st.J B) := by
  rw [Store.isViable'_iff] at hv
  constructor
  · rcases hv with hv | ⟨hv, -⟩ <;> omega
  · intro htop hB
    rcases hv with hv | ⟨hv, hgap | hJ⟩
    · omega
    · omega
    · exact hJ.trans hQB

/-- At equal height a proposal's top-window J clause transfers to its report. -/
theorem report_kind_of_proposal_viable {B R : NodeBlock P ACP}
    (hj : st.hj < st.hmax)
    (hB : st.hmax - 1 ≤ (st.σ B.root).h ∧
      (st.hmax = st.hj + 1 → (st.σ B.root).h = st.hmax - 1 → st.Anc st.J B))
    (hBR : st.Anc B R) (heq : (st.σ R.root).h = (st.σ B.root).h) :
    st.hj < (st.σ R.root).h ∨
      ((st.σ R.root).h = st.hj ∧ st.Anc st.J R) := by
  by_cases hlt : st.hj < (st.σ R.root).h
  · exact Or.inl hlt
  · have htop : st.hmax = st.hj + 1 := by omega
    exact Or.inr ⟨by omega, (hB.2 htop (by omega)).trans hBR⟩

/-- The unchanged rise count covers the P-U proposal's height deficit. -/
theorem pred_add_riseRounds_frameKey'' {HZ : Nat} (hkey : 2 * HZ ≤ frameKey'' st) :
    HZ + 1 ≤ st.hmax - 1 + riseRounds HZ (frameKey'' st) := by
  classical
  by_cases htop : st.hmax = st.hj + 1
  · simp only [riseRounds_eq, frameKey''_def, ite_eq_left htop] at hkey ⊢
    omega
  · simp only [riseRounds_eq, frameKey''_def, ite_eq_right htop] at hkey ⊢
    omega

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The full P-U frame has a viable maximum-height witness above its finalized root. -/
theorem full_frame_viable_witness_at' {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace' sp ro} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    ∃ Q ∈ (Node.frame' (tr.state y i)).tree,
      Q ∈ (Node.frame' (tr.state y i)).viableHeads ∧
      (Node.frame' (tr.state y i)).Anc (Node.frame' (tr.state y i)).fcRoot Q := by
  have ht := hrun.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hr := Compose.Growing.reachable_at' hrun ht hy hle
  have hu := Store.finalitySpec_updateFinality' (P := sp.toParams)
    (ACP := Payload sp.n)
  simp only [Node.frame'_eq]
  apply full_frame_viable_witness_of_max hr
  intro Q hQ hheight
  exact Store.F_anc_of_hmax_le_of_safe_with hu hr.reachableWith hr.reachableWith
    (Store.accepted_tree_with hu hr.reachableWith).2.1 subset_rfl subset_rfl hf
    (held_atts_safe_at' hrun hnc ht hle hy ht hle hy le_rfl le_rfl) hQ hheight.ge

/-- V-B5's full growing contract. Unresolved while proposal extraction and transfer
suppliers are being assembled; no stock execution premise replaces the shadow run. -/
theorem proposal_viable_at {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace' sp ro} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {lo hi : Time} {M u : Nat} {isTop : Prop}
    {J B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : FrameWindow' tr H lo hi M isTop J)
    {z : Fin sp.n} {kB : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hB : tr.ProposesAt z kB B) (hBs : B.slot = u)
    (hlo : lo ≤ sp.ts u) (hhi : sp.ts u ≤ hi)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    M - 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h ∧
      (isTop → ((tr.state z (kB + 1)).fg.σ B.root).h = M - 1 →
        Anc (tr.HonestBlocksAt H) J B) := by
  have htime : tr.time kB = sp.ts u := by
    simpa only [sp.slotTime_eq, hBs, ACParams.ts] using hB.2.2
  have hzk : z ∈ H (tr.time kB) := htime ▸ hz
  have ht := hrun.time_nonneg kB
  have hr := hrun.upTo ht
  have hB' : (tr.upTo (tr.time kB)).ProposesAt z kB B :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hB.1⟩, hB.2.1, hB.2.2⟩
  obtain ⟨_, ip, ell, d, pay, hc, hcall, hd, hti, hpar, _⟩ :=
    Coherence.honestProposalRun_of_proposesAt' hr (hnc.upTo _) hzk hdes hB' hBs
  rw [← hdes] at hc hd
  have hip : tr.time ip = sp.ts u := hti
  have hzi : z ∈ H (tr.time ip) := hip ▸ hz
  have hleip : ∀ q < ip, tr.time q ≤ tr.time kB := by
    intro q hq
    exact (hrun.time_mono hq.le).trans (by rw [hip, htime])
  have hleB : ∀ q < kB + 1, tr.time q ≤ tr.time kB :=
    fun q hq => hrun.time_mono (by omega)
  have hfr := Node.frame_of_projAC_at' hr.toLocalRun' hzk hc
  have hfr' : ell.frame = Node.frame' (tr.state z ip) := by
    rw [Trace.upTo_state tr z hleip] at hfr
    exact hfr
  obtain ⟨Q, hQ, hv, hroot⟩ := full_frame_viable_witness_at' hrun hnc hzi (hip ▸ hf)
  rw [← hfr'] at hQ hv hroot
  have hac := (Compose.goldilocks_ac_projection_from' hr (hnc.upTo _)).localRun
  have hvd := Healing.proposal_head_viable hac hr.vstart hzk hc hcall
    (by rw [sp.slotTime_eq]; exact hti) hd
    ⟨(AC.frameIn_of_callAt hac hzk hc).1.fcRoot_mem, .refl, Q, hQ, hv, hroot⟩
  rw [hfr, Node.frame'_eq, Store.toFrame'_viableHeads] at hvd
  obtain ⟨hDm, _, hDv⟩ := hvd
  have hBm : B ∈ ((tr.upTo (tr.time kB)).state z (kB + 1)).fg.tree := by
    exact (Coherence.accept_of_proposesAt' hr (hnc.upTo _) hzk hB').2.1
  have hDhist : d.head ∈ (tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB)) :=
    ⟨z, hzk, ip, hDm⟩
  have hBhist : B ∈ (tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB)) :=
    ⟨z, hzk, kB + 1, hBm⟩
  have hDB : Anc ((tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB))) d.head B :=
    .single ⟨hDhist, hBhist, hpar⟩
  have hDBs := Coherence.honest_held_anc' hr (hnc.upTo _) hzk hDB hBm
  have hDpost : d.head ∈ ((tr.upTo (tr.time kB)).state z (kB + 1)).fg.tree := by
    by_cases he : d.head = B
    · exact he ▸ hBm
    · exact (Anc.mem hDBs he).1
  have hσ := Store.σ_eq_of_mem_with
    (Node.fg_reachable_at' hr.toLocalRun' hzk ip).reachableWith
    Store.finalitySpec_updateFinality'
    (Node.fg_reachable_at' hr.toLocalRun' hzk (kB + 1)).reachableWith
    (Coherence.honest_blocks_coherent' hr.toLocalRun' (hnc.upTo _)).1
    (fun _ hm => ⟨z, hzk, ip, hm⟩) (fun _ hm => ⟨z, hzk, kB + 1, hm⟩) hDm hDpost
  have hh := (Coherence.honest_held_height' hr (hnc.upTo _) hzk hDBs).1
  rw [← hσ] at hh
  have hM : ((tr.upTo (tr.time kB)).state z ip).fg.hmax = M := by
    rw [Trace.upTo_state tr z hleip]
    exact hwin.M_eq z ip hzi (hip ▸ hlo) (hip ▸ hhi)
  have hpred : M - 1 ≤
      (((tr.upTo (tr.time kB)).state z ip).fg.σ d.head.root).h := by
    rw [Store.isViable'_iff] at hDv
    rcases hDv with hh | ⟨hh, _⟩ <;> omega
  have hheight := hpred.trans hh
  rw [Trace.upTo_state tr z hleB] at hheight
  refine ⟨hheight, ?_⟩
  intro htop heq
  have htop' : ((tr.upTo (tr.time kB)).state z ip).fg.hmax =
      ((tr.upTo (tr.time kB)).state z ip).fg.hj + 1 := by
    rw [Trace.upTo_state tr z hleip]
    exact (hwin.top_iff z ip hzi (hip ▸ hlo) (hip ▸ hhi)).2 htop
  have hJ : ((tr.upTo (tr.time kB)).state z ip).fg.J = J := by
    rw [Trace.upTo_state tr z hleip]
    exact hwin.root_eq z ip hzi (hip ▸ hlo) (hip ▸ hhi) htop
  rw [Trace.upTo_state tr z hleB, heq] at hh
  have hJD : ((tr.upTo (tr.time kB)).state z ip).fg.Anc J d.head := by
    rw [Store.isViable'_iff] at hDv
    rcases hDv with hh | ⟨hh, hgap | hJD⟩
    · omega
    · omega
    · exact hJ ▸ hJD
  have hJD' : Anc ((tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB))) J d.head :=
    Anc.mono (fun _ hm => ⟨z, hzk, ip, hm⟩) hJD
  exact Anc.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono ht) (hJD'.trans hDB)

/-- Leaf 8's arithmetic assembly, conditional on actual proposal viability. -/
private theorem rounds_le_of_proposal_viable
    {tr : GoldilocksTrace' sp ro} {H : Time → Set (Fin sp.n)}
    {lo hi : Time} {M v HZ : Nat} {isTop : Prop}
    {J B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : FrameWindow' tr H lo hi M isTop J)
    {z : Fin sp.n} {kB : Nat} (hz : z ∈ H (tr.time kB))
    (hlo : lo ≤ tr.time kB) (hhi : tr.time kB ≤ hi)
    (hkey : frameKey'' (tr.state z kB).fg = v) (hv : 2 * HZ ≤ v)
    (hB : M - 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h) :
    HZ + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + riseRounds HZ v := by
  have h := pred_add_riseRounds_frameKey'' (st := (tr.state z kB).fg)
    (HZ := HZ) (by rw [hkey]; exact hv)
  rw [hkey, hwin.M_eq z kB hz hlo hhi] at h
  exact h.trans (Nat.add_le_add_right hB _)

/-- The shadow key bounds the height deficit at an honest proposal cut. -/
theorem rounds_le_warm_proposal_at {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace' sp ro} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g af len : Time} {u M v : Nat} {isTop : Prop}
    {J B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : FrameWindow' tr H af (af + len) M isTop J)
    (hK : ∀ y i, y ∈ H (tr.time i) → af ≤ tr.time i → tr.time i ≤ af + len →
      frameKey'' (tr.state y i).fg = v)
    (hv : 2 * HZ tr H g ≤ v) (hlo : af ≤ sp.ts u) (hhi : sp.ts u ≤ af + len)
    {z : Fin sp.n} {kB : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hB : tr.ProposesAt z kB B) (hBs : B.slot = u)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + riseRounds (HZ tr H g) v := by
  have ht : tr.time kB = sp.ts u := by
    simpa only [sp.slotTime_eq, hBs, ACParams.ts] using hB.2.2
  have hzk : z ∈ H (tr.time kB) := ht ▸ hz
  exact rounds_le_of_proposal_viable hwin hzk (ht ▸ hlo) (ht ▸ hhi)
    (hK z kB hzk (ht ▸ hlo) (ht ▸ hhi)) hv
    (proposal_viable_at hrun hnc hwin hz hdes hB hBs hlo hhi hf).1

section Reset

open AC (gbar)
open Consensus.Goldilocks.Shadow.PU.Growing (proposal_report_follow_delayed_at')

variable {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace' sp ro} {hold : Time}

/-- The latency deadline of a high report is also a reset deadline for a shadow run. -/
private theorem reset_of_high_report_within_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini) {g D : Time}
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    {y : Fin sp.n} {i : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i + D)))
    (hq : (H (max (cutZ sp.toParams g) (tr.time i + D)))ᶜ.ncard < sp.toParams.fg.q)
    {ell : ACLabel (goldilocksNode' sp ro)} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.ToFGAt tr.projAC y i ell R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i + D := by
  have hy := hrun.antitone ((le_add_of_nonneg_right hD).trans (le_max_right _ _)) hyz
  obtain ⟨hc, hto, hres⟩ := hR
  apply Generic.Shadow.reset_of_high_report_within_from hrun.toLocalRun' hlat hyz hq ?_ hh
  refine ⟨ell, Compose.projAC_callAt.mp hc, hto, ?_⟩
  change (AC.acToFG sp (tr.state y i).ac ell.frame (tr.time i)).2 = some R
  rw [← Goldilocks.Shadow.PU.Growing.projAC_state_at' hrun hy]
  exact hres

/-- A high proposal yields a reset by its delayed report and vote-latency deadline. -/
theorem reset_of_high_proposal_within_at
    {g ΔF b D t₀ : Time} {s₀ u N M Gs : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ) M
      isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ ≤ b)
    (hH : (H b).Nonempty)
    (hlat : Generic.VoteLatencyAt tr H D) (hD : 0 ≤ D)
    (hDb : sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ sp.ts s₀)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + (D + (Gs : Time) * sp.Δ) := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hGs0 : (0 : Time) ≤ (Gs : Time) * sp.Δ :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans sp.toParams.hΔ)
  have hts : sp.ts (u + 1 : Nat) ≤ sp.ts N := (AC.ts_le_iff sp).2 (by exact_mod_cast hN)
  have hs₀ : sp.ts s₀ ≤ sp.ts (u + 1 : Nat) :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ u + 1 by omega))
  have hmax : max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (Gs : Time) * sp.Δ) ≤
      sp.ts N + 2 * sp.Δ + (Gs : Time) * sp.Δ := max_le (by linarith) (by linarith)
  obtain ⟨y, hy⟩ := hH
  obtain ⟨i, ell, R, hyi, hR, htil, hti, hPR, _⟩ :=
    proposal_report_follow_delayed_at' (hframe.mono le_rfl hmax) hrun hnc hsvc hawake hf
      hcatch hnr hm hwarm hN (hmax.trans hmb) hz hdes hP hPs hcal hgap (by linarith)
      (hrun.antitone (by linarith) hy) hK
  have hcz : cutZ sp.toParams g ≤ tr.time i := by
    have h4 : sp.ts (s₀ + 4 : Nat) ≤ sp.ts u :=
      (AC.ts_le_iff sp).2 (by exact_mod_cast (show s₀ + 4 ≤ u by have := sp.two_le_k; omega))
    have he : sp.ts (s₀ + 4 : Nat) = sp.ts s₀ + 16 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    linarith [cutZ_le sp g]
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [htime]; linarith) hz
  have hr := hrun.upTo (hrun.time_nonneg kP)
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  have hPm := (Coherence.accept_of_proposesAt' hr (hnc.upTo _) hzk hP').2.1
  rw [Trace.upTo_state tr z (fun q hq => hrun.time_mono (by omega))] at hPm
  have hRm : R ∈ (tr.state y i).fg.tree := by
    have hsource := (AC.toFG_source hR.2.2).1.1
    rw [Goldilocks.Shadow.PU.Growing.frame_of_projAC_at' hrun hyi hR.1,
      Node.frame'_eq, Store.toFrame'_tree] at hsource
    exact hsource.1
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hPy := mem_of_honest_anc_at' hrun hnc (hrun.time_nonneg i) hle hyi hPR hRm
  have hσ := σ_eq_honest_at' hrun hnc (hrun.time_nonneg kP)
    (fun q hq => hrun.time_mono (by omega)) hzk (hrun.time_nonneg i) hle hyi hPm hPy
  rw [hσ] at hh
  have hhR := hh.trans (Store.h_le_of_store_anc_with Store.finalitySpec_updateFinality'
    (Compose.Growing.reachable_at' hrun (hrun.time_nonneg i) hyi hle).reachableWith
    (store_anc_of_honest_anc_at' hrun hnc (hrun.time_nonneg i) hle hyi hPR hRm))
  have hiD : tr.time i + D ≤ b := by linarith
  have hcD : max (cutZ sp.toParams g) (tr.time i + D) = tr.time i + D :=
    max_eq_right (by linarith)
  have hyD : y ∈ H (max (cutZ sp.toParams g) (tr.time i + D)) := by
    rw [hcD]; exact hrun.antitone hiD hy
  have hq : (H (max (cutZ sp.toParams g) (tr.time i + D)))ᶜ.ncard < sp.toParams.fg.q := by
    have hf' := hf _ (by linarith [hrun.time_nonneg i]) hiD
    have hn := sp.toParams.hn
    rw [hcD]
    change (H (tr.time i + D))ᶜ.ncard < (2 * sp.n + 2) / 3
    omega
  obtain ⟨a, ha, hat⟩ := reset_of_high_report_within_at hrun hlat hD hyD hq hR hhR
  exact ⟨a, ha, by linarith⟩

end Reset

end Consensus.Goldilocks.Healing.Growing.Shadow

end
