module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.DrainCrossing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Warm proposal height from snapshot relay at the proposal call

The full proposal frame has a viable head. Relay of the original snapshot frontier to that
call therefore bounds the selected parent, without a vote cohort or a cast-time argument.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The current honest observation has a viable head above its fork-choice root. -/
theorem full_frame_viable_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    ∃ Q ∈ (Node.frame (tr.state y i)).tree,
      Q ∈ (Node.frame (tr.state y i)).viableHeads ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot Q := by
  classical
  have ht := hrun.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hr := fg_reachable_at hrun ht hle hy
  obtain ⟨hF, hJt, hFJ, ⟨B, hB, hBJ, hBh⟩, _, ⟨Q, hQ, hQh⟩, _⟩ :=
    Store.cache_invariants _ _ _ _ hr
  have hsub : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun _ h => h.1
  have hframe := (Store.frame_realization _ _ _ _ hr).1
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬ (tr.state y i).fg.Contest
  · obtain ⟨E, hE, hEr, hh⟩ := J_entry_h hr hB
    obtain rfl : E = (tr.state y i).fg.J :=
      (Store.accepted_tree _ _ _ _ hr).2.1.1 hE hJt (hEr.trans hBJ)
    rw [hBh] at hh
    have hheight : (tr.state y i).fg.headHeightFloor ≤
        ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h := by
      change (if _ then _ else _) ≤ _
      rw [ite_eq_right hk.2, hk.1]
      omega
    have he : (tr.state y i).fg.fcRoot = (tr.state y i).fg.J := ite_eq_left hk
    have hJ : (tr.state y i).fg.J ∈ (Node.frame (tr.state y i)).tree := ⟨hJt, hFJ⟩
    refine ⟨_, hJ, ⟨hJt, hFJ, ?_, hheight⟩, ?_⟩
    · rw [he]; exact .refl
    · change Anc (Node.frame (tr.state y i)).tree (tr.state y i).fg.fcRoot _
      rw [he]; exact .refl
  · have hFQ := F_anc_of_hmax_le_at hrun hnc ht hle hy ht hle hy
      (by simpa only [max_self] using hf) hQ hQh.ge
    have hFQs := store_anc_of_honest_anc_at hrun hnc ht hle hy hFQ hQ
    have he : (tr.state y i).fg.fcRoot = (tr.state y i).fg.F := ite_eq_right hk
    have hQt : Q ∈ (Node.frame (tr.state y i)).tree := ⟨hQ, hFQs⟩
    refine ⟨Q, hQt, ⟨hQ, hFQs, ?_, ?_⟩, ?_⟩
    · rw [he]; exact hFQs
    · exact (Store.headHeightFloor_bounds _).2.trans_eq hQh.symm
    · exact SA.anc_tree_of_anc_U
        ((Store.accepted_tree _ _ _ _ hr).2.1) hframe hsub hframe.fcRoot_mem
        (by change (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot Q
            rw [he]; exact hFQs) hQt

/-- Public ticks supply the snapshot relay call before the receiver's actual observation. -/
theorem snapshotCall_of_awake_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hfit : cutZ sp.toParams g + sp.Δ + 1 ≤ tr.time m) (hmb : tr.time m ≤ b) :
    (∃ j, FirstCutAfter tr j (cutZ sp.toParams g)) ∧
      ∃ j < m, tr.IsCall z j ∧
        tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j := by
  have hr := hrun.upTo (hrun.time_nonneg m)
  have ha : ∀ y ∈ H (tr.time m), ∀ t, gbar g ≤ t → t ≤ tr.time m →
      (tr.upTo (tr.time m)).awake y t := fun y hy t ht htm =>
    ⟨hawake y t (hrun.antitone htm hy) ht (htm.trans hmb), htm⟩
  obtain ⟨j, hj, -⟩ := Healing.snapshot_of_awake hr ha ⟨z, hz⟩
    (show cutZ sp.toParams g + sp.Δ ≤ tr.time m by linarith)
  refine ⟨⟨j, hj⟩, ?_⟩
  obtain ⟨j, hjm, hc, hd⟩ := Healing.snapshotCall_of_awake hr ha hfit
    (T := tr.time m + 1) le_rfl z hz m le_rfl
    (show tr.time m < tr.time m + 1 by linarith)
  have hjt := ((RunTrace.upTo_isCall tr).mp hc).1
  refine ⟨j, hjm, ((RunTrace.upTo_isCall tr).mp hc).2, ?_⟩
  rwa [RunTrace.upTo_deadline hrun.time_mono hjt] at hd

/-- Snapshot relay at the proposal call bounds a warm proposal's replay height. -/
theorem warm_proposal_height_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s₀ u : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hwarm : s₀ + 2 * sp.k ≤ u) (hub : sp.ts u ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u) :
    HZ tr H g ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + 1 := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [htime]; linarith) hz
  have hr := hrun.upTo (hrun.time_nonneg kP)
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  obtain ⟨_, ip, ell, d, pay, hc, hcall, hd, hti, hpar, _, _, _, ja, hja, hacc, hta⟩ :=
    Healing.honestProposalRun_of_proposesAt hr (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hc hd hacc
  have hip : tr.time ip = sp.ts u := hti
  have hipk : tr.time ip ≤ tr.time kP := by rw [hip, htime]
  have hzi : z ∈ H (tr.time ip) := hrun.antitone hipk hzk
  have hc' : tr.projAC.CallAt z ip ell := by
    rw [RunTrace.upTo_projAC] at hc
    exact ((Trace.upTo_callAt tr.projAC).mp hc).2
  have hframe : ell.frame = Node.frame (tr.state z ip) :=
    (hrun.cutLaw z ip (.ac ell) (Compose.projAC_callAt.mp hc') hzi).1
  have hfi : (H (tr.time ip))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf _ (hrun.time_nonneg ip) (hip ▸ hub)
    have hn := sp.toParams.hn
    change (H (tr.time ip))ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  obtain ⟨Q, hQ, hv, hroot⟩ := full_frame_viable_witness_at hrun hnc hzi hfi
  rw [← hframe] at hQ hv hroot
  have hac := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time kP)) _ proposer
    hr (hnc.upTo _)).localRun
  have hvd := Healing.proposal_head_viable hac hzk hc hcall
    (by rw [sp.slotTime_eq]; exact hti) hd
    ⟨(SA.frameIn_of_callAt hac hzk hc).1.fcRoot_mem, .refl, Q, hQ, hv, hroot⟩
  rw [hframe] at hvd
  have hfit : cutZ sp.toParams g + sp.Δ + 1 ≤ tr.time ip := by
    have hk := sp.two_le_k
    have h4 : sp.ts (s₀ + 4 : Nat) ≤ sp.ts u :=
      (SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ + 4 ≤ u by omega))
    have he : sp.ts (s₀ + 4 : Nat) = sp.ts s₀ + 16 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rw [he] at h4
    rw [hip]
    linarith [cutZ_le sp g]
  obtain ⟨hsnap, hcallZ⟩ := snapshotCall_of_awake_at hrun hawake hzi hfit (hip ▸ hub)
  have hcz : cutZ sp.toParams g ≤ tr.time ip := by linarith
  have hZ := HZ_le_hmax_at hrun hnc hsvc hcatch
    ⟨z, hrun.antitone hcz hzi⟩ hsnap hzi (by simpa only [max_eq_right hcz] using hfi)
    hcallZ (by
      have hsu : sp.ts s₀ ≤ sp.ts u := (SA.ts_le_iff sp).2 (by exact_mod_cast (by omega : s₀ ≤ u))
      rw [hip]; linarith)
  have hheight := Store.height_le_of_isViable hvd.2.2.2 hZ
  have hle : ∀ q < kP + 1, tr.time q ≤ tr.time kP := fun q hq => hrun.time_mono (by omega)
  have hs1 := Trace.upTo_state tr z hle
  obtain ⟨_, hPm, _⟩ := Healing.accept_of_proposesAt hr (hnc.upTo _) hzk hP'
  rw [hs1] at hPm
  have hDhist : d.head ∈ tr.HonestBlocksAt H :=
    ⟨z, ip, _, hrun.time_nonneg ip, fun q hq => hrun.time_mono hq.le, hzi, hvd.1⟩
  have hPhist : P ∈ tr.HonestBlocksAt H :=
    ⟨z, kP + 1, _, hrun.time_nonneg kP, hle, hzk, hPm⟩
  have hDP : Anc (tr.HonestBlocksAt H) d.head P := .single ⟨hDhist, hPhist, hpar⟩
  have hDpost := mem_of_honest_anc_at hrun hnc (hrun.time_nonneg kP) hle hzk hDP hPm
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg ip)
    (fun q hq => hrun.time_mono hq.le) hzi (hrun.time_nonneg kP) hle hzk hvd.1 hDpost
  rw [hσ] at hheight
  have hh := h_le_of_store_anc (fg_reachable_at hrun (hrun.time_nonneg kP) hle hzk)
    (.single ⟨hDpost, hPm, hpar⟩)
  omega

/-- Finite service supplies the frozen drain contract. The full proposal frame suffices;
no cast-time frame or signature-height restriction is needed for this lower bound. -/
theorem drainOutputs_of_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {G Ld : Nat} (hLd : 2 * sp.k + G ≤ Ld + 1) :
    DrainOutputs tr proposer H g G Ld b where
  warm := by
    intro s₀ N floor kindJ J _ hm hN hb _ hgp
    obtain ⟨u, hlu, hhu, hz, kP, P, hP, hPs⟩ :=
      proposalGap_iff.mp hgp (s₀ + 2 * sp.k) (by omega) (by omega)
    have huN : u ≤ N := by omega
    have hts : sp.ts u ≤ sp.ts N := (SA.ts_le_iff sp).2 (by exact_mod_cast huN)
    have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
    exact ⟨u, hlu, by omega, proposer u, kP, P, hz, rfl, hP, hPs,
      warm_proposal_height_at hrun hnc hsvc hawake hf hcatch hm hlu
        (by linarith) hz rfl hP hPs⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
