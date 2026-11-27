module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVeto
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshViable
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Honest support at the receiver's next-slot vote branch

The supporting committee is honest at this read. Proposal acceptance is instead
charged to its historical sender, so that sender need not belong to the committee.
The receiver's branch need not emit a vote, so the receiver need not be a committee member.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

/-- Every member of the slot committee `K u` still honest at the next-slot read supports the
unanimous proposal in the merged view of the receiver's next-slot vote branch, for a run from
`K`'s committee start, over a run bundle. -/
theorem Core.unanimous_next_cast_supporters_at
    {uf : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
    {K : AC.CommitteeDict sp.n}
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {z : Fin sp.n} {a : Nat} (hz : z ∈ H (tr.time a))
    (ha : tr.projAC.AcceptAt z a P) (hta : tr.time a = sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {R : AC.ACState sp.n}
    (hb : AC.VoteBranchAt tr.projAC y j ell R) (hjs : sp.slot (tr.time j) = u + 1)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hPt : P ∈ ell.frame.tree)
    (hvotes : ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u → ∃ i ev,
      AC.VoteAt tr.projAC x i ev ∧ ev.msg.slot = u ∧ tr.time i ≤ tr.time j)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u →
      x ∈ AC.supporters ell.frame (AC.mergedVoteView sp R ell.frame (u + 1)) u P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hS := hK.healthy_base_before_at_core hrun hnc hsvc hawake hf hcatch (hrun.time_nonneg j) hjb
  have hr := hS.run.localRun
  have hb' : AC.VoteBranchAt (tr.projAC.upTo (tr.time j)) y j ell R :=
    (voteBranchAt_upTo_iff hrun.time_mono).2 ⟨le_rfl, hb⟩
  have hPhi := AC.frameIn_of_callAt hr hy hb'.callAt
  have hsub := hrun.upTo_subset (hrun.time_nonneg j)
  obtain ⟨q, hqj, haq, hqt⟩ := Core.accepted_relay_before_at hrun hsvc hnr hz ha
    (hta ▸ hgu) hy hb.callAt (by rw [hta]; linarith)
    ((hPhi.1.rooted.2 P hPt).mono (fun Q hQ => hsub (hPhi.2 hQ)))
  have haq' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time j)) y q P := by
    obtain ⟨ellq, hcq, heq⟩ := haq
    exact ⟨ellq, (Trace.upTo_callAt _).mpr ⟨hrun.time_mono hqj, hcq⟩, heq⟩
  have hrst : ∀ k ≤ j, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y k →
      tr.time k < sp.ts u := by
    intro k _ ⟨ellk, hck, hk⟩
    have hkt := ((Trace.upTo_callAt _).mp hck).1
    have hb := hnr y k (hrun.antitone hkt hy)
      (Compose.projAC_restartAt.mp ⟨ellk, ((Trace.upTo_callAt _).mp hck).2, hk⟩)
    linarith
  intro x hx hxK
  obtain ⟨i, ev, hv, hs, hit⟩ := hvotes x hx hxK
  have hv' : AC.VoteAt (tr.projAC.upTo (tr.time j)) x i ev := by
    obtain ⟨ellx, hcx, he⟩ := hv
    exact ⟨ellx, (Trace.upTo_callAt _).mpr ⟨hit, hcx⟩, he⟩
  have hval := (AC.castAt_specU hr.toU hx ⟨hv'.choose_spec.1, hv'.choose_spec.2⟩).1
  have heP := hun x i ev (hrun.antitone hit hx) hv hs
  have hheld : AC.HeldBefore R ev.msg (sp.ts u + 2 * sp.Δ) := by
    apply AC.heldBefore_readPoint_branchU hr.toU hy hb' (fun h => by
      have h' : ev.msg.slot = u + 1 := h.symm.trans hjs
      omega)
    simpa only [hs] using AC.honest_vote_early_pool_before hS hy hb'.callAt hgu ht le_rfl
      (fun k hkj t _ => Compose.ac_deadline_le_of_restarts
        (fun r hr hrs => (hrst r (hr.trans hkj) hrs).le) t)
      hrst hx hv' hs (j + 1) (Or.inr rfl)
  have hsupp := AC.carried_supporter_branchU hS.run.toU hy hb' hjs hPt hs
    ⟨hheld.1, lt_trans hheld.2
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by linarith)))⟩
    ⟨P, hPhi.2 hPt, heP.symm, hPs.le, .refl,
      Or.inr ⟨q, haq', by change tr.time q < _; rw [hta] at hqt; linarith⟩⟩
    (AC.honest_not_equivocator_branchU hS.run.toU hy hb' (hval ▸ hx))
  rwa [hval] at hsupp

/-- Every member of the slot committee `K u` still honest at the next-slot read supports the
unanimous proposal in the merged view of the receiver's next-slot vote branch, for a run from
`K`'s committee start. -/
theorem unanimous_next_cast_supporters_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {z : Fin sp.n} {a : Nat} (hz : z ∈ H (tr.time a))
    (ha : tr.projAC.AcceptAt z a P) (hta : tr.time a = sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {R : AC.ACState sp.n}
    (hb : AC.VoteBranchAt tr.projAC y j ell R) (hjs : sp.slot (tr.time j) = u + 1)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hPt : P ∈ ell.frame.tree)
    (hvotes : ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u → ∃ i ev,
      AC.VoteAt tr.projAC x i ev ∧ ev.msg.slot = u ∧ tr.time i ≤ tr.time j)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ x, x ∈ H (tr.time j) → x ∈ K.committee u →
      x ∈ AC.supporters ell.frame (AC.mergedVoteView sp R ell.frame (u + 1)) u P :=
  Core.unanimous_next_cast_supporters_at hrun.toCore hnc hsvc hawake hf hcatch hnr hmargin hPs hun
    hz ha hta hy hb hjs ht hjb hPt hvotes hK

/-- The receiver's next-slot vote branch clears every older incompatible lock before the update,
including labels surviving an intervening update, at the slot committees `K` of a run from `K`'s
committee start. The honest members of `K u` support the proposal at the branch's unlock and are
more than half of `K u`. The receiver need not vote in either slot. -/
theorem Core.older_locks_compatible_at_update_at
    {uf : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
    {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hviable : ∀ {y' : Fin sp.n} {j' : Nat} {ell' : ACLabel (goldilocksNode sp)},
      y' ∈ H (tr.time j') → tr.projAC.CallAt y' j' ell' →
      sp.ts u + 2 * sp.Δ ≤ tr.time j' → tr.time j' ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ →
      P ∈ ell'.frame.viableTree ell'.frame.tree)
    (hrun : GoldilocksRunCore uf frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P := by
  have _ := hdes
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hnext : sp.ts (u + 1 : Nat) + sp.Δ ≤ tr.time k := by
    rw [hkt]; simp only [ACParams.ts]; push_cast; linarith
  have hkb : tr.time k ≤ b := by rw [hkt, ← hT]; exact hTb
  have hS := hK.healthy_base_before_at_core hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts (u + 1 : Nat) + sp.Δ by
      have ht : sp.ts u ≤ sp.ts (u + 1 : Nat) := (AC.ts_le_iff sp).2 (by omega)
      linarith [AC.gbar_nonneg g]) (hnext.trans hkb)
  have hslot : sp.slot (sp.ts (u + 1 : Nat) + sp.Δ) = u + 1 := by
    apply AC.slot_of_mem sp (u + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith
  have hjn : ∀ x, x ∈ H (sp.ts (u + 1 : Nat) + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts (u + 1 : Nat) + sp.Δ) := by
    intro x hx r hrs hrt
    change tr.time r ≤ sp.ts ((sp.slot (sp.ts (u + 1 : Nat) + sp.Δ) : Int) - 1)
    rw [hslot, show ((u + 1 : Nat) : Int) - 1 = u by omega]
    exact (hnr x r (hrun.antitone hrt hx) (Compose.projAC_restartAt.mp hrs)).trans hgu
  obtain ⟨j, ellj, R, hb, hjs, hjt⟩ := honest_vote_branches_of_joined_before_at hS
    (by have := (AC.ts_le_iff sp).2 (show (u : Int) ≤ u + 1 by omega); linarith) hjn y
    (hrun.antitone hnext hy)
  replace hjs : sp.slot (tr.time j) = u + 1 := by omega
  have hjk : j < k := by
    by_contra hn
    have hm := hrun.time_mono (show k ≤ j by omega)
    rw [hkt] at hm
    simp only [ACParams.ts] at hjt
    push_cast at hjt
    simp only [ACParams.ts] at hm
    linarith
  have hjlo : sp.ts (u + 1 : Nat) ≤ tr.time j :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega)
  have hjlate : sp.ts u + 2 * sp.Δ ≤ tr.time j := by
    simp only [ACParams.ts] at hjlo ⊢; push_cast at hjlo; linarith
  have hjfinite : tr.time j ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by linarith
  have hyj := hrun.antitone (hrun.time_mono hjk.le) hy
  have hshort : sp.ts u + sp.Δ ≤ tr.time j := by linarith
  have hS0 := hK.healthy_base_before_at_core hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts u + sp.Δ by linarith [AC.gbar_nonneg g])
    (hshort.trans (hrun.time_mono hjk.le |>.trans hkb))
  have hvotes := honest_votes_of_joined_before_at hS0 hgu hjoin
  have hvi := hviable hyj hb.callAt hjlate hjfinite
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) :=
    hrun.antitone (by rw [htime]; linarith) hz
  have hp := hrun.upTo (hrun.time_nonneg kP)
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  have hacc := (hp.accept_of_proposesAt (hnc.upTo _) hzk hP').1
  obtain ⟨ha', hta', _⟩ := hp.ac_block_after z hzk hacc
  have ha : tr.projAC.AcceptAt z (kP + 1) P := by
    rw [RunTrace.upTo_projAC] at ha'
    obtain ⟨ella, hca, hea⟩ := ha'
    exact ⟨ella, ((Trace.upTo_callAt _).mp hca).2, hea⟩
  have hta : tr.time (kP + 1) = sp.ts u := hta'.trans htime
  have hza : z ∈ H (tr.time (kP + 1)) := hta' ▸ hzk
  have hjb := (hrun.time_mono hjk.le).trans hkb
  have hsupp := Core.unanimous_next_cast_supporters_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hPs hun hza ha hta hyj hb hjs hjlate hjb hvi.1
    (fun x hx hxK => by
      obtain ⟨i, ev, hv, hes, hit⟩ := hvotes x (hrun.antitone hshort hx) hxK
      exact ⟨i, ev, hv, hes, hit.trans hshort⟩) hK
  have hhalf : sp.committeeSize ≤ 2 * (K.committee u ∩ H (tr.time j)).ncard := by
    have hsplit : (K.committee u ∩ H (tr.time j)).ncard +
        (K.committee u ∩ (H (tr.time j))ᶜ).ncard = sp.committeeSize := by
      rw [← hK.facts.hsize u, Set.inter_comm (K.committee u) (H (tr.time j))ᶜ,
        ← Set.sdiff_eq_compl_inter]
      exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
    have hcs := hK.cs2 u hgu (by linarith) (tr.time j) (hrun.time_nonneg j) hjb
    omega
  exact Core.older_locks_compatible_after_unlock_at hrun hnc hy hb hjs hjk hvi.1
    (fun x hx => Or.inr (hsupp x hx.2 hx.1).2) hhalf

/-- The receiver's next-slot vote branch clears every older incompatible lock before the update,
including labels surviving an intervening update, at the slot committees `K` of a run from `K`'s
committee start. The honest members of `K u` support the proposal at the branch's unlock and are
more than half of `K u`. The receiver need not vote in either slot. -/
theorem FrameWindow.older_locks_compatible_at_update_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P :=
  Core.older_locks_compatible_at_update_at
    (fun hy' hc' hlo hhi => (hframe.proposal_viable_after_votes_at hrun hnc hsvc hf hnr
      (by linarith [sp.toParams.hΔ]) hTb hz hdes hP hPs hy' hc' hlo hhi).1)
    hrun.toCore hnc hsvc hawake hf hcatch hnr hmargin hjoin hTb hz hdes hP hPs hun hy hu hK

end Consensus.Goldilocks.Healing.Growing

end
