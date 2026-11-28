module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNextCore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Highest
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.CarryServed
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry

public section

/-! # Fresh locks: support, next-slot votes and veto -/

namespace Consensus.Goldilocks.Healing.Growing

/-! ## No veto from compatible historical lock roots

Lock labels refer to historical honest blocks, while the veto is evaluated in the
receiver's current frame. Coherence bridges those two domains at the read cut.
-/

section

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- Compatible historical roots cannot veto a proposal in the current frame. -/
theorem no_veto_of_lock_roots_compatible_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y k ell)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    (hlocks : ∀ l ∈ (tr.projAC.state y k).locks,
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P) :
    ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P := by
  have hr := (Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg k)).localRun
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hPhi := AC.frameIn_of_callAt hr hy hc'
  have hsub := Compose.Growing.upTo_subset hrun (hrun.time_nonneg k)
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have down : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y →
      Compatible (tr.HonestBlocksAt H) Y P → Compatible (tr.HonestBlocksAt H) X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact AC.anc_total hU hXY h
  intro hconf
  obtain ⟨L, hLive, hconflict⟩ := AC.exists_of_conflictsWithLock hconf
  obtain ⟨hLt, l', ⟨l, hl, B, hB, hBr, _, rfl⟩, hLr⟩ := hLive
  have hanc := AC.anc_viableAncestor ell.frame B
  have hLva : L = ell.frame.viableAncestor B :=
    hPhi.1.coherent.1 hLt (AC.mem_of_anc hanc hB) hLr.symm
  have hcomp := down (hLva ▸ hanc.mono (fun Q hQ => hsub (hPhi.2 hQ)))
    (hlocks l hl B (hsub (hPhi.2 hB)) hBr)
  apply hconflict
  rcases hcomp with h | h
  · exact Or.inr (AC.anc_tree_of_anc_U hU hPhi.1 (fun Q hQ => hsub (hPhi.2 hQ)) hLt h hPt)
  · exact Or.inl (AC.anc_tree_of_anc_U hU hPhi.1 (fun Q hQ => hsub (hPhi.2 hQ)) hPt h hLt)

end

/-! ## Honest support at the receiver's next-slot vote branch

The supporting committee is honest at this read. Proposal acceptance is instead
charged to its historical sender, so that sender need not belong to the committee.
The receiver's branch need not emit a vote, so the receiver need not be a committee member.
-/

section

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

/-- Every member of the slot committee `K u` still honest at the next-slot read supports the
unanimous proposal in the merged view of the receiver's next-slot vote branch, for a run from
`K`'s committee start. -/
theorem unanimous_next_cast_supporters_at
    {K : AC.CommitteeDict sp.n}
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
      x ∈ AC.supporters ell.frame (AC.mergedVoteView sp R ell.frame (u + 1)) u P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch (hrun.time_nonneg j) hjb
  have hr := hS.run.localRun
  have hb' : AC.VoteBranchAt (tr.projAC.upTo (tr.time j)) y j ell R :=
    (voteBranchAt_upTo_iff hrun.time_mono).2 ⟨le_rfl, hb⟩
  have hPhi := AC.frameIn_of_callAt hr hy hb'.callAt
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg j)
  obtain ⟨q, hqj, haq, hqt⟩ := accepted_relay_before_at hrun hsvc hnr hz ha
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

/-- The receiver's next-slot vote branch clears every older incompatible lock before the update,
including labels surviving an intervening update, at the slot committees `K` of a run from `K`'s
committee start. The honest members of `K u` support the proposal at the branch's unlock and are
more than half of `K u`. The receiver need not vote in either slot. -/
theorem older_locks_compatible_at_update_at
    {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hviable : ∀ {y' : Fin sp.n} {j' : Nat} {ell' : ACLabel (goldilocksNode sp)},
      y' ∈ H (tr.time j') → tr.projAC.CallAt y' j' ell' →
      sp.ts u + 2 * sp.Δ ≤ tr.time j' → tr.time j' ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ →
      P ∈ ell'.frame.viableTree ell'.frame.tree)
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
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
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
  have hS0 := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
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
  have hacc := (Healing.accept_of_proposesAt hp (hnc.upTo _) hzk hP').1
  obtain ⟨ha', hta', _⟩ := Healing.ac_block_after hp.toLocalRun hzk hacc
  have ha : tr.projAC.AcceptAt z (kP + 1) P := by
    rw [RunTrace.upTo_projAC] at ha'
    obtain ⟨ella, hca, hea⟩ := ha'
    exact ⟨ella, ((Trace.upTo_callAt _).mp hca).2, hea⟩
  have hta : tr.time (kP + 1) = sp.ts u := hta'.trans htime
  have hza : z ∈ H (tr.time (kP + 1)) := hta' ▸ hzk
  have hjb := (hrun.time_mono hjk.le).trans hkb
  have hsupp := unanimous_next_cast_supporters_at hrun hnc hsvc hawake hf hcatch hnr
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
  exact older_locks_compatible_after_unlock_at hrun hnc hy hb hjs hjk hvi.1
    (fun x hx => Or.inr (hsupp x hx.2 hx.1).2) hhalf

end

/-! ## Next-slot extension from the warm frame

The warm frame supplies the fork-choice root and height floor at each cast.
Participation is counted at that cast, never at a fixed honest cohort.
-/

section

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

variable {ini : Fin sp.n → (goldilocksNode sp).State}

private theorem relayed_of_service
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold) {z : Fin sp.n} {k : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hz : z ∈ H (tr.time k))
    (hacc : tr.projAC.AcceptAt z k B) (hgk : g ≤ tr.time k)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)} (hy : y ∈ H (tr.time i))
    (hci : tr.projAC.CallAt y i ell) (hdl : tr.projAC.deadline y i (tr.time k) ≤ tr.time i)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k' ≤ i, tr.projAC.AcceptAt y k' B ∧ tr.time k' < tr.projAC.deadline y k' (tr.time k) := by
  apply hrun.toLocalRun.acRelayAt (σ := tr.time k) hz hacc hy hci hanc
  intro q hq hz' haq hj hF
  have hgq : g ≤ tr.time q := hq ▸ hgk
  have he : max (tr.time q) g = tr.time k := (max_eq_left hgq).trans hq
  simpa only [he] using hsvc.relay z q B hz' haq hgq y i hy hj
    (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

private theorem carry_votes
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e u (Compose.Growing.honestVotes tr H u) := by
  have hm := hrun.time_mono
  have hmA : Monotone tr.projAC.time := hm
  have hd := hrun.time_nonneg i
  have hΔ := sp.toParams.hΔ
  have hgg := AC.le_gbar g
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub := Compose.Growing.upTo_subset hrun hd
  have hac := Compose.Growing.acRun_upTo hrun hnc hd
  have hr := hac.localRun
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hti : sp.ts (u + 1 : Nat) ≤ tr.time i := by
    have h := (AC.castAt_specU hr.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at h
    exact (AC.ts_le_iff_le_slot sp hd _).2 (by omega)
  have hcarry := Compose.carryAt_of_served hr hac.vstart (Compose.frame_anc_acceptedU hr.toU hy)
    hy hc' hs (CV := Compose.Growing.honestVotes tr H u) fun v hv => by
    obtain ⟨z, q, e', hz, ⟨ell', hcz⟩, rfl, hsl⟩ := hv
    have hdq := hrun.time_nonneg q
    have haq := Compose.Growing.acRun_upTo hrun hnc hdq
    have hrq := haq.localRun
    have hcz' : AC.CastAt (tr.projAC.upTo (tr.time q)) z q ell' e' :=
      AC.upTo_castAt.mpr ⟨le_rfl, hcz⟩
    have hslq := (AC.castAt_specU hrq.toU hz hcz').2.1
    change e'.msg.slot = sp.slot (tr.time q) at hslq
    have hqts : sp.ts u ≤ tr.time q := (AC.ts_le_iff_le_slot sp hdq _).2 (by omega)
    obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hrq haq.vstart hz hcz'
    rw [hsl] at hqt
    change tr.time q ≤ _ at hqt
    have hqi : tr.time q ≤ tr.time i := by linarith
    have hHdp := (AC.frameIn_of_callAt hrq hz hcz'.1).2 hHd
    obtain rfl : Hd = P := hU.1 (Compose.Growing.upTo_subset hrun hdq hHdp) hP
      (hHdr.trans (hun z q e' hz ⟨ell', hcz⟩ (hqi.trans hib) hsl))
    refine ⟨hsl, ⟨tr.time q, hqts, by linarith, fun hdl => ?_⟩, Hd, hHdr, ?_⟩
    · rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      exact (AC.upTo_messageServedBefore hmA le_rfl).mpr
        (served_of_resetService hsvc hz hcz (hgg.trans (hg.trans hqts)) hy hcast.1 hdl)
    rcases Compose.frame_anc_acceptedU hrq.toU hz q ell' hcz'.1 Hd hHd Hd .refl with
      h0 | ⟨k, hk, ha⟩
    · exact Or.inr (Or.inl h0)
    obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp ha
    change tr.time k ≤ tr.time q at hkq
    have hzk := hrun.antitone hkq hz
    by_cases hkg : gbar g ≤ tr.time k
    · refine Or.inl ⟨tr.time k, by linarith, fun hdl => ?_⟩
      rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      obtain ⟨ky, hky, hacc, hkyt⟩ := relayed_of_service hrun hsvc hzk ha (hgg.trans hkg) hy
        hcast.1 hdl hFP
      have hkyd := hm hky
      exact ⟨ky, hky, (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨hkyd, hacc⟩,
        by rw [ACTrace.upTo_deadline hmA hkyd]; exact hkyt⟩
    · obtain ⟨ky, hky, hacc, hkyt⟩ := hrun.toLocalRun.acCatchAt hc hzk ha (not_le.mp hkg) hy
        hcast.1 (by linarith) hFP
      exact Or.inr (Or.inr ⟨ky, (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr
        ⟨hm hky, hacc⟩, by change tr.time ky < _; linarith⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hsub hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHv hX)).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, ((ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp hk).2, hkt⟩

private theorem head_accepted
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    (hcall : tr.projAC.CallAt y j ell) (hti : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    (hvote : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hanc : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    ∃ k' ≤ j, tr.projAC.AcceptAt y k' P ∧ tr.time k' < sp.ts u + 3 * sp.Δ := by
  have hm := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨w, q, e', hwq, ⟨ellv, hv⟩, hvs, hq⟩ := hvote
  have hqj : tr.time q ≤ tr.time j := by linarith
  have hrq := Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg q)
  have hvq : AC.CastAt (tr.projAC.upTo (tr.time q)) w q ellv e' :=
    AC.upTo_castAt.mpr ⟨le_rfl, hv⟩
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hrq.localRun hrq.vstart hwq hvq
  have hHdq := (AC.frameIn_of_callAt hrq.localRun hwq hvq.1).2 hHd
  obtain rfl : Hd = P := hU.1 (Compose.Growing.upTo_subset hrun (hrun.time_nonneg q) hHdq) hP
    (he.trans (hun w q e' hwq ⟨ellv, hv⟩ (hqj.trans hjb) hvs))
  obtain hz | ⟨k, hk, ha⟩ := AC.frame_genesis_or_acceptedU sp hrq.localRun.toU hwq hvq.1 Hd hHd
  · omega
  obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mp ha
  change tr.time k ≤ tr.time q at hkq
  have hwk := hrun.antitone hkq hwq
  have hdl : ∀ c ≤ j, tr.projAC.deadline y c (tr.time k) ≤ max (tr.time k) (gbar g) + sp.Δ :=
    fun c hcj => Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := c)
      (fun r hrc hrs => hnr r (hrc.trans hcj) (Compose.projAC_restartAt.mp hrs)) (tr.time k)
  by_cases hkg : gbar g ≤ tr.time k
  · obtain ⟨k', hk'j, ha', hlt⟩ := relayed_of_service hrun hsvc hwk ha
      ((AC.le_gbar g).trans hkg) hy hcall
      ((hdl j le_rfl).trans (by rw [max_eq_left hkg]; linarith)) hanc
    have := hdl k' hk'j
    rw [max_eq_left hkg] at this
    exact ⟨k', hk'j, ha', by linarith⟩
  · obtain ⟨k', hk'j, ha', hlt⟩ := hrun.toLocalRun.acCatchAt hc hwk ha (not_le.mp hkg) hy
      hcall (by linarith) hanc
    exact ⟨k', hk'j, ha', by linarith⟩

private theorem cast_bounds
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) :
    sp.ts e.msg.slot ≤ tr.time j ∧ tr.time j ≤ sp.ts e.msg.slot + sp.Δ := by
  have hr := Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg j)
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
    AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hs := (AC.castAt_specU hr.localRun.toU hy hc').2.1
  change e.msg.slot = sp.slot (tr.time j) at hs
  exact ⟨(AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega),
    (Compose.cast_head_fcRoot hr.localRun hr.vstart hy hc').2⟩

private theorem next_viable
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) (hjb : tr.time j ≤ b)
    (hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g)
    (hvote : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hroot : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P)
    (hv : P ∈ ell.frame.viableHeads) :
    Anc (tr.HonestBlocksAt H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hd := hrun.time_nonneg j
  have hr := Compose.Growing.acRun_upTo hrun hnc hd
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
    AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr.localRun hy hc'.1
  have hsub := Compose.Growing.upTo_subset hrun hd
  have hFP := ((hPhi.F_anc_fcRoot.mono hPhiU).mono hsub).trans hroot
  have hti := (cast_bounds hrun hnc hy hcast).1
  have hΔ := sp.toParams.hΔ
  rw [hs] at hti
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  obtain ⟨k, hkj, ha, hkt⟩ := head_accepted hrun hnc hsvc hc hP hslot hu hun hg hy hcast.1
    (by linarith) hjb hnr hvote hFP
  have ha' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time j)) y k P :=
    (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨hrun.time_mono hkj, ha⟩
  have hPu : P ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
    obtain ⟨ella, hca, hea⟩ := ha'
    exact (AC.frameIn_of_callAt hr.localRun hy hca).2
      ((AC.accept_new sp hr.localRun hy ⟨ella, hca, hea⟩).1 ella hca)
  have hroot' := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hPu hroot
  have hFP' := (hPhi.F_anc_fcRoot.mono hPhiU).trans hroot'
  have hPt := AC.mem_tree_of_acceptAtU sp hr.localRun.toU hy ha' hkj hc'.1 hFP'
  have hfreeze : AC.freeze sp e.msg.slot = sp.ts u + 3 * sp.Δ := by
    simp only [AC.freeze, hs, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have hstamp := AC.readPoint_blockStamp_lt_of_acceptedBefore hr.localRun hr.vstart hy hc' hPt
    (Or.inr ⟨k, ha', by rw [hfreeze]; exact hkt⟩)
    (fun r hrj hrs => by
      rw [hfreeze]
      change tr.time r < _
      obtain ⟨ella, hca, hea⟩ := hrs
      have := hnr r hrj (Compose.projAC_restartAt.mp
        ⟨ella, ((Trace.upTo_callAt _).mp hca).2, hea⟩)
      linarith) (by rw [hfreeze]; change _ ≤ tr.time j; linarith)
  have hPv : P ∈ AC.voterBlockTree sp e.readPoint ell.frame (u + 1) :=
    ⟨hPt, Or.inl (by simpa only [hs] using hstamp)⟩
  have hanc := AC.anc_tree_of_anc_U hr.localRun.coherent hPhi hPhiU hPhi.fcRoot_mem hroot' hPt
  exact ⟨hFP, hPv, hanc, P, hPv, hv, .refl⟩

private theorem next_votes
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hg : gbar g ≤ sp.ts u) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteePAt K tr.projAC H) (hTK : AC.CommitteeTAt K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    (hnr : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ gbar g)
    (hwit : ∃ w q e', w ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC w q e' ∧ e'.msg.slot = u ∧
      tr.time q ≤ sp.ts u + sp.Δ)
    (hvotes : ∀ x, x ∈ H (sp.ts (u + 1 : Nat)) → x ∈ K.committee u → ∃ q e,
      AC.VoteAt tr.projAC x q e ∧ e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ)
    (hfault : ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      AC.FaultBoundK K u tr.projAC (H (tr.time i)) (tr.time i))
    (hcs2 : ∀ i, sp.ts (u + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      2 * (K.committee (u + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (geometry : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b →
      Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have all : ∀ j, tr.time j ≤ b → ∀ y e, y ∈ H (tr.time j) →
      AC.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rintro hjb y e hy ⟨ell, hcast⟩ hs
      have htime := (cast_bounds hrun hnc hy hcast).1
      rw [hs] at htime
      obtain ⟨hroot, hv⟩ := geometry y j ell e hy hcast hs hjb
      obtain ⟨hFP, hvi⟩ := next_viable hrun hnc hsvc hc hP hslot hu hun hg hy hcast hs hjb
        (fun r hrj hrs => hnr y r (hrun.antitone (hrun.time_mono hrj) hy) hrs
          ((hrun.time_mono hrj).trans hjb)) hwit hroot hv
      have hcarry := carry_votes hrun hnc hsvc hc hP hun hg hy hcast hs hjb hFP
      have hf := hfault j htime hjb
      have hhalf : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time j) ∧ ∃ q e', x ∈ H (tr.time q) ∧
          AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = u}.ncard := by
        have hsub : K.committee u ∩ H (tr.time j) ⊆ {x | x ∈ H (tr.time j) ∧ ∃ q e',
            x ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = u} := by
          rintro x ⟨hxK, hx⟩
          obtain ⟨q, e', hv, hvs, hq⟩ := hvotes x (hrun.antitone htime hx) hxK
          exact ⟨hx, q, e', hrun.antitone (by linarith) hx, hv, hvs⟩
        have h₁ := Set.ncard_le_ncard hsub
        have h₂ := Set.ncard_le_ncard (s := K.committee u ∩ {y | y ∈ H (tr.time j) ∧
            tr.projAC.awake y (tr.time j) ∧ AC.JoinedAt tr.projAC y (tr.time j)})
          (t := K.committee u ∩ H (tr.time j)) (fun x hx => ⟨hx.1, hx.2.1⟩)
        have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee u) (H (tr.time j))
          (Set.toFinite _)
        rw [hsize u, Set.sdiff_eq_compl_inter, Set.inter_comm (H (tr.time j))ᶜ] at hsplit
        unfold AC.FaultBoundK at hf
        omega
      refine AC.Growing.next_transfer_from (Compose.Growing.goldilocks_ac_projection_from hrun hnc)
        K hPK hTK hsize hy hcast hs ?_
        hhalf hcarry hf (hcs2 j htime hjb) (Or.inl hvi) ?_
      · intro x q e' hx hv hvs
        have hq := (cast_bounds hrun hnc hx hv.choose_spec).2
        rw [hvs] at hq
        exact ⟨P, hP, (hun x q e' hx hv (by linarith) hvs).symm, .refl⟩
      · intro x q hq hx e' hv hvs
        exact ih q hq ((hrun.time_mono hq.le).trans hjb) x e' hx hv hvs
  exact fun y j e hy hv hjb hs => all j hjb y e hy hv hs

/-- Next-slot extension from call-local full-frame geometry, independently of the frame handler. -/
theorem unanimous_next_votes_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
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
      e.msg.slot = u → e.msg.head = P.root) (hK : CommitteeHalfUpTo tr H K g b)
    (geometry : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b →
      Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have _ := hdes
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hu0 : 0 < u := by
    by_contra hn
    have he : u = 0 := by omega
    rw [he] at hmargin
    simp only [ACParams.ts, Nat.cast_zero, mul_zero] at hmargin
    linarith [AC.gbar_nonneg g]
  have hshort : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) := by
    simp only [ACParams.ts]; push_cast; linarith
  have hdeadline : sp.ts u + sp.Δ ≤ b := by linarith
  have hnextb : sp.ts (u + 1 : Nat) ≤ b := by linarith
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts u + sp.Δ by linarith [AC.gbar_nonneg g]) hdeadline
  have hvotes := honest_votes_of_joined_before_at hS hgu hjoin
  have hPh : P ∈ tr.HonestBlocksAt H := by
    have ht : tr.time kP = sp.ts u := by
      simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
    have hzP : z ∈ H (tr.time kP) := hrun.antitone (by rw [ht]; linarith) hz
    have hp := hrun.upTo (hrun.time_nonneg kP)
    have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
      ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
    obtain ⟨ha, hta, _⟩ := Healing.ac_block_after hp.toLocalRun hzP
      (Healing.accept_of_proposesAt hp (hnc.upTo _) hzP hP').1
    have hzA : z ∈ H (tr.time (kP + 1)) := hta ▸ hzP
    rw [RunTrace.upTo_projAC] at ha
    obtain ⟨ella, hca, hea⟩ := ha
    have ha' : tr.projAC.AcceptAt z (kP + 1) P :=
      ⟨ella, ((Trace.upTo_callAt _).mp hca).2, hea⟩
    have hr := Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg (kP + 1))
    have ha'' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time (kP + 1))) z (kP + 1) P :=
      (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨le_rfl, ha'⟩
    obtain ⟨ellb, hcb, heb⟩ := ha''
    exact Compose.Growing.upTo_subset hrun (hrun.time_nonneg (kP + 1))
      ((AC.frameIn_of_callAt hr.localRun hzA hcb).2
        ((AC.accept_new sp hr.localRun hzA ⟨ellb, hcb, heb⟩).1 ellb hcb))
  -- an honest member of the slot-`u` committee witnesses `P` by the slot's vote deadline
  have hnext0 : 0 ≤ sp.ts (u + 1 : Nat) := (AC.gbar_nonneg g).trans (hgu.trans (by linarith))
  obtain ⟨w, hwK, hw⟩ : (K.committee u ∩ H (sp.ts (u + 1 : Nat))).Nonempty := by
    have hcs := hK.cs2 u hgu (by linarith) _ hnext0 hnextb
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee u)
      (H (sp.ts (u + 1 : Nat))) (Set.toFinite _)
    rw [hK.facts.hsize u, Set.sdiff_eq_compl_inter, Set.inter_comm (H _)ᶜ] at hsplit
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  have hw' := hrun.antitone hshort hw
  obtain ⟨q, e, hv, hes, hq⟩ := hvotes w hw' hwK
  refine next_votes hrun hnc hsvc hcatch hPh hPs hu0
    (fun y j e hy hv _ hs => hun y j e hy hv hs) hgu hK.facts.hP
    (Compose.Growing.CommitteeFacts.committeeTAt hK.facts hrun hnc)
    hK.facts.hsize (fun y k hy hk _ => hnr y k hy hk)
    ⟨w, q, e, hrun.antitone hq hw', hv, hes, hq⟩
    (fun x hx hxK => hvotes x (hrun.antitone hshort hx) hxK) ?_ ?_ geometry
  · intro i hlo hib
    have hslot : u + 1 ≤ sp.slot (tr.time i) := by
      exact_mod_cast (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).1 hlo
    exact KernelProof.faultBoundK_of_service_at hK hrun hawake hnr hgu (by linarith)
      (hrun.time_nonneg i) (hgu.trans ((AC.ts_le_iff sp).2 (by omega))) hib
  · intro i hlo hib
    exact hK.cs2 (u + 1) (hgu.trans (by linarith)) hnextb _ (hrun.time_nonneg i) hib

end

/-! ## Compatibility of all lock labels at the warm update -/

section

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

/-- Old labels use the receiver's unlock; new fast labels use an honest vote
at the counting cut, and slow labels use the raw unanimous confirmation. At the slot committees
`K` of a run from `K`'s committee start. -/
theorem Core.unanimous_update_no_veto_at
    {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b)
    (hselect : ∀ y k, y ∈ H (tr.time k) →
      ∀ ell, AC.UpdateAt tr.projAC y k u ell →
        P ∈ ell.frame.viableTree ell.frame.tree ∧
          AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P)
    (hnext : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hold : ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P) :
    ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hkb : tr.time k ≤ b := by rw [hkt, ← hT]; exact hTb
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
    (hrun.time_nonneg k) hkb
  have hr := hS.run.localRun
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg k)
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hslot : sp.slot (tr.time k) = u + 1 := by
    rw [hkt]
    apply AC.slot_of_mem sp (u + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hPhi := AC.frameIn_of_callAt hr hy hc'
  have hvi := (hselect y k hy ell hu).1
  have down : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y →
      Compatible (tr.HonestBlocksAt H) Y P → Compatible (tr.HonestBlocksAt H) X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact AC.anc_total hU hXY h
  apply Healing.Growing.no_veto_of_lock_roots_compatible_at hrun hnc hy hu.1 hvi.1
  intro l hl L hL hLr
  by_cases hlt : l.slot < u
  · exact hold l hl hlt L hL hLr
  have hl' : l ∈ ((tr.projAC.upTo (tr.time k)).state y k).locks := by rwa [hs]
  have hle : l.slot ≤ u + 1 := by
    obtain ⟨r, hrk, B, horig, _⟩ := AC.lock_provenanceU (hr := hr.toU) hrun.vstart hy k l hl'
    have hm := AC.slot_mono sp (hr.time_nonneg r) (hr.time_mono hrk.le)
    change sp.slot (tr.time r) ≤ sp.slot (tr.time k) at hm
    rw [hslot] at hm
    rcases horig with ⟨CV, ellr, A, _, hsl, _⟩ | ⟨ellr, _, _, hrt, _⟩
    · change sp.slot (tr.time r) = l.slot at hsl
      omega
    · have hls := (AC.ts_le_iff_le_slot sp (hr.time_nonneg r) (l.slot : Int)).1
        (show sp.ts l.slot ≤ (tr.projAC.upTo (tr.time k)).time r by rw [hrt]; linarith)
      change (l.slot : Int) ≤ sp.slot (tr.time r) at hls
      omega
  cases hfast : l.fast
  · obtain ⟨r, hrk, B, ⟨ellr, C, hup, hC, hB⟩, L₁, hL₁, hL₁r, hLB⟩ :=
      AC.slow_lock_provenance hr hrun.vstart hy k l hl' hfast
    have hm := hrun.time_mono hrk.le
    have hrt : tr.time r = sp.ts l.slot + 6 * sp.Δ := hup.2.2.1
    have hls : l.slot = u := by
      have := (AC.ts_le_iff sp).1 (show sp.ts l.slot ≤ sp.ts u by linarith)
      omega
    rw [hls] at hup hC
    have hup' := (AC.upTo_updateAt hrun.time_mono).mp hup |>.2
    have hCP : C = P := by
      have hconf := (hselect y r (hrun.antitone hm hy) _ hup').2
      have hsr := Trace.upTo_state tr.projAC y (i := r)
        (fun q hq => (hrun.time_mono hq.le).trans hm)
      rw [hsr] at hC
      exact Option.some.inj (hC.symm.trans hconf)
    have hBP := (AC.deepest_mem hB).1.1.2.2
    rw [hCP] at hBP
    have hLL₁ : L = L₁ := hU.1 hL (hsub hL₁) (hLr.trans hL₁r.symm)
    rw [← hLL₁] at hLB
    exact Or.inl ((hLB.mono hsub).trans
      (hBP.mono (fun Q hQ => hsub ((AC.frameIn_of_callAt hr hy hup.1).2 hQ))))
  · obtain ⟨r, hrk, B, CV, hfl, L₁, hL₁, hL₁r, hLB⟩ :=
      AC.fast_lock_provenance hr hrun.vstart hy k l hl' hfast
    have hLL₁ : L = L₁ := hU.1 hL (hsub hL₁) (hLr.trans hL₁r.symm)
    rw [← hLL₁] at hLB
    have hgl : gbar g ≤ sp.ts l.slot := hgu.trans ((AC.ts_le_iff sp).2 (by omega))
    have hlk : sp.ts l.slot ≤ tr.time k := by
      have := (AC.ts_le_iff sp).2 (show (l.slot : Int) ≤ (u + 1 : Nat) by omega)
      linarith
    obtain ⟨x, hx, q, e, hv, hes, D, hD, hDr, hBD⟩ :=
      AC.fastLock_honest_vote hS.run K hS.hP hy hfl (hS.cs2 l.slot hgl hlk)
    obtain ⟨hqt, hv⟩ := AC.upTo_voteAt.mp hv
    apply down (hLB.mono hsub)
    rcases (show l.slot = u ∨ l.slot = u + 1 by omega) with hls | hls
    · have hDP : D = P := hU.1 (hsub hD) (hsub (hPhi.2 hvi.1))
        (hDr.trans (hun x q e (hrun.antitone hqt hx) hv (hes.trans hls)))
      rw [hDP] at hBD
      exact Or.inl (hBD.mono hsub)
    · obtain ⟨D', hD', hD'r, hPD⟩ := hnext x q e (hrun.antitone hqt hx) hv
        (hqt.trans hkb) (hes.trans hls)
      have hDD' : D = D' := hU.1 (hsub hD) hD' (hDr.trans hD'r.symm)
      rw [← hDD'] at hPD
      exact AC.anc_total hU (hBD.mono hsub) hPD

end

end Consensus.Goldilocks.Healing.Growing

end
