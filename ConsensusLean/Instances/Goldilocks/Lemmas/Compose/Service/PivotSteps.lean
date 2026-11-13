module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.ProposalCall
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the steps of the pivot of an honest proposal

The steps of `Compose/Service/Pivot`, which imports them privately, shared with the growing-fault
pivot (`Growing/Sleepy/Service/PivotWalk`): the relay of an honest supporting head to the proposer
(`proposer_relay_before`, `proposer_accepts_head_before`), the children towards an old origin
winning the walk (`proposal_best_toward_old_before`), the proposal's rows, `fc_root` and locks below
the old origins (`proposal_rows_old_of`, `proposal_fcRoot_old_of`, `proposal_lock_below`), its
anchor (`proposal_anchor_old_of`), a voter's anchor cases (`vote_anchor_cases_of_old`, with
`honest_eq_proposal_of_root`), and the viability of the suffix (`proposal_suffix_viable_of`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ### Over a run -/

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- An old origin of slot `s` is an origin of a label below `s`. -/
private theorem OldOrigin.origin {s : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : OldOrigin tr H s O) : ∃ m < s, Origin tr H O m := by
  obtain ⟨x, hx, k, m, CV, ⟨hR, hm⟩ | ⟨hO, hm⟩⟩ := oldOrigin_iff.1 h
  · exact ⟨m, by omega, Origin.of_result hx hR⟩
  · exact ⟨m, by omega, Origin.of_optimistic hx hO⟩

/-- Blocks with the same fields are equal. -/
theorem blk_eq_of_fields {X Y : SA.Blk sp.n (List (FG.Att sp.n))} (h0 : X.root = Y.root)
    (h1 : X.parent = Y.parent) (h2 : X.slot = Y.slot) (h3 : X.proposer = Y.proposer)
    (h4 : X.input = Y.input) (h5 : X.fgPayload = Y.fgPayload) (h6 : X.acPayload = Y.acPayload) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-- **An honest block with the root of an honest proposal is that proposal** (`NoColl`): both
roots are digests, of an occurring block, and the slot's proposer made both. -/
theorem honest_eq_proposal_of_root (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ tr.HonestBlocks H) (hr : R.root = P.root) : R = P := by
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, hpp, -⟩ := hP
  rcases blockCall_cases hrun.toLocalRun hp hcB with hg | ⟨j, x, rfl, -, hPr, d, pay, -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hok : P.RootOk dg := by rw [hB]; rfl
  have hpr : P.proposer = proposer P.slot := by
    rw [hpp, hB]
    exact hPr.2.2.symm
  have hpar : P.parent ≠ none := by rw [hB]; simp [Node.mkBlock]
  have hocc : tr.Occurs P := ⟨p, _, acc, hcB⟩
  obtain ⟨y, hy, i, hRt⟩ := hR
  rcases tree_cases hrun.toLocalRun hy hRt with rfl | ⟨k', -, hk'⟩
  · have := (hnc _ (Set.mem_insert _ _) P (Or.inr hocc)
      (hrun.genesis_root_ok.symm.trans (hr.trans hok))).1
    exact absurd this.symm (by simpa [Params.genesisBlock] using hpar)
  obtain ⟨hRok, hRpr, -⟩ := accept_facts hrun.toLocalRun hy hk'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hnc R (Or.inr ⟨y, k', true, hk'⟩) P (Or.inr hocc)
    (hRok.symm.trans (hr.trans hok))
  exact blk_eq_of_fields hr h1 h2 (by rw [hRpr, hpr, h2]) h3 h4 h5
/-- **A block an honest node accepts before `t_{s−1} + 2Δ` reaches the proposer** of slot `s`
(`Sync`, the proposer awake since its last restart at or before `t_{s−1}`): when the proposer's
`Σ.F` is below it, it is in the proposal's frame, accepted before `t_{s−1} + 3Δ`. -/
theorem proposer_relay_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {b : Time} (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b)
    {x : Fin sp.n} (hx : x ∈ H) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hacc : B.root = sp.genesisRoot ∨ ∃ kx, tr.projAC.AcceptAt x kx B ∧
      tr.projAC.time kx < sp.ts ((s : Int) - 1) + 2 * sp.Δ)
    (hFB : Anc (tr.HonestBlocks H) ℓp.frame.F B) :
    B ∈ ℓp.frame.tree ∧ SA.AcceptedBefore tr.projAC p B (sp.ts ((s : Int) - 1) + 3 * sp.Δ) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  rcases hacc with hg | ⟨kx, hacc, hkxt⟩
  · refine ⟨?_, Or.inl hg⟩
    have h2 := (honest_genesis_anc hrun (hΦU hΦ.rooted.1)).2
    rw [← honest_eq_genesis hrun hU hB hg] at h2
    rw [← Anc.antisymm hU hFB h2]
    exact hΦ.rooted.1
  obtain ⟨hdl, hdi⟩ := proposal_relay_deadline (T := tr.projAC) hti
    (proposal_call_restarts hrun hnc hp hc hcall hd) hkxt.le
  obtain ⟨k', hk'i, hAp, hk't⟩ := hsync.relay x hx kx B hacc (hr.time_nonneg kx)
    p hp i ℓp hc (hdi.trans hb) hdi hFB
  exact ⟨SA.mem_tree_of_acceptAt sp hr hp hAp hk'i hc hFB,
    Or.inr ⟨k', hAp, lt_of_lt_of_le hk't (hdl k' hk'i)⟩⟩

/-- **The head of an honest vote of a slot before `s` reaches the proposer** of slot `s`: its
voter accepted it (or it is genesis) by `t_{s−1} + Δ` (`frame_anc_accepted`), and
`proposer_relay_before`. -/
theorem proposer_accepts_head_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {b : Time} (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x j e) (hes : e.msg.slot + 1 ≤ s)
    {Hd : SA.Blk sp.n (List (FG.Att sp.n))} (hHd : Hd ∈ tr.HonestBlocks H)
    (hHdr : Hd.root = e.msg.head) (hFHd : Anc (tr.HonestBlocks H) ℓp.frame.F Hd) :
    Hd ∈ ℓp.frame.tree ∧ SA.AcceptedBefore tr.projAC p Hd (sp.ts ((s : Int) - 1) + 3 * sp.Δ) ∧
      Hd.slot ≤ e.msg.slot := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨ℓx, hcx, hex⟩ := hv
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hjt⟩ := cast_head_fcRoot hr hx ⟨hcx, hex⟩
  have hHdeq : Hd' = Hd :=
    hU.1 ((SA.frameIn_of_callAt hr hx hcx).2 hHd't) hHd (hHd'r.trans hHdr.symm)
  rw [hHdeq] at hHd't
  have hjt' : tr.projAC.time j ≤ sp.ts ((s : Int) - 1) + sp.Δ := by
    have : sp.ts (e.msg.slot : Int) ≤ sp.ts ((s : Int) - 1) := by
      simp only [SAParams.ts]
      exact mul_le_mul_of_nonneg_left (show (e.msg.slot : Int) ≤ (s : Int) - 1 by omega)
        (mul_nonneg zero_le_four hΔ.le)
    linarith only [hjt, this]
  have hslot : Hd.slot ≤ e.msg.slot := by
    rw [(SA.castAt_spec hr hx ⟨hcx, hex⟩).2.1]
    exact SA.frame_slot_le sp hr hx hcx Hd hHd't
  have hacc : Hd.root = sp.genesisRoot ∨ ∃ kx, tr.projAC.AcceptAt x kx Hd ∧
      tr.projAC.time kx < sp.ts ((s : Int) - 1) + 2 * sp.Δ := by
    rcases frame_anc_accepted hr hx j ℓx hcx Hd hHd't Hd .refl with hg | ⟨kx, hkx, hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨kx, hacc, lt_of_le_of_lt (hr.time_mono hkx) (by linarith only [hjt', hΔ])⟩
  obtain ⟨h1, h2⟩ := proposer_relay_before hrun hnc hsync hp hc hcall hd hti hb hx hHd hacc hFHd
  exact ⟨h1, h2, hslot⟩

/-- **The children towards an old origin win the proposal walk**: at every
block `X` (of the full viable tree, with the proposal's slot-`(s−1)` pool view `pay`), a viable
child `Cx` of `X` below an old origin held by the proposer is the best eligible child. A vote of
the proposer's pool is held with a finite stamp; an honest validator has one vote in it
(`one_vote_per_slot`). For an origin of label below `s − 1`, every honest slot-`(s−1)` vote
extends it (S2), is relayed to the proposer (`SA.sync_forward`) and resolved there (its head is
relayed too, `proposer_accepts_head_before`), so the honest slot-`(s−1)` voters support it, and the
other voters are faulty (the fault bound, `SA.isBest_of_majority`). For an optimistic
origin of label `s − 1`, the at least `3n/4` votes it counted (`optimistic_writer_votes`) are
relayed likewise, so each of its seats supports it or equivocates, and the equivocators and the
voters outside are fewer (`2f < n`, `SA.isBest_of_cover`). -/
theorem proposal_best_toward_old_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) :
    ∀ O, OldOrigin tr H s O → O ∈ ℓp.frame.tree → ∀ X Cx : SA.Blk sp.n (List (FG.Att sp.n)),
      Cx ∈ ℓp.frame.viableTree ℓp.frame.tree → Cx.parent = some X.root → ℓp.frame.Anc Cx O →
      SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
        {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
          SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1) B}
        Cx := by
  intro O hO hOt X Cx hCx hpar hCxO
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have hzero := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb0)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at hzero
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := by
    obtain ⟨m, hm, -⟩ := hO.origin
    exact ⟨s - 1, by omega⟩
  have hσ : (((s' + 1 : Nat) : Int) - 1) = (s' : Int) := by push_cast; ring
  have hsi : sp.slot (tr.time i) = s' + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s' + 1)).1 0 (by omega)
  have hts : sp.ts ((s' + 1 : Nat) : Int) = sp.ts (s' : Int) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hii : tr.projAC.time i = tr.time i := rfl
  rw [hσ]
  set A := tr.projAC.state p i with hA
  -- the payload is the proposer's slot-`(s−1)` pool
  obtain ⟨hvotes, hsupv⟩ := acProposal_pay_view hd hsi
  have hsub : (SA.View.ofLists pay).support ⊆ (SA.View.ofLists pay).votes := fun v hv =>
    (hvotes v).2 ((hsupv v).1 hv).1
  -- the pool's votes have finite stamps
  have hstamp : ∀ v ∈ A.pool s', A.voteStamp v < ⊤ := by
    intro v hv
    have hvs : v.slot = s' := SA.state_pool_slot sp hr hp i s' v hv
    rcases SA.pool_origin hr hp i v (by rw [hvs]; exact hv) with
      ⟨k, -, -, hst, -⟩ | ⟨k, -, -, -, -, hst, -⟩ <;>
    · rw [hst]; exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  have hvotes' : ∀ v, v ∈ (SA.View.ofLists pay).votes ↔ v ∈ A.pool s' := fun v =>
    ⟨fun h => ((hvotes v).1 h).1, fun h => (hvotes v).2 ⟨h, hstamp v h⟩⟩
  -- an honest validator has at most one vote in the pool
  have hnoeq : ∀ w ∈ H, w ∉ SA.equivocators {v | v ∈ A.pool s'} := by
    rintro w hw ⟨v₁, hv₁, v₂, hv₂, hne, rfl, h2⟩
    obtain ⟨j₁, -, e₁, hve₁, rfl⟩ := hrun'.honest.pool_vote p hp i s' v₁ hv₁ hw
    obtain ⟨j₂, -, e₂, hve₂, rfl⟩ := hrun'.honest.pool_vote p hp i s' v₂ hv₂ (h2 ▸ hw)
    have hs₁ := SA.state_pool_slot sp hr hp i s' _ hv₁
    have hs₂ := SA.state_pool_slot sp hr hp i s' _ hv₂
    obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr _ hw j₁ j₂ e₁ e₂ hve₁
      (h2 ▸ hve₂) (hs₁.trans hs₂.symm)
    exact hne rfl
  have hequiv : SA.equivocators (SA.View.ofLists pay).votes ⊆ Hᶜ := by
    rintro w ⟨v₁, hv₁, v₂, hv₂, hne, h1, h2⟩ hw
    exact hnoeq w hw ⟨v₁, (hvotes' v₁).1 hv₁, v₂, (hvotes' v₂).1 hv₂, hne, h1, h2⟩
  -- the proposer's restarts, and the relay window
  have hrs := proposal_call_restarts hrun hnc hp hc hcall hd
  rw [hsi, hσ] at hrs
  have hac := hsync.ac
  -- a vote sent or admitted by an honest node in `[t_{s−1}, t_{s−1} + 2Δ)` is in the pool
  have hfwd : ∀ x ∈ H, ∀ kx v, tr.projAC.SendOrAdmit x kx v → v.slot = s' →
      sp.ts (s' : Int) ≤ tr.projAC.time kx → tr.projAC.time kx < sp.ts (s' : Int) + 2 * sp.Δ →
      v ∈ A.pool s' ∨ v.val ∈ SA.equivocators {w | w ∈ A.pool s'} := by
    intro x hx kx v hsend hvs hk1 hk2
    have h := SA.sync_before_forward hr hac hx hsend
      (by rw [hti, hts] at hb; linarith only [hk2, hb, hΔ]) hp hc
      (fun k' hk' hrk' => (hrs k' hk' hrk').trans hk1)
      (by rw [hii, hti, hts]; linarith only [hk2, hΔ])
      (fun t ht1 ht2 => by
        have := SA.slot_of_mem sp s' (hk1.trans ht1) (by rw [hts]; linarith only [ht2, hk2, hΔ])
        omega)
    rwa [hvs] at h
  -- a vote of the pool whose head, of a slot at most its own, the proposer accepted is resolved
  have hres : ∀ v ∈ A.pool s', ∀ Hv ∈ ℓp.frame.tree, Hv.root = v.head → Hv.slot ≤ v.slot →
      SA.AcceptedBefore tr.projAC p Hv (sp.ts (s' : Int) + 3 * sp.Δ) →
      v ∈ (SA.View.ofLists pay).support := by
    intro v hv Hv hHv hHvr hHvs hacc
    refine (hsupv v).2 ⟨⟨hv, hstamp v hv⟩, ?_⟩
    have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hp hc hHv hacc
      (fun k hk hrk => lt_of_le_of_lt (hrs k hk hrk) (lt_add_of_pos_right _ (mul_pos three_pos hΔ)))
      (Or.inl (by
        rw [hii, hti, hts]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by norm_num : (3 : Time) ≤ 4) hΔ.le)))
    unfold SA.resolutionTime
    split
    · rename_i hl
      exact absurd ⟨Hv, hHv, hHvr⟩ (SA.lookup_eq_none hl)
    · rename_i Hd' hl
      obtain ⟨hHd', hr'⟩ := SA.lookup_eq_some hl
      obtain rfl : Hd' = Hv := hΦ.coherent.1 hHd' hHv (hr'.trans hHvr.symm)
      split_ifs with hlt
      · omega
      · rw [← hHvr]
        exact max_lt (hstamp v hv) (lt_trans hbs (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)))
  have hFO : Anc (tr.HonestBlocks H) ℓp.frame.F O := Anc.mono hΦU (hΦ.rooted.2 O hOt)
  have hcase : (∃ m < s', OriginWithin tr H O m b) ∨
      ∃ x ∈ H, ∃ k CV, SA.OptimisticLockAt tr.projAC x k s' O CV := by
    obtain ⟨x, hx, k, m, CV, ⟨hR, hm⟩ | ⟨hOp, hm⟩⟩ := oldOrigin_iff.1 hO
    · refine Or.inl ⟨m, by omega, originWithin_iff.2 ⟨x, hx, k, CV, ?_, Or.inl hR⟩⟩
      obtain ⟨ℓ, hu, _⟩ := hR
      have ht : tr.time k = sp.ts m + 6 * sp.Δ := hu.2.2.1
      have hm' : (m : Int) + 2 ≤ s' + 1 := by exact_mod_cast hm
      rw [hts] at hti
      simp only [SAParams.ts] at ht hti
      linarith only [ht, hti, hb, hΔ, mul_le_mul_of_nonneg_left hm' (SA.four_delta_pos sp).le]
    rcases Nat.lt_or_ge m s' with hm' | hm'
    · refine Or.inl ⟨m, hm', originWithin_iff.2 ⟨x, hx, k, CV, ?_, Or.inr hOp⟩⟩
      obtain ⟨ℓ, A, _, hs, _⟩ := hOp
      change sp.slot (tr.time k) = m at hs
      have ht : tr.time k < sp.ts (s' + 1 : Nat) := by
        by_contra ht
        have hh := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) ((s' + 1 : Nat) : Int)).1
          (le_of_not_gt ht)
        rw [hs] at hh
        omega
      exact ht.le.trans (hti ▸ hb)
    obtain rfl : s' = m := by omega
    exact Or.inr ⟨x, hx, k, CV, hOp⟩
  rcases hcase with ⟨m, hml, hOm⟩ | ⟨x, hx, k, CV, hOp⟩
  · -- an origin of label below `s − 1`: every honest slot-`(s−1)` vote extends it
    refine SA.isBest_of_majority hΦ hsub (fun B hB => hB.1)
      (SX := {w | w ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC w j e ∧ e.msg.slot = s'})
      (VX := {w | w ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC w j e ∧ e.msg.slot = s'} ∪ Hᶜ) ?_ ?_ ?_
      hCx hpar hCxO
    · rintro w ⟨hw, j, e, hv, hes⟩
      have hjb : tr.time j ≤ b := by
        obtain ⟨ℓ, hc, he⟩ := hv
        have ht := (cast_head_fcRoot hr hw ⟨hc, he⟩).2
        rw [hes] at ht
        change tr.time j ≤ sp.ts s' + sp.Δ at ht
        rw [hti, hts] at hb
        linarith only [ht, hb, hΔ]
      obtain ⟨Hd, hHd, hHdr, hOHd⟩ := hinv.vote_extends O m hOm w hw j e hv hjb (by omega)
      obtain ⟨hHdt, hacc, hHds⟩ := proposer_accepts_head_before hrun hnc hac hp hc hcall hd hti hb
        hw hv (by omega) hHd hHdr (hFO.trans hOHd)
      obtain ⟨ℓw, hcw, hew⟩ := hv
      have hvw : e.msg.val = w := (SA.castAt_spec hr hw ⟨hcw, hew⟩).1
      have hjt := (cast_head_fcRoot hr hw ⟨hcw, hew⟩).2
      have hj1 : sp.ts (s' : Int) ≤ tr.projAC.time j := by
        rw [← hes, (SA.castAt_spec hr hw ⟨hcw, hew⟩).2.1]
        exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 le_rfl
      have hvp : e.msg ∈ A.pool s' := by
        rcases hfwd w hw j e.msg ⟨ℓw, hcw, Or.inl ⟨e, hew, rfl⟩⟩ hes hj1
          (by rw [hes] at hjt; linarith only [hjt, hΔ]) with h | h
        · exact h
        · exact absurd (hvw ▸ h) (hnoeq w hw)
      refine ⟨fun h => hnoeq w hw (by
          obtain ⟨v₁, hv₁, v₂, hv₂, hne, h1, h2⟩ := h
          exact ⟨v₁, (hvotes' v₁).1 hv₁, v₂, (hvotes' v₂).1 hv₂, hne, h1, h2⟩),
        e.msg, hres e.msg hvp Hd hHdt hHdr hHds (by rw [← hσ]; exact hacc), hvw, by rw [hes],
        Hd, hHdt, hHdr, SA.anc_tree_of_anc_U hU hΦ hΦU hOt hOHd hHdt⟩
    · rintro w ⟨v, hv, rfl⟩
      by_cases hw : v.val ∈ H
      · obtain ⟨j, -, e, hve, rfl⟩ := hrun'.honest.pool_vote p hp i s' v ((hvotes' v).1 hv) hw
        exact Or.inl ⟨hw, j, e, hve, SA.state_pool_slot sp hr hp i s' _ ((hvotes' _).1 hv)⟩
      · exact Or.inr hw
    · have hcount : Hᶜ.ncard <
          {w | w ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC w j e ∧ e.msg.slot = s'}.ncard := by
        have hfault := hfb s' sp.Δ (by simp) (by rw [hti, hts] at hb; linarith only [hb, hΔ])
        change Hᶜ.ncard <
          {w | w ∈ H ∧ tr.awake w (sp.ts s' + sp.Δ) ∧ tr.JoinedAt w (sp.ts s' + sp.Δ)}.ncard
          at hfault
        refine hfault.trans_le (Set.ncard_le_ncard ?_)
        rintro w ⟨hw, hawake, hjoined⟩
        obtain ⟨j, e, hv, hs, _⟩ :=
          vote_of_awake_joined hrun hnc hw (mayVote_stock hrun hnc hw _) hawake hjoined
        exact ⟨hw, j, e, hv, hs⟩
      have := Set.ncard_union_le {w | w ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC w j e ∧ e.msg.slot = s'}
        Hᶜ
      omega
  · -- an optimistic origin of label `s − 1`: its counted votes
    have hW := optimistic_writer_votes hr hx hOp
    obtain ⟨ℓx, Ax, hpt, hslx, hsel, rfl⟩ := hOp
    have hsel' := hsel
    unfold SA.optimisticSelect at hsel'
    dsimp only at hsel'
    split_ifs at hsel'
    have h34 := (SA.deepest_mem hsel').1.2.1
    rw [hslx] at h34
    have hΦxU := (SA.frameIn_of_callAt hr hx hpt.1).2
    refine SA.isBest_of_cover hΦ hsub (fun B hB => hB.1) (SX := SA.optimisticVoters sp Ax ℓx.frame
      s' O) ?_ ?_ hCx hpar hCxO
    · rintro u ⟨v, hvA, rfl, R, hR, hRr, hOR⟩
      obtain ⟨hvs, ⟨kx, hsend, hk1, hk2⟩, Hv, hHv, hHvr, hOHv, hacc⟩ :=
        hW v ⟨hvA, R, hR, hRr, hOR⟩
      have hRHv : R = Hv := hU.1 (hΦxU hR) hHv (hRr.trans hHvr.symm)
      rw [← hRHv] at hHv hOHv hacc
      by_cases heq : v.val ∈ SA.equivocators (SA.View.ofLists pay).votes
      · exact Or.inr heq
      left
      rcases hfwd x hx kx v hsend hvs hk1 hk2 with hvp | ⟨a₁, ha₁, a₂, ha₂, hne, h1, h2⟩
      swap
      · exact absurd ⟨a₁, (hvotes' a₁).2 ha₁, a₂, (hvotes' a₂).2 ha₂, hne, h1, h2⟩ heq
      obtain ⟨hRt, hacc'⟩ := proposer_relay_before hrun hnc hac hp hc hcall hd hti hb hx hHv
        (by rw [hσ]; exact hacc) (hFO.trans hOHv)
      have hRs : R.slot ≤ v.slot := by
        rw [hvs, ← hslx]
        exact SA.frame_slot_le sp hr hx hpt.1 R hR
      exact ⟨heq, v, hres v hvp R hRt hRr hRs (by rw [← hσ]; exact hacc'), rfl,
        by rw [hvs], R, hRt, hRr, SA.anc_tree_of_anc_U hU hΦ hΦU hOt hOHv hRt⟩
    · have hle : (SA.voters (SA.View.ofLists pay).votes \ SA.optimisticVoters sp Ax ℓx.frame s'
          O).ncard + (SA.optimisticVoters sp Ax ℓx.frame s' O).ncard ≤ sp.n := by
        rw [← Set.ncard_union_eq Set.disjoint_sdiff_left]
        exact (Set.ncard_le_ncard (Set.subset_univ _)).trans (by simp)
      have := Set.ncard_le_ncard hequiv (Set.toFinite _)
      have hstock := hrun.stock
      omega

set_option linter.unusedVariables false in
/-- **The proposer's honest attestations have sources below old origins**: every
honest attestation the proposer holds was signed before cut `i`, with a source below an origin
before the signing (`attestation_source`); a regular one of label `l` is written at
`t_l + 6Δ ≤ t_s`, so `l ≤ s − 2`; an optimistic one has label at most `s`, and not `s`
(`proposal_no_optimistic`). -/
theorem proposal_rows_old_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    HonestRowsSourced tr H
      (fun D => ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) D O) p i := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ := sp.toParams.hΔ
  refine honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmi, -, k', hkm, hsg⟩ := honest_row_signed_before hrun hnc hp hX ha hav
  obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  refine ⟨D, ⟨C, ?_, hDC⟩, hDs⟩
  have hii : tr.projAC.time i = tr.time i := rfl
  obtain ⟨z, hz, c, hck, CV, hR | hOp⟩ := originBefore_iff.1 hC
  · refine oldOrigin_iff.2 ⟨z, hz, c, l, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
    obtain ⟨-, ⟨-, -, htc, -⟩, -⟩ := hR
    have := hr.time_mono (show c ≤ i by omega)
    linarith only [htc, this, hii, hti, hΔ]
  · refine oldOrigin_iff.2 ⟨z, hz, c, l, CV, Or.inr ⟨hOp, ?_⟩⟩
    obtain ⟨-, -, -, hsc, -⟩ := id hOp
    have hle := SA.slot_mono sp (hr.time_nonneg c) (hr.time_mono (show c ≤ i by omega))
    have hsi : sp.slot (tr.projAC.time i) = s := by
      rw [hii, hti]
      simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
    rcases Nat.lt_or_ge l s with h | h
    · omega
    obtain rfl : l = s := by omega
    exact absurd hOp
      (proposal_no_optimistic_of hrun hnc hf hp hc hcall hti z hz c (by omega) C CV)
/-- **The proposer's `fc_root` is below an old origin, or genesis**
(`F ≤ fc_root ≤ D_s` at the proposal read), from the sources of its honest attestations
(`proposal_rows_old_of`). -/
theorem proposal_fcRoot_old_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    ℓp.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot O := by
  rw [frame_of_projAC hrun hp hc]
  exact fcRoot_of_rows_of hrun hnc hf hp
    (fun _ _ hAB ⟨O, hO, hBO⟩ => ⟨O, hO, hAB.trans hBO⟩)
    (proposal_rows_old_of hrun hnc hf hp hc hcall hd hti)
/-- A live lock block of the proposal's anchor sits below an origin, of the slot of a stored
lock, before the proposal (`lock_origin`; unlocking and `live_locks` only move locks back). -/
theorem proposal_lock_below (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {i : Nat} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ tr.HonestBlocks H) {t : Time} {σ : Int}
    {V : SA.View sp.n} {A₁ : SA.SAState sp.n}
    (hA₁ : A₁.locks = SA.unlock sp (tr.projAC.state p i).locks Φ t σ V) :
    ∀ L ∈ SA.liveLockBlocks sp A₁.locks Φ t, ∃ l ∈ (tr.state p i).ac.locks, ∃ O,
      OriginBefore tr H O l.slot i ∧ Anc (tr.HonestBlocks H) L O := by
  have hU := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  rintro L ⟨hL, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hlL⟩
  obtain rfl : L = Φ.viableAncestor B :=
    hΦ.coherent.1 hL (SA.viableAncestor_anc hΦ hB).1 hlL.symm
  rw [hA₁] at hl
  obtain ⟨l₁, hl₁, -, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hB'B₁⟩ :=
    ((SA.locks_move_back sp) _ Φ _ t hΦ).2.2 σ V l hl
  obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
  rw [projAC_state hrun.toLocalRun hp i] at hl₁
  obtain ⟨L₁, hL₁, hL₁r, O, hO, hL₁O⟩ := lock_origin hrun hnc hp i l₁ hl₁
  obtain rfl : L₁ = B₁ := hU.1 ⟨p, hp, i, hL₁⟩ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
  exact ⟨l₁, hl₁, O, hO,
    (Anc.mono hΦU ((SA.anc_viableAncestor Φ _).trans hB'B₁)).trans hL₁O⟩
/-- **The proposal's anchor is below an old origin, or genesis** ("both
unlocked anchors are `≤ D_s`"): a live lock block sits below an origin before `t_s` of a slot
below `s` (`proposal_locks_slot_of`), which is old (a regular origin of label `s − 1` is written at
`t_s + 2Δ`); `fc_root` by `proposal_fcRoot_old_of`. -/
theorem proposal_anchor_old_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hfault : 2 * Hᶜ.ncard < sp.n)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    d.start.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) d.start O := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨A₁, hA₁, hst, -⟩ := acProposal_walk hd
  rw [hst]
  rcases anchor_mem ℓp.frame A₁ (tr.time i) with hL | hf
  · right
    obtain ⟨l, hl, O, hO, hLO⟩ := proposal_lock_below hrun hnc hp hΦ hΦU hA₁ _ hL
    have hls := proposal_locks_slot_of hrun hnc hfault hp hc hcall hd hti l hl
    refine ⟨O, ?_, hLO⟩
    obtain ⟨x, hx, k', hki, CV, hR | hOp⟩ := originBefore_iff.1 hO
    · refine oldOrigin_iff.2 ⟨x, hx, k', l.slot, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
      obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
      have := hr.time_mono hki.le
      have hii : tr.projAC.time i = tr.time i := rfl
      linarith only [htk, this, hii, hti, sp.toParams.hΔ]
    · exact oldOrigin_iff.2 ⟨x, hx, k', l.slot, CV, Or.inr ⟨hOp, by omega⟩⟩
  · rw [Set.mem_singleton_iff.1 hf]
    exact proposal_fcRoot_old_of hrun hnc hfault hp hc hcall hd hti
/-- **A voter's anchor is below `D`, or on `P`'s chain above `D`**: for a block `D` above every
old origin and below `Q = P.parent`, at an honest slot-`s` vote whose earlier honest slot-`s`
votes are `P`. -/
theorem vote_anchor_cases_of_old (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P Q D : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hs0 : 0 < s) (hPQ : P.parent = some Q.root) (hQU : Q ∈ tr.HonestBlocks H)
    (hDQ : Anc (tr.HonestBlocks H) D Q) (hDU : D ∈ tr.HonestBlocks H)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O D)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root) :
    Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocks H) D (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
        Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
        P ∈ tr.HonestBlocks H) := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hslj : e.msg.slot = sp.slot (tr.time j) := (SA.castAt_spec hr hy hcy).2.1
  have htj : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot hr hy hcy).2
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have haS := anchor_mem ℓy.frame e.readPoint (tr.time j)
  generalize SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = a at hat haS ⊢
  rcases haS with ⟨-, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hl'r⟩ | haf
  swap
  · -- `fc_root` is below an old origin, or genesis
    left
    rw [Set.mem_singleton_iff.1 haf]
    rcases vote_fcRoot_old_of hrun hnc hf hs0 hy hcy hes with hg | ⟨O, hO, hfO⟩
    · exact honest_genesis_root_anc hrun hU (hΦU hΦ.fcRoot_mem) hg hDU
    · exact hfO.trans (hDold O hO)
  -- a live lock block: the viable ancestor of the block of a read-point lock
  obtain rfl : a = ℓy.frame.viableAncestor B :=
    hΦ.coherent.1 hat (SA.viableAncestor_anc hΦ hB).1 hl'r.symm
  have haB : Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor B) B :=
    Anc.mono hΦU (SA.anc_viableAncestor _ B)
  by_cases hls : l.slot = s
  · -- a lock of slot `s`: below an optimistic selection with an honest earlier supporter
    obtain ⟨Φ', A', D', -, hΦ'U, -, h34, hpool, -, L, hLU, hLr, hLD'⟩ :=
      SA.lock_origin_readPoint hrun' hy hcy l hl (by rw [hes, hls]; omega)
    rw [hrun'.stock] at h34
    obtain rfl : L = B := hU.1 hLU (hΦU hB) (hLr.trans hBr.symm)
    obtain ⟨x, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A' Φ' l.slot D') (by omega)
    have hvH : v.val ∈ H := not_not.1 hxH
    obtain ⟨hvs, j', hj', e', hv', rfl⟩ := hpool v hv hvH
    have hRP : R = P := honest_eq_proposal_of_root hrun hnc hp hP (hΦ'U hR)
      (hRr.trans (hE _ hvH j' hj' e' hv' (hvs.trans hls)))
    rw [hRP] at hR hDR
    have hPU : P ∈ tr.HonestBlocks H := hΦ'U hR
    have haP := haB.trans (hLD'.trans (Anc.mono hΦ'U hDR))
    have hDP : Anc (tr.HonestBlocks H) D P :=
      hDQ.trans (Relation.ReflTransGen.single ⟨hQU, hPU, hPQ⟩)
    rcases Anc.total hU haP hDP with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haP, hPU⟩
  · -- a lock of another slot: below a stored lock, below an old origin
    left
    obtain ⟨l₁, hl₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hB'B₁⟩ :=
      SA.readPoint_locks_below_stored hr hy hcy (hslj ▸ hes ▸ hs0) l hl
        (by change l.slot ≠ sp.slot (tr.time j); rw [← hslj, hes]; exact hls)
    obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
    rw [projAC_state hrun.toLocalRun hy j] at hl₁
    obtain ⟨L₁, hL₁, hL₁r, O, hO, hL₁O⟩ := lock_origin hrun hnc hy j l₁ hl₁
    obtain rfl : L₁ = B₁ := hU.1 ⟨y, hy, j, hL₁⟩ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
    have hOld : OldOrigin tr H s O := by
      obtain ⟨x, hx, k', hkj, CV, hR | hOp⟩ := originBefore_iff.1 hO
      · refine oldOrigin_iff.2 ⟨x, hx, k', l₁.slot, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
        obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
        have := hr.time_mono hkj.le
        have hjj : tr.projAC.time j = tr.time j := rfl
        linarith only [htk, this, hjj, htj]
      · refine oldOrigin_iff.2 ⟨x, hx, k', l₁.slot, CV, Or.inr ⟨hOp, ?_⟩⟩
        obtain ⟨-, -, -, hsk, -⟩ := hOp
        have := SA.slot_mono sp (hr.time_nonneg k') (hr.time_mono hkj.le)
        have hjj : sp.slot (tr.projAC.time j) = sp.slot (tr.time j) := rfl
        omega
    exact (haB.trans (Anc.mono hΦU hB'B₁)).trans (hL₁O.trans (hDold O hOld))
/-- **The proposal walk from `D` to `Q` is through viable heads** (at `t_s`,
`F ⪯ fc_root ⪯ D_s` and the head height floor is at most `ht(D_s)`, heights increase along the
path), for `D` above every old origin. `fc_root` is genesis or below an old origin
(`proposal_fcRoot_old_of`), so below `D ⪯ X`. The proposer's honest attestations have sources below
old origins, hence below `D` and pairwise compatible (`proposal_rows_old_of`), so with no contest
the floor is reached by `X`, or a crossing entry `E ⪰ X` of the floor's height is below its source,
below `D ⪯ X`, and `E = X` (`floor_or_crossing`). -/
theorem proposal_suffix_viable_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {D : SA.Blk sp.n (List (FG.Att sp.n))} (hDt : D ∈ ℓp.frame.tree)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O D) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads := by
  intro X hDX _
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  have hXt : X ∈ ℓp.frame.tree := mem_of_anc_left hDX hDt
  have hDXU : Anc (tr.HonestBlocks H) D X := Anc.mono hΦU hDX
  -- `fc_root` is genesis or below an old origin, below `D`
  have hfX : ℓp.frame.Anc ℓp.frame.fcRoot X := by
    refine SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem ?_ hXt
    rcases proposal_fcRoot_old_of hrun hnc hf hp hc hcall hd hti with hg | ⟨O, hO, hfO⟩
    · exact honest_genesis_root_anc hrun hU (hΦU hΦ.fcRoot_mem) hg (hΦU hXt)
    · exact (hfO.trans (hDold O hO)).trans hDXU
  -- the sources of the proposer's honest attestations are below old origins, below `D ⪯ X`
  have hsrc := proposal_rows_old_of hrun hnc hf hp hc hcall hd hti
  rw [frame_of_projAC hrun hp hc] at hXt hfX ⊢
  obtain ⟨hXs, hFX⟩ := hXt
  refine ⟨hXs, hFX, Anc.mono (fun _ h => h.1) hfX, ?_⟩
  rcases floor_or_crossing_scoped hrun hnc hf hp
      (fun X hX a ha hav _ => honestRowsSourced_iff.1 hsrc X hX a ha hav)
      (fun D₁ D₂ ⟨O₁, hO₁, h₁⟩ ⟨O₂, hO₂, h₂⟩ =>
        Anc.total hU (h₁.trans (hDold O₁ hO₁)) (h₂.trans (hDold O₂ hO₂)))
      (fun D' ⟨O, hO, h⟩ => Or.inl ((h.trans (hDold O hO)).trans hDXU)) hXs with
    hle | ⟨D', E, -, ⟨O, hO, hD'O⟩, hD's, hE, hXE, hEh, -⟩
  · exact hle
  -- a crossing entry `E ⪰ X` is below its source, below `D ⪯ X`: `E = X`
  obtain ⟨x, hx, k', -, -, hED', -, -⟩ := honest_source_entry hrun hnc hD's ⟨p, hp, i, hE⟩ rfl
  obtain rfl : X = E := Anc.antisymm hU
    (Anc.mono (T := tr.HonestBlocks H) (fun _ h => ⟨p, hp, i, h⟩) hXE)
    (((Anc.mono (T := tr.HonestBlocks H) (fun _ h => ⟨x, hx, k', h⟩) hED').trans hD'O).trans
      ((hDold O hO).trans hDXU))
  exact hEh.ge
end Consensus.Goldilocks.Compose

end
