module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
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
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.ProposalCall
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the steps of the pivot of an honest proposal

The steps of the growing-fault pivot (`Growing/Sleepy/Service/PivotWalk`): the proposal's rows,
`fc_root` and locks below the old origins (`proposal_rows_old_of`, `proposal_fcRoot_old_of`,
`proposal_lock_below`), its anchor (`proposal_anchor_old_of`), a voter's anchor cases
(`vote_anchor_cases_of_old`, with `honest_eq_proposal_of_root`), and the viability of the suffix
(`proposal_suffix_viable_of`). -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ### Over a run -/

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- Blocks with the same fields are equal. -/
theorem blk_eq_of_fields {X Y : AC.Blk sp.n (List (FG.Att sp.n))} (h0 : X.root = Y.root)
    (h1 : X.parent = Y.parent) (h2 : X.slot = Y.slot) (h3 : X.proposer = Y.proposer)
    (h4 : X.input = Y.input) (h5 : X.fgPayload = Y.fgPayload) (h6 : X.acPayload = Y.acPayload) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-- **An honest block with the root of an honest proposal is that proposal** (`NoColl`): both
roots are digests, of an occurring block, and the slot's proposer made both. -/
theorem honest_eq_proposal_of_root {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ tr.HonestBlocks H) (hr : R.root = P.root) : R = P := by
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, hpp, -⟩ := hP
  rcases blockCall_cases hrun.toLocalRun hp hcB with hg |
    ⟨j, x, fgDue, rfl, -, hPr, d, pay, -, hB, -⟩
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
set_option linter.unusedVariables false in
/-- **The proposer's honest attestations have sources below old origins**: every
honest attestation the proposer holds was signed before cut `i`, with a source below an origin
before the signing (`attestation_source`); a regular one of label `l` is written at
`t_l + 6Δ ≤ t_s`, so `l ≤ s − 2`; an optimistic one has label at most `s`, and not `s`
(`proposal_no_optimistic_of`). -/
theorem proposal_rows_old_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {K : AC.CommitteeDict sp.n}
    (hP : AC.CommitteeP K tr.projAC H)
    (hfK : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) :
    HonestRowsSourced tr H
      (fun D => ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) D O) p i := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
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
    have hle := AC.slot_mono sp (hr.time_nonneg c) (hr.time_mono (show c ≤ i by omega))
    have hsi : sp.slot (tr.projAC.time i) = s := by
      rw [hii, hti]
      simpa using (AC.slot_arithmetic sp s).1 0 (by omega)
    rcases Nat.lt_or_ge l s with h | h
    · omega
    obtain rfl : l = s := by omega
    exact absurd hOp
      (proposal_no_optimistic_of hrun hnc hP hfK hp hc hcall hti z hz c (by omega) C CV)
/-- **The proposer's `fc_root` is below an old origin, or genesis**
(`F ≤ fc_root ≤ D_s` at the proposal read), from the sources of its honest attestations
(`proposal_rows_old_of`). -/
theorem proposal_fcRoot_old_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {K : AC.CommitteeDict sp.n}
    (hP : AC.CommitteeP K tr.projAC H)
    (hfK : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) :
    ℓp.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot O := by
  rw [frame_of_projAC hrun hp hc]
  exact fcRoot_of_rows_of hrun hnc hf hp
    (fun _ _ hAB ⟨O, hO, hBO⟩ => ⟨O, hO, hAB.trans hBO⟩)
    (proposal_rows_old_of hrun hnc hp hc hcall hd hti hP hfK)
/-- A live lock block of the proposal's anchor sits below an origin, of the slot of a stored
lock, before the proposal (`lock_origin`; unlocking and `live_locks` only move locks back). -/
theorem proposal_lock_below {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {i : Nat} {Φ : AC.Frm sp.n (List (FG.Att sp.n))}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ tr.HonestBlocks H) {t : Time} {σ : Int}
    {V : AC.View sp.n} {A₁ : AC.ACState sp.n}
    (hA₁ : A₁.locks = AC.unlock sp (tr.projAC.state p i).locks Φ t σ V) :
    ∀ L ∈ AC.liveLockBlocks sp A₁.locks Φ t, ∃ l ∈ (tr.state p i).ac.locks, ∃ O,
      OriginBefore tr H O l.slot i ∧ Anc (tr.HonestBlocks H) L O := by
  have hU := (goldilocks_ac_projection_from hrun hnc).localRun.coherent
  rintro L ⟨hL, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hlL⟩
  obtain rfl : L = Φ.viableAncestor B :=
    hΦ.coherent.1 hL (AC.viableAncestor_anc hΦ hB).1 hlL.symm
  rw [hA₁] at hl
  obtain ⟨l₁, hl₁, -, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hB'B₁⟩ :=
    ((AC.locks_move_back sp) _ Φ _ t hΦ).2.2 σ V l hl
  obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
  rw [projAC_state hrun.toLocalRun hp i] at hl₁
  obtain ⟨L₁, hL₁, hL₁r, O, hO, hL₁O⟩ := lock_origin hrun hnc hp i l₁ hl₁
  obtain rfl : L₁ = B₁ := hU.1 ⟨p, hp, i, hL₁⟩ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
  exact ⟨l₁, hl₁, O, hO,
    (Anc.mono hΦU ((AC.anc_viableAncestor Φ _).trans hB'B₁)).trans hL₁O⟩
/-- **The proposal's anchor is below an old origin, or genesis** ("both
unlocked anchors are `≤ D_s`"): a live lock block sits below an origin before `t_s` of a slot
below `s` (`proposal_locks_slot_of`), which is old (a regular origin of label `s − 1` is written at
`t_s + 2Δ`); `fc_root` by `proposal_fcRoot_old_of`. -/
theorem proposal_anchor_old_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hfault : 2 * Hᶜ.ncard < sp.n)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {K : AC.CommitteeDict sp.n}
    (hP : AC.CommitteeP K tr.projAC H)
    (hfK : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) :
    d.start.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) d.start O := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr hp hc
  obtain ⟨A₁, hA₁, hst, -⟩ := acProposal_walk hd
  rw [hst]
  rcases anchor_mem ℓp.frame A₁ (tr.time i) with hL | hf
  · right
    obtain ⟨l, hl, O, hO, hLO⟩ := proposal_lock_below hrun hnc hp hΦ hΦU hA₁ _ hL
    refine ⟨O, ?_, hLO⟩
    obtain ⟨x, hx, k', hki, CV, hR | hOp⟩ := originBefore_iff.1 hO
    · refine oldOrigin_iff.2 ⟨x, hx, k', l.slot, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
      obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
      have := hr.time_mono hki.le
      have hii : tr.projAC.time i = tr.time i := rfl
      linarith only [htk, this, hii, hti, sp.toParams.hΔ]
    · have hls := proposal_locks_slot_of hrun hnc hp hc hcall hd hti hP hfK l hl
      exact oldOrigin_iff.2 ⟨x, hx, k', l.slot, CV, Or.inr ⟨hOp, hls⟩⟩
  · rw [Set.mem_singleton_iff.1 hf]
    exact proposal_fcRoot_old_of hrun hnc hfault hp hc hcall hd hti hP hfK
/-- **A voter's anchor is below `D`, or on `P`'s chain above `D`**: for a block `D` above every
old origin and below `Q = P.parent`, at an honest slot-`s` vote whose earlier honest slot-`s`
votes are `P`. -/
theorem vote_anchor_cases_of_old {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P Q D : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hs0 : 0 < s) (hPQ : P.parent = some Q.root) (hQU : Q ∈ tr.HonestBlocks H)
    (hDQ : Anc (tr.HonestBlocks H) D Q) (hDU : D ∈ tr.HonestBlocks H)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O D)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcy : AC.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', AC.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root)
    (K : AC.CommitteeDict sp.n) (hPK : AC.CommitteeP K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    (hfK : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) (hyK : y ∈ K.committee s) :
    Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocks H) D (AC.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
        Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
        P ∈ tr.HonestBlocks H) := by
  have hrun' := goldilocks_ac_projection_from hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr hy hcy.1
  have hslj : e.msg.slot = sp.slot (tr.time j) := (AC.castAt_specU hr.toU hy hcy).2.1
  have htj : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot hr hrun.vstart hy hcy).2
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have haS := anchor_mem ℓy.frame e.readPoint (tr.time j)
  generalize AC.getAnchor sp e.readPoint ℓy.frame (tr.time j) = a at hat haS ⊢
  rcases haS with ⟨-, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hl'r⟩ | haf
  swap
  · -- `fc_root` is below an old origin, or genesis
    left
    rw [Set.mem_singleton_iff.1 haf]
    rcases vote_fcRoot_old_of hrun hnc hf hs0 hy hcy hes K hPK hsize hfK hyK with hg | ⟨O, hO, hfO⟩
    · exact honest_genesis_root_anc hrun hU (hΦU hΦ.fcRoot_mem) hg hDU
    · exact hfO.trans (hDold O hO)
  -- a live lock block: the viable ancestor of the block of a read-point lock
  obtain rfl : a = ℓy.frame.viableAncestor B :=
    hΦ.coherent.1 hat (AC.viableAncestor_anc hΦ hB).1 hl'r.symm
  have haB : Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor B) B :=
    Anc.mono hΦU (AC.anc_viableAncestor _ B)
  by_cases hls : l.slot = s
  · -- a lock of slot `s`: below an optimistic selection with an honest earlier supporter
    obtain ⟨Φ', A', D', -, hΦ'U, -, h34, hpool, ⟨c, -, hsub⟩, L, hLU, hLr, hLD'⟩ :=
      AC.lock_origin_readPoint hrun' hy hcy l hl (by rw [hes, hls]; omega)
    have hoptK : AC.optimisticVoters sp A' Φ' l.slot D' ⊆ K.committee s := by
      rintro u ⟨v, hv, rfl, -⟩
      exact hls ▸ hPK.1 y hy (c + 1) l.slot v (hsub hv)
    obtain rfl : L = B := hU.1 hLU (hΦU hB) (hLr.trans hBr.symm)
    obtain ⟨x, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := K.committee s ∩ Hᶜ)
        (t := AC.optimisticVoters sp A' Φ' l.slot D') (by omega)
    have hvH : v.val ∈ H := by
      by_contra hn
      exact hxH ⟨hoptK ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hn⟩
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
      AC.readPoint_locks_below_stored hr hy hcy (hslj ▸ hes ▸ hs0) l hl
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
        have := AC.slot_mono sp (hr.time_nonneg k') (hr.time_mono hkj.le)
        have hjj : sp.slot (tr.projAC.time j) = sp.slot (tr.time j) := rfl
        omega
    exact (haB.trans (Anc.mono hΦU hB'B₁)).trans (hL₁O.trans (hDold O hOld))
/-- **The proposal walk from `D` to `Q` is through viable heads**, for `D` above every old
origin. The proposer's honest row sources are below old origins (`proposal_rows_old_of`), hence
below `D ⪯ X`. Their justified entry is below `X`, and `X` reaches height `h_max − 1`: a crossing
entry above `X` at that height is also below its source, hence below `X`. These two facts give
P-U viability. -/
theorem proposal_suffix_viable_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {D : AC.Blk sp.n (List (FG.Att sp.n))} (hDt : D ∈ ℓp.frame.tree)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O D)
    {K : AC.CommitteeDict sp.n} (hP : AC.CommitteeP K tr.projAC H)
    (hfK : 2 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads := by
  intro X hDX _
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr hp hc
  have hXt : X ∈ ℓp.frame.tree := mem_of_anc_left hDX hDt
  have hDXU : Anc (tr.HonestBlocks H) D X := Anc.mono hΦU hDX
  -- `fc_root` is genesis or below an old origin, below `D`
  have hfX : ℓp.frame.Anc ℓp.frame.fcRoot X := by
    refine AC.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem ?_ hXt
    rcases proposal_fcRoot_old_of hrun hnc hf hp hc hcall hd hti hP hfK with hg | ⟨O, hO, hfO⟩
    · exact honest_genesis_root_anc hrun hU (hΦU hΦ.fcRoot_mem) hg (hΦU hXt)
    · exact (hfO.trans (hDold O hO)).trans hDXU
  -- the sources of the proposer's honest attestations are below old origins, below `D ⪯ X`
  have hsrc := proposal_rows_old_of hrun hnc hp hc hcall hd hti hP hfK
  rw [frame_of_projAC hrun hp hc] at hXt hfX ⊢
  obtain ⟨hXs, hFX⟩ := hXt
  refine ⟨hXs, hFX, ?_⟩
  have hJX : (tr.state p i).fg.Anc (tr.state p i).fg.J X := by
    rcases justified_of_rows_of hrun hnc hf hp
      (R := fun Y => Anc (tr.HonestBlocks H) Y X)
      (fun _ _ hAB hBX => hAB.trans hBX)
      (honestRowsSourced_iff.2 fun B hB a ha hav => by
        obtain ⟨D', ⟨O, hO, hD'O⟩, hDs⟩ := honestRowsSourced_iff.1 hsrc B hB a ha hav
        exact ⟨D', (hD'O.trans (hDold O hO)).trans hDXU, hDs⟩) with hg | hJX
    · have hJt := (Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hp i)).2.1
      rw [honest_eq_genesis hrun hU ⟨p, hp, i, hJt⟩ hg]
      exact (Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hp i)).2.2.2 X hXs
    · exact honest_held_anc hrun hnc hp hJX hXs
  suffices hh : (tr.state p i).fg.hmax - 1 ≤ ((tr.state p i).fg.σ X.root).h by
    change _ ∨ (_ ∧ _)
    by_cases hm : (tr.state p i).fg.hmax ≤ ((tr.state p i).fg.σ X.root).h
    · exact Or.inl hm
    · exact Or.inr ⟨by omega, Or.inr hJX⟩
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
