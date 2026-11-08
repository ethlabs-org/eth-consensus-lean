module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.PivotOld
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
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
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the pivot of a proposal

The σ-copy of the second half of `Compose/Service/Pivot`: the proposal walk passes every old
origin (`proposal_walk_passes_old_at`), and the pivot `D` of a proposal (`pivot_at`). The
proposer is honest at `t_s + Δ` (the hold), so at its proposal and at every slot-`s` vote, which is
cast by `t_s + Δ`; a voter is honest at its vote.

**Class L′ (copied static helper, lifted).** The private helpers of `Compose/Service/Pivot` whose
nodes are honest at one time are copied verbatim, in their static form, and applied to the prefix
through that time: the proposal's anchor and suffix at `d = t_s` (`proposal_anchor_old_of`,
`proposal_suffix_viable_of`, with `proposal_rows_old_of`, `proposal_fcRoot_old_of`,
`proposal_lock_below`), and a voter's anchor at the vote's time (`vote_anchor_cases`, with
`eq_proposal`), where the proposer is honest by the hold. Their old origins are origins of the
prefix, so old origins of the run (`oldOrigin_of_upTo`). When the static helpers are made public,
the post-swap pass deletes these copies. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Blocks with the same fields are equal. -/
private theorem block_eq {X Y : SA.Blk sp.n (List (FG.Att sp.n))} (h0 : X.root = Y.root)
    (h1 : X.parent = Y.parent) (h2 : X.slot = Y.slot) (h3 : X.proposer = Y.proposer)
    (h4 : X.input = Y.input) (h5 : X.fgPayload = Y.fgPayload) (h6 : X.acPayload = Y.acPayload) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-- **An honest block with the root of an honest proposal is that proposal** (`NoColl`): both
roots are digests, of an occurring block, and the slot's proposer made both. -/
private theorem eq_proposal (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
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
  exact block_eq hr h1 h2 (by rw [hRpr, hpr, h2]) h3 h4 h5


set_option linter.unusedVariables false in
/-- **The proposer's honest attestations have sources below old origins**: every
honest attestation the proposer holds was signed before cut `i`, with a source below an origin
before the signing (`attestation_source`); a regular one of label `l` is written at
`t_l + 6Δ ≤ t_s`, so `l ≤ s − 2`; an optimistic one has label at most `s`, and not `s`
(`proposal_no_optimistic`). -/
private theorem proposal_rows_old_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
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
private theorem proposal_fcRoot_old_of (hrun : GoldilocksRun proposer dg H tr)
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
private theorem proposal_lock_below (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
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
private theorem proposal_anchor_old_of (hrun : GoldilocksRun proposer dg H tr)
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
private theorem vote_anchor_cases (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
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
    obtain rfl : L = B := hU.1 hLU (hΦU hB) (hLr.trans hBr.symm)
    obtain ⟨x, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A' Φ' l.slot D') (by omega)
    have hvH : v.val ∈ H := not_not.1 hxH
    obtain ⟨hvs, j', hj', e', hv', rfl⟩ := hpool v hv hvH
    have hRP : R = P := eq_proposal hrun hnc hp hP (hΦ'U hR)
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
private theorem proposal_suffix_viable_of (hrun : GoldilocksRun proposer dg H tr)
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


namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- An old origin of the prefix through `d` is an old origin of the run. -/
theorem oldOrigin_of_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) {d : Time} {s : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (h : Compose.OldOrigin (tr.upTo d) (H d) s O) :
    OldOrigin tr H s O := by
  obtain ⟨x, hx, k, m, CV, ⟨hR, hm⟩ | ⟨hO, hm⟩⟩ := Compose.oldOrigin_iff.1 h
  · rw [RunTrace.upTo_projAC] at hR
    obtain ⟨hkd, hR⟩ := (sa_resultAt_upTo hrun.time_mono).mp hR
    exact oldOrigin_iff.2 ⟨x, k, m, CV, hrun.antitone hkd hx, Or.inl ⟨hR, hm⟩⟩
  · rw [RunTrace.upTo_projAC] at hO
    obtain ⟨hkd, hO⟩ := (sa_optimisticLockAt_upTo hrun.time_mono).mp hO
    exact oldOrigin_iff.2 ⟨x, k, m, CV, hrun.antitone hkd hx, Or.inr ⟨hO, hm⟩⟩

/-- The proposal call and its duty head, read in the prefix through the call's time. -/
private theorem proposal_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) {p : Fin sp.n}
    {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hc : tr.projAC.CallAt p i ℓp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay)) :
    (tr.upTo (tr.time i)).projAC.CallAt p i ℓp ∧
      (SA.acProposal sp ((tr.upTo (tr.time i)).projAC.state p i) ℓp.frame (tr.time i)).2 =
        some (d, pay) := by
  rw [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl]
  exact ⟨(Trace.upTo_callAt_of_le _ le_rfl).mpr hc, hd⟩

/-- **The proposal's anchor is below an old origin, or genesis** (lifted at `t_s`). -/
theorem proposal_anchor_old_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} {s i : Nat} (hp : p ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    d.start.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocksAt H) d.start O := by
  have h0 := hrun.time_nonneg i
  obtain ⟨hc', hd'⟩ := proposal_upTo hrun hc hd
  rcases proposal_anchor_old_of (hrun.upTo h0) (hnc.upTo _) hf hp hc' hcall hd' hti with
    h | ⟨O, hO, hsO⟩
  · exact Or.inl h
  · exact Or.inr ⟨O, oldOrigin_of_upTo hrun hO, hsO.mono (upTo_subset hrun h0)⟩

/-- **The proposal walk from `D` to `Q` is through viable heads**, for `D` of the proposal's frame
above every old origin (lifted at `t_s`). -/
theorem proposal_suffix_viable_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} {s i : Nat} (hp : p ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {D : SA.Blk sp.n (List (FG.Att sp.n))} (hDt : D ∈ ℓp.frame.tree)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocksAt H) O D) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads := by
  have h0 := hrun.time_nonneg i
  obtain ⟨hc', hd'⟩ := proposal_upTo hrun hc hd
  exact proposal_suffix_viable_of (hrun.upTo h0) (hnc.upTo _) hf hp hc' hcall hd' hti hDt
    fun O hO => RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0
      (frame_upTo_at hrun hnc hp hc hDt) (hDold O (oldOrigin_of_upTo hrun hO))

/-- **A voter's anchor is below `D`, or on `P`'s chain above `D`** (lifted at the vote's time `d`,
with the proposer honest then): for a block `D` above every old origin and below `Q = P.parent`, at
a slot-`s` vote of a node honest then whose earlier slot-`s` votes by nodes honest at them are
`P`. -/
theorem vote_anchor_cases_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    (hf : 2 * (H (tr.time j))ᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H (tr.time j)) {k : Nat}
    {P Q D : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hkj : tr.time k ≤ tr.time j) (hs0 : 0 < s) (hPQ : P.parent = some Q.root)
    (hQU : Q ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)))
    (hDQ : Anc (tr.HonestBlocksAt H) D Q)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocksAt H) O D)
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)
    (hE : ∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s → e'.msg.head = P.root) :
    Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocksAt H) D (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
        Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
        P ∈ tr.HonestBlocksAt H) := by
  have h0 := hrun.time_nonneg j
  have hm := hrun.time_mono
  have hsub := upTo_subset hrun h0
  have hDQ' := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0 hQU hDQ
  have hDU : D ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
    by_cases h : D = Q
    · exact h ▸ hQU
    · exact (hDQ'.mem h).1
  have h := vote_anchor_cases (hrun.upTo h0) (hnc.upTo _) hf hp
    (k := k) (P := P) ⟨(RunTrace.upTo_ownBlockAt tr).mpr ⟨hkj, hP.1⟩, hP.2.1, hP.2.2⟩ hs0 hPQ hQU
    hDQ' hDU (fun O hO => RunTrace.anc_upTo_of_right hrun.toLocalRun hnc h0 hDU
      (hDold O (oldOrigin_of_upTo hrun hO))) hy
    (by rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hcy⟩) hes
    (fun x hx j' hj' e' hv hs => by
      rw [RunTrace.upTo_projAC] at hv
      obtain ⟨hjd, hv⟩ := sa_voteAt_upTo.mp hv
      exact hE x j' e' hj' (hVoteAt_iff.2 ⟨hrun.antitone hjd hx, hv⟩) hs)
  rcases h with h | ⟨h1, h2, h3⟩
  · exact Or.inl (h.mono hsub)
  · exact Or.inr ⟨h1.mono hsub, h2.mono hsub, hsub h3⟩

/-- A live lock block of the proposal's anchor sits below the proposer's own lock write of the
slot of a stored lock, written up to the proposal (`lock_write_at`; unlocking and `live_locks`
only move locks back). -/
theorem proposal_lock_below_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {p : Fin sp.n} {i : Nat} (hp : p ∈ H (tr.time i))
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ tr.HonestBlocksAt H)
    {t : Time} {σ : Int} {V : SA.View sp.n} {A₁ : SA.SAState sp.n}
    (hA₁ : A₁.locks = SA.unlock sp (tr.projAC.state p i).locks Φ t σ V) :
    ∀ L ∈ SA.liveLockBlocks sp A₁.locks Φ t, ∃ l ∈ (tr.state p i).ac.locks, ∃ D,
      LockWithin tr H D l.slot (tr.time i) ∧ Anc (tr.HonestBlocksAt H) L D := by
  have hU := honestBlocksAt_coherent hrun hnc
  rintro L ⟨hL, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hlL⟩
  obtain rfl : L = Φ.viableAncestor B :=
    hΦ.coherent.1 hL (SA.viableAncestor_anc hΦ hB).1 hlL.symm
  rw [hA₁] at hl
  obtain ⟨l₁, hl₁, -, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hB'B₁⟩ :=
    ((SA.locks_move_back sp) _ Φ _ t hΦ).2.2 σ V l hl
  obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
  rw [projAC_state_at hrun hp] at hl₁
  obtain ⟨L₁, hL₁, hL₁r, D, hD, hL₁D⟩ :=
    lock_write_at hrun hnc (hrun.time_nonneg i) (fun _ hk => hrun.time_mono hk.le) hp l₁ hl₁
  obtain rfl : L₁ = B₁ :=
    hU.1 (mem_honestBlocksAt hrun hp hL₁) (hΦU hB₁) (hL₁r.trans hB₁r.symm)
  exact ⟨l₁, hl₁, D, hD,
    (Anc.mono hΦU ((SA.anc_viableAncestor Φ _).trans hB'B₁)).trans hL₁D⟩

/-- **The proposal walk passes every old origin**: the origin is held by the proposer (or below
its `Σ.F`, below the walk's start), so viable or at or below `fc_root` (`held_origin_viable_at`,
`2 f_d < n` at `d = t_s`); the proposer's live locks sit below origins, compatible with it (S1);
and the children towards it win (`proposal_best_toward_old_at`, `SA.anc_getHead`). -/
theorem proposal_walk_passes_old_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {s i : Nat}
    (hp : p ∈ H (tr.time i))
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) :
    ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocksAt H) O d.head := by
  intro O hO
  have hU := honestBlocksAt_coherent hrun hnc
  have hf := hB.two _ (hrun.time_nonneg i) hb
  have hib : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hb
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hp hc
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦ hd
  obtain ⟨A₁, hA₁, -, hhd⟩ := acProposal_walk hd
  obtain ⟨m, _, hOm⟩ := hO.within hrun (hti ▸ hb)
  rcases proposal_holds_old_at hrun hnc hsync hB hinv hp hc hcall hd hti hb O hO with hOt | hOF
  swap
  · exact hOF.trans (Anc.mono hΦU ((hΦ.rooted.2 _ hstart).trans hsQ))
  have hfr := frame_of_projAC_at hrun hp hc
  have hviab := held_origin_viable_at hrun hnc hp hf
    (fun C l D n hC hD => hinv.origins_compatible C l D n (hC.mono hb) (hD.mono hb))
    (fun C m' hC => hinv.origins_compatible O m C m' hOm (hC.within hib)) (hfr ▸ hOt)
  rw [← hfr] at hviab
  have hsl_i : sp.slot (tr.time i) = s := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  have hbest := proposal_best_toward_old_at hrun hnc hsync hB hinv hp hc hcall hd hti hb O hO hOt
  rw [← hsl_i] at hbest
  rw [hhd]
  refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A₁ (tr.time i) _ _ (fun _ h => h)
    (fun B hB X hXB => SA.mem_of_anc hXB hB) hviab.symm ?_ hbest)
  intro L hL
  obtain ⟨l, -, D, hD, hLD⟩ := proposal_lock_below_at hrun hnc hp hΦ hΦU hA₁ L hL
  obtain ⟨O', hO', hDO'⟩ := hD.below_origin hrun hnc
  rcases hinv.origins_compatible O' l.slot O m (hO'.mono hb) hOm with h | h
  · exact Or.inl ((hLD.trans hDO').trans h)
  · exact SA.anc_total hU (hLD.trans hDO') h


/-- **The pivot** under growing faults. The proposer of slot `s` is honest at `t_s + Δ` (the
hold), so at its proposal and at every slot-`s` vote. For a voter honest at its vote, the earlier
slot-`s` votes by nodes honest at them are assumed to be `P` (the caller's strong induction on the
cut). -/
theorem pivot_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBoundsFrom tr H 0 b)
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) (hib : tr.time i ≤ b) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      (∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads) ∧
      ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → tr.time j ≤ b →
        e.msg.slot = s →
        (∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  have h0 := hrun.time_nonneg i
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by rw [hti]; linarith) hp
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := hB.two _ h0 hib
  obtain ⟨hΦp, hΦpU⟩ := frameIn_at hrun hnc hpi hc
  have hkt : tr.time k = sp.ts s := by
    rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hs0 : 0 < s := by
    have hk0 := hrun.time_nonneg k
    have hpk : p ∈ H (tr.time k) := hrun.antitone (by rw [hkt]; linarith) hp
    obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, -⟩ := hP
    rcases blockCall_cases (hrun.upTo hk0).toLocalRun hpk
        ((Trace.upTo_callAt_of_le _ le_rfl).mpr hcB) with
      hg | ⟨j, x, rfl, -, hPr, d', pay', -, hB, -⟩
    · have h := (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1
      simp only [Nat.add_zero] at h
      exact absurd h hpos
    rw [← hPs, hB]
    exact hPr.1
  -- the proposal walk, from its start to `Q`
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hstart
  have hpass := proposal_walk_passes_old_at hrun hnc hsync hB hinv hpi hc hcall hd hti hib
  have hanch := proposal_anchor_old_at hrun hnc hpi hf hc hcall hd hti
  -- `D`: the deepest of the start and the old origins on the proposal walk
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦp (S := {X | X ∈ ℓp.frame.tree ∧
      ℓp.frame.Anc d.start X ∧ ℓp.frame.Anc X d.head ∧ (X = d.start ∨ OldOrigin tr H s X)})
    (fun X hX => hX.1) ⟨d.start, hstart, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hΦp (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hΦp.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocksAt H) O D := by
    intro O hO
    have hOQ := hpass O hO
    rcases Anc.total hU hOQ (Anc.mono hΦpU hsQ) with h | h
    · exact h.trans (Anc.mono hΦpU hsD)
    have hOt := mem_between hU hΦp hΦpU hstart hQt h hOQ
    exact Anc.mono hΦpU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hΦp hΦpU hstart h hOt,
      SA.anc_tree_of_anc_U hU hΦp hΦpU hOt hOQ hQt, Or.inr hO⟩)
  -- `D` is genesis or an old origin
  have hDkind : D.root = sp.genesisRoot ∨ OldOrigin tr H s D := by
    rcases hDk with rfl | h
    · rcases hanch with h | ⟨O, hO, hsO⟩
      · exact Or.inl h
      · rw [Anc.antisymm hU hsO (hDold O hO)]
        exact Or.inr hO
    · exact Or.inr h
  refine ⟨D, hsD, hDQ, proposal_suffix_viable_at hrun hnc hpi hf hc hcall hd hti hDt hDold,
    fun y j ℓy e hy hcy hjb hes hE => ?_⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hcy.1
  have hhead := (castAt_spec_at hrun hnc hy hcy).2.2.2
  rw [hes] at hhead
  have hjt : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hrun hnc hy hcy).2
  have hj1 : sp.ts s ≤ tr.time j := by
    have h := (castAt_spec_at hrun hnc hy hcy).2.1
    rw [hes] at h
    exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by rw [← h])
  have hpj : p ∈ H (tr.time j) := hrun.antitone hjt hp
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have hah : ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) :=
    SA.anc_ghost (fun B hB => (SA.voteDomain_subset_tree hB.1)) _ hat
  have hht := mem_of_anc_left hah hat
  -- the vote's head extends `D` (S2, or genesis)
  have hDh : Anc (tr.HonestBlocksAt H) D (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
      (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
    rcases hDkind with hg | hO
    · exact honestAt_genesis_root_anc hrun hU (hΦpU hDt) hg (hΦU hht)
    obtain ⟨m, hm, hO⟩ := hO.within hrun (hti ▸ hib)
    obtain ⟨Hd, hHd, hHdr, hDHd⟩ :=
      hinv.vote_extends D m hO y j e (hVoteAt_iff.2 ⟨hy, ℓy, hcy.1, hcy.2⟩) hjb (by omega)
    rwa [hU.1 hHd (hΦU hht) (hHdr.trans hhead)] at hDHd
  have hij : tr.time i ≤ tr.time j := hti ▸ hj1
  rcases vote_anchor_cases_at hrun hnc hy (hB.two _ (hrun.time_nonneg j) hjb) hpj hP
      (hkt.trans_le hj1) hs0 hPQ (mem_upTo_of_frame hrun hpj hij hc hQt) (Anc.mono hΦpU hDQ)
      hDold hcy hes hE with haD | ⟨hDa, haP, hPU⟩
  · have hDt' := mem_between hU hΦ hΦU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hΦ hΦU hat haD hDt',
      SA.anc_tree_of_anc_U hU hΦ hΦU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := anc_parent hU haP haPe hPQ (hΦpU hQt)
  have hat' := mem_between hU hΦp hΦpU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hΦp hΦpU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hΦp hΦpU hat' haQ hQt⟩, .refl, hah⟩

end Consensus.Goldilocks.Compose.Growing

end
