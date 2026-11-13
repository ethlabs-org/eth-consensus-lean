module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.LiveReader
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Held
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The honest votes of a slot after the split slot

The unanimity of slot `s ≥ σ + 1` after a hand-over, for a proposal at `t_s ∈ [t₁, b]` by a
proposer honest through `t_s + Δ`: every slot-`s` vote of a node honest at its vote is the proposal
(`seeded_votes_eq_proposal`), from the pivot over the old family (`pivot_of`, `SeededOld`) and the
suffix lemmas under the service from `ḡ` (`suffix_agree_from` and its siblings).

* `proposer_row_labels`, `voter_row_labels`: a high row held by the proposer (by a voter of slot
  `s`) is sourced below a member of a label below `s`: a result written by the read has label at
  most `s − 2`, and an optimistic origin of label `s` is excluded (`proposal_no_optimistic_of`,
  `no_optimistic_before_held_row_of`);
* `seeded_start_old`: the walk's start is below a member of the old family: `fc_root`
  (`seeded_reader_old`), or a live lock block, below the proposer's lock write of a label in
  `[r, s)`;
* `seeded_vote_anchor`: a voter's anchor is below a block above the old family, or on `P`'s chain
  above it: `fc_root` and the lock blocks of other slots are below members of the old family; a
  lock of slot `s` is below an optimistic selection with an honest earlier supporter, so below
  `P`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}
  {T : Time} {r σ : Nat} {t₁ b : Time}

/-- A result of label `l` written at a time `≤ t_s + Δ` has `l ≤ s − 2`. -/
private theorem result_label_le {x : Fin sp.n} {c l s : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} {OV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC x c l O OV) (hc : tr.time c ≤ sp.ts s + sp.Δ) : l + 2 ≤ s := by
  obtain ⟨ℓ, hu, _⟩ := hR
  have ht : tr.time c = sp.ts l + 6 * sp.Δ := hu.2.2.1
  have hΔ := sp.toParams.hΔ
  have : sp.ts (l : Int) + 4 * sp.Δ < sp.ts (s : Int) := by linarith
  have h2 : sp.ts ((l + 1 : Nat) : Int) < sp.ts (s : Int) := by
    simp only [SAParams.ts] at this ⊢; push_cast; linarith
  have := (SA.ts_lt_iff sp).1 h2
  omega

/-- An optimistic origin of label `l` written at a time `≤ t` has `l ≤ slot t`. -/
private theorem optimistic_label_le (hrun : Growing.GoldilocksRun proposer dg H tr)
    {x : Fin sp.n} {c l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))} {OV : Set (Vote sp.n)}
    (hO : SA.OptimisticLockAt tr.projAC x c l O OV) {t : Time} (hc : tr.time c ≤ t) :
    l ≤ sp.slot t := by
  obtain ⟨ℓ, A, _, hs, _⟩ := hO
  change sp.slot (tr.time c) = l at hs
  rw [← hs]
  exact SA.slot_mono sp (hrun.time_nonneg c) hc

variable {p : Fin sp.n} {s i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}

/-- **The high rows of the proposer of slot `s` are sourced below members of labels below `s`**
(the row classification of `seeded_reader_old` at the proposal cut). -/
theorem proposer_row_labels (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hp : p ∈ H (tr.time i)) (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) :
    ∀ m < i, ∀ X, tr.AcceptAt p m X → ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time i) →
      ∀ k < m, tr.SignAt a.val k a → ∀ c < k, ∀ C l O OV,
        HealedOrigin tr H g r (r + sp.k - 1) C l (tr.time c) →
        (SA.ResultAt tr.projAC a.val c l O OV ∨ SA.OptimisticLockAt tr.projAC a.val c l O OV) →
        l + 1 ≤ s := by
  intro m hm X hX a ha hav k hkm hsg c hck C l O OV hC hO
  have hΔ := sp.toParams.hΔ
  have hci : tr.time c ≤ tr.time i := hS.run.time_mono (by omega)
  rcases hO with hR | hOp
  · have := result_label_le hR (by linarith)
    omega
  have hl := optimistic_label_le hS.run hOp hci
  have hsi : sp.slot (tr.time i) = s := by
    rw [hti]; simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  rw [hsi] at hl
  rcases hl.lt_or_eq with hlt | rfl
  · omega
  exfalso
  have hd := hS.run.time_nonneg i
  refine Compose.proposal_no_optimistic_of (hS.run.upTo hd) (hS.noColl.upTo _)
    (hS.bounds.two _ hd hb) hp
    (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hcall hti
    a.val hav c (by omega) O OV ?_
  rw [RunTrace.upTo_projAC]
  exact (sa_optimisticLockAt_upTo hS.run.time_mono).mpr ⟨hci, hOp⟩

/-- **The high rows of a voter of slot `s` are sourced below members of labels below `s`** (the
row classification of `seeded_reader_old` at the vote cut). -/
theorem voter_row_labels (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) {y : Fin sp.n}
    {j : Nat} (hy : y ∈ H (tr.time j)) {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) (hs0 : 0 < s) (hjb : tr.time j ≤ b) :
    ∀ m < j, ∀ X, tr.AcceptAt y m X → ∀ a ∈ X.fgPayload, a.val ∈ H (tr.time j) →
      ∀ k < m, tr.SignAt a.val k a → ∀ c < k, ∀ C l O OV,
        HealedOrigin tr H g r (r + sp.k - 1) C l (tr.time c) →
        (SA.ResultAt tr.projAC a.val c l O OV ∨ SA.OptimisticLockAt tr.projAC a.val c l O OV) →
        l + 1 ≤ s := by
  intro m hmj X hX a ha hav k hkm hsg c hck C l O OV hC hO
  have hΔ := sp.toParams.hΔ
  have hcj : tr.time c ≤ tr.time j := hS.run.time_mono (by omega)
  have hjt : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hS.run hS.noColl hy hcy).2
  rcases hO with hR | hOp
  · have := result_label_le hR (by linarith)
    omega
  have hl := optimistic_label_le hS.run hOp hcj
  have hsj : sp.slot (tr.time j) = s :=
    ((castAt_spec_at hS.run hS.noColl hy hcy).2.1).symm.trans hes
  rw [hsj] at hl
  rcases hl.lt_or_eq with hlt | rfl
  · omega
  exfalso
  have hd := hS.run.time_nonneg j
  have hm := hS.run.time_mono
  obtain ⟨s', rfl⟩ : ∃ s', l = s' + 1 := ⟨l - 1, by omega⟩
  exact Compose.no_optimistic_before_held_row_of (hS.run.upTo hd) (hS.noColl.upTo _) _
    SA.CommitteeP.full (SA.size_binding_full hS.stock)
    (SA.cs2_full hS.stock (hS.bounds.two _ hd hjb))
    hy (SA.mem_full _ _)
    (by rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hcy⟩) hes
    ((RunTrace.upTo_acceptAt tr).mpr ⟨hm hmj.le, hX⟩) hmj hav hkm
    ((RunTrace.upTo_signAt tr).mpr ⟨hm (by omega : k ≤ j), hsg⟩) hav hck
    (by rw [RunTrace.upTo_projAC]; exact (sa_optimisticLockAt_upTo hm).mpr ⟨hcj, hOp⟩)

/-- The label of a lock write by a time `≤ t_s + Δ` is at most `s`. -/
private theorem lockWithin_label_le (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {D : SA.Blk sp.n (List (FG.Att sp.n))} {l : Nat} {τ : Time}
    (hD : LockWithin tr H D l τ) (hτ : τ ≤ sp.ts s + sp.Δ) : l ≤ s := by
  obtain ⟨O, hO, -⟩ := hD.below_origin hrun hnc
  obtain ⟨x, k, CV, -, hkτ, hR | hOp⟩ := originWithin_iff.1 hO
  · have := result_label_le hR (hkτ.trans hτ)
    omega
  · have h := optimistic_label_le hrun hOp (hkτ.trans hτ)
    have hs : sp.slot (sp.ts s + sp.Δ) = s := by
      simpa using (SA.slot_arithmetic sp s).1 1 (by omega)
    rw [hs] at h
    exact h

/-- **The start of the proposal walk of slot `s ≥ σ + 1` is below a member of the old family**,
at a proposal at `t_s ∈ [t₁, b]`: `fc_root` by `seeded_reader_old`; a live lock block is below the
proposer's lock write of the lock's slot, of a label in `[r, s)` (`SeededRun.live_label`,
`proposal_locks_slot_of`), so below a member of the old family (`old_cover`). -/
theorem seeded_start_old (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) (hs : σ + 1 ≤ s)
    (hp : p ∈ H (tr.time i)) (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (ht₁ : t₁ ≤ tr.time i) (hb : tr.time i ≤ b) :
    ∃ O, SeededOld tr H g r b s O ∧ Anc (tr.HonestBlocksAt H) d.start O := by
  have hΔ := sp.toParams.hΔ
  have hrun := hS.run
  have hnc := hS.noColl
  have h0 := hrun.time_nonneg i
  have hi : ∀ k < i, tr.time k ≤ tr.time i := fun _ h => hrun.time_mono h.le
  have hdt : sp.ts (r + sp.k : Nat) ≤ tr.time i := hS.drain.trans ht₁
  have hold := seeded_reader_old hS hs hdt hi (by linarith) hb hp (hS.called hp hdt le_rfl)
    (proposer_row_labels hS hp hc hcall hti hb)
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hp hc
  obtain ⟨A₁, hA₁, hst, -⟩ := acProposal_walk hd
  rw [hst]
  rcases anchor_mem ℓp.frame A₁ (tr.time i) with hL | hf
  · obtain ⟨l, hl, hlive, D', hD', hLD'⟩ :=
      proposal_live_lock_below_at hrun hnc hp hΦ hΦU hA₁ _ hL
    have hlr := hS.live_label hp hdt hl hlive
    have hls := Compose.proposal_locks_slot_of (hrun.upTo h0) (hnc.upTo _)
      (hS.bounds.two _ h0 hb) hp
      (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hcall
      (by rw [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl]; exact hd) hti l
      (by rw [Trace.upTo_state tr p hi]; exact hl)
    obtain ⟨O, hO, hD'O⟩ := old_cover (s := s) (l := l.slot) (τ := tr.time i) hrun hnc
      (.of_lock hlr hD')
      (by omega) (by linarith) hb
    exact ⟨O, hO, hLD'.trans hD'O⟩
  · rw [Set.mem_singleton_iff.1 hf, frame_of_projAC_at hrun hp hc]
    exact hold.1

/-- **A voter's anchor is below a block above the old family, or on `P`'s chain above it**, at a
vote of slot `s ≥ σ + 1` at a time in `[t₁, b]` whose earlier slot-`s` votes by nodes honest at
them are `P`: `fc_root` is below a member of the old family (`seeded_reader_old`); a lock block of
another slot is below the voter's lock write of a label in `[r, s)`, below a member of the old
family; a lock of slot `s` is below an optimistic selection, supported by an honest earlier voter
of slot `s`, whose vote is `P`. -/
theorem seeded_vote_anchor (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b) (hs : σ + 1 ≤ s)
    {P D : SA.Blk sp.n (List (FG.Att sp.n))} (hPU : P ∈ tr.HonestBlocksAt H)
    (hDP : Anc (tr.HonestBlocksAt H) D P)
    (hDold : ∀ O, SeededOld tr H g r b s O → Anc (tr.HonestBlocksAt H) O D)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) (ht₁ : t₁ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hE : ∀ x j' e', j' < j → HVoteAt tr H x j' e' → e'.msg.slot = s → e'.msg.head = P.root) :
    Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocksAt H) D (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
        Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
        P ∈ tr.HonestBlocksAt H) := by
  have hΔ := sp.toParams.hΔ
  have hrun := hS.run
  have hnc := hS.noColl
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg j
  have hi : ∀ k < j, tr.time k ≤ tr.time j := fun _ h => hm h.le
  have hdt : sp.ts (r + sp.k : Nat) ≤ tr.time j := hS.drain.trans ht₁
  have hjt : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hrun hnc hy hcy).2
  have hs0 : 0 < s := by have := hS.seed.timing.2.1; omega
  have hU := honestBlocksAt_coherent hrun hnc
  have hold := seeded_reader_old hS hs hdt hi hjt hjb hy (hS.called hy hdt le_rfl)
    (voter_row_labels hS hy hcy hes hs0 hjb)
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hcy.1
  have hfr := frame_of_projAC_at hrun hy hcy.1
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have haS := anchor_mem ℓy.frame e.readPoint (tr.time j)
  generalize SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = a at hat haS ⊢
  rcases haS with ⟨-, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hl'r⟩ | haf
  swap
  · left
    rw [Set.mem_singleton_iff.1 haf, hfr]
    obtain ⟨O, hO, hfO⟩ := hold.1
    exact hfO.trans (hDold O hO)
  obtain rfl : a = ℓy.frame.viableAncestor B :=
    hΦ.coherent.1 hat (SA.viableAncestor_anc hΦ hB).1 hl'r.symm
  have haB : Anc (tr.HonestBlocksAt H) (ℓy.frame.viableAncestor B) B :=
    Anc.mono hΦU (SA.anc_viableAncestor _ B)
  have hrun' := acRun_upTo hrun hnc hd
  have hr' := hrun'.localRun
  have hcy' : SA.CastAt (tr.projAC.upTo (tr.time j)) y j ℓy e := sa_castAt_upTo.mpr ⟨le_rfl, hcy⟩
  have hsub := upTo_subset hrun hd
  have hBP : B ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) :=
    mem_upTo_of_frame hrun hy le_rfl hcy.1 hB
  by_cases hls : l.slot = s
  · -- a lock of slot `s`: below an optimistic selection with an honest earlier supporter
    obtain ⟨Φ', A', D', -, hΦ'U, -, h34, hpool, -, L, hLU, hLr, hLD'⟩ :=
      SA.lock_origin_readPoint hrun' hy hcy' l hl (by rw [hes, hls]; omega)
    rw [hS.stock] at h34
    obtain rfl : L = B := hr'.coherent.1 hLU hBP (hLr.trans hBr.symm)
    have hf := hS.bounds.two _ hd hjb
    obtain ⟨x, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H (tr.time j))ᶜ)
        (t := SA.optimisticVoters sp A' Φ' l.slot D') (by omega)
    have hvH : v.val ∈ H (tr.time j) := not_not.1 hxH
    obtain ⟨hvs, j', hj', e', hv', rfl⟩ := hpool v hv hvH
    obtain ⟨hj'd, hv'⟩ := sa_voteAt_upTo.mp hv'
    have hhead := hE _ j' e' hj' (hVoteAt_iff.2 ⟨hrun.antitone hj'd hvH, hv'⟩) (hvs.trans hls)
    obtain rfl : R = P := hU.1 (hsub (hΦ'U hR)) hPU (hRr.trans hhead)
    have haP := haB.trans (Anc.mono hsub (hLD'.trans (Anc.mono hΦ'U hDR)))
    rcases Anc.total hU haP hDP with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haP, hPU⟩
  · -- a lock of another slot: below the voter's lock write of a label in `[r, s)`
    left
    have hsj : sp.slot (tr.time j) = s := ((castAt_spec_at hrun hnc hy hcy).2.1).symm.trans hes
    obtain ⟨l₁, hl₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hB'B₁⟩ :=
      SA.readPoint_locks_below_stored hr' hy hcy'
        (by change 0 < sp.slot (tr.time j); rw [hsj]; exact hs0) l hl
        (by change l.slot ≠ sp.slot (tr.time j); rw [hsj]; exact hls)
    have hlr : r ≤ l₁.slot := by
      rw [← hs₁]
      exact handover_live_lock_label_at hS.seed hy hcy (by omega)
        ({ l with block := (ℓy.frame.viableAncestor B).root } : SA.Lock)
        ⟨l, hl, B, hB, hBr, hlive, rfl⟩
    obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
    rw [projAC_upTo_state hrun le_rfl, projAC_state_at hrun hy] at hl₁
    obtain ⟨L₁, hL₁, hL₁r, D₁, hD₁, hL₁D₁⟩ := lock_write_at hrun hnc hd hi hy l₁ hl₁
    obtain rfl : L₁ = B₁ :=
      hU.1 (mem_honestBlocksAt hrun hy hL₁) (hΦU hB₁) (hL₁r.trans hB₁r.symm)
    have hle := lockWithin_label_le hrun hnc hD₁ hjt
    obtain ⟨O, hO, hD₁O⟩ := old_cover (s := s) (l := l₁.slot) (τ := tr.time j) hrun hnc
      (.of_lock hlr hD₁)
      (by omega) (by linarith) hjb
    exact (haB.trans (Anc.mono hΦU hB'B₁)).trans (hL₁D₁.trans (hD₁O.trans (hDold O hO)))

/-- The voter facts of the suffix lemmas at a vote of slot `s ≥ σ + 1` at a time in `[t₁, b]`,
when every member of the old family is below `Q`: `fc_root` is below `Q`, and the head height floor
is at most the height of every block of the voter's tree above `Q` (`seeded_reader_old`). -/
private theorem seeded_voter_facts (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hs : σ + 1 ≤ s) {Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpass : ∀ O, SeededOld tr H g r b s O → Anc (tr.HonestBlocksAt H) O Q)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) (ht₁ : t₁ ≤ tr.time j) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) ℓy.frame.fcRoot Q ∧
      ∀ B ∈ (tr.state y j).fg.tree, Anc (tr.HonestBlocksAt H) Q B →
        (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  have hdt : sp.ts (r + sp.k : Nat) ≤ tr.time j := hS.drain.trans ht₁
  have hjt : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot_at hS.run hS.noColl hy hcy).2
  have hs0 : 0 < s := by have := hS.seed.timing.2.1; omega
  have hR := seeded_reader_old hS hs hdt (fun _ h => hS.run.time_mono h.le) hjt hjb hy
    (hS.called hy hdt le_rfl) (voter_row_labels hS hy hcy hes hs0 hjb)
  refine ⟨?_, fun B hB hQB => hR.2 B hB fun O hO => (hpass O hO).trans hQB⟩
  rw [frame_of_projAC_at hS.run hy hcy.1]
  obtain ⟨O, hO, hfO⟩ := hR.1
  exact hfO.trans (hpass O hO)

/-- **The honest votes of a slot `s ≥ σ + 1` after a hand-over are the proposal**: for the
proposal `P` of slot `s` at `t_s ≥ t₁` by a proposer honest at `t_s + Δ ≤ b`, every slot-`s` vote
of a node honest at its vote is `P` (`honest_votes_eq_proposal_of`), with the pivot over the old
family (`pivot_of`: `seeded_walk_passes`, `seeded_start_old`, `seeded_vote_anchor`, the floor of
`seeded_reader_old`) and the suffix lemmas under the service from `ḡ`. -/
theorem seeded_votes_eq_proposal (hS : SeededRun tr H proposer dg g ΔF T r σ t₁ b)
    (hs : σ + 1 ≤ s) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H (sp.ts s + sp.Δ)) (hP : tr.ProposesAt p k P) (hPs : P.slot = s)
    (ht₁ : t₁ ≤ sp.ts s) (hsb : sp.ts s + sp.Δ ≤ b) :
    ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root := by
  have hΔ := sp.toParams.hΔ
  have hrun := hS.run
  have hnc := hS.noColl
  have hU := honestBlocksAt_coherent hrun hnc
  have hkt : tr.time k = sp.ts s := by rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hpk : p ∈ H (tr.time k) := hrun.antitone (by rw [hkt]; linarith) hp
  obtain ⟨i, ℓp, d, pay, hc, hcall, hd, hti, hPQ, -⟩ := proposal_data_at hrun hpk hP hPs
  have hib : tr.time i ≤ b := by rw [hti]; linarith
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by rw [hti]; linarith) hp
  have hti₁ : t₁ ≤ tr.time i := hti ▸ ht₁
  obtain ⟨hs0, hrs, hga, -⟩ := hS.slot_timing hs
  obtain ⟨hΦp, hΦpU⟩ := frameIn_at hrun hnc hpi hc
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hstart
  have hPU := proposal_honest_at hrun hnc hpk hP
  have hQP : Anc (tr.HonestBlocksAt H) d.head P := .single ⟨hΦpU hQt, hPU, hPQ⟩
  have hpass := fun O (hO : SeededOld tr H g r b s O) =>
    seeded_walk_passes hS hs hpi hc hcall hd hti hti₁ hib hO
  have hextV : ∀ X, SeededOld tr H g r b s X → ∀ y j e, HVoteAt tr H y j e → tr.time j ≤ b →
      e.msg.slot = s → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
    intro X hX y j e hv hjb hes
    obtain ⟨l, hl, hXm⟩ := hX.member hrun (by linarith) hrs
    exact hS.inv.vote_extends X l hXm y j e hv hjb (by omega)
  have hvt₁ : ∀ y j ℓy e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ℓy e → e.msg.slot = s →
      t₁ ≤ tr.time j := fun y j ℓy e hy hcy hes => by
    have h := (castAt_spec_at hrun hnc hy hcy).2.1
    rw [hes] at h
    exact ht₁.trans ((SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by rw [← h]))
  have hrd := seeded_reader_old hS hs (hS.drain.trans hti₁) (fun _ h => hrun.time_mono h.le)
    (by linarith) hib hpi (hS.called hpi (hS.drain.trans hti₁) le_rfl)
    (proposer_row_labels hS hpi hc hcall hti hib)
  obtain ⟨A₁, -, hst, -⟩ := acProposal_walk hd
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := pivot_of hrun hnc hp hc hd hti hPQ
    (Old := SeededOld tr H g r b s) hpass
    (fun X hX y j e hv hjb hes => by
      rcases hX with rfl | hO
      · obtain ⟨O, hO, hsO⟩ := seeded_start_old hS hs hpi hc hcall hd hti hti₁ hib
        obtain ⟨Hd, hHd, hHdr, hOH⟩ := hextV O hO y j e hv hjb hes
        exact ⟨Hd, hHd, hHdr, hsO.trans hOH⟩
      · exact hextV X hO y j e hv hjb hes)
    (fun D hDt hsD hDold X hDX hXQ => by
      have hXt : X ∈ ℓp.frame.tree := mem_of_anc_left hDX hDt
      have hfX : ℓp.frame.Anc ℓp.frame.fcRoot X := by
        have h := SA.fcRoot_anc_getAnchor hΦp A₁ (tr.time i)
        rw [← hst] at h
        exact (h.trans hsD).trans hDX
      have hfl := hrd.2 X (by rw [frame_of_projAC_at hrun hpi hc] at hXt; exact hXt.1)
        fun O hO => (hDold O hO).trans (Anc.mono hΦpU hDX)
      rw [frame_of_projAC_at hrun hpi hc] at hXt hfX ⊢
      obtain ⟨hXs, hFX⟩ := hXt
      exact ⟨hXs, hFX, Anc.mono (fun _ h => h.1) hfX, hfl⟩)
    (fun D hDt hDQ hDold y j ℓy e hy hcy hjb hes hE =>
      seeded_vote_anchor hS hs hPU ((Anc.mono hΦpU hDQ).trans hQP) hDold hy hcy hes
        (hvt₁ y j ℓy e hy hcy hes) hjb hE)
  intro x j e hv hes
  have hjb : tr.time j ≤ b := by
    obtain ⟨hx, ℓx, hcx⟩ := hVoteAt_iff.1 hv
    have h := (cast_head_fcRoot_at hrun hnc hx hcx).2
    rw [hes] at h
    linarith
  refine honest_votes_eq_proposal_of hrun hnc hp hP hPs hc hd hti hPQ hsD hDQ hvot
    (fun y j ℓy e hy hcy hes hjb => ?_) (fun y j ℓy e hy hcy hes hjb => ?_)
    (fun y j ℓy e hy hcy hes hjb => ?_) x j e hv hes hjb
  · obtain ⟨hfcQ, hflQ⟩ :=
      seeded_voter_facts hS hs hpass hy hcy hes (hvt₁ y j ℓy e hy hcy hes) hjb
    exact suffix_agree_from hrun hnc hS.sync hp hP hPs hc hcall hd hti hPQ hsD hDQ hviab hy hcy
      hes hib hjb hga hfcQ hflQ
  · obtain ⟨hfcQ, hflQ⟩ :=
      seeded_voter_facts hS hs hpass hy hcy hes (hvt₁ y j ℓy e hy hcy hes) hjb
    exact proposal_at_voter_from hrun hnc hS.sync hp hP hPs hc hd hti hPQ hy hcy hes hjb hga
      hfcQ hflQ
  · obtain ⟨hfcQ, hflQ⟩ :=
      seeded_voter_facts hS hs hpass hy hcy hes (hvt₁ y j ℓy e hy hcy hes) hjb
    exact fun B => old_child_ineligible_from hrun hnc hS.sync hp hP hPs hc hcall hd hti hPQ hDQ
      hviab hy hcy hes hib hjb hga hfcQ hflQ (B := B)

end Consensus.Goldilocks.Compose.Growing

end
