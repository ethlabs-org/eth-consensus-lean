module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote

public section

/-! # Goldilocks under `Sleepy`: the next vote batch (extending `V_s` to `V_{s+1}`)

workbench#11 §2.3, §2.4 and §4 "Extend the vote frontier, simultaneously". Fix an honest
slot-`(s+1)` vote, and assume `P_{s+1}`, `V_s` and that the honest slot-`(s+1)` votes at earlier
cuts extend the block in question (the first-bad-vote argument). The lock and later-batch steps
are stated for a block `B` with the hypotheses they use, so that the proposal-adoption bootstrap
(workbench#12 §4) applies them to the protected proposal; for an origin `C` of label `j ≤ s`:

* **Locks** (`vote_locks_compatible`): every live lock block after the unlocking is compatible
  with `C`: a lock of slot at most `s` sits below an origin of its slot, compared with `C` by
  `P_{s+1}`; one of slot `s + 1` is optimistic and was selected over earlier honest
  slot-`(s+1)` votes, which extend `C` (`SA.locks_compatible`).
* **First transfer** (`first_transfer_step`, `j = s`): `C` at or below `fc_root` (the vote's head
  extends `fc_root`), or, with `vote_frame` and the transport (`result_carry`,
  `optimistic_carry`, `result_writer_pool`), A1.8 for a result and A1.4 (a) for an optimistic
  selection.
* **Later batch** (`later_transfer_step`, `j < s`): the slot-`s` honest votes all extend `C`
  (`V_s`); the more than `f` of them cast by the validators awake and joined at `t_s + Δ` are held
  and resolved at the vote freeze, and only faulty seats oppose or equivocate, so `C`'s children
  towards the vote win the walk (`SA.isBest_of_majority`, `SA.anc_getHead`).
* `votes_below_succ`: strong induction on the cut index over the slot-`(s+1)` votes. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

/-! ### Over an SA trace -/

section SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro}

/-- The read point of `try_vote`'s emission holds the input's locks, unlocked against the merged
view for a slot `s > 0`. -/
private theorem tryVote_readPoint_locks {x : Fin sp.n} {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n FGP} {t : Time} {e : SA.Em sp FGP} (he : e ∈ (SA.tryVote sp x A Φ t).2) :
    e.readPoint.locks = if 0 < sp.slot t then
      SA.unlock sp A.locks Φ t ((sp.slot t : Int) - 1) (SA.mergedVoteView sp A Φ (sp.slot t))
      else A.locks := by
  unfold SA.tryVote at he
  dsimp only at he
  split_ifs at he with h1 h2 h3
  · simp at he
  · simp at he
  all_goals
    rw [List.mem_singleton] at he
    subst he
    split_ifs
    rfl

/-- The input of the `try_vote` that emits an honest vote: the state before the call, or the
optimistic check after the receipt of a message or a block, which keeps the locks. -/
private theorem emits_tryVote (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) :
    ∃ P, e ∈ (SA.tryVote sp y P ℓ.frame (tr.time i)).2 ∧ (P = tr.state y i ∨
      ∃ A : SA.SAState sp.n, P = SA.optimisticConfirmation sp A ℓ.frame (tr.time i) ∧
        A.locks = (tr.state y i).locks) := by
  obtain ⟨hc, he⟩ := hc
  have hΦ := (SA.frameIn_of_callAt hr hy hc).1
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have he' : e ∈ ((SA.goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 := by
    rw [hx]
    exact he
  clear hx he
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at he'
    change e ∈ (SA.acOnTick sp y _ ℓ.frame _).2 at he'
    unfold SA.acOnTick at he'
    dsimp only at he'
    split_ifs at he' <;> first | exact ⟨_, he', Or.inl rfl⟩ | simp at he'
  | proposal =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | toFG =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | message m =>
    rw [hcall] at he'
    exact ⟨_, he', Or.inr ⟨_, rfl, SA.admitVote_locks_eq _ _ _⟩⟩
  | block B =>
    rw [hcall] at he'
    exact ⟨_, he', Or.inr ⟨_, rfl, SA.blockReceipt_locks _ _ _⟩⟩
  | restart =>
    rw [hcall] at he'
    change e ∈ (SA.acRestart sp ro y _ ℓ.frame (tr.time i)).2 at he'
    rw [((SA.restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- **The read point's locks come from the stored ones.** At an honest vote of a slot `> 0`,
a lock of the read point of a slot other than the vote's sits (in the frame) below a stored
lock of the same slot: `try_vote`'s unlocking and the receipt's optimistic check only move
locks back, and the optimistic check writes locks of the vote's slot. -/
private theorem readPoint_locks_stored (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} (hc : SA.CastAt tr y i ℓ e) (hpos : 0 < sp.slot (tr.time i)) :
    ∀ l' ∈ e.readPoint.locks, l'.slot ≠ sp.slot (tr.time i) →
      ∃ l ∈ (tr.state y i).locks, l'.slot = l.slot ∧ ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧
        ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧ ℓ.frame.Anc B' B := by
  obtain ⟨P, he, hP⟩ := emits_tryVote hr hy hc
  have hΦ := (SA.frameIn_of_callAt hr hy hc.1).1
  intro l' hl' hne
  rw [tryVote_readPoint_locks he] at hl'
  simp only [hpos, ↓reduceIte] at hl'
  obtain ⟨l₁, hl₁, hs₁, -, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩ :=
    ((SA.locks_move_back sp) FGP ℓ.frame P.locks (tr.time i) hΦ).2.2 _ _ l' hl'
  rcases hP with rfl | ⟨A, rfl, hAl⟩
  · exact ⟨l₁, hl₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩
  unfold SA.optimisticConfirmation at hl₁
  split at hl₁
  · exact ⟨l₁, hAl ▸ hl₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩
  rw [SA.updateLatestConfirmed_locks_eq] at hl₁
  obtain ⟨l₂, hl₂, hs₂, -, B₂, hB₂, hB₂r, B₁', hB₁', hB₁'r, hA'⟩ :=
    ((SA.locks_move_back sp) FGP ℓ.frame A.locks (tr.time i) hΦ).2.1 _ _ l₁ hl₁
  rcases hl₂ with hl₂ | ⟨p, hp, rfl⟩
  · obtain rfl : B₁' = B₁ := hΦ.coherent.1 hB₁' hB₁ (hB₁'r.trans hB₁r.symm)
    exact ⟨l₂, hAl ▸ hl₂, hs₁.trans hs₂, B₂, hB₂, hB₂r, B', hB', hB'r, hA.trans hA'⟩
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    exact absurd (hs₁.trans hs₂) hne

/-- **The later-batch walk** (A1.3 with the strict honest majority of §2.4 in place of the
half-committee bound): at an honest slot-`(s+1)` vote, if every honest slot-`s` vote extends `B`,
the honest slot-`s` voters outnumber the faulty validators, the voter holds every honest slot-`s`
vote and accepted its head before `t_s + 3Δ` (`Carry_y`), `B` is in the viable voter block tree
or at or below `fc_root`, and every live lock block is compatible with `B`, the vote extends
`B`: only faulty seats oppose or equivocate, so `B`'s children towards the vote win the walk. -/
theorem vote_extends_of_batch (hrun : SA.ACRun tr H U) {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : SA.Blk sp.n FGP}
    (hviab : SA.ViableAtVote ℓ e (s + 1) B)
    (hall : ∀ x ∈ H, ∀ j e', SA.VoteAt tr x j e' → e'.msg.slot = s → SA.VoteExtends U e'.msg B)
    (hcount : Hᶜ.ncard < {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg.slot = s}.ncard)
    (hcarry : SA.CarryAt tr U y i e s
      {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B) :
    SA.VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨-, -, -, hhead⟩ := SA.castAt_spec hr hy hc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := SA.voterBlockTree_anc hr hy hc
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact SA.mem_of_anc h hΦ.fcRoot_mem
  -- the honest voters of slot `s` are supporters of `B` at `y`
  set SX : Set (Fin sp.n) := {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg.slot = s}
  have hsupp : SX ⊆
      SA.supporters ℓ.frame (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s B := by
    rintro w ⟨hw, j, e', hv, hvs⟩
    obtain ⟨ℓw, hcw⟩ := id hv
    have hvw : e'.msg.val = w := (SA.castAt_spec hr hw hcw).1
    have hmem : e'.msg ∈ {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} :=
      ⟨w, hw, j, e', hv, rfl, hvs⟩
    -- `y` holds `e'.msg` itself (an honest validator has one slot-`s` vote)
    have hheld : SA.HeldBefore e.readPoint e'.msg (sp.ts s + 3 * sp.Δ) := by
      rcases hcarry.holds _ hmem with h | ⟨v₁, v₂, h12, h1, h2, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
      · exact h
      · exfalso
        have hm : ∀ u, u.slot = s → SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
            u ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
          intro u hus hu
          refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
          · simp only [SA.SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega,
              ite_false]
            simpa [hus] using hu.1
          · simpa [SA.freeze] using hu.2
        obtain ⟨j₁, -, e₁, hv₁', he₁⟩ :=
          SA.honest_merged_vote hrun hy hc (hm v₁ hs₁ hh₁) (hv₁.trans hvw ▸ hw)
        have := (SA.one_vote_per_slot sp) FGP ro H U tr hr w hw j₁ j e₁ e'
          (hv₁.trans hvw ▸ hv₁') hv (by rw [he₁, hs₁, hvs])
        exact h1 (he₁ ▸ this.2 ▸ rfl)
    obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads _ hmem
    obtain ⟨Hd, hHd, hHdr, hHds⟩ := SA.honest_head hrun hw hv
    obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hall w hw j e' hv hvs
    have h1 : Hd = Hv := hU.1 hHd hHv (hHdr.trans hHvr.symm)
    have h2 : Hd' = Hv := hU.1 hHd' hHv (hHd'r.trans hHvr.symm)
    have := SA.carried_supporter hrun hy hc hs hBt hvs hheld
      ⟨Hv, hHv, hHvr, h1 ▸ hvs ▸ hHds, h2 ▸ hBHd', hacc Hv Relation.ReflTransGen.refl⟩
      (SA.honest_not_equivocator hrun hy hc (hvw ▸ hw))
    exact hvw ▸ this
  -- counting: the voters at `y` are honest slot-`s` voters or faulty, and `f < |SX|`
  have hvoters : SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆
      SX ∪ Hᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e', hv', he'⟩ := SA.honest_merged_vote hrun hy hc hv hw
      exact Or.inl ⟨hw, j, e', hv', by rw [he']; exact SA.merged_vote_slot hr hy hc v hv⟩
    · exact Or.inr hw
  have h3 : (SX ∪ Hᶜ).ncard < 2 * SX.ncard := by
    have := Set.ncard_union_le SX Hᶜ
    omega
  have hcore := SA.anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB => hB.1) hdomA hviab
    hlocks fun X' Cx hCx hp hCxC =>
      SA.isBest_of_majority hΦ (SA.merged_support_subset hr hy hc (s + 1)) (fun B hB => hB.1.1)
        hsupp hvoters h3 hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = SA.getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

end SA

/-! ### Over a run -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- An origin is an honest block: a block of its writer's frame. -/
private theorem origin_mem (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hC : Origin tr H C s) :
    C ∈ tr.HonestBlocks H := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  obtain ⟨x, hx, i, CV, ⟨ℓ, hupd, hconf, -⟩ | ⟨ℓ, A, hpt, -, hsel, -⟩⟩ := origin_iff.1 hC
  · exact (SA.frameIn_of_callAt hr hx hupd.1).2 (SA.deepest_mem hconf).1.1
  · unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (SA.frameIn_of_callAt hr hx hpt.1).2 (SA.deepest_mem hsel).1.1

/-- An honest vote of a slot `m ≤ s` is cast by `t_s + Δ`. -/
private theorem vote_time_le (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x k e) {s : Nat} (hs : e.msg.slot ≤ s) :
    tr.time k ≤ sp.ts s + sp.Δ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  obtain ⟨ℓ, hc, he⟩ := hv
  have h : tr.time k ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hx ⟨hc, he⟩).2
  have h2 : sp.ts (e.msg.slot : Int) ≤ sp.ts (s : Int) := by
    unfold SAParams.ts
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (by linarith [sp.toParams.hΔ])
  linarith

variable {b : Time}

/-- **§2.4 up to `b`, the timely honest batch**: for `t_s + Δ ≤ b`, the honest validators with a
slot-`s` vote outnumber the faulty ones. -/
theorem faults_lt_honest_voters_upTo (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) (s : Nat) (hs : sp.ts s + sp.Δ ≤ b) :
    Hᶜ.ncard < {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = s}.ncard := by
  refine lt_of_lt_of_le (faults_lt_awake_joined_upTo hpre s hs) (Set.ncard_le_ncard ?_)
  rintro x ⟨hx, hw, hj⟩
  obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined hrun hnc hx hw hj
  exact ⟨hx, k, e, hv, hs⟩

/-- **§2.4, the timely honest batch**: the honest validators with a slot-`s` vote outnumber the
faulty ones. The more than `f` honest validators awake and joined at `t_s + Δ` (`Sleepy`) tick
there and vote in slot `s` (`try_vote` votes at `t_s + Δ` unless it already voted in slot `s`). -/
theorem faults_lt_honest_voters (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (s : Nat) :
    Hᶜ.ncard < {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = s}.ncard :=
  faults_lt_honest_voters_upTo hrun hnc (hsl.prefix (le_max_right (sp.ts s + sp.Δ) 0)) s
    (le_max_left _ _)

/-- **§2.4 up to `b`, the batch reaches the next voters** at times `≤ b` (`Carry_y` for the
honest slot-`s` votes), when they all extend `B` and the voter's `Σ.F` is at or below `B`. -/
theorem honest_batch_carry_upTo (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s
      {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = s} := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti := (honest_vote_restarts hrun hnc hy hc hs).2
  have hsync := syncAC_of_prefix hrun hpre (a := 0) (b' := sp.ts s + 2 * sp.Δ) le_rfl
    (by linarith)
  -- each vote of the batch, with its own validator as the writer
  have hone : ∀ v ∈ {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = s},
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s {v} := by
    rintro v ⟨x, hx, k, e', ⟨ℓk, hck, he'⟩, rfl, hvs⟩
    have hk := (SA.castAt_spec hr hx ⟨hck, he'⟩).2.1
    obtain ⟨⟨Hd, hHd, hHdr, -⟩, hkt⟩ := cast_head_fcRoot hr hx ⟨hck, he'⟩
    obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hall x hx k e' ⟨ℓk, hck, he'⟩ hvs
    obtain rfl : Hd = Hv :=
      hU.1 ((SA.frameIn_of_callAt hr hx hck).2 hHd) hHv (hHdr.trans hHvr.symm)
    have hkt' : tr.projAC.time k < sp.ts s + 2 * sp.Δ := by
      rw [hvs] at hkt
      linarith
    refine carryAt_of_writer hr hsync le_rfl hx hy hc hs ?_
    rintro v rfl
    refine ⟨hvs, ⟨k, ⟨ℓk, hck, Or.inl ⟨e', he', rfl⟩⟩,
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega), hkt'⟩,
      Hd, hHv, hHvr, hF.trans hBHv, ?_⟩
    rcases frame_anc_accepted hr hx k ℓk hck Hd hHd Hd .refl with hg | ⟨k', hk', hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k', hacc, lt_of_le_of_lt (hr.time_mono hk') hkt'⟩
  exact ⟨hr.awake_of_call y hy i ℓ hc.1, (SA.castAt_spec hr hy hc).2.2.1,
    fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩

/-- **§2.4, the batch reaches the next voters** (`Carry_y` for the honest slot-`s` votes), when
they all extend `B` and the voter's `Σ.F` is at or below `B`. Under `Sync[0, ∞)`: each honest
slot-`s` vote is cast by `t_s + Δ`, forwarded, and processed by the voter (joined at its vote, so
awake since `t_s` with its pool kept) before `t_s + 2Δ`; its head, accepted by its voter by then,
is relayed to the voter before `t_s + 2Δ`, since the voter's `Σ.F` is below `B`, below the head
(finality is monotone along the voter's chain). The analogue of `result_carry` for the whole
honest batch. -/
theorem honest_batch_carry (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s
      {v | ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = s} :=
  honest_batch_carry_upTo hrun hnc (hsl.prefix (le_max_right (tr.time i) 0)) hy hc hs
    (le_max_left _ _) hall hF

/-- **The live locks at a slot-`(s+1)` vote at a time `≤ b` are compatible with `B`**, a block
compatible with every origin within `b` of label at most `s` that the earlier honest
slot-`(s+1)` votes extend. -/
theorem vote_locks_compatible_upTo (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hsi : e.msg.slot = sp.slot (tr.time i) := (SA.castAt_spec hr hy hc).2.1
  have hib' : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hib
  -- compatibility with `B` passes to ancestors
  have down : ∀ {X Y}, Anc (tr.HonestBlocks H) X Y → Compatible (tr.HonestBlocks H) Y B →
      Compatible (tr.HonestBlocks H) X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact SA.anc_total hU hXY h
  rintro L ⟨hL, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩, hlL⟩
  have hLe : L = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hL) (hΦU (SA.viableAncestor_anc hΦ hB₀).1) hlL.symm
  subst hLe
  refine down (Anc.mono hΦU (SA.anc_viableAncestor _ B₀)) ?_
  rcases le_or_gt l₀.slot s with hle | hlt
  · -- a lock of slot at most `s` sits below a stored lock, below an origin of its slot
    obtain ⟨l₁, hl₁, hsl₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
      readPoint_locks_stored hr hy hc (show 0 < sp.slot (tr.time i) by omega) l₀ hl₀
        (show l₀.slot ≠ sp.slot (tr.time i) by omega)
    obtain rfl : B₀' = B₀ := hΦ.coherent.1 hB₀' hB₀ (hB₀'r.trans hB₀r.symm)
    rw [projAC_state hrun.toLocalRun hy i] at hl₁
    obtain ⟨L₁, hL₁, hL₁r, O, hO, hL₁O⟩ := lock_origin hrun hnc hy i l₁ hl₁
    obtain rfl : L₁ = B₁ := hU.1 ⟨y, hy, i, hL₁⟩ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
    exact down ((Anc.mono hΦU hA).trans hL₁O) (hBc O l₁.slot (hO.within hib') (by omega)).symm
  · -- a lock of slot `s + 1` or later is optimistic, over earlier honest slot-`(s+1)` votes
    obtain ⟨Φ', A, D, -, hΦ'U, -, h34, hpool, -, L₀, hL₀, hL₀r, hL₀D⟩ :=
      SA.lock_origin_readPoint hrun' hy hc l₀ hl₀ (by rw [hs]; push_cast; omega)
    obtain rfl : L₀ = B₀ := hU.1 hL₀ (hΦU hB₀) (hL₀r.trans hB₀r.symm)
    refine down hL₀D (SA.origin_compatible hU hΦ'U h34 (two_faults_lt_of_prefix hpre)
      fun v hv hvH => ?_)
    obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
    obtain ⟨ℓ', hcj⟩ := id hvote
    have hsj : e'.msg.slot = sp.slot (tr.time j) := (SA.castAt_spec hr hvH hcj).2.1
    have : sp.slot (tr.time j) ≤ sp.slot (tr.time i) :=
      SA.slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    exact hE _ hvH j hj e' hvote (by omega)

/-- **The live locks at a slot-`(s+1)` vote are compatible with `B`**, a block compatible with
every origin of label at most `s` that the earlier honest slot-`(s+1)` votes extend. -/
theorem vote_locks_compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C j, Origin tr H C j → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B :=
  vote_locks_compatible_upTo hrun hnc (hsl.prefix (le_max_right (tr.time i) 0)) hy hc hs
    (le_max_left _ _) (fun C j hC hj => hBc C j hC.origin hj) hE

/-- **First transfer up to `b`** (§2.3): an honest slot-`(s+1)` vote at a time `≤ b` extends an
origin `C` within `b` of label `s` that the earlier honest slot-`(s+1)` votes extend. -/
theorem first_transfer_step_upTo (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : OriginWithin tr H C s b)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hrun'.localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hCU := origin_mem hrun hnc hC.origin
  have hCc : ∀ C' j, OriginWithin tr H C' j b → j ≤ s → Compatible (tr.HonestBlocks H) C C' :=
    fun C' j hC' hj => originsBelowUpTo_iff.1 hP C s C' j (by omega) (by omega) hC hC'
  obtain ⟨x', hx', k', e', hv', -, hs', hext'⟩ := honest_supporter_upTo hrun hnc hpre hC
  rcases vote_frame_upTo hrun hnc hpre hP hy hc hs hib hCU hCc
      ⟨x', hx', k', e', hv', hs', hext'⟩ with hv | hCf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot hr hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hCf.trans (Anc.mono hΦU hfHd)⟩
  have hF : Anc (tr.HonestBlocks H) ℓ.frame.F C := Anc.mono hΦU (hΦ.rooted.2 C hv.1.1)
  obtain ⟨x, hx, i₀, CV, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · exact SA.result_transfer sp _ ro H _ tr.projAC hrun' s x y i₀ i C CV ℓ e hx hR hy hc hs
      (result_carry_upTo hrun hnc hpre hx hR hy hc hs hib hF) (Or.inl hv)
      (vote_locks_compatible_upTo hrun hnc hpre hy hc hs hib hCc hE)
      (result_writer_pool_upTo hrun hnc hpre hx hR hi₀ hy hc hs)
  · exact SA.optimistic_transfer_stored sp hrun' hx hO .refl (two_faults_lt_of_prefix hpre) hy
      hc hs (optimistic_carry_upTo hrun hnc hpre hx hO hy hc hs hib hF) (Or.inl hv) hE

/-- **First transfer** (§2.3): an honest slot-`(s+1)` vote extends an origin `C` of label `s`
that the earlier honest slot-`(s+1)` votes extend. -/
theorem first_transfer_step (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : Origin tr H C s)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg C :=
  have ⟨bC, hbC⟩ := hC.exists_within
  first_transfer_step_upTo hrun hnc (hsl.prefix (le_max_right (max (tr.time i) bC) 0))
    (hP.upTo _) hy hc hs ((le_max_left _ bC).trans (le_max_left _ 0))
    (hbC.mono ((le_max_right _ bC).trans (le_max_left _ 0))) hE

/-- **Later batch up to `b`** (§2.4): an honest slot-`(s+1)` vote at a time `≤ b` extends a block
`B` that every honest slot-`s` vote extends, compatible with every origin within `b` of label at
most `s`, and extended by the earlier honest slot-`(s+1)` votes. -/
theorem later_transfer_step_upTo (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hrun'.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti := (honest_vote_restarts hrun hnc hy hc hs).2
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  obtain ⟨x, hx, k, e', hv, hvs⟩ := honest_vote_exists_upTo hrun hnc hpre s (by linarith)
  rcases vote_frame_upTo hrun hnc hpre hP hy hc hs hib hB hBc
      ⟨x, hx, k, e', hv, hvs, hall x hx k e' hv hvs⟩ with hvB | hBf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot hr hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  exact vote_extends_of_batch hrun' hy hc hs (Or.inl hvB) hall
    (faults_lt_honest_voters_upTo hrun hnc hpre s (by linarith))
    (honest_batch_carry_upTo hrun hnc hpre hy hc hs hib hall
      (Anc.mono hΦU (hΦ.rooted.2 B hvB.1.1)))
    (vote_locks_compatible_upTo hrun hnc hpre hy hc hs hib hBc hE)

/-- **Later batch** (§2.4): an honest slot-`(s+1)` vote extends a block `B` that every honest
slot-`s` vote extends, compatible with every origin of label at most `s`, and extended by the
earlier honest slot-`(s+1)` votes (an origin of label `j < s` by `V_s` and `P_{s+1}`; a protected
proposal by its common batch, workbench#12 §4, S2P). -/
theorem later_transfer_step (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, Origin tr H C j → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B :=
  later_transfer_step_upTo hrun hnc (hsl.prefix (le_max_right (tr.time i) 0)) (hP.upTo _) hy hc
    hs (le_max_left _ _) hB (fun C j hC hj => hBc C j hC.origin hj) hall hE

/-- **Extending the vote frontier up to `b`**: `P_{s+1}` and `V_s` up to `b` give `V_{s+1}` up
to `b`. -/
theorem votes_below_succ_upTo (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    (hV : VotesBelowUpTo tr H s b) : VotesBelowUpTo tr H (s + 1) b := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  -- the slot-`(s+1)` votes at times `≤ b`, by strong induction on the cut (the first bad vote)
  have key : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → tr.time i ≤ b →
      e.msg.slot = s + 1 → ∀ C j, OriginWithin tr H C j b → j ≤ s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rintro y hy e ⟨ℓ, hc⟩ hib hs C j hC hj
      have hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C :=
        fun x hx k hk e' hv hs' =>
          ih k hk x hx e' hv ((hrun.time_mono hk.le).trans hib) hs' C j hC hj
      rcases hj.lt_or_eq with hj | rfl
      · have hti := (honest_vote_restarts hrun hnc hy hc hs).2
        exact later_transfer_step_upTo hrun hnc hpre hP hy hc hs hib (origin_mem hrun hnc hC.origin)
          (fun C' j' hC' hj' => originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
          (fun x hx k e' hv hs' => votesBelowUpTo_iff.1 hV C j hC x hx k e' hv
            (by linarith [vote_time_le hrun hnc hx hv hs'.le]) (by omega) hs'.le) hE
      · exact first_transfer_step_upTo hrun hnc hpre hP hy hc hs hib hC hE
  refine votesBelowUpTo_iff.2 fun C j hC y hy i e hv hib hj hm => ?_
  rcases Nat.lt_or_ge e.msg.slot (s + 1) with h | h
  · exact votesBelowUpTo_iff.1 hV C j hC y hy i e hv hib hj (by omega)
  · exact key i y hy e hv hib (by omega) C j hC (by omega)

/-- **Extending the vote frontier**: `P_{s+1}` and `V_s` give `V_{s+1}`. -/
theorem votes_below_succ (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1))
    (hV : VotesBelow tr H s) : VotesBelow tr H (s + 1) := by
  refine votesBelow_iff.2 fun C j hC y hy i e hv hj hm => ?_
  obtain ⟨bC, hbC⟩ := hC.exists_within
  exact votesBelowUpTo_iff.1 (votes_below_succ_upTo hrun hnc
    (hsl.prefix (le_max_right (max (tr.time i) bC) 0)) (hP.upTo _) (hV.upTo _)) C j
    (hbC.mono ((le_max_right _ bC).trans (le_max_left _ 0))) y hy i e hv
    ((le_max_left _ bC).trans (le_max_left _ 0)) hj hm

end Consensus.Goldilocks.Compose

end
