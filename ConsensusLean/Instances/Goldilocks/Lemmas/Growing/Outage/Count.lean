module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety under growing faults: the counts

* `compatible_of_head_anc`, `compatible_of_voteCompat`, `compatible_of_anc`: compatibility with
  `B` through a vote head, inside a coherent set of blocks;
* `OutageLockPremises.compatible_of_within`, `vote_extends_pre`: origins and votes within `b₀`
  are compatible with, or extend, `P` (the Sleepy invariant up to `b₀`);
* `OutageVoteInv.voteCompat_of_not_lateWaker_at` (OL-W): a vote of a slot `≥ j₀`, by a node
  honest at its cast, still honest at `z` and not a late waker when the slot is at most `j₀ + k`,
  has a head compatible with `P`;
* `counted_honest_vote_at` (Lemma G at a result): a counted vote of a validator honest at the
  writer's update was cast by it while honest;
* `OutageVoteInv.result_compatible_at` (R): the result of an update of an unpolluted label by a
  node honest at it is compatible with `P`. Every branch counts at the writer's update cut `k`:
  R-pre (within `b₀`), R-j₀ (the slot count at `t_{j₀} + 6Δ`, pre-`b₀` service), R-mid (the cohort
  `A₀` against `(H z)ᶜ ∪ W`, at `t_k ≤ z` by `hzc`), R-late (`late` and the slot count at
  `t_m + 6Δ`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

section Compat

variable {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}

/-- A block below a block compatible with `B` is compatible with `B`. -/
theorem compatible_of_head_anc (hU : Coherent U) {C R B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hCR : Anc U C R) (hR : Compatible U R B) : Compatible U C B := by
  rcases hR with h | h
  · exact Or.inl (hCR.trans h)
  · exact Anc.total hU hCR h

/-- A vote compatible with `B` whose head extends `C` makes `C` compatible with `B`. -/
theorem compatible_of_voteCompat (hU : Coherent U) {v : Vote sp.n}
    {C R B : SA.Blk sp.n (List (FG.Att sp.n))} (hR : R ∈ U) (hRr : R.root = v.head)
    (hCR : Anc U C R) (hv : VoteCompat U v B) : Compatible U C B := by
  obtain ⟨Hd, hHd, hHdr, hHdB⟩ := voteCompat_iff.1 hv
  obtain rfl : Hd = R := hU.1 hHd hR (hHdr.trans hRr.symm)
  exact compatible_of_head_anc hU hCR hHdB

/-- `B ⪯ B'` and `C` compatible with `B'` give `C` compatible with `B`. -/
theorem compatible_of_anc_right (hU : Coherent U) {B B' C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBB' : Anc U B B') (h : Compatible U C B') : Compatible U C B := by
  rcases h with h | h
  · exact Anc.total hU h hBB'
  · exact Or.inr (hBB'.trans h)

end Compat

variable {D : OutageLockPremises tr H proposer dg ini}

/-- A cut of an honest call witnesses an honest call reaching every earlier time. -/
theorem honestCall_mono {t t' : Time}
    (h : ∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ t ≤ tr.time i) (ht : t' ≤ t) :
    ∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ t' ≤ tr.time i :=
  let ⟨x, i, hx, hc, hi⟩ := h
  ⟨x, i, hx, hc, ht.trans hi⟩

/-- A vote of a node honest at its cast is a call of it. -/
theorem HVoteAt.isCall {x : Fin sp.n} {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e) : tr.IsCall x k := by
  obtain ⟨-, ℓ, hc, -⟩ := hVoteAt_iff.1 hv
  exact ⟨_, projAC_callAt.1 hc⟩

/-- The cast of a vote by a node honest then is in `[t_s, t_s + Δ]` of its slot `s`. -/
theorem HVoteAt.ts_le_cast (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e) :
    sp.ts e.msg.slot ≤ tr.time k ∧ tr.time k ≤ sp.ts e.msg.slot + sp.Δ := by
  obtain ⟨hx, ℓ, hc, he⟩ := hVoteAt_iff.1 hv
  have hsl := (castAt_spec_at hrun hnc hx ⟨hc, he⟩).2.1
  exact ⟨(SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) _).2 (by rw [hsl]),
    (cast_head_fcRoot_at hrun hnc hx ⟨hc, he⟩).2⟩

/-- The head of a vote by a node honest at its cast is held while honest. -/
theorem HVoteAt.head_mem (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e) : ∃ Hd ∈ tr.HonestBlocksAt H, Hd.root = e.msg.head := by
  obtain ⟨hx, ℓ, hc, he⟩ := hVoteAt_iff.1 hv
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := cast_head_fcRoot_at hrun hnc hx ⟨hc, he⟩
  exact ⟨Hd, (frameIn_at hrun hnc hx hc).2 hHd, hHdr⟩

/-- A counted vote of a validator honest at the writer's update was cast by it at an earlier
cut at which it was honest, of the update's slot, and its head extends the result inside the
blocks held while honest (Lemma G at the update's pool). -/
theorem counted_honest_vote_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {X : Fin sp.n} {i₀ s : Nat} (hX : X ∈ H (tr.time i₀))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) {v : Vote sp.n} (hv : v ∈ CV)
    (hvH : v.val ∈ H (tr.time i₀)) :
    ∃ j < i₀, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v ∧ v.slot = s ∧
      ∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) C R := by
  obtain ⟨ℓ, hu, -, hCV⟩ := hR
  rw [hCV] at hv
  obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
  obtain ⟨j, hj, e, hve, he⟩ := pool_vote_at hrun hnc hX hvp hvH
  obtain ⟨-, hΦU⟩ := frameIn_at hrun hnc hX hu.1
  exact ⟨j, hj, e, hve, he, state_pool_slot_at hrun hnc hX s v hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

/-- The result of an update by a node honest at it is held while honest. -/
theorem result_mem_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {X : Fin sp.n} {i₀ s : Nat} (hX : X ∈ H (tr.time i₀))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i₀ s C CV) : C ∈ tr.HonestBlocksAt H := by
  obtain ⟨ℓ, hu, hC, -⟩ := hR
  exact (frameIn_at hrun hnc hX hu.1).2 (SA.deepest_mem hC).1.1

namespace OutageLockPremises

theorem coherent (D : OutageLockPremises tr H proposer dg ini) : Coherent (tr.HonestBlocksAt H) :=
  honestBlocksAt_coherent D.hrun D.hnc

/-- `2 f_d < n` at the time of a cut of an honest call. -/
theorem two_faults_lt_at (D : OutageLockPremises tr H proposer dg ini) {x : Fin sp.n} {i : Nat}
    (hx : x ∈ H (tr.time i)) (hc : tr.IsCall x i) : 2 * (H (tr.time i))ᶜ.ncard < sp.n :=
  (D.hB _ ⟨x, i, hx, hc, le_rfl⟩).two _ (D.hrun.time_nonneg i) le_rfl

/-- A genesis `P` is below every block held while honest. -/
theorem anc_of_genesis (D : OutageLockPremises tr H proposer dg ini)
    (hg : D.P.root = sp.genesisRoot)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ tr.HonestBlocksAt H) :
    Anc (tr.HonestBlocksAt H) D.P C := by
  rw [honestAt_eq_genesis D.hrun D.coherent D.hP.1 hg]
  exact (honestAt_genesis_anc D.hrun hC).2

/-- A genesis `P` is extended by every vote of a node honest at its cast. -/
theorem vote_extends_of_genesis (D : OutageLockPremises tr H proposer dg ini)
    (hg : D.P.root = sp.genesisRoot) {x : Fin sp.n} {k : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
  obtain ⟨Hd, hHd, hHdr⟩ := hv.head_mem D.hrun D.hnc
  exact ⟨Hd, hHd, hHdr, D.anc_of_genesis hg hHd⟩

/-- A block held while honest is compatible with `P` when `P` is genesis, and otherwise when it
is compatible with every origin `P` of label `σ` within `b₀`. -/
theorem compatible_of (D : OutageLockPremises tr H proposer dg ini)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ tr.HonestBlocksAt H)
    (h : OriginWithin tr H D.P D.σ D.b₀ → Compatible (tr.HonestBlocksAt H) C D.P) :
    Compatible (tr.HonestBlocksAt H) C D.P := by
  rcases D.hP.2 with hg | hP
  · exact Or.inr (D.anc_of_genesis hg hC)
  · exact h hP

/-- **An origin within `b₀` is compatible with `P`.** -/
theorem compatible_of_within (D : OutageLockPremises tr H proposer dg ini)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s D.b₀) (hCU : C ∈ tr.HonestBlocksAt H) :
    Compatible (tr.HonestBlocksAt H) C D.P :=
  D.compatible_of hCU fun hP => D.hpre.origins_compatible C s D.P D.σ hC hP

/-- **A vote at a time `≤ b₀` of a slot after `σ`, by a node honest at its cast, extends `P`.** -/
theorem vote_extends_pre (D : OutageLockPremises tr H proposer dg ini) {x : Fin sp.n}
    {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e) (hk : tr.time k ≤ D.b₀) (hs : D.σ < e.msg.slot) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
  rcases D.hP.2 with hg | hP
  · exact D.vote_extends_of_genesis hg hv
  · exact D.hpre.vote_extends D.P D.σ hP x k e hv hk hs

end OutageLockPremises

namespace OutageVoteInv

/-- The invariant at `i` gives it at every earlier cut. -/
theorem mono {i i' : Nat} (hinv : OutageVoteInv D i) (hi : i' ≤ i) : OutageVoteInv D i' :=
  ⟨fun x k hk => hinv.votes x k (hk.trans_le hi), fun x k hk => hinv.late x k (hk.trans_le hi)⟩

/-- **OL-W**: at a cut before `i`, a vote of a slot `≥ j₀` by a node honest at its cast has a
head compatible with `P` when, for a slot at most `j₀ + k`, its voter is still honest at `z` and
is not a late waker. -/
theorem voteCompat_of_not_lateWaker_at {i : Nat} (hinv : OutageVoteInv D i) {x : Fin sp.n}
    {k : Nat} (hk : k < i) {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e)
    (hs : D.j₀ ≤ e.msg.slot) (hxz : e.msg.slot ≤ D.j₀ + sp.k → x ∈ H D.z ∧ x ∉ D.W) :
    VoteCompat (tr.HonestBlocksAt H) e.msg D.P := by
  by_cases hlate : D.j₀ + sp.k < e.msg.slot
  · exact hinv.late x k hk e hv hlate
  have hσ := D.hσ
  by_cases hpre : tr.time k ≤ D.b₀ ∨ x ∈ D.A₀
  · exact (hinv.votes x k hk e hv (by omega) (by omega) hpre).voteCompat
  exfalso
  push Not at hpre
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hts, hte⟩ := hv.ts_le_cast D.hrun D.hnc
  obtain ⟨hxz, hxW⟩ := hxz (by omega)
  have hjs : sp.ts D.j₀ ≤ sp.ts e.msg.slot := ts_le_ts hs
  have hsK : sp.ts e.msg.slot ≤ sp.ts (D.j₀ + sp.k : Nat) := ts_le_ts (by omega)
  have hx := (hVoteAt_iff.1 hv).1
  have hz := D.hzc (tr.time k) (by linarith) ⟨x, k, hx, hv.isCall, le_rfl⟩
  have haw := D.hrun.awake_of_call x k hx hv.isCall
  rcases D.hawake x (tr.time k) (by linarith [D.ha]) hz hxz haw with h | h
  · exact hpre.2 h
  · exact hxW h

/-- A member of `A₀` is awake and joined at `t_m + Δ` for a label `m ∈ [j₀ + 1, j₀ + k]` that an
honest call reaches. -/
theorem cohort_ready_at (D : OutageLockPremises tr H proposer dg ini) {x : Fin sp.n}
    (hx : x ∈ D.A₀) {m : Nat} (hm : D.j₀ + 1 ≤ m) (hmK : m ≤ D.j₀ + sp.k)
    (hcall : ∃ y i, y ∈ H (tr.time i) ∧ tr.IsCall y i ∧ sp.ts m + sp.Δ ≤ tr.time i) :
    tr.awake x (sp.ts m + sp.Δ) ∧ tr.JoinedAt x (sp.ts m + sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hj := ts_le_ts (sp := sp) (show D.j₀ ≤ m - 1 by omega)
  have hmK' := ts_le_ts (sp := sp) hmK
  have hm1 : sp.ts (m - 1 : Nat) + 4 * sp.Δ = sp.ts m := by
    simp only [SAParams.ts]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hz := D.hzc (sp.ts m + sp.Δ) (by linarith) hcall
  refine ⟨D.hA₀awake x hx _ (by linarith [D.ha]) hz, fun k hk hkt => ?_⟩
  have hslot : sp.slot (sp.ts m + sp.Δ) = m :=
    SA.slot_of_mem sp m (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  change 0 < sp.slot (sp.ts m + sp.Δ) ∧
    tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
  rw [hslot, sp.slotTime_eq]
  refine ⟨by omega, ?_⟩
  have := (D.hA₀join x hx k hk (hkt.trans hz)).trans D.ha
  have h' : sp.ts (m - 1 : Nat) = 4 * sp.Δ * ((m - 1 : Nat) : Int) := rfl
  rw [← h']
  linarith

/-- The pool of an update of a restored label by a node honest at it holds the slot votes of the
validators honest at `t_m + Δ` that are awake and joined then. -/
private theorem voter_of_ready (D : OutageLockPremises tr H proposer dg ini) {y : Fin sp.n}
    {k m : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hy : y ∈ H (tr.time k)) (hu : SA.UpdateAt tr.projAC y k m ℓ) (hm : D.r ≤ m) {x : Fin sp.n}
    (hx : x ∈ H (sp.ts m + sp.Δ)) (haw : tr.awake x (sp.ts m + sp.Δ))
    (hjn : tr.JoinedAt x (sp.ts m + sp.Δ)) :
    x ∈ SA.voters {v | v ∈ (tr.projAC.state y k).pool m} := by
  obtain ⟨k', e, hve, hes, -⟩ := vote_of_awake_joined_at D.hrun D.hnc hx
    -- TEMP(C2): C3a replaces
    (mayVote_at D.hrun D.hnc (ts_add_delta_nonneg _) hx (D.hmv _ _)) haw hjn
  obtain ⟨hx', ℓ', hc', he'⟩ := hVoteAt_iff.1 hve
  have hval := (castAt_spec_at D.hrun D.hnc hx' ⟨hc', he'⟩).1
  rcases D.PG y k m ℓ hy hu hm x k' e hve hes with hpool | ⟨v, hv, -, -, -, hvx, -⟩
  · rw [← projAC_state_at D.hrun hy] at hpool
    exact ⟨e.msg, hpool, hval⟩
  · rw [← projAC_state_at D.hrun hy] at hv
    exact ⟨v, hv, hvx.trans hval⟩

/-- **(R) at a cut `k ≤ i`**: the result of an update of an unpolluted label by a node honest
at it is compatible with `P`. Each branch counts at the writer's update cut `k`. -/
theorem result_compatible_at {i : Nat} (hinv : OutageVoteInv D i) {y : Fin sp.n} {k : Nat}
    (hk : k ≤ i) (hy : y ∈ H (tr.time k)) {m : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt tr.projAC y k m C CV) (hm : m ≤ D.j₀ ∨ D.r ≤ m) :
    Compatible (tr.HonestBlocksAt H) C D.P := by
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hCU := result_mem_at D.hrun D.hnc hy hR
  obtain ⟨ℓ, hu, -, -⟩ := id hR
  have ht : tr.time k = sp.ts m + 6 * sp.Δ := hu.2.2.1
  have hcallk : tr.IsCall y k := ⟨_, projAC_callAt.1 hu.1⟩
  have hcall : ∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ tr.time k ≤ tr.time i :=
    ⟨y, k, hy, hcallk, le_rfl⟩
  have hj₀ := D.hj₀
  have hrk := D.hrk
  have hσ := D.hσ
  -- a counted vote honest at `k` and compatible with `P` makes `C` compatible with `P`
  have finish : ∀ v ∈ CV, v.val ∈ H (tr.time k) →
      (∀ j < k, ∀ e, HVoteAt tr H v.val j e → e.msg = v → e.msg.slot = m →
        VoteCompat (tr.HonestBlocksAt H) e.msg D.P) →
      Compatible (tr.HonestBlocksAt H) C D.P := by
    intro v hv hvH hcompat
    obtain ⟨j, hj, e, hve, rfl, hvs, R, hRU, hRr, hCR⟩ :=
      counted_honest_vote_at D.hrun D.hnc hy hR hv hvH
    exact compatible_of_voteCompat hU hRU hRr hCR (hcompat j hj e hve rfl hvs)
  -- the slot count at the writer's update
  have hslot : (H (tr.time k))ᶜ.ncard < {x | x ∈ H (tr.time k) ∧ tr.awake x (sp.ts m + sp.Δ) ∧
      tr.JoinedAt x (sp.ts m + sp.Δ)}.ncard :=
    (D.hB _ hcall).slot m (tr.time k) (Nat.zero_le _) (by rw [ht]; linarith) le_rfl ht.le
  rcases lt_or_ge m D.j₀ with hlt | hge
  · -- R-pre: the update is within `b₀`
    have hmj : sp.ts m + 6 * sp.Δ ≤ D.b₀ := by
      have := ts_le_ts (sp := sp) (show m + 1 ≤ D.j₀ by omega)
      have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith
    exact D.compatible_of_within (OriginWithin.of_result hy (ht ▸ hmj) hR) hCU
  rcases hm with hm | hm
  · -- R-j₀: the voters awake and joined at `t_{j₀} + Δ` and honest at the update reach it by the
    -- early cutoff `≤ b₀`
    have hmeq : m = D.j₀ := le_antisymm hm hge
    have hd := D.hrun.time_nonneg k
    have hsvc := (SleepyServiceBefore.upTo D.hrun D.hpreSvc hd).ac
    have hT : {x | x ∈ H (tr.time k) ∧ tr.awake x (sp.ts m + sp.Δ) ∧
        tr.JoinedAt x (sp.ts m + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state y k).pool m} := fun x hx => by
      have h := awake_participant_early (D.hrun.upTo hd) (D.hnc.upTo _) hsvc
        (le_min (hmeq ▸ hj₀.1) (by rw [ht]; linarith)) hy
        (by rw [RunTrace.upTo_projAC]; exact (sa_updateAt_upTo D.hrun.time_mono).mpr ⟨le_rfl, hu⟩)
        hx.1 -- TEMP(C2): C3a replaces
        (mayVote_of_start (D.hrun.upTo hd) (D.hnc.upTo _) hx.1 (D.hmv _ _))
        ⟨hx.2.1, by rw [ht]; linarith⟩
        (joinedAt_upTo hx.2.2)
      rwa [RunTrace.upTo_projAC, projAC_upTo_state D.hrun le_rfl] at h
    obtain ⟨v, hv, hvT⟩ := Compose.exists_counted_of_participants hR hT hslot
    have hvH : v.val ∈ H (tr.time k) := hvT.elim (fun h => h.1) not_not.1
    refine finish v hv hvH fun j hj e hve he hs => ?_
    obtain ⟨-, hte⟩ := hve.ts_le_cast D.hrun D.hnc
    rw [hs, hmeq] at hte
    exact (hinv.votes v.val j (by omega) e hve (by omega) (by omega)
      (Or.inl (by linarith))).voteCompat
  rcases le_or_gt m (D.j₀ + sp.k) with hmK | hmK
  · -- R-mid: `A₀` votes in slot `m` and extends `P`; the counted set is in `(H z)ᶜ ∪ W`, at
    -- the update's time `t_m + 6Δ ≤ z`
    have hkz : tr.time k ≤ D.z :=
      D.hzc _ (by rw [ht]; linarith [ts_le_ts (sp := sp) hmK]) hcall
    have hT : D.A₀ ⊆ SA.voters {v | v ∈ (tr.projAC.state y k).pool m} := by
      intro x hx
      have hcm := honestCall_mono hcall (show sp.ts m + sp.Δ ≤ tr.time k by rw [ht]; linarith)
      obtain ⟨haw, hjn⟩ := cohort_ready_at D hx (by omega) hmK hcm
      exact voter_of_ready D hy hu hm
        (D.hrun.antitone (D.hzc _ (by linarith [ts_le_ts (sp := sp) hmK]) hcm) (D.hA₀ hx)) haw hjn
    obtain ⟨v, hv, hvT⟩ := Compose.exists_counted_of_participants hR hT D.hcohort
    have hvz : v.val ∈ H D.z := by
      rcases hvT with h | h
      · exact D.hA₀ h
      · by_contra hn; exact h (Or.inl hn)
    refine finish v hv (D.hrun.antitone hkz hvz) fun j hj e hve he hs => ?_
    rcases hvT with hA | hQ
    · exact (hinv.votes v.val j (by omega) e hve (by omega) (by omega) (Or.inr hA)).voteCompat
    · exact hinv.voteCompat_of_not_lateWaker_at (by omega) hve (by omega)
        fun _ => ⟨hvz, fun h => hQ (Or.inr h)⟩
  · -- R-late: every slot-`m` vote is compatible with `P` (`late`); the validators honest at the
    -- update and awake and joined at `t_m + Δ` reach it
    have hT : {x | x ∈ H (tr.time k) ∧ tr.awake x (sp.ts m + sp.Δ) ∧
        tr.JoinedAt x (sp.ts m + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state y k).pool m} := fun x hx =>
      voter_of_ready D hy hu hm (D.hrun.antitone (by rw [ht]; linarith) hx.1) hx.2.1 hx.2.2
    obtain ⟨v, hv, hvT⟩ := Compose.exists_counted_of_participants hR hT hslot
    have hvH : v.val ∈ H (tr.time k) := hvT.elim (fun h => h.1) not_not.1
    exact finish v hv hvH fun j hj e hve he hs => hinv.late v.val j (by omega) e hve (by omega)

end OutageVoteInv

end Consensus.Goldilocks.Compose.Growing

end
