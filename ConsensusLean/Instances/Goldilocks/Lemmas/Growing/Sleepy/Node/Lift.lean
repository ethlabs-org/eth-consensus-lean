module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest

public section

/-! # Goldilocks under `Sleepy` with growing faults: lifting static facts to the prefix

The tools that apply a static fact to the prefix `tr.upTo d` with the honest set `H d`
(`Growing.GoldilocksRun.upTo`, `0 ≤ d`) and carry its hypotheses and conclusions across:

* the blocks held while honest: membership at a cut of a node honest then, their coherence, and
  genesis below each of them;
* the AC trace of the prefix (`tr.projAC.upTo d`) at cuts at times `≤ d`: restarts, acceptances,
  processing, sends, wakes and deadlines, the SA events (votes, results, optimistic selections) and
  the retained and fresh message service;
* the transport of the finite service (`SleepyServiceBefore.upTo`) and of the slot count
  (`faultBound_upTo`);
* the origin chain (`OnOriginChainWithin.compatible`, `OnOriginChainWithin.of_anc`), the σ-copies
  of `Compose/Sleepy/Chain`.

Ancestry comes down into the prefix by `RunTrace.anc_upTo_of_right`; conclusions go back up by
`Anc.mono` with `RunTrace.honestBlocks_upTo_subset`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

/-! ### The AC trace of the prefix -/

section ACUpTo

variable {P : Params} {FGP : Type} {A : ACInterface P FGP} (trA : ACTrace A) {d : Time}

theorem ac_restartAt_upTo {y : Fin P.n} {k : Nat} :
    ACTrace.RestartAt (trA.upTo d) y k ↔ trA.time k ≤ d ∧ ACTrace.RestartAt trA y k := by
  simp only [ACTrace.RestartAt, Trace.upTo_callAt]
  exact ⟨fun ⟨ℓ, ⟨h, hc⟩, hl⟩ => ⟨h, ℓ, hc, hl⟩, fun ⟨h, ℓ, hc, hl⟩ => ⟨ℓ, ⟨h, hc⟩, hl⟩⟩

theorem ac_acceptAt_upTo {y : Fin P.n} {k : Nat} {B : A.Blk} :
    ACTrace.AcceptAt (trA.upTo d) y k B ↔ trA.time k ≤ d ∧ ACTrace.AcceptAt trA y k B := by
  simp only [ACTrace.AcceptAt, Trace.upTo_callAt]
  exact ⟨fun ⟨ℓ, ⟨h, hc⟩, hl⟩ => ⟨h, ℓ, hc, hl⟩, fun ⟨h, ℓ, hc, hl⟩ => ⟨ℓ, ⟨h, hc⟩, hl⟩⟩

theorem ac_processAt_upTo {y : Fin P.n} {k : Nat} {m : A.Msg} :
    ACTrace.ProcessAt (trA.upTo d) y k m ↔ trA.time k ≤ d ∧ ACTrace.ProcessAt trA y k m := by
  simp only [ACTrace.ProcessAt, Trace.upTo_callAt]
  exact ⟨fun ⟨ℓ, ⟨h, hc⟩, hl⟩ => ⟨h, ℓ, hc, hl⟩, fun ⟨h, ℓ, hc, hl⟩ => ⟨ℓ, ⟨h, hc⟩, hl⟩⟩

variable {trA}

theorem ac_state_upTo (hmono : Monotone trA.time) {y : Fin P.n} {i : Nat} (hi : trA.time i ≤ d) :
    (trA.upTo d).state y i = trA.state y i :=
  Trace.upTo_state trA y fun _ hk => (hmono hk.le).trans hi

theorem ac_sendOrAdmit_upTo (hmono : Monotone trA.time) {x : Fin P.n} {i : Nat} {m : A.Msg} :
    ACTrace.SendOrAdmit (trA.upTo d) x i m ↔ trA.time i ≤ d ∧ ACTrace.SendOrAdmit trA x i m := by
  simp only [ACTrace.SendOrAdmit, Trace.upTo_callAt]
  constructor
  · rintro ⟨ℓ, ⟨h, hc⟩, hm⟩
    rw [ac_state_upTo hmono h] at hm
    exact ⟨h, ℓ, hc, hm⟩
  · rintro ⟨h, ℓ, hc, hm⟩
    rw [← ac_state_upTo hmono h] at hm
    exact ⟨ℓ, ⟨h, hc⟩, hm⟩

theorem ac_lastWake_upTo (hmono : Monotone trA.time) (y : Fin P.n) :
    ∀ {k : Nat}, trA.time k ≤ d → ACTrace.lastWake (trA.upTo d) y k = ACTrace.lastWake trA y k
  | 0, h => by
    unfold ACTrace.lastWake
    by_cases hr : ACTrace.RestartAt trA y 0
    · have hr' : ACTrace.RestartAt (trA.upTo d) y 0 := (ac_restartAt_upTo trA).mpr ⟨h, hr⟩
      simp only [hr, hr', ite_true]
      rfl
    · have hr' : ¬ ACTrace.RestartAt (trA.upTo d) y 0 :=
        fun h' => hr ((ac_restartAt_upTo trA).mp h').2
      simp only [hr, hr', ite_false]
  | k + 1, h => by
    have ih := ac_lastWake_upTo hmono y (k := k) ((hmono (Nat.le_succ k)).trans h)
    unfold ACTrace.lastWake
    by_cases hr : ACTrace.RestartAt trA y (k + 1)
    · have hr' : ACTrace.RestartAt (trA.upTo d) y (k + 1) := (ac_restartAt_upTo trA).mpr ⟨h, hr⟩
      simp only [hr, hr', ite_true]
      rfl
    · have hr' : ¬ ACTrace.RestartAt (trA.upTo d) y (k + 1) :=
        fun h' => hr ((ac_restartAt_upTo trA).mp h').2
      simp only [hr, hr', ite_false]
      exact ih

theorem ac_deadline_upTo (hmono : Monotone trA.time) {y : Fin P.n} {k : Nat}
    (h : trA.time k ≤ d) (τ : Time) :
    ACTrace.deadline (trA.upTo d) y k τ = ACTrace.deadline trA y k τ := by
  simp only [ACTrace.deadline, ac_lastWake_upTo hmono y h]

end ACUpTo

section SAUpTo

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {trS : SA.SATrace sp FGP ro}
  {d : Time}

theorem sa_voteAt_upTo {y : Fin sp.n} {i : Nat} {e : SA.Em sp FGP} :
    SA.VoteAt (trS.upTo d) y i e ↔ trS.time i ≤ d ∧ SA.VoteAt trS y i e := by
  simp only [SA.VoteAt, Trace.upTo_callAt]
  exact ⟨fun ⟨ℓ, ⟨h, hc⟩, hl⟩ => ⟨h, ℓ, hc, hl⟩, fun ⟨h, ℓ, hc, hl⟩ => ⟨ℓ, ⟨h, hc⟩, hl⟩⟩

theorem sa_castAt_upTo {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    {e : SA.Em sp FGP} :
    SA.CastAt (trS.upTo d) y i ℓ e ↔ trS.time i ≤ d ∧ SA.CastAt trS y i ℓ e := by
  simp only [SA.CastAt, Trace.upTo_callAt, and_assoc]

theorem sa_updateAt_upTo (hmono : Monotone trS.time) {x : Fin sp.n} {i s : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} :
    SA.UpdateAt (trS.upTo d) x i s ℓ ↔ trS.time i ≤ d ∧ SA.UpdateAt trS x i s ℓ := by
  simp only [SA.UpdateAt, Trace.upTo_callAt]
  constructor
  · rintro ⟨⟨h, hc⟩, hl, ht, hj⟩
    rw [ac_state_upTo hmono h] at hj
    exact ⟨h, hc, hl, ht, hj⟩
  · rintro ⟨h, hc, hl, ht, hj⟩
    rw [← ac_state_upTo hmono h] at hj
    exact ⟨⟨h, hc⟩, hl, ht, hj⟩

theorem sa_resultAt_upTo (hmono : Monotone trS.time) {x : Fin sp.n} {i s : Nat}
    {C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)} :
    SA.ResultAt (trS.upTo d) x i s C CV ↔ trS.time i ≤ d ∧ SA.ResultAt trS x i s C CV := by
  simp only [SA.ResultAt]
  constructor
  · rintro ⟨ℓ, hu, hc, hCV⟩
    obtain ⟨h, hu⟩ := (sa_updateAt_upTo hmono).mp hu
    rw [ac_state_upTo hmono h] at hc hCV
    exact ⟨h, ℓ, hu, hc, hCV⟩
  · rintro ⟨h, ℓ, hu, hc, hCV⟩
    rw [← ac_state_upTo hmono h] at hc hCV
    exact ⟨ℓ, (sa_updateAt_upTo hmono).mpr ⟨h, hu⟩, hc, hCV⟩

theorem sa_optimisticLockAt_upTo (hmono : Monotone trS.time) {x : Fin sp.n} {i s : Nat}
    {C : SA.Blk sp.n FGP} {CV : Set (Vote sp.n)} :
    SA.OptimisticLockAt (trS.upTo d) x i s C CV ↔
      trS.time i ≤ d ∧ SA.OptimisticLockAt trS x i s C CV := by
  simp only [SA.OptimisticLockAt, SA.OptimisticPoint, Trace.upTo_callAt]
  constructor
  · rintro ⟨ℓ, A, ⟨⟨h, hc⟩, hA⟩, hs⟩
    rw [ac_state_upTo hmono h] at hA
    exact ⟨h, ℓ, A, ⟨hc, hA⟩, hs⟩
  · rintro ⟨h, ℓ, A, ⟨hc, hA⟩, hs⟩
    rw [← ac_state_upTo hmono h] at hA
    exact ⟨ℓ, A, ⟨⟨h, hc⟩, hA⟩, hs⟩

theorem sa_retainedBefore_upTo (hmono : Monotone trS.time) {y : Fin sp.n} {j : Nat}
    (hj : trS.time j ≤ d) {v : Vote sp.n} {T : Time} (h : SA.RetainedBefore trS y j v T) :
    SA.RetainedBefore (trS.upTo d) y j v T := by
  obtain ⟨q, hqj, hq, hr⟩ := (SA.retainedBefore_iff _ _ _ _).mp h
  refine (SA.retainedBefore_iff _ _ _ _).mpr ⟨q, hqj, ?_, fun r h1 h2 hrr => hr r h1 h2
    ((ac_restartAt_upTo trS).mp hrr).2⟩
  rwa [ac_state_upTo hmono ((hmono hqj).trans hj)]

theorem sa_messageServedBefore_upTo (hmono : Monotone trS.time) {y : Fin sp.n} {j : Nat}
    (hj : trS.time j ≤ d) {τ : Time} {v : Vote sp.n} (h : SA.MessageServedBefore trS y j τ v) :
    SA.MessageServedBefore (trS.upTo d) y j τ v := by
  rcases (SA.messageServedBefore_iff _ _ _ _).mp h with ⟨k, hkj, hk0, hk, hkd⟩ | hr
  · have hkd' : trS.time k ≤ d := (hmono hkj).trans hj
    exact (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inl ⟨k, hkj, hk0,
      (ac_processAt_upTo trS).mpr ⟨hkd', hk⟩, by rw [ac_deadline_upTo hmono hkd']; exact hkd⟩)
  · refine (SA.messageServedBefore_iff _ _ _ _).mpr (Or.inr ?_)
    rw [ac_deadline_upTo hmono hj]
    exact sa_retainedBefore_upTo hmono hj hr

end SAUpTo

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {d : Time}

/-! ### The blocks held while honest -/

/-- A block of the tree of a node honest at cut `i`, before `i`, is held while honest. -/
theorem mem_honestBlocksAt (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.tree) : B ∈ tr.HonestBlocksAt H :=
  ⟨y, i, tr.time i, hrun.time_nonneg i, fun _ hk => hrun.time_mono hk.le, hy, hB⟩

/-- The prefix's honest blocks are held while honest. -/
theorem upTo_subset (hrun : Growing.GoldilocksRun proposer dg H tr) (hd : 0 ≤ d) :
    (tr.upTo d).HonestBlocks (H d) ⊆ tr.HonestBlocksAt H :=
  RunTrace.honestBlocks_upTo_subset hrun.time_mono hd

/-- Every block held while honest is held in the prefix through the time it is held at. -/
theorem exists_upTo_of_mem {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H) :
    ∃ t, 0 ≤ t ∧ B ∈ (tr.upTo t).HonestBlocks (H t) := by
  obtain ⟨y, i, t, ht, hi, hy, hBt⟩ := hB
  exact ⟨t, ht, y, hy, i, by rw [Trace.upTo_state tr y hi]; exact hBt⟩

/-- **The blocks held while honest are coherent** under `NoColl` (stand-in for the Compose
growing-fault coherence lemma). -/
theorem honestBlocksAt_coherent (_hrun : Growing.GoldilocksRun proposer dg H tr)
    (_hnc : NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) := by
  sorry

/-- Genesis is held while honest, below every block held while honest. -/
theorem honestAt_genesis_anc (hrun : Growing.GoldilocksRun proposer dg H tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H) :
    sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∈ tr.HonestBlocksAt H ∧
      Anc (tr.HonestBlocksAt H)
        (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B := by
  obtain ⟨t, ht, hBt⟩ := exists_upTo_of_mem hB
  obtain ⟨hg, hanc⟩ := honest_genesis_anc (hrun.upTo ht) hBt
  exact ⟨upTo_subset hrun ht hg, hanc.mono (upTo_subset hrun ht)⟩

/-- A block held while honest with the genesis root is genesis. -/
theorem honestAt_eq_genesis (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hU : Coherent (tr.HonestBlocksAt H)) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocksAt H) (hr : B.root = sp.genesisRoot) :
    B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
  hU.1 hB (honestAt_genesis_anc hrun hB).1 hr

/-- Genesis has no parent, so its only ancestor is itself. -/
private theorem anc_genesis {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {A : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc S A (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)) :
    A = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, -, hY⟩
  · exact heq.symm
  · exact absurd hY.2.2 (by simp [Params.genesisBlock])

/-- Compatibility of two blocks of the prefix's honest blocks comes down into the prefix
(`RunTrace.anc_upTo_of_right`). -/
theorem compatible_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hd : 0 ≤ d) {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.upTo d).HonestBlocks (H d)) (hC : C ∈ (tr.upTo d).HonestBlocks (H d))
    (h : Compatible (tr.HonestBlocksAt H) B C) : Compatible ((tr.upTo d).HonestBlocks (H d)) B C :=
  h.imp (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hC)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hB)

/-- A vote extension of a vote cast in the prefix by a node honest at `d` comes down into the
prefix: the vote's head is held by its voter. -/
theorem voteExtends_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hd : 0 ≤ d) {x : Fin sp.n} (hx : x ∈ H d) {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt (tr.upTo d).projAC x k e) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.VoteExtends (tr.HonestBlocksAt H) e.msg C) :
    SA.VoteExtends ((tr.upTo d).HonestBlocks (H d)) e.msg C := by
  obtain ⟨Hd, hHd, hHdr, hCHd⟩ := h
  obtain ⟨Hd₂, hHd₂, hHd₂r, -⟩ := SA.honest_head
    (goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer (hrun.upTo hd) (hnc.upTo d))
    hx hv
  obtain rfl : Hd = Hd₂ := (honestBlocksAt_coherent hrun hnc).1 hHd (upTo_subset hrun hd hHd₂)
    (hHdr.trans hHd₂r.symm)
  exact ⟨Hd, hHd₂, hHdr, RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHd₂ hCHd⟩

/-! ### The origin chain (σ-copies of `Compose/Sleepy/Chain`) -/

/-- Blocks below tips that are pairwise compatible (`Q`) or genesis are compatible. -/
private theorem chain_compatible (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {Q : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hcomp : ∀ C s C' s', Q C s → Q C' s' → Compatible (tr.HonestBlocksAt H) C C')
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H)
    (hB' : B' ∈ tr.HonestBlocksAt H)
    (h : B.root = sp.genesisRoot ∨ ∃ C s, Q C s ∧ Anc (tr.HonestBlocksAt H) B C)
    (h' : B'.root = sp.genesisRoot ∨ ∃ C s, Q C s ∧ Anc (tr.HonestBlocksAt H) B' C) :
    Compatible (tr.HonestBlocksAt H) B B' := by
  have hU := honestBlocksAt_coherent hrun hnc
  rcases h with hg | ⟨C, s, hC, hBC⟩
  · rw [honestAt_eq_genesis hrun hU hB hg]
    exact Or.inl (honestAt_genesis_anc hrun hB').2
  rcases h' with hg' | ⟨C', s', hC', hBC'⟩
  · rw [honestAt_eq_genesis hrun hU hB' hg']
    exact Or.inr (honestAt_genesis_anc hrun hB).2
  rcases hcomp C s C' s' hC hC' with hCC | hCC
  · exact Anc.total hU (hBC.trans hCC) hBC'
  · exact Anc.total hU hBC (hBC'.trans hCC)

/-- **Blocks on the chain of the origins within `b` are compatible** when those origins are. -/
theorem OnOriginChainWithin.compatible (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time}
    (hcomp : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
      Compatible (tr.HonestBlocksAt H) C C')
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H)
    (hB' : B' ∈ tr.HonestBlocksAt H) (h : OnOriginChainWithin tr H B b)
    (h' : OnOriginChainWithin tr H B' b) : Compatible (tr.HonestBlocksAt H) B B' :=
  chain_compatible hrun hnc (Q := fun C s => OriginWithin tr H C s b) hcomp hB hB'
    (onOriginChainWithin_iff.1 h) (onOriginChainWithin_iff.1 h')

/-- **An ancestor of a block on the chain of the origins within `b` is on it.** -/
theorem OnOriginChainWithin.of_anc (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} {A B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : A ∈ tr.HonestBlocksAt H) (hAB : Anc (tr.HonestBlocksAt H) A B)
    (h : OnOriginChainWithin tr H B b) : OnOriginChainWithin tr H A b := by
  rcases onOriginChainWithin_iff.1 h with hg | ⟨C, s, hC, hBC⟩
  · have hBU : B ∈ tr.HonestBlocksAt H := by
      by_cases hne : A = B
      · exact hne ▸ hA
      · exact (hAB.mem hne).2
    rw [honestAt_eq_genesis hrun (honestBlocksAt_coherent hrun hnc) hBU hg] at hAB
    exact onOriginChainWithin_iff.2 (Or.inl (by rw [anc_genesis hAB]; rfl))
  · exact onOriginChainWithin_iff.2 (Or.inr ⟨C, s, hC, hAB.trans hBC⟩)

/-! ### Transport of the premises -/

/-- In the prefix, a node joined at `t` in the run is joined at `t`. -/
theorem joinedAt_upTo {y : Fin sp.n} {t : Time} (h : tr.JoinedAt y t) :
    (tr.upTo d).JoinedAt y t :=
  fun k hk hkt => h k ((RunTrace.upTo_restartAt tr).mp hk).2 hkt

/-- **The slot count in the prefix**: `f_d < h_τ` (charged at `d`) is the static count `f < h_τ`
of the prefix through `d` for the validators honest at `d`, when `τ ≤ d`. -/
theorem faultBound_upTo {τ : Time} (hτ : τ ≤ d) (h : tr.FaultBoundAt H τ d) :
    (tr.upTo d).FaultBound (H d) τ :=
  lt_of_lt_of_le h (Set.ncard_le_ncard (fun _ hx => ⟨hx.1, ⟨hx.2.1, hτ⟩, joinedAt_upTo hx.2.2⟩)
    (Set.toFinite _))

/-- **Transport of the finite service** to the prefix through `d ≥ 0`, for the validators
honest at `d`, with the deadline bound `min b d`. -/
theorem SleepyServiceBefore.upTo (hrun : Growing.GoldilocksRun proposer dg H tr) {ΔF b : Time}
    (h : SleepyServiceBefore tr H ΔF b) (hd : 0 ≤ d) :
    Compose.SleepyServiceBefore (tr.upTo d) (H d) ΔF (min b d) := by
  have hm := hrun.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => hrun.antitone ht
  have hsub := upTo_subset hrun hd
  refine ⟨h.deltaF, ?_, fun x hx i B hB h0 y hy j hc hdb hdj ha => ?_⟩
  · rw [RunTrace.upTo_projAC]
    refine ⟨fun x hx i v hv h0 y hy j ℓ hc hdb hdj => ?_,
      fun x hx i B hB h0 y hy j ℓ hc hdb hdj ha => ?_⟩
    · obtain ⟨hid, hv⟩ := (ac_sendOrAdmit_upTo hm).mp hv
      obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
      rw [ac_deadline_upTo hm hjd] at hdb hdj
      exact sa_messageServedBefore_upTo hm hjd
        (h.message x i v (anti hid hx) hv h0 y j ℓ (anti hjd hy) hc (hdb.trans (min_le_left _ _))
          hdj)
    · obtain ⟨hid, hB⟩ := (ac_acceptAt_upTo _).mp hB
      obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
      rw [ac_deadline_upTo hm hjd] at hdb hdj
      obtain ⟨k, hkj, hk, hkt⟩ := h.acRelay x i B (anti hid hx) hB h0 y j ℓ (anti hjd hy) hc
        (hdb.trans (min_le_left _ _)) hdj (ha.mono hsub)
      have hkd : tr.time k ≤ d := (hm hkj).trans hjd
      exact ⟨k, hkj, (ac_acceptAt_upTo _).mpr ⟨hkd, hk⟩,
        by rw [ac_deadline_upTo hm hkd]; exact hkt⟩
  · obtain ⟨hid, hB⟩ := (RunTrace.upTo_acceptAt _).mp hB
    obtain ⟨hjd, hc⟩ := (RunTrace.upTo_isCall _).mp hc
    rw [RunTrace.upTo_deadline hm hjd] at hdb hdj
    rw [RunTrace.upTo_state_of_le hm hjd] at ha
    obtain ⟨k, hkj, hk, hkt⟩ := h.relay x i B (anti hid hx) hB h0 y j (anti hjd hy) hc
      (hdb.trans (min_le_left _ _)) hdj (ha.mono hsub)
    have hkd : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (RunTrace.upTo_acceptAt _).mpr ⟨hkd, hk⟩,
      by rw [RunTrace.upTo_deadline hm hkd]; exact hkt⟩

end Consensus.Goldilocks.Compose.Growing

end
