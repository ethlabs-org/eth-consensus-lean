module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock

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
  of `Compose/Sleepy/Chain`;
* node-local AC facts at a cut, lifted at the cut's time; the stored locks below the holder's own
  lock writes (`lock_write_at`), and each lock write below an origin of its label
  (`lock_below_origin_at`).

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

/-- **The blocks held while honest are coherent** under `NoColl` (`honest_blocks_coherent`). -/
theorem honestBlocksAt_coherent (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) :=
  honest_blocks_coherent hrun hnc

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

/-- **Transport of the AC service from `a`** to the prefix through `d ≥ 0`: the static AC service
window from `a` of the validators honest at `d`, with the deadline bound `min b d`. -/
theorem SleepyServiceFrom.acWindow_upTo (hrun : Growing.GoldilocksRun proposer dg H tr)
    {ΔF a κ b : Time} (h : SleepyServiceFrom tr H ΔF a κ b) (hd : 0 ≤ d) :
    SA.ServiceWindowBefore (H d) ((tr.upTo d).HonestBlocks (H d)) a (min b d)
      (tr.upTo d).projAC := by
  have hm := hrun.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => hrun.antitone ht
  have hsub := upTo_subset hrun hd
  rw [RunTrace.upTo_projAC]
  refine ⟨fun x hx i v hv hai y hy j ℓ hc hdb hdj => ?_,
    fun x hx i B hB hai y hy j ℓ hc hdb hdj ha => ?_⟩
  · obtain ⟨hid, hv⟩ := (ac_sendOrAdmit_upTo hm).mp hv
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ac_deadline_upTo hm hjd] at hdb hdj
    exact sa_messageServedBefore_upTo hm hjd
      (h.message x i v (anti hid hx) hv hai y j ℓ (anti hjd hy) hc (hdb.trans (min_le_left _ _))
        hdj)
  · obtain ⟨hid, hB⟩ := (ac_acceptAt_upTo _).mp hB
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ac_deadline_upTo hm hjd] at hdb hdj
    obtain ⟨k, hkj, hk, hkt⟩ := h.acRelay x i B (anti hid hx) hB hai y j ℓ (anti hjd hy) hc
      (hdb.trans (min_le_left _ _)) hdj (ha.mono hsub)
    have hkd : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (ac_acceptAt_upTo _).mpr ⟨hkd, hk⟩,
      by rw [ac_deadline_upTo hm hkd]; exact hkt⟩

/-! ### Node-local AC facts at a cut (lifted at the time of the cut) -/

/-- The AC state of the prefix before a cut at a time `≤ d` is the run's. -/
theorem projAC_upTo_state (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {i : Nat} (hi : tr.time i ≤ d) : (tr.projAC.upTo d).state y i = tr.projAC.state y i :=
  ac_state_upTo (trA := tr.projAC) hrun.time_mono hi

/-- **The AC run of the prefix** through `d ≥ 0`, for the validators honest at `d`. -/
theorem acRun_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hd : 0 ≤ d) :
    SA.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) := by
  have h := goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer (hrun.upTo hd) (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- A frame of a call of a node honest then is well formed, inside the blocks held while honest. -/
theorem frameIn_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H :=
  have h := SA.frameIn_of_callAt (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  ⟨h.1, h.2.trans (upTo_subset hrun (hrun.time_nonneg i))⟩

/-- The frame of a call of a node honest then is in the prefix's honest blocks at its time. -/
theorem frame_upTo_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) :
    ℓ.frame.tree ⊆ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
  (SA.frameIn_of_callAt (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)).2

theorem castAt_spec_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ SA.joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (SA.getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (SA.voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (SA.mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root :=
  SA.castAt_spec (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    (sa_castAt_upTo.mpr ⟨le_rfl, hc⟩)

theorem cast_head_fcRoot_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e) :
    (∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc ℓ.frame.fcRoot Hd) ∧
      tr.time i ≤ sp.ts e.msg.slot + sp.Δ :=
  cast_head_fcRoot (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    (sa_castAt_upTo.mpr ⟨le_rfl, hc⟩)

theorem frame_of_projAC_at (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) : ℓ.frame = Node.frame (tr.state y i) := by
  have h := frame_of_projAC (hrun.upTo (hrun.time_nonneg i)) hy
    (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

theorem projAC_state_at (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) : tr.projAC.state y i = (tr.state y i).ac := by
  have h := projAC_state (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy i
  rwa [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl,
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

theorem frame_slot_le_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) : ∀ B ∈ ℓ.frame.tree, B.slot ≤ sp.slot (tr.time i) :=
  SA.frame_slot_le sp (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)

theorem state_pool_slot_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (σ : Nat) :
    ∀ v ∈ (tr.projAC.state y i).pool σ, v.slot = σ := by
  have h := SA.state_pool_slot sp (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy i σ
  rwa [projAC_upTo_state hrun le_rfl] at h

/-- **Lemma G at a pool**: a vote of the pool of a node honest at cut `i` whose validator is honest
at `i` was cast by it, at a cut at which it was honest. -/
theorem pool_vote_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {σ : Nat} {v : Vote sp.n}
    (hv : v ∈ (tr.projAC.state y i).pool σ) (hvH : v.val ∈ H (tr.time i)) :
    ∃ j < i, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v := by
  have hm := hrun.time_mono
  obtain ⟨j, hj, e, hve, hev⟩ := (acRun_upTo hrun hnc (hrun.time_nonneg i)).honest.pool_vote y hy
    i σ v (by rw [projAC_upTo_state hrun le_rfl]; exact hv) hvH
  obtain ⟨hjd, hve⟩ := sa_voteAt_upTo.mp hve
  exact ⟨j, hj, e, hVoteAt_iff.2 ⟨hrun.antitone hjd hvH, hve⟩, hev⟩

/-- **One vote per slot** of a node honest at both casts. -/
theorem one_vote_per_slot_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {j j' : Nat} {e e' : SA.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x j e) (hv' : HVoteAt tr H x j' e') (hs : e.msg.slot = e'.msg.slot) :
    j = j' ∧ e = e' := by
  wlog hjj : j ≤ j' generalizing j j' e e'
  · obtain ⟨h1, h2⟩ := this hv' hv hs.symm (by omega)
    exact ⟨h1.symm, h2.symm⟩
  have hd := hrun.time_nonneg j'
  have hjd := hrun.time_mono hjj
  have hr := (acRun_upTo hrun hnc hd).localRun
  exact SA.one_vote_per_slot sp _ ro _ _ _ hr x (hVoteAt_iff.1 hv').1 j j' e e'
    (sa_voteAt_upTo.mpr ⟨hjd, (hVoteAt_iff.1 hv).2⟩)
    (sa_voteAt_upTo.mpr ⟨le_rfl, (hVoteAt_iff.1 hv').2⟩) hs

/-- Every ancestor (held while honest) of a block of the frame of a call is genesis or was
accepted by the caller by then. -/
theorem frame_anc_accepted_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ℓ)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXB : Anc (tr.HonestBlocksAt H) X B) :
    X.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.projAC.AcceptAt y k X := by
  have hd := hrun.time_nonneg i
  rcases frame_anc_accepted (acRun_upTo hrun hnc hd).localRun hy i ℓ
      ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) B hB X
      (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd (frame_upTo_at hrun hnc hy hc hB) hXB)
    with h | ⟨k, hk, hA⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk, ((ac_acceptAt_upTo _).mp hA).2⟩

/-- A node honest at `t_s + Δ`, awake and joined then, casts a slot-`s` vote by then, at a cut at
which it is honest. -/
theorem vote_of_awake_joined_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {s : Nat} (hy : y ∈ H (sp.ts s + sp.Δ))
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    ∃ k e, HVoteAt tr H y k e ∧ e.msg.slot = s ∧ tr.time k ≤ sp.ts s + sp.Δ := by
  have hd : 0 ≤ sp.ts s + sp.Δ := add_nonneg (by
    simp only [SAParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (by exact_mod_cast Nat.zero_le s))
    sp.toParams.hΔ.le
  obtain ⟨k, e, hv, hs, hk⟩ := vote_of_awake_joined (hrun.upTo hd) (hnc.upTo _) hy ⟨hw, le_rfl⟩
    (joinedAt_upTo hj)
  rw [RunTrace.upTo_projAC] at hv
  obtain ⟨hkd, hv⟩ := sa_voteAt_upTo.mp hv
  exact ⟨k, e, hVoteAt_iff.2 ⟨hrun.antitone hkd hy, hv⟩, hs, hk⟩

/-- The counted votes of an optimistic selection by a node honest at its check: each is of the
slot, sent or admitted by the checker in `[t_s, t_s + 2Δ)`, with a head held while honest above the
selection, genesis or accepted by the checker before `t_s + 2Δ`. -/
theorem optimistic_writer_votes_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {i₀ s : Nat} (hx : x ∈ H (tr.time i₀))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hO : SA.OptimisticLockAt tr.projAC x i₀ s C CV) :
    ∀ v ∈ CV, v.slot = s ∧
      (∃ k, x ∈ H (tr.time k) ∧ tr.projAC.SendOrAdmit x k v ∧ sp.ts s ≤ tr.time k ∧
        tr.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ tr.HonestBlocksAt H, Hv.root = v.head ∧ Anc (tr.HonestBlocksAt H) C Hv ∧
        (Hv.root = sp.genesisRoot ∨ ∃ k, x ∈ H (tr.time k) ∧ tr.projAC.AcceptAt x k Hv ∧
          tr.time k < sp.ts s + 2 * sp.Δ) := by
  have hd := hrun.time_nonneg i₀
  have hsub := upTo_subset hrun hd
  intro v hv
  obtain ⟨hvs, ⟨k, hk, hk1, hk2⟩, Hv, hHv, hHvr, hCHv, hacc⟩ :=
    optimistic_writer_votes (acRun_upTo hrun hnc hd).localRun hx
      ((sa_optimisticLockAt_upTo hrun.time_mono).mpr ⟨le_rfl, hO⟩) v hv
  obtain ⟨hkd, hk⟩ := (ac_sendOrAdmit_upTo hrun.time_mono).mp hk
  refine ⟨hvs, ⟨k, hrun.antitone hkd hx, hk, hk1, hk2⟩, Hv, hsub hHv, hHvr, hCHv.mono hsub,
    hacc.imp_right fun ⟨k', hk', hk't⟩ => ?_⟩
  obtain ⟨hk'd, hk'⟩ := (ac_acceptAt_upTo _).mp hk'
  exact ⟨k', hrun.antitone hk'd hx, hk', hk't⟩

/-- A block of the frame of a call at a time `≤ d`, of a node honest at `d`, is in the prefix's
honest blocks through `d`. -/
theorem mem_upTo_of_frame (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H d) (hkd : tr.time k ≤ d) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) :
    B ∈ (tr.upTo d).HonestBlocks (H d) := by
  rw [frame_of_projAC_at hrun (hrun.antitone hkd hy) hc] at hB
  exact ⟨y, hy, k, by rw [RunTrace.upTo_state_of_le hrun.time_mono hkd]; exact hB.1⟩

/-- A block a node honest at cut `i` accepted at a cut `≤ i` and that extends the frame's `Σ.F`
(inside the blocks held while honest) is in the frame. -/
theorem mem_tree_of_acceptAt_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {k i : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time i)) (hk : tr.projAC.AcceptAt y k B)
    (hki : k ≤ i) (hc : tr.projAC.CallAt y i ℓ) (hFB : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    B ∈ ℓ.frame.tree := by
  have hd := hrun.time_nonneg i
  have hm := hrun.time_mono
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hkd : tr.time k ≤ tr.time i := hm hki
  have hk' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k B :=
    (ac_acceptAt_upTo _).mpr ⟨hkd, hk⟩
  obtain ⟨ℓk, hck, -⟩ := hk
  have hBU : B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    mem_upTo_of_frame hrun hy hkd hck
      ((SA.accept_new sp hr hy hk').1 ℓk ((Trace.upTo_callAt_of_le tr.projAC hkd).mpr hck))
  exact SA.mem_tree_of_acceptAt sp hr hy hk' hki ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hBU hFB)

/-- A vote of the pool of a node honest at cut `i` has a finite stamp. -/
theorem pool_stamp_lt_top_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {σ : Nat}
    {v : Vote sp.n} (hv : v ∈ (tr.projAC.state y i).pool σ) :
    (tr.projAC.state y i).voteStamp v < ⊤ := by
  have hvs := state_pool_slot_at hrun hnc hy σ v hv
  have h := SA.pool_origin (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy i v
    (by rw [projAC_upTo_state hrun le_rfl, hvs]; exact hv)
  rw [projAC_upTo_state hrun le_rfl] at h
  rcases h with ⟨k, -, -, hst, -⟩ | ⟨k, -, -, -, -, hst, -⟩ <;>
  · rw [hst]; exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)

/-- A block of the frame that a node honest at cut `i` accepted before `T ≤ tr.time i`, with its
restarts up to `i` before `T`, has a stamp before `T`. -/
theorem blockStamp_lt_of_acceptedBefore_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ℓ)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) {T : Time}
    (hacc : SA.AcceptedBefore tr.projAC y B T)
    (hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k < T) (hT : T ≤ tr.time i) :
    (tr.projAC.state y i).blockStamp B.root < SA.ETime.of T := by
  have hm := hrun.time_mono
  have h := SA.blockStamp_lt_of_acceptedBefore sp
    (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hB
    (hacc.imp_right fun ⟨k, hk, hkT⟩ => ⟨k, (ac_acceptAt_upTo _).mpr ⟨(hkT.le.trans hT), hk⟩, hkT⟩)
    (fun k hk hrk => hrs k hk ((ac_restartAt_upTo _).mp hrk).2) (Or.inl hT)
  rwa [projAC_upTo_state hrun le_rfl] at h

/-- **Forwarding under the finite service**: a vote sent or admitted at cut `k` by a node honest
then reaches a node honest at its call `i` (not restarted since `t_k`, `t_k + Δ ≤ t_i`): it is in
the receiver's pool, or its validator is an equivocator there. -/
theorem sync_before_forward_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {ΔF b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    {y X : Fin sp.n} {k : Nat} {v : Vote sp.n} (hy : y ∈ H (tr.time k))
    (hsend : tr.projAC.SendOrAdmit y k v) (hb : tr.time k + sp.Δ ≤ b) {i : Nat}
    (hX : X ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt X i ℓ)
    (hrs : ∀ k' ≤ i, tr.projAC.RestartAt X k' → tr.time k' ≤ tr.time k)
    (hdl : tr.time k + sp.Δ ≤ tr.time i)
    (hslot : ∀ t, tr.time k ≤ t → t < tr.time k + sp.Δ →
      (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t) :
    v ∈ (tr.projAC.state X i).pool v.slot ∨
      v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X i).pool v.slot} := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg i
  have hdl' : tr.projAC.deadline X i (tr.time k) ≤ tr.time k + sp.Δ :=
    (ac_deadline_le_of_restarts hrs _).trans (by rw [max_self])
  have hserv := hsync.message y k v hy hsend (hrun.time_nonneg k) X i ℓ hX hc
    (hdl'.trans hb) (hdl'.trans hdl)
  have h := SA.held_of_deadline_service (acRun_upTo hrun hnc hd).localRun (k := k) hX
    (fun k' hk' hrk => hrs k' hk' ((ac_restartAt_upTo _).mp hrk).2) hdl hslot
    (sa_messageServedBefore_upTo hm le_rfl hserv)
  rwa [projAC_upTo_state hrun le_rfl] at h

/-! ### Origins and stored locks -/

/-- An origin of the prefix before cut `i` is an origin of the run before cut `i`. -/
theorem originBefore_of_upTo (hrun : Growing.GoldilocksRun proposer dg H tr)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s i : Nat}
    (h : Compose.OriginBefore (tr.upTo d) (H d) C s i) : OriginBefore tr H C s i := by
  obtain ⟨x, hx, k, hk, CV, hO⟩ := Compose.originBefore_iff.1 h
  rw [RunTrace.upTo_projAC] at hO
  rcases hO with hO | hO
  · obtain ⟨hkd, hO⟩ := (sa_resultAt_upTo hrun.time_mono).mp hO
    exact originBefore_iff.2 ⟨x, k, CV, hk, hrun.antitone hkd hx, Or.inl hO⟩
  · obtain ⟨hkd, hO⟩ := (sa_optimisticLockAt_upTo hrun.time_mono).mp hO
    exact originBefore_iff.2 ⟨x, k, CV, hk, hrun.antitone hkd hx, Or.inr hO⟩

/-- A slow lock write of the prefix through `d` is one of the run, at a cut at a time `≤ d`. -/
private theorem slowLockAt_of_upTo (hrun : Growing.GoldilocksRun proposer dg H tr) {x : Fin sp.n}
    {i s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.SlowLockAt (tr.projAC.upTo d) x i s B) :
    tr.time i ≤ d ∧ SA.SlowLockAt tr.projAC x i s B := by
  obtain ⟨ℓ, C, hu, hconf, hdeep⟩ := h
  obtain ⟨hid, hu⟩ := (sa_updateAt_upTo hrun.time_mono).mp hu
  have hst := projAC_upTo_state hrun (y := x) hid
  refine ⟨hid, ℓ, C, hu, by rwa [hst] at hconf, ?_⟩
  simpa only [hst, Trace.upTo_time] using hdeep

/-- **A lock write sits below an origin of its label**, written by the same node at the same cut:
a fast update and a slow lock keep a prefix of their update's confirmation, the result; an
optimistic selection is an origin. -/
theorem lock_below_origin_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {i s : Nat} (hx : x ∈ H (tr.time i))
    {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : (∃ CV, SA.FastLockAt tr.projAC x i s C CV) ∨ SA.SlowLockAt tr.projAC x i s C) :
    ∃ O OV, (SA.ResultAt tr.projAC x i s O OV ∨ SA.OptimisticLockAt tr.projAC x i s O OV) ∧
      Anc (tr.HonestBlocksAt H) C O := by
  rcases h with ⟨CV, ⟨ℓ, O, hu, hconf, hdeep, -⟩ | hop⟩ | ⟨ℓ, O, hu, hconf, hdeep⟩
  · exact ⟨O, _, Or.inl ⟨ℓ, hu, hconf, rfl⟩,
      ((SA.deepest_mem hdeep).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2⟩
  · exact ⟨C, CV, Or.inr hop, .refl⟩
  · exact ⟨O, _, Or.inl ⟨ℓ, hu, hconf, rfl⟩,
      ((SA.deepest_mem hdeep).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2⟩

/-- A lock write within `b` sits below an origin of its label within `b`. -/
theorem LockWithin.below_origin (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time}
    (h : LockWithin tr H C s b) : ∃ O, OriginWithin tr H O s b ∧ Anc (tr.HonestBlocksAt H) C O := by
  obtain ⟨x, i, hx, hib, h⟩ := lockWithin_iff.1 h
  obtain ⟨O, OV, hO, hCO⟩ := lock_below_origin_at hrun hnc hx h
  exact ⟨O, originWithin_iff.2 ⟨x, i, OV, hx, hib, hO⟩, hCO⟩

/-- **Stored locks sit below the holder's own lock writes**: a node honest at `t ≥ 0`, read
before cut `i` whose earlier cuts are at times `≤ t`, holds each stored lock on a block of its tree
that is below a lock write of the lock's slot within `t` (`SA.fast_lock_provenance` and
`SA.slow_lock_provenance` on the prefix through `t`: the holder wrote it at an earlier cut). -/
theorem lock_write_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) :
    ∀ l ∈ (tr.state y i).ac.locks, ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧
      ∃ B, LockWithin tr H B l.slot t ∧ Anc (tr.HonestBlocksAt H) L B := by
  have hst := Trace.upTo_state tr y (d := t) hi
  have hr := (acRun_upTo hrun hnc ht0).localRun
  have hU := hr.coherent
  have hsA : (tr.projAC.upTo t).state y i = (tr.state y i).ac := by
    rw [← RunTrace.upTo_projAC, projAC_state (hrun.upTo ht0).toLocalRun hy i, hst]
  intro l hl
  obtain ⟨L, hL, hLr, -⟩ := lock_origin (hrun.upTo ht0) (hnc.upTo _) hy i l (by rw [hst]; exact hl)
  have hLU : L ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, i, hL⟩
  rw [hst] at hL
  have hl' : l ∈ ((tr.projAC.upTo t).state y i).locks := by rw [hsA]; exact hl
  have hw : ∃ j < i, ∃ B, ((∃ CV, SA.FastLockAt (tr.projAC.upTo t) y j l.slot B CV) ∨
      SA.SlowLockAt (tr.projAC.upTo t) y j l.slot B) ∧
      ∃ L' ∈ (tr.upTo t).HonestBlocks (H t), L'.root = l.block ∧
        Anc ((tr.upTo t).HonestBlocks (H t)) L' B := by
    cases hf : l.fast
    · obtain ⟨j, hj, B, h, hB⟩ := SA.slow_lock_provenance hr hy i l hl' hf
      exact ⟨j, hj, B, Or.inr h, hB⟩
    · obtain ⟨j, hj, B, CV, h, hB⟩ := SA.fast_lock_provenance hr hy i l hl' hf
      exact ⟨j, hj, B, Or.inl ⟨CV, h⟩, hB⟩
  obtain ⟨j, -, B, h, L', hL', hL'r, hL'B⟩ := hw
  obtain rfl : L' = L := hU.1 hL' hLU (hL'r.trans hLr.symm)
  have hjt : tr.time j ≤ t ∧ ((∃ CV, SA.FastLockAt tr.projAC y j l.slot B CV) ∨
      SA.SlowLockAt tr.projAC y j l.slot B) := by
    rcases h with ⟨CV, h⟩ | h
    · obtain ⟨hjt, h⟩ := (SA.upTo_fastLockAt hrun.time_mono).mp h
      exact ⟨hjt, Or.inl ⟨CV, h⟩⟩
    · obtain ⟨hjt, h⟩ := slowLockAt_of_upTo hrun h
      exact ⟨hjt, Or.inr h⟩
  exact ⟨L', hL, hLr, B, lockWithin_iff.2 ⟨y, j, hrun.antitone hjt.1 hy, hjt.1, hjt.2⟩,
    hL'B.mono (upTo_subset hrun ht0)⟩

end Consensus.Goldilocks.Compose.Growing

end
