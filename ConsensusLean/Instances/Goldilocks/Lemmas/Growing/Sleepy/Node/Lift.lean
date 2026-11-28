module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Committee
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
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVoteTransfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock

public section

/-! # Goldilocks under `Sleepy` with growing faults: lifting static facts to the prefix

The tools that apply a static fact to the prefix `tr.upTo d` with the honest set `H d`
(`Growing.GoldilocksRun.upTo`, `0 ≤ d`) and carry its hypotheses and conclusions across:

* the blocks held while honest: membership at a cut of a node honest then, their coherence, and
  genesis below each of them;
* the AC trace of the prefix (`tr.projAC.upTo d`) at cuts at times `≤ d`: restarts, acceptances,
  processing, sends, wakes and deadlines, the AC events (votes, results, optimistic selections) and
  the retained and fresh message service;
* the transport of the finite service (`SleepyServiceBefore.upTo`);
* the origin chain (`OnOriginChainWithin.of_anc`), the σ-copies of `Compose/Sleepy/Chain`;
* node-local AC facts at a cut, lifted at the cut's time; the stored locks below the holder's own
  lock writes (`lock_write_at`), and each lock write below an origin of its label
  (`lock_below_origin_at`).

Ancestry comes down into the prefix by `RunTrace.anc_upTo_of_right`; conclusions go back up by
`Anc.mono` with `RunTrace.honestBlocks_upTo_subset`. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

/-! ### The AC trace of the prefix -/

section ACUpTo

variable {P : Params} {FGP : Type} {A : ACInterface P FGP} (trA : ACTrace A) {d : Time}

variable {trA}

theorem ac_state_upTo (hmono : Monotone trA.time) {y : Fin P.n} {i : Nat} (hi : trA.time i ≤ d) :
    (trA.upTo d).state y i = trA.state y i :=
  Trace.upTo_state trA y fun _ hk => (hmono hk.le).trans hi

end ACUpTo

section GoldilocksACUpTo

variable {sp : ACParams} {FGP : Type} {trS : AC.GTrace sp FGP}
  {d : Time}

theorem ac_voteAt_upTo {y : Fin sp.n} {i : Nat} {e : AC.Em sp FGP} :
    AC.VoteAt (trS.upTo d) y i e ↔ trS.time i ≤ d ∧ AC.VoteAt trS y i e := by
  simp only [AC.VoteAt, Trace.upTo_callAt]
  exact ⟨fun ⟨ℓ, ⟨h, hc⟩, hl⟩ => ⟨h, ℓ, hc, hl⟩, fun ⟨h, ℓ, hc, hl⟩ => ⟨ℓ, ⟨h, hc⟩, hl⟩⟩

theorem ac_castAt_upTo {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP)}
    {e : AC.Em sp FGP} :
    AC.CastAt (trS.upTo d) y i ℓ e ↔ trS.time i ≤ d ∧ AC.CastAt trS y i ℓ e := by
  simp only [AC.CastAt, Trace.upTo_callAt, and_assoc]

theorem ac_updateAt_upTo (hmono : Monotone trS.time) {x : Fin sp.n} {i s : Nat}
    {ℓ : ACLabel (AC.goldilocksAC sp FGP)} :
    AC.UpdateAt (trS.upTo d) x i s ℓ ↔ trS.time i ≤ d ∧ AC.UpdateAt trS x i s ℓ := by
  simp only [AC.UpdateAt, Trace.upTo_callAt]
  constructor
  · rintro ⟨⟨h, hc⟩, hl, ht, hj⟩
    rw [ac_state_upTo hmono h] at hj
    exact ⟨h, hc, hl, ht, hj⟩
  · rintro ⟨h, hc, hl, ht, hj⟩
    rw [← ac_state_upTo hmono h] at hj
    exact ⟨⟨h, hc⟩, hl, ht, hj⟩

theorem ac_resultAt_upTo (hmono : Monotone trS.time) {x : Fin sp.n} {i s : Nat}
    {C : AC.Blk sp.n FGP} {CV : Set (Vote sp.n)} :
    AC.ResultAt (trS.upTo d) x i s C CV ↔ trS.time i ≤ d ∧ AC.ResultAt trS x i s C CV := by
  simp only [AC.ResultAt]
  constructor
  · rintro ⟨ℓ, hu, hc, hCV⟩
    obtain ⟨h, hu⟩ := (ac_updateAt_upTo hmono).mp hu
    rw [ac_state_upTo hmono h] at hc hCV
    exact ⟨h, ℓ, hu, hc, hCV⟩
  · rintro ⟨h, ℓ, hu, hc, hCV⟩
    rw [← ac_state_upTo hmono h] at hc hCV
    exact ⟨ℓ, (ac_updateAt_upTo hmono).mpr ⟨h, hu⟩, hc, hCV⟩

theorem ac_optimisticLockAt_upTo (hmono : Monotone trS.time) {x : Fin sp.n} {i s : Nat}
    {C : AC.Blk sp.n FGP} {CV : Set (Vote sp.n)} :
    AC.OptimisticLockAt (trS.upTo d) x i s C CV ↔
      trS.time i ≤ d ∧ AC.OptimisticLockAt trS x i s C CV := by
  simp only [AC.OptimisticLockAt, AC.OptimisticPoint, Trace.upTo_callAt]
  constructor
  · rintro ⟨ℓ, A, ⟨⟨h, hc⟩, hA⟩, hs⟩
    rw [ac_state_upTo hmono h] at hA
    exact ⟨h, ℓ, A, ⟨hc, hA⟩, hs⟩
  · rintro ⟨h, ℓ, A, ⟨hc, hA⟩, hs⟩
    rw [← ac_state_upTo hmono h] at hA
    exact ⟨ℓ, A, ⟨⟨h, hc⟩, hA⟩, hs⟩

theorem ac_retainedBefore_upTo (hmono : Monotone trS.time) {y : Fin sp.n} {j : Nat}
    (hj : trS.time j ≤ d) {v : Vote sp.n} {T : Time} (h : AC.RetainedBefore trS y j v T) :
    AC.RetainedBefore (trS.upTo d) y j v T := by
  obtain ⟨q, hqj, hq, hr⟩ := (AC.retainedBefore_iff _ _ _ _).mp h
  refine (AC.retainedBefore_iff _ _ _ _).mpr ⟨q, hqj, ?_, fun r h1 h2 hrr => hr r h1 h2
    ((ACTrace.upTo_restartAt (tr := trS)).mp hrr).2⟩
  rwa [ac_state_upTo hmono ((hmono hqj).trans hj)]

theorem ac_messageServedBefore_upTo (hmono : Monotone trS.time) {y : Fin sp.n} {j : Nat}
    (hj : trS.time j ≤ d) {τ : Time} {v : Vote sp.n} (h : AC.MessageServedBefore trS y j τ v) :
    AC.MessageServedBefore (trS.upTo d) y j τ v := by
  rcases (AC.messageServedBefore_iff _ _ _ _).mp h with ⟨k, hkj, hk0, hk, hkd⟩ | hr
  · have hkd' : trS.time k ≤ d := (hmono hkj).trans hj
    exact (AC.messageServedBefore_iff _ _ _ _).mpr (Or.inl ⟨k, hkj, hk0,
      (ACTrace.upTo_processAt (tr := trS)).mpr ⟨hkd', hk⟩,
      by rw [ACTrace.upTo_deadline hmono hkd']; exact hkd⟩)
  · refine (AC.messageServedBefore_iff _ _ _ _).mpr (Or.inr ?_)
    rw [ACTrace.upTo_deadline hmono hj]
    exact ac_retainedBefore_upTo hmono hj hr

end GoldilocksACUpTo

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {d : Time}

/-! ### The blocks held while honest -/

/-- A block of the tree of a node honest at cut `i`, before `i`, is held while honest. -/
theorem mem_honestBlocksAt {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.tree) : B ∈ tr.HonestBlocksAt H :=
  ⟨y, i, tr.time i, hrun.time_nonneg i, fun _ hk => hrun.time_mono hk.le, hy, hB⟩

/-- The prefix's honest blocks are held while honest. -/
theorem upTo_subset {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hd : 0 ≤ d) :
    (tr.upTo d).HonestBlocks (H d) ⊆ tr.HonestBlocksAt H :=
  RunTrace.honestBlocks_upTo_subset hrun.time_mono hd

/-- Every block held while honest is held in the prefix through the time it is held at. -/
theorem exists_upTo_of_mem {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H) :
    ∃ t, 0 ≤ t ∧ B ∈ (tr.upTo t).HonestBlocks (H t) := by
  obtain ⟨y, i, t, ht, hi, hy, hBt⟩ := hB
  exact ⟨t, ht, y, hy, i, by rw [Trace.upTo_state tr y hi]; exact hBt⟩

/-- **The blocks held while honest are coherent** under `NoColl` (`honest_blocks_coherent`). -/
theorem honestBlocksAt_coherent {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) :=
  honest_blocks_coherent hrun hnc

/-- Genesis is held while honest, below every block held while honest. -/
theorem honestAt_genesis_anc {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H) :
    sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload ∈ tr.HonestBlocksAt H ∧
      Anc (tr.HonestBlocksAt H)
        (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload) B := by
  obtain ⟨t, ht, hBt⟩ := exists_upTo_of_mem hB
  obtain ⟨hg, hanc⟩ := honest_genesis_anc (hrun.upTo ht) hBt
  exact ⟨upTo_subset hrun ht hg, hanc.mono (upTo_subset hrun ht)⟩

/-- A block held while honest with the genesis root is genesis. -/
theorem honestAt_eq_genesis {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hU : Coherent (tr.HonestBlocksAt H)) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocksAt H) (hr : B.root = sp.genesisRoot) :
    B = sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload :=
  hU.1 hB (honestAt_genesis_anc hrun hB).1 hr

/-- Genesis has no parent, so its only ancestor is itself. -/
private theorem anc_genesis {S : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    {A : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc S A (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload)) :
    A = sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, -, hY⟩
  · exact heq.symm
  · exact absurd hY.2.2 (by simp [Params.genesisBlock])

/-- Compatibility of two blocks of the prefix's honest blocks comes down into the prefix
(`RunTrace.anc_upTo_of_right`). -/
theorem compatible_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    (hd : 0 ≤ d) {B C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.upTo d).HonestBlocks (H d)) (hC : C ∈ (tr.upTo d).HonestBlocks (H d))
    (h : Compatible (tr.HonestBlocksAt H) B C) : Compatible ((tr.upTo d).HonestBlocks (H d)) B C :=
  h.imp (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hC)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hB)

/-- A vote extension of a vote cast in the prefix by a node honest at `d` comes down into the
prefix: the vote's head is held by its voter. -/
theorem voteExtends_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    (hd : 0 ≤ d) {x : Fin sp.n} (hx : x ∈ H d) {k : Nat} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : AC.VoteAt (tr.upTo d).projAC x k e) {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : AC.VoteExtends (tr.HonestBlocksAt H) e.msg C) :
    AC.VoteExtends ((tr.upTo d).HonestBlocks (H d)) e.msg C := by
  obtain ⟨Hd, hHd, hHdr, hCHd⟩ := h
  obtain ⟨Hd₂, hHd₂, hHd₂r, -⟩ := AC.honest_headU
    (Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hnc.upTo d)).toU
    hx hv
  obtain rfl : Hd = Hd₂ := (honestBlocksAt_coherent hrun hnc).1 hHd (upTo_subset hrun hd hHd₂)
    (hHdr.trans hHd₂r.symm)
  exact ⟨Hd, hHd₂, hHdr, RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHd₂ hCHd⟩

/-! ### The origin chain (σ-copies of `Compose/Sleepy/Chain`) -/

/-- Blocks below tips that are pairwise compatible (`Q`) or genesis are compatible. -/
private theorem chain_compatible {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {Q : AC.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hcomp : ∀ C s C' s', Q C s → Q C' s' → Compatible (tr.HonestBlocksAt H) C C')
    {B B' : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H)
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
theorem OnOriginChainWithin.compatible {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time}
    (hcomp : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
      Compatible (tr.HonestBlocksAt H) C C')
    {B B' : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H)
    (hB' : B' ∈ tr.HonestBlocksAt H) (h : OnOriginChainWithin tr H B b)
    (h' : OnOriginChainWithin tr H B' b) : Compatible (tr.HonestBlocksAt H) B B' :=
  chain_compatible hrun hnc (Q := fun C s => OriginWithin tr H C s b) hcomp hB hB'
    (onOriginChainWithin_iff.1 h) (onOriginChainWithin_iff.1 h')

/-- **An ancestor of a block on the chain of the origins within `b` is on it.** -/
theorem OnOriginChainWithin.of_anc {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} {A B : AC.Blk sp.n (List (FG.Att sp.n))}
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

/-- **Transport of the finite service** to the prefix through `d ≥ 0`, for the validators
honest at `d`, with the deadline bound `min b d`. -/
theorem SleepyServiceBefore.upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {ΔF b : Time}
    (h : SleepyServiceBefore tr H ΔF b) (hd : 0 ≤ d) :
    Compose.SleepyServiceBefore (tr.upTo d) (H d) ΔF (min b d) := by
  have hm := hrun.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => hrun.antitone ht
  have hsub := upTo_subset hrun hd
  refine ⟨h.deltaF, ?_⟩
  rw [RunTrace.upTo_projAC]
  refine ⟨fun x hx i v hv h0 y hy j ℓ hc hdb hdj => ?_,
    fun x hx i B hB h0 y hy j ℓ hc hdb hdj ha => ?_⟩
  · obtain ⟨hid, hv⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hv
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ACTrace.upTo_deadline hm hjd] at hdb hdj
    exact ac_messageServedBefore_upTo hm hjd
      (h.message x i v (anti hid hx) hv h0 y j ℓ (anti hjd hy) hc (hdb.trans (min_le_left _ _))
        hdj)
  · obtain ⟨hid, hB⟩ := (ACTrace.upTo_acceptAt (tr := _)).mp hB
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ACTrace.upTo_deadline hm hjd] at hdb hdj
    obtain ⟨k, hkj, hk, hkt⟩ := h.acRelay x i B (anti hid hx) hB h0 y j ℓ (anti hjd hy) hc
      (hdb.trans (min_le_left _ _)) hdj (ha.mono hsub)
    have hkd : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (ACTrace.upTo_acceptAt (tr := _)).mpr ⟨hkd, hk⟩,
      by rw [ACTrace.upTo_deadline hm hkd]; exact hkt⟩

/-- **Transport of the AC service from `a`** to the prefix through `d ≥ 0`: the static AC service
window from `a` of the validators honest at `d`, with the deadline bound `min b d`. -/
theorem SleepyServiceFrom.acWindow_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {ΔF a κ b : Time} (h : SleepyServiceFrom tr H ΔF a κ b) (hd : 0 ≤ d) :
    AC.ServiceWindowBefore (H d) ((tr.upTo d).HonestBlocks (H d)) a (min b d)
      (tr.upTo d).projAC := by
  have hm := hrun.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => hrun.antitone ht
  have hsub := upTo_subset hrun hd
  rw [RunTrace.upTo_projAC]
  refine ⟨fun x hx i v hv hai y hy j ℓ hc hdb hdj => ?_,
    fun x hx i B hB hai y hy j ℓ hc hdb hdj ha => ?_⟩
  · obtain ⟨hid, hv⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hv
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ACTrace.upTo_deadline hm hjd] at hdb hdj
    exact ac_messageServedBefore_upTo hm hjd
      (h.message x i v (anti hid hx) hv hai y j ℓ (anti hjd hy) hc (hdb.trans (min_le_left _ _))
        hdj)
  · obtain ⟨hid, hB⟩ := (ACTrace.upTo_acceptAt (tr := _)).mp hB
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ACTrace.upTo_deadline hm hjd] at hdb hdj
    obtain ⟨k, hkj, hk, hkt⟩ := h.acRelay x i B (anti hid hx) hB hai y j ℓ (anti hjd hy) hc
      (hdb.trans (min_le_left _ _)) hdj (ha.mono hsub)
    have hkd : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (ACTrace.upTo_acceptAt (tr := _)).mpr ⟨hkd, hk⟩,
      by rw [ACTrace.upTo_deadline hm hkd]; exact hkt⟩

/-! ### Node-local AC facts at a cut (lifted at the time of the cut) -/

/-- The AC state of the prefix before a cut at a time `≤ d` is the run's. -/
theorem projAC_upTo_state {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hi : tr.time i ≤ d) : (tr.projAC.upTo d).state y i = tr.projAC.state y i :=
  ac_state_upTo (trA := tr.projAC) hrun.time_mono hi

/-- **The AC run of the prefix** through `d ≥ 0`, for the validators honest at `d`. -/
theorem acRun_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    (hd : 0 ≤ d) :
    AC.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) ini := by
  have h := Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hnc.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- A frame of a call of a node honest then is well formed, inside the blocks held while honest. -/
theorem frameIn_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ℓ) : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H :=
  have h := AC.frameIn_of_callAt (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  ⟨h.1, h.2.trans (upTo_subset hrun (hrun.time_nonneg i))⟩

/-- The frame of a call of a node honest then is in the prefix's honest blocks at its time. -/
theorem frame_upTo_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ℓ) :
    ℓ.frame.tree ⊆ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
  (AC.frameIn_of_callAt (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)).2

theorem castAt_spec_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ AC.joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (AC.getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (AC.voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (AC.mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root :=
  AC.castAt_specU (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun.toU hy
    (ac_castAt_upTo.mpr ⟨le_rfl, hc⟩)

theorem cast_head_fcRoot_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ℓ e) :
    (∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc ℓ.frame.F Hd) ∧
      tr.time i ≤ sp.ts e.msg.slot + sp.Δ :=
  have ha := acRun_upTo hrun hnc (hrun.time_nonneg i)
  cast_head_fcRoot ha.localRun ha.vstart hy (ac_castAt_upTo.mpr ⟨le_rfl, hc⟩)

theorem frame_of_projAC_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ℓ) : ℓ.frame = Node.frame (tr.state y i) := by
  have h := frame_of_projAC (hrun.upTo (hrun.time_nonneg i)) hy
    (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

theorem projAC_state_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) : tr.projAC.state y i = (tr.state y i).ac := by
  have h := projAC_state (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy i
  rwa [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl,
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- A cast of a node honest then is at a slot the node may vote in. -/
theorem mayVote_of_castAt_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ℓ e) : (tr.state y i).ac.mayVote e.msg.slot = true := by
  have h := AC.mayVote_of_castAt (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun hy
    (ac_castAt_upTo.mpr ⟨le_rfl, hc⟩)
  rwa [projAC_upTo_state hrun le_rfl, projAC_state_at hrun hy] at h

theorem frame_slot_le_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ℓ) : ∀ B ∈ ℓ.frame.tree, B.slot ≤ sp.slot (tr.time i) :=
  AC.frame_slot_leU sp (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun.toU hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)

theorem state_pool_slot_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (σ : Nat) :
    ∀ v ∈ (tr.projAC.state y i).pool σ, v.slot = σ := by
  have h := AC.state_pool_slotU sp (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun.toU
      hrun.vstart hy i σ
  rwa [projAC_upTo_state hrun le_rfl] at h

/-- **Lemma G at a pool**: a vote of the pool of a node honest at cut `i` whose validator is honest
at `i` was cast by it, at a cut at which it was honest. -/
theorem pool_vote_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {σ : Nat} {v : Vote sp.n}
    (hv : v ∈ (tr.projAC.state y i).pool σ) (hvH : v.val ∈ H (tr.time i)) :
    ∃ j < i, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v := by
  have hm := hrun.time_mono
  obtain ⟨j, hj, e, hve, hev⟩ := (acRun_upTo hrun hnc (hrun.time_nonneg i)).honest.pool_vote y hy
    i σ v (by rw [projAC_upTo_state hrun le_rfl]; exact hv) hvH
  obtain ⟨hjd, hve⟩ := ac_voteAt_upTo.mp hve
  exact ⟨j, hj, e, hVoteAt_iff.2 ⟨hrun.antitone hjd hvH, hve⟩, hev⟩

/-- **One vote per slot** of a node honest at both casts. -/
theorem one_vote_per_slot_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {j j' : Nat} {e e' : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x j e) (hv' : HVoteAt tr H x j' e') (hs : e.msg.slot = e'.msg.slot) :
    j = j' ∧ e = e' := by
  wlog hjj : j ≤ j' generalizing j j' e e'
  · obtain ⟨h1, h2⟩ := this hv' hv hs.symm (by omega)
    exact ⟨h1.symm, h2.symm⟩
  have hd := hrun.time_nonneg j'
  have hjd := hrun.time_mono hjj
  have hr := (acRun_upTo hrun hnc hd).localRun
  exact AC.one_vote_per_slotU sp _ _ _ _ hr.toU x (hVoteAt_iff.1 hv').1 j j' e e'
    (ac_voteAt_upTo.mpr ⟨hjd, (hVoteAt_iff.1 hv).2⟩)
    (ac_voteAt_upTo.mpr ⟨le_rfl, (hVoteAt_iff.1 hv').2⟩) hs

/-- Every ancestor (held while honest) of a block of the frame of a call is genesis or was
accepted by the caller by then. -/
theorem frame_anc_accepted_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ℓ)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hXB : Anc (tr.HonestBlocksAt H) X B) :
    X.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.projAC.AcceptAt y k X := by
  have hd := hrun.time_nonneg i
  rcases frame_anc_acceptedU (acRun_upTo hrun hnc hd).localRun.toU hy i ℓ
      ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) B hB X
      (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd (frame_upTo_at hrun hnc hy hc hB) hXB)
    with h | ⟨k, hk, hA⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk, ((ACTrace.upTo_acceptAt (tr := _)).mp hA).2⟩

theorem ts_add_delta_nonneg (s : Nat) : (0 : Time) ≤ sp.ts s + sp.Δ :=
  add_nonneg (by
    simp only [ACParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (by exact_mod_cast Nat.zero_le s))
    sp.toParams.hΔ.le

/-- A permission held before every cut whose earlier cuts are at times `≤ d` holds at every state
of the prefix through `d` (`upTo_state_exists`). -/
theorem mayVote_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {s : Nat}
    (hmv : ∀ i, (∀ k < i, tr.time k ≤ d) → (tr.state y i).ac.mayVote s = true) :
    ∀ i, ((tr.upTo d).state y i).ac.mayVote s = true := fun i => by
  obtain ⟨i₀, -, hb, h⟩ := Trace.upTo_state_exists tr hrun.time_mono y i
  rw [h]
  exact hmv i₀ hb

/-- The permission of a node honest at `d ≥ 0` on a stock run, up to `d`: the static
`mayVote_of_start` at the initial starts, on the prefix through `d`. -/
theorem mayVote_stock_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {s : Nat} :
    ∀ i, (∀ k < i, tr.time k ≤ d) → (tr.state y i).ac.mayVote s = true :=
  fun i hb => Trace.upTo_state tr y hb ▸ mayVote_of_start (hrun.upTo hd) (hnc.upTo _) hy rfl i

/-- **The stock committee facts**: at `K = full` with `committeeSize = n`, size and P hold for
every signer, and the gate is the default start's permission (`mayVote_stock_at`). -/
theorem CommitteeFacts.of_full (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hstock : sp.committeeSize = sp.n) :
    CommitteeFacts tr H (AC.CommitteeDict.full sp.n) :=
  ⟨AC.size_binding_full hstock, AC.CommitteePAt.full,
    fun _ ht _ hx i hi s =>
      ⟨fun _ => AC.mem_full s _, fun _ => mayVote_stock_at hrun hnc ht hx i hi⟩⟩

/-- **T from P**: a vote of the merged view of a cast of a node honest at it is backed in the read
point's pool by itself or by a vote of its validator of its slot
(`AC.merged_declared_backing_at_vote_slot`), and the read point's pool is in the node's pool after
the cast (`AC.readPoint_poolU`, P). -/
theorem CommitteeFacts.committeeTAt {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K) {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr) :
    AC.CommitteeTAt K tr.projAC H := by
  intro y i ℓ e hy hc m v hv
  have hacr := acRun_upTo hrun hnc (hrun.time_nonneg i)
  have hb : ∀ k < i + 1, tr.time k ≤ tr.time i := fun k hk =>
    hrun.time_mono (Nat.lt_succ_iff.mp hk)
  have hcU := ac_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hpool : ∀ k, ∀ w ∈ e.readPoint.pool k, w.slot = k := fun k w hw =>
    AC.state_pool_slotU _ hacr.localRun.toU hacr.vstart hy (i + 1) k w
      (AC.readPoint_poolU hacr.localRun.toU hy hcU hw).1
  have hmem : ∀ w ∈ e.readPoint.pool v.slot, w.val = v.val → v.val ∈ K.committee v.slot := by
    intro w hw hwv
    have hp := (AC.readPoint_poolU hacr.localRun.toU hy hcU hw).1
    rw [Trace.upTo_state tr.projAC y hb] at hp
    exact hwv ▸ hKB.hP.1 (tr.time i) y hy (i + 1) hb _ w hp
  rcases AC.merged_declared_backing_at_vote_slot hpool hv with h | ⟨w, hw, -, -, -, hwv, -⟩
  · exact hmem v h rfl
  · exact hmem w hw hwv

/-- **The stock committee bounds**: at `K = full`, CS is the population slot count read at the AC
projection, and CS2 is the population half bound. -/
theorem CommitteeBoundsFrom.of_full {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {σ₀ : Nat} {b : Time} (hB : SleepyBoundsFrom tr H σ₀ b) :
    CommitteeBoundsFrom tr H (AC.CommitteeDict.full sp.n) σ₀ b := by
  refine ⟨fun s d hs h1 hd h6 => (AC.faultBoundK_full_iff s _).2 ?_,
    fun s d hs h0 hd _ => (AC.mul_ncard_inter_full_lt_iff 2 s _).2 (hB.two d ?_ hd)⟩
  · have hJ : {y | y ∈ H d ∧ tr.projAC.awake y (sp.ts s + sp.Δ) ∧
        AC.JoinedAt tr.projAC y (sp.ts s + sp.Δ)} =
        {y | y ∈ H d ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)} :=
      Set.ext fun _ => and_congr_right fun _ => mem_awakeJoined_projAC hrun
    change (H d)ᶜ.ncard < Set.ncard _
    rw [hJ]
    exact hB.slot s d hs h1 hd h6
  · refine le_trans ?_ h0
    simp only [ACParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (by exact_mod_cast Nat.zero_le s)

/-- The permission of a committee member honest at `d ≥ 0`, from the gate `hGate`. -/
theorem mayVote_of_committee {K : AC.CommitteeDict sp.n}
    (hGate : ∀ t, 0 ≤ t → ∀ x, x ∈ H t → ∀ i, (∀ k < i, tr.time k ≤ t) → ∀ s,
      ((tr.state x i).ac.mayVote s = true ↔ x ∈ K.committee s))
    (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {s : Nat} (hyK : y ∈ K.committee s) :
    ∀ i, (∀ k < i, tr.time k ≤ d) → (tr.state y i).ac.mayVote s = true :=
  fun i hi => (hGate d hd y hy i hi s).2 hyK

/-- A node honest at `t_s + Δ`, awake and joined then, and permitted to vote in slot `s` before
then, casts a slot-`s` vote by then, at a cut at which it is honest. -/
theorem vote_of_awake_joined_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {s : Nat} (hy : y ∈ H (sp.ts s + sp.Δ))
    (hmv : ∀ i, (∀ k < i, tr.time k ≤ sp.ts s + sp.Δ) → (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    ∃ k e, HVoteAt tr H y k e ∧ e.msg.slot = s ∧ tr.time k ≤ sp.ts s + sp.Δ := by
  have hd := ts_add_delta_nonneg (sp := sp) s
  obtain ⟨k, e, hv, hs, hk⟩ := vote_of_awake_joined (hrun.upTo hd) (hnc.upTo _) hy
    (mayVote_upTo hrun hmv) ⟨hw, le_rfl⟩ (joinedAt_upTo hj)
  rw [RunTrace.upTo_projAC] at hv
  obtain ⟨hkd, hv⟩ := ac_voteAt_upTo.mp hv
  exact ⟨k, e, hVoteAt_iff.2 ⟨hrun.antitone hkd hy, hv⟩, hs, hk⟩

/-- The counted votes of an optimistic selection by a node honest at its check: each is of the
slot, sent or admitted by the checker in `[t_s, t_s + 2Δ)`, with a head held while honest above the
selection, genesis or accepted by the checker before `t_s + 2Δ`. -/
theorem optimistic_writer_votes_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {i₀ s : Nat} (hx : x ∈ H (tr.time i₀))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hO : AC.OptimisticLockAt tr.projAC x i₀ s C CV) :
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
    optimistic_writer_votes (acRun_upTo hrun hnc hd).localRun (acRun_upTo hrun hnc hd).vstart hx
      ((ac_optimisticLockAt_upTo hrun.time_mono).mpr ⟨le_rfl, hO⟩) v hv
  obtain ⟨hkd, hk⟩ := (ACTrace.upTo_sendOrAdmit hrun.time_mono).mp hk
  refine ⟨hvs, ⟨k, hrun.antitone hkd hx, hk, hk1, hk2⟩, Hv, hsub hHv, hHvr, hCHv.mono hsub,
    hacc.imp_right fun ⟨k', hk', hk't⟩ => ?_⟩
  obtain ⟨hk'd, hk'⟩ := (ACTrace.upTo_acceptAt (tr := _)).mp hk'
  exact ⟨k', hrun.antitone hk'd hx, hk', hk't⟩

/-- A block of the frame of a call at a time `≤ d`, of a node honest at `d`, is in the prefix's
honest blocks through `d`. -/
theorem mem_upTo_of_frame {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {k : Nat}
    (hy : y ∈ H d) (hkd : tr.time k ≤ d) {ℓ : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y k ℓ) {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) :
    B ∈ (tr.upTo d).HonestBlocks (H d) := by
  rw [frame_of_projAC_at hrun (hrun.antitone hkd hy) hc] at hB
  exact ⟨y, hy, k, by rw [RunTrace.upTo_state_of_le hrun.time_mono hkd]; exact hB.1⟩

/-- A block a node honest at cut `i` accepted at a cut `≤ i` and that extends the frame's `Σ.F`
(inside the blocks held while honest) is in the frame. -/
theorem mem_tree_of_acceptAt_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {k i : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {ℓ : ACLabel (goldilocksNode sp)} (hy : y ∈ H (tr.time i)) (hk : tr.projAC.AcceptAt y k B)
    (hki : k ≤ i) (hc : tr.projAC.CallAt y i ℓ) (hFB : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    B ∈ ℓ.frame.tree := by
  have hd := hrun.time_nonneg i
  have hm := hrun.time_mono
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hkd : tr.time k ≤ tr.time i := hm hki
  have hk' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y k B :=
    (ACTrace.upTo_acceptAt (tr := _)).mpr ⟨hkd, hk⟩
  obtain ⟨ℓk, hck, -⟩ := hk
  have hBU : B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    mem_upTo_of_frame hrun hy hkd hck
      ((AC.accept_new sp hr hy hk').1 ℓk ((Trace.upTo_callAt_of_le tr.projAC hkd).mpr hck))
  exact AC.mem_tree_of_acceptAtU sp hr.toU hy hk' hki ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hBU hFB)

/-- A vote of the pool of a node honest at cut `i` has a finite stamp. -/
theorem pool_stamp_lt_top_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {σ : Nat}
    {v : Vote sp.n} (hv : v ∈ (tr.projAC.state y i).pool σ) :
    (tr.projAC.state y i).voteStamp v < ⊤ := by
  have hvs := state_pool_slot_at hrun hnc hy σ v hv
  have h := AC.pool_origin (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun
    hrun.vstart hy i v
    (by rw [projAC_upTo_state hrun le_rfl, hvs]; exact hv)
  rw [projAC_upTo_state hrun le_rfl] at h
  rcases h with ⟨k, -, -, hst, -⟩ | ⟨k, -, -, -, -, hst, -⟩ <;>
  · rw [hst]; exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)

/-- A block of the frame that a node honest at cut `i` accepted before `T ≤ tr.time i`, with its
restarts up to `i` before `T`, has a stamp before `T`. -/
theorem blockStamp_lt_of_acceptedBefore_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ℓ)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree) {T : Time}
    (hacc : AC.AcceptedBefore tr.projAC y B T)
    (hrs : ∀ k ≤ i, tr.projAC.RestartAt y k → tr.time k < T) (hT : T ≤ tr.time i) :
    (tr.projAC.state y i).blockStamp B.root < AC.ETime.of T := by
  have hm := hrun.time_mono
  have h := AC.blockStamp_lt_of_acceptedBeforeU sp
    (acRun_upTo hrun hnc (hrun.time_nonneg i)).localRun.toU hrun.vstart hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hB
    (hacc.imp_right fun ⟨k, hk, hkT⟩ =>
      ⟨k, (ACTrace.upTo_acceptAt (tr := _)).mpr ⟨hkT.le.trans hT, hk⟩, hkT⟩)
    (fun k hk hrk => hrs k hk ((ACTrace.upTo_restartAt (tr := _)).mp hrk).2) (Or.inl hT)
  rwa [projAC_upTo_state hrun le_rfl] at h

/-! ### Origins and stored locks -/

/-- An origin of the prefix before cut `i` is an origin of the run before cut `i`. -/
theorem originBefore_of_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {s i : Nat}
    (h : Compose.OriginBefore (tr.upTo d) (H d) C s i) : OriginBefore tr H C s i := by
  obtain ⟨x, hx, k, hk, CV, hO⟩ := Compose.originBefore_iff.1 h
  rw [RunTrace.upTo_projAC] at hO
  rcases hO with hO | hO
  · obtain ⟨hkd, hO⟩ := (ac_resultAt_upTo hrun.time_mono).mp hO
    exact originBefore_iff.2 ⟨x, k, CV, hk, hrun.antitone hkd hx, Or.inl hO⟩
  · obtain ⟨hkd, hO⟩ := (ac_optimisticLockAt_upTo hrun.time_mono).mp hO
    exact originBefore_iff.2 ⟨x, k, CV, hk, hrun.antitone hkd hx, Or.inr hO⟩

/-- A slow lock write of the prefix through `d` is one of the run, at a cut at a time `≤ d`. -/
private theorem slowLockAt_of_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n}
    {i s : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : AC.SlowLockAt (tr.projAC.upTo d) x i s B) :
    tr.time i ≤ d ∧ AC.SlowLockAt tr.projAC x i s B := by
  obtain ⟨ℓ, C, hu, hconf, hdeep⟩ := h
  obtain ⟨hid, hu⟩ := (ac_updateAt_upTo hrun.time_mono).mp hu
  have hst := projAC_upTo_state hrun (y := x) hid
  refine ⟨hid, ℓ, C, hu, by rwa [hst] at hconf, ?_⟩
  simpa only [hst, Trace.upTo_time] using hdeep

/-- **A lock write sits below an origin of its label**, written by the same node at the same cut:
a fast update and a slow lock keep a prefix of their update's confirmation, the result; an
optimistic selection is an origin. -/
theorem lock_below_origin_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {i s : Nat} (hx : x ∈ H (tr.time i))
    {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : (∃ CV, AC.FastLockAt tr.projAC x i s C CV) ∨ AC.SlowLockAt tr.projAC x i s C) :
    ∃ O OV, (AC.ResultAt tr.projAC x i s O OV ∨ AC.OptimisticLockAt tr.projAC x i s O OV) ∧
      Anc (tr.HonestBlocksAt H) C O := by
  rcases h with ⟨CV, ⟨ℓ, O, hu, hconf, hdeep, -⟩ | hop⟩ | ⟨ℓ, O, hu, hconf, hdeep⟩
  · exact ⟨O, _, Or.inl ⟨ℓ, hu, hconf, rfl⟩,
      ((AC.deepest_mem hdeep).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2⟩
  · exact ⟨C, CV, Or.inr hop, .refl⟩
  · exact ⟨O, _, Or.inl ⟨ℓ, hu, hconf, rfl⟩,
      ((AC.deepest_mem hdeep).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2⟩

/-- A lock write within `b` sits below an origin of its label within `b`. -/
theorem LockWithin.below_origin {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time}
    (h : LockWithin tr H C s b) : ∃ O, OriginWithin tr H O s b ∧ Anc (tr.HonestBlocksAt H) C O := by
  obtain ⟨x, i, hx, hib, h⟩ := lockWithin_iff.1 h
  obtain ⟨O, OV, hO, hCO⟩ := lock_below_origin_at hrun hnc hx h
  exact ⟨O, originWithin_iff.2 ⟨x, i, OV, hx, hib, hO⟩, hCO⟩

/-- **Stored locks sit below the holder's own lock writes**: a node honest at `t ≥ 0`, read
before cut `i` whose earlier cuts are at times `≤ t`, holds each stored lock on a block of its tree
that is below a lock write of the lock's slot within `t` (`AC.fast_lock_provenance` and
`AC.slow_lock_provenance` on the prefix through `t`: the holder wrote it at an earlier cut). -/
theorem lock_write_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
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
  have hw : ∃ j < i, ∃ B, ((∃ CV, AC.FastLockAt (tr.projAC.upTo t) y j l.slot B CV) ∨
      AC.SlowLockAt (tr.projAC.upTo t) y j l.slot B) ∧
      ∃ L' ∈ (tr.upTo t).HonestBlocks (H t), L'.root = l.block ∧
        Anc ((tr.upTo t).HonestBlocks (H t)) L' B := by
    cases hf : l.fast
    · obtain ⟨j, hj, B, h, hB⟩ := AC.slow_lock_provenance hr hrun.vstart hy i l hl' hf
      exact ⟨j, hj, B, Or.inr h, hB⟩
    · obtain ⟨j, hj, B, CV, h, hB⟩ := AC.fast_lock_provenance hr hrun.vstart hy i l hl' hf
      exact ⟨j, hj, B, Or.inl ⟨CV, h⟩, hB⟩
  obtain ⟨j, -, B, h, L', hL', hL'r, hL'B⟩ := hw
  obtain rfl : L' = L := hU.1 hL' hLU (hL'r.trans hLr.symm)
  have hjt : tr.time j ≤ t ∧ ((∃ CV, AC.FastLockAt tr.projAC y j l.slot B CV) ∨
      AC.SlowLockAt tr.projAC y j l.slot B) := by
    rcases h with ⟨CV, h⟩ | h
    · obtain ⟨hjt, h⟩ := (AC.upTo_fastLockAt hrun.time_mono).mp h
      exact ⟨hjt, Or.inl ⟨CV, h⟩⟩
    · obtain ⟨hjt, h⟩ := slowLockAt_of_upTo hrun h
      exact ⟨hjt, Or.inr h⟩
  exact ⟨L', hL, hLr, B, lockWithin_iff.2 ⟨y, j, hrun.antitone hjt.1 hy, hjt.1, hjt.2⟩,
    hL'B.mono (upTo_subset hrun ht0)⟩

end Consensus.Goldilocks.Compose.Growing

end
