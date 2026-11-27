module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Participants
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # P-U shadow, V-B7: the counts of the outage invariant over the shadow run

The shadow copy of `Growing/Outage/Count` (and the node-local lifts of
`Growing/Sleepy/Node/Lift` that it reads) over `OutageLockPremises'` and `Growing.GoldilocksRun'`.
The proofs are the stock ones: the counts read the AC projection, the committee facts and the
trace, and the shadow frame enters only as the frame of an AC call, which is `Node.frame'`
(`frame_of_projAC_at'`). The static lock provenance comes from `Shadow/PU/Provenance`. -/

namespace Consensus.Goldilocks.Shadow.PU

open Consensus.Goldilocks.Compose Consensus.Goldilocks.Compose.Growing
open Consensus.Goldilocks.Coherence Consensus.Goldilocks.Shadow.PU.Growing
open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace' sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State} {d : Time}

/-! ## Node-local lifts at a cut (`Growing/Sleepy/Node/Lift`) -/

theorem projAC_upTo_state' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} (hi : tr.time i ≤ d) :
    (tr.projAC.upTo d).state y i = tr.projAC.state y i :=
  ac_state_upTo (trA := tr.projAC) hrun.time_mono hi

theorem castAt_spec_at' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ AC.joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (AC.getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (AC.voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (AC.mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root :=
  AC.castAt_specU (acRun_upTo' hrun hnc (hrun.time_nonneg i)).localRun.toU hy
    (ac_castAt_upTo.mpr ⟨le_rfl, hc⟩)

theorem cast_head_fcRoot_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ℓ e) :
    (∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc ℓ.frame.fcRoot Hd) ∧
      tr.time i ≤ sp.ts e.msg.slot + sp.Δ :=
  have ha := acRun_upTo' hrun hnc (hrun.time_nonneg i)
  cast_head_fcRoot ha.localRun ha.vstart hy (ac_castAt_upTo.mpr ⟨le_rfl, hc⟩)

theorem state_pool_slot_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (σ : Nat) :
    ∀ v ∈ (tr.projAC.state y i).pool σ, v.slot = σ := by
  have h := AC.state_pool_slotU sp (acRun_upTo' hrun hnc (hrun.time_nonneg i)).localRun.toU
      hrun.vstart hy i σ
  rwa [projAC_upTo_state' hrun le_rfl] at h

/-- **Lemma G at a pool**: a vote of the pool of a node honest at cut `i` whose validator is honest
at `i` was cast by it, at a cut at which it was honest. -/
theorem pool_vote_at' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {σ : Nat}
    {v : Vote sp.n} (hv : v ∈ (tr.projAC.state y i).pool σ) (hvH : v.val ∈ H (tr.time i)) :
    ∃ j < i, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v := by
  have hm := hrun.time_mono
  obtain ⟨j, hj, e, hve, hev⟩ :=
    (acRun_upTo' hrun hnc (hrun.time_nonneg i)).honest.pool_vote y hy i σ v
      (by rw [projAC_upTo_state' hrun le_rfl]; exact hv) hvH
  obtain ⟨hjd, hve⟩ := ac_voteAt_upTo.mp hve
  exact ⟨j, hj, e, hVoteAt_iff.2 ⟨hrun.antitone hjd hvH, hve⟩, hev⟩

/-- A permission held before every cut whose earlier cuts are at times `≤ d` holds at every state
of the prefix through `d`. -/
theorem mayVote_upTo' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} {s : Nat}
    (hmv : ∀ i, (∀ k < i, tr.time k ≤ d) → (tr.state y i).ac.mayVote s = true) :
    ∀ i, ((tr.upTo d).state y i).ac.mayVote s = true := fun i => by
  obtain ⟨i₀, -, hb, h⟩ := Trace.upTo_state_exists tr hrun.time_mono y i
  rw [h]
  exact hmv i₀ hb

/-- **Awake and joined at the AC projection** is awake and joined at the run. -/
theorem mem_awakeJoined_projAC'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {t : Time} {y : Fin sp.n} :
    (tr.projAC.awake y t ∧ AC.JoinedAt tr.projAC y t) ↔ (tr.awake y t ∧ tr.JoinedAt y t) :=
  and_congr Iff.rfl (projAC_joinedAt_iff hrun.time_nonneg y t).symm

/-- A node honest at `t_s + Δ`, awake and joined then, and permitted to vote in slot `s` before
then, casts a slot-`s` vote by then, at a cut at which it is honest. -/
theorem vote_of_awake_joined_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {s : Nat} (hy : y ∈ H (sp.ts s + sp.Δ))
    (hmv : ∀ i, (∀ k < i, tr.time k ≤ sp.ts s + sp.Δ) → (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    ∃ k e, HVoteAt tr H y k e ∧ e.msg.slot = s ∧ tr.time k ≤ sp.ts s + sp.Δ := by
  have hd := ts_add_delta_nonneg (sp := sp) s
  obtain ⟨k, e, hv, hs, hk⟩ := Compose.vote_of_awake_joined' (hrun.upTo hd) (hnc.upTo _) hy
    (mayVote_upTo' hrun hmv) ⟨hw, le_rfl⟩ (joinedAt_upTo hj)
  rw [RunTrace.upTo_projAC] at hv
  obtain ⟨hkd, hv⟩ := ac_voteAt_upTo.mp hv
  exact ⟨k, e, hVoteAt_iff.2 ⟨hrun.antitone hkd hy, hv⟩, hs, hk⟩

/-- **Transport of the finite service** to the prefix through `d ≥ 0`
(`SleepyServiceBefore.upTo`). -/
theorem sleepyServiceBefore_upTo'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {ΔF b : Time} (h : SleepyServiceBefore tr H ΔF b) (hd : 0 ≤ d) :
    Compose.SleepyServiceBefore (tr.upTo d) (H d) ΔF (min b d) := by
  have hm := hrun.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => hrun.antitone ht
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  refine ⟨h.deltaF, ?_⟩
  rw [RunTrace.upTo_projAC]
  refine ⟨fun x hx i v hv h0 y hy j ℓ hc hdb hdj => ?_,
    fun x hx i B hB h0 y hy j ℓ hc hdb hdj ha => ?_⟩
  · obtain ⟨hid, hv⟩ := (ac_sendOrAdmit_upTo hm).mp hv
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [ac_deadline_upTo hm hjd] at hdb hdj
    exact ac_messageServedBefore_upTo hm hjd
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

/-! ## Votes, results and the store of a node (`Growing/Outage/Count`) -/

/-- The cast of a vote by a node honest then is in `[t_s, t_s + Δ]` of its slot `s`. -/
theorem HVoteAt.ts_le_cast'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {k : Nat} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e) :
    sp.ts e.msg.slot ≤ tr.time k ∧ tr.time k ≤ sp.ts e.msg.slot + sp.Δ := by
  obtain ⟨hx, ℓ, hc, he⟩ := hVoteAt_iff.1 hv
  have hsl := (castAt_spec_at' hrun hnc hx ⟨hc, he⟩).2.1
  exact ⟨(AC.ts_le_iff_le_slot sp (hrun.time_nonneg k) _).2 (by rw [hsl]),
    (cast_head_fcRoot_at' hrun hnc hx ⟨hc, he⟩).2⟩

/-- The head of a vote by a node honest at its cast is held while honest. -/
theorem HVoteAt.head_mem' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {x : Fin sp.n} {k : Nat} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e) : ∃ Hd ∈ tr.HonestBlocksAt H, Hd.root = e.msg.head := by
  obtain ⟨hx, ℓ, hc, he⟩ := hVoteAt_iff.1 hv
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := cast_head_fcRoot_at' hrun hnc hx ⟨hc, he⟩
  exact ⟨Hd, (frameIn_at' hrun hnc hx hc).2 hHd, hHdr⟩

/-- A counted vote of a validator honest at the writer's update was cast by it at an earlier
cut at which it was honest, of the update's slot, and its head extends the result inside the
blocks held while honest (Lemma G at the update's pool). -/
theorem counted_honest_vote_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {X : Fin sp.n} {i₀ s : Nat} (hX : X ∈ H (tr.time i₀))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : AC.ResultAt tr.projAC X i₀ s C CV) {v : Vote sp.n} (hv : v ∈ CV)
    (hvH : v.val ∈ H (tr.time i₀)) :
    ∃ j < i₀, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v ∧ v.slot = s ∧
      ∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ Anc (tr.HonestBlocksAt H) C R := by
  obtain ⟨ℓ, hu, -, hCV⟩ := hR
  rw [hCV] at hv
  obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
  obtain ⟨j, hj, e, hve, he⟩ := pool_vote_at' hrun hnc hX hvp hvH
  obtain ⟨-, hΦU⟩ := frameIn_at' hrun hnc hX hu.1
  exact ⟨j, hj, e, hve, he, state_pool_slot_at' hrun hnc hX s v hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

/-- The result of an update by a node honest at it is held while honest. -/
theorem result_mem_at' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {X : Fin sp.n} {i₀ s : Nat} (hX : X ∈ H (tr.time i₀))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : AC.ResultAt tr.projAC X i₀ s C CV) : C ∈ tr.HonestBlocksAt H := by
  obtain ⟨ℓ, hu, hC, -⟩ := hR
  exact (frameIn_at' hrun hnc hX hu.1).2 (AC.deepest_mem hC).1.1

/-- **A result's counted validators meet a participant set.** At an honest update with result
`C`, if `T` are voters of the update's pool and `|Q| < |T|`, some counted vote is of a validator in
`T` or outside `Q`. -/
private theorem exists_counted_of_participants' {X : Fin sp.n} {i₀ s : Nat}
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : AC.ResultAt tr.projAC X i₀ s C CV) {T Q : Set (Fin sp.n)}
    (hT : T ⊆ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}) (hQT : Q.ncard < T.ncard) :
    ∃ v ∈ CV, v.val ∈ T ∨ v.val ∉ Q := by
  by_contra hno
  push Not at hno
  have hmaj := AC.result_majority hR
  obtain ⟨ℓ, -, -, hCV⟩ := hR
  have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
    rintro w ⟨v, hv, rfl⟩
    rw [hCV] at hv
    exact ⟨v, hv.1, rfl⟩
  have hdisj : Disjoint T {w | ∃ v ∈ CV, v.val = w} :=
    Set.disjoint_left.2 fun w hwT ⟨v, hv, hvw⟩ => (hno v hv).1 (hvw ▸ hwT)
  have h1 := Set.ncard_union_eq hdisj
  have h2 := Set.ncard_le_ncard (Set.union_subset hT hSV)
  have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Q.ncard :=
    Set.ncard_le_ncard fun w ⟨v, hv, hvw⟩ => hvw ▸ (hno v hv).2
  omega

namespace OutageLockPremises'

variable {D : OutageLockPremises' tr H proposer dg ini}

/-- **N6 inside a band committee**: `2·|K m ∩ ((H z)ᶜ ∪ W)| < committeeSize` at a band label `m`
that an honest call reaches. -/
theorem two_mul_lt_K (D : OutageLockPremises' tr H proposer dg ini) {m : Nat} (h₁ : D.j₀ ≤ m)
    (h₂ : m ≤ D.j₀ + sp.k)
    (hr : ∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ sp.ts m ≤ tr.time i) :
    2 * (D.K.committee m ∩ ((H D.z)ᶜ ∪ D.W)).ncard < sp.committeeSize := by
  have hdisj : Disjoint (D.K.committee m ∩ D.A₀) (D.K.committee m ∩ ((H D.z)ᶜ ∪ D.W)) := by
    refine Disjoint.mono Set.inter_subset_right Set.inter_subset_right ?_
    rw [Set.disjoint_union_right]
    exact ⟨Set.disjoint_left.2 fun x hx hxc => hxc (D.hA₀ hx), D.hW.2⟩
  have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have h2 : (D.K.committee m ∩ D.A₀ ∪ D.K.committee m ∩ ((H D.z)ᶜ ∪ D.W)).ncard ≤
      (D.K.committee m).ncard :=
    Set.ncard_le_ncard (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
  rw [D.facts.hsize m] at h2
  have := D.hopponentsK m h₁ h₂ hr
  omega

/-- **CS2 inside a slot committee**: at `d ∈ [t_s, t_s + 6Δ]` that an honest call reaches, the
members of the slot-`s` committee compromised by `d` are fewer than half of it. -/
theorem two_faults_lt_K (D : OutageLockPremises' tr H proposer dg ini) {s : Nat} {d : Time}
    (h₁ : sp.ts s ≤ d) (h₂ : d ≤ sp.ts s + 6 * sp.Δ)
    (hr : ∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ d ≤ tr.time i) :
    2 * (D.K.committee s ∩ (H d)ᶜ).ncard < sp.committeeSize := by
  rw [← D.facts.hsize s]
  have hB := D.hBK d hr
  by_cases hd : d ≤ sp.ts s + 2 * sp.Δ
  · exact hB.twoK s d (Nat.zero_le _) h₁ le_rfl hd
  exact hB.two_of_slotK (Nat.zero_le _) (by linarith [sp.toParams.hΔ]) le_rfl h₂

theorem coherent (D : OutageLockPremises' tr H proposer dg ini) :
    Coherent (tr.HonestBlocksAt H) :=
  honestBlocksAt_coherent' D.hrun D.hnc

/-- `2 f_d < n` at the time of a cut of an honest call. -/
theorem two_faults_lt_at (D : OutageLockPremises' tr H proposer dg ini) {x : Fin sp.n} {i : Nat}
    (hx : x ∈ H (tr.time i)) (hc : tr.IsCall x i) : 2 * (H (tr.time i))ᶜ.ncard < sp.n :=
  (D.hB _ ⟨x, i, hx, hc, le_rfl⟩).two _ (D.hrun.time_nonneg i) le_rfl

/-- A genesis `P` is below every block held while honest. -/
theorem anc_of_genesis (D : OutageLockPremises' tr H proposer dg ini)
    (hg : D.P.root = sp.genesisRoot)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ tr.HonestBlocksAt H) :
    Anc (tr.HonestBlocksAt H) D.P C := by
  have hP : D.P = sp.toParams.genesisBlock (goldilocksNode' sp ro).genesisPayload :=
    D.coherent.1 D.hP.1 (honestAt_genesis_anc' D.hrun D.hP.1).1 hg
  rw [hP]
  exact (honestAt_genesis_anc' D.hrun hC).2

/-- A genesis `P` is extended by every vote of a node honest at its cast. -/
theorem vote_extends_of_genesis (D : OutageLockPremises' tr H proposer dg ini)
    (hg : D.P.root = sp.genesisRoot) {x : Fin sp.n} {k : Nat}
    {e : AC.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
  obtain ⟨Hd, hHd, hHdr⟩ := HVoteAt.head_mem' D.hrun D.hnc hv
  exact ⟨Hd, hHd, hHdr, D.anc_of_genesis hg hHd⟩

/-- **An origin within `b₀` is compatible with `P`.** -/
theorem compatible_of_within (D : OutageLockPremises' tr H proposer dg ini)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s D.b₀) (hCU : C ∈ tr.HonestBlocksAt H) :
    Compatible (tr.HonestBlocksAt H) C D.P := by
  rcases D.hP.2 with hg | hP
  · exact Or.inr (D.anc_of_genesis hg hCU)
  · exact D.hpre.origins_compatible C s D.P D.σ hC hP

/-- **A vote at a time `≤ b₀` of a slot after `σ`, by a node honest at its cast, extends `P`.** -/
theorem vote_extends_pre (D : OutageLockPremises' tr H proposer dg ini) {x : Fin sp.n}
    {k : Nat} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H x k e) (hk : tr.time k ≤ D.b₀) (hs : D.σ < e.msg.slot) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
  rcases D.hP.2 with hg | hP
  · exact D.vote_extends_of_genesis hg hv
  · exact D.hpre.vote_extends D.P D.σ hP x k e hv hk hs

/-- **Holder or opponent**: a vote cast in `[a, z]` by a node honest at its cast is by a
member of `A₀`, by a member of `W`, or by a validator compromised by `z`. -/
theorem holder_or_opponent (D : OutageLockPremises' tr H proposer dg ini) {x : Fin sp.n}
    {k : Nat} {e : AC.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e) (hka : D.a ≤ tr.time k)
    (hkz : tr.time k ≤ D.z) : x ∈ D.A₀ ∨ x ∈ D.W ∨ x ∉ H D.z := by
  by_cases hxz : x ∈ H D.z
  · obtain ⟨hx, ℓ, hc, -⟩ := hVoteAt_iff.1 hv
    have haw := D.hrun.awake_of_call x k hx ⟨_, projAC_callAt.1 hc⟩
    rcases D.hawake x (tr.time k) hka hkz hxz haw with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hxz)

end OutageLockPremises'

namespace OutageVoteInv'

variable {D : OutageLockPremises' tr H proposer dg ini}

/-- The invariant at `i` gives it at every earlier cut. -/
theorem mono {i i' : Nat} (hinv : OutageVoteInv' D i) (hi : i' ≤ i) : OutageVoteInv' D i' :=
  ⟨fun x k hk => hinv.votes x k (hk.trans_le hi), fun x k hk => hinv.late x k (hk.trans_le hi)⟩

/-- **OL-W**: at a cut before `i`, a vote of a slot `≥ j₀` by a node honest at its cast has a
head compatible with `P` when, for a slot at most `j₀ + k`, its voter is still honest at `z` and
is not a look-back opponent. -/
theorem voteCompat_of_not_opponent_at {i : Nat} (hinv : OutageVoteInv' D i) {x : Fin sp.n}
    {k : Nat} (hk : k < i) {e : AC.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e)
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
  obtain ⟨hts, hte⟩ := HVoteAt.ts_le_cast' D.hrun D.hnc hv
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
theorem holder_ready_at (D : OutageLockPremises' tr H proposer dg ini) {x : Fin sp.n}
    (hx : x ∈ D.A₀) {m : Nat} (hm : D.j₀ + 1 ≤ m) (hmK : m ≤ D.j₀ + sp.k)
    (hcall : ∃ y i, y ∈ H (tr.time i) ∧ tr.IsCall y i ∧ sp.ts m + sp.Δ ≤ tr.time i) :
    tr.awake x (sp.ts m + sp.Δ) ∧ tr.JoinedAt x (sp.ts m + sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hj := ts_le_ts (sp := sp) (show D.j₀ ≤ m - 1 by omega)
  have hmK' := ts_le_ts (sp := sp) hmK
  have hm1 : sp.ts (m - 1 : Nat) + 4 * sp.Δ = sp.ts m := by
    simp only [ACParams.ts]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hz := D.hzc (sp.ts m + sp.Δ) (by linarith) hcall
  refine ⟨D.hA₀awake x hx _ (by linarith [D.ha]) hz, fun k hk hkt => ?_⟩
  have hslot : sp.slot (sp.ts m + sp.Δ) = m :=
    AC.slot_of_mem sp m (by linarith) (by simp only [ACParams.ts]; push_cast; linarith)
  change 0 < sp.slot (sp.ts m + sp.Δ) ∧
    tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
  rw [hslot, sp.slotTime_eq]
  refine ⟨by omega, ?_⟩
  have := (D.hA₀join x hx k hk (hkt.trans hz)).trans D.ha
  have h' : sp.ts (m - 1 : Nat) = 4 * sp.Δ * ((m - 1 : Nat) : Int) := rfl
  rw [← h']
  linarith

/-- The pool of an update of a restored label by a node honest at it holds the slot votes of the
members of the slot committee honest at `t_m + Δ` that are awake and joined then. -/
theorem voter_of_ready (D : OutageLockPremises' tr H proposer dg ini) {y : Fin sp.n}
    {k m : Nat} {ℓ : ACLabel (AC.goldilocksAC sp (List (FG.Att sp.n)) ro)}
    (hy : y ∈ H (tr.time k)) (hu : AC.UpdateAt tr.projAC y k m ℓ) (hm : D.r ≤ m) {x : Fin sp.n}
    (hx : x ∈ H (sp.ts m + sp.Δ)) (hxK : x ∈ D.K.committee m)
    (haw : tr.awake x (sp.ts m + sp.Δ)) (hjn : tr.JoinedAt x (sp.ts m + sp.Δ)) :
    x ∈ AC.voters {v | v ∈ (tr.projAC.state y k).pool m} := by
  obtain ⟨k', e, hve, hes, -⟩ := vote_of_awake_joined_at' D.hrun D.hnc hx
    (mayVote_of_committee D.facts.hGate (ts_add_delta_nonneg _) hx hxK) haw hjn
  obtain ⟨hx', ℓ', hc', he'⟩ := hVoteAt_iff.1 hve
  have hval := (castAt_spec_at' D.hrun D.hnc hx' ⟨hc', he'⟩).1
  rcases D.PG y k m ℓ hy hu hm x k' e hve hes with hpool | ⟨v, hv, -, -, -, hvx, -⟩
  · rw [← projAC_state_at' D.hrun hy] at hpool
    exact ⟨e.msg, hpool, hval⟩
  · rw [← projAC_state_at' D.hrun hy] at hv
    exact ⟨v, hv, hvx.trans hval⟩

/-- **(R) at a cut `k ≤ i`**: the result of an update of an unpolluted label by a node honest
at it is compatible with `P`. Each branch counts at the writer's update cut `k`. -/
theorem result_compatible_at {i : Nat} (hinv : OutageVoteInv' D i) {y : Fin sp.n} {k : Nat}
    (hk : k ≤ i) (hy : y ∈ H (tr.time k)) {m : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : AC.ResultAt tr.projAC y k m C CV) (hm : m ≤ D.j₀ ∨ D.r ≤ m) :
    Compatible (tr.HonestBlocksAt H) C D.P := by
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hCU := result_mem_at' D.hrun D.hnc hy hR
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
      counted_honest_vote_at' D.hrun D.hnc hy hR hv hvH
    exact compatible_of_voteCompat hU hRU hRr hCR (hcompat j hj e hve rfl hvs)
  -- the counted signers are slot-`m` committee members (P at the writer's update)
  have hmemCV : ∀ v ∈ CV, v.val ∈ D.K.committee m := by
    obtain ⟨ℓ', -, -, hCV⟩ := id hR
    intro v hv
    rw [hCV] at hv
    exact D.facts.hP.1 (tr.time k) y hy k (fun _ hk' => D.hrun.time_mono hk'.le) m v hv.1
  -- the committee slot count at the writer's update
  have hslot : (D.K.committee m ∩ (H (tr.time k))ᶜ).ncard <
      (D.K.committee m ∩ {x | x ∈ H (tr.time k) ∧ tr.projAC.awake x (sp.ts m + sp.Δ) ∧
        AC.JoinedAt tr.projAC x (sp.ts m + sp.Δ)}).ncard :=
    (D.hBK _ hcall).slotK m (tr.time k) (Nat.zero_le _) (by rw [ht]; linarith) le_rfl ht.le
  rcases lt_or_ge m D.j₀ with hlt | hge
  · -- R-pre: the update is within `b₀`
    have hmj : sp.ts m + 6 * sp.Δ ≤ D.b₀ := by
      have := ts_le_ts (sp := sp) (show m + 1 ≤ D.j₀ by omega)
      have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      linarith
    exact D.compatible_of_within (OriginWithin.of_result hy (ht ▸ hmj) hR) hCU
  rcases hm with hm | hm
  · -- R-j₀: the voters awake and joined at `t_{j₀} + Δ` and honest at the update reach it by the
    -- early cutoff `≤ b₀`
    have hmeq : m = D.j₀ := le_antisymm hm hge
    have hd := D.hrun.time_nonneg k
    have hsvc := (sleepyServiceBefore_upTo' D.hrun D.hpreSvc hd).ac
    have hT : D.K.committee m ∩ {x | x ∈ H (tr.time k) ∧ tr.projAC.awake x (sp.ts m + sp.Δ) ∧
        AC.JoinedAt tr.projAC x (sp.ts m + sp.Δ)} ⊆
        AC.voters {v | v ∈ (tr.projAC.state y k).pool m} := fun x hx => by
      obtain ⟨hxK, hx, hwj⟩ := hx
      obtain ⟨hw, hj⟩ := (mem_awakeJoined_projAC' D.hrun).1 hwj
      have h := Compose.awake_participant_early' (D.hrun.upTo hd) (D.hnc.upTo _) hsvc
        (le_min (hmeq ▸ hj₀.1) (by rw [ht]; linarith)) hy
        (by rw [RunTrace.upTo_projAC]; exact (ac_updateAt_upTo D.hrun.time_mono).mpr ⟨le_rfl, hu⟩)
        hx (mayVote_upTo' D.hrun (mayVote_of_committee D.facts.hGate hd hx hxK))
        ⟨hw, by rw [ht]; linarith⟩
        (joinedAt_upTo hj)
      rwa [RunTrace.upTo_projAC, projAC_upTo_state' D.hrun le_rfl] at h
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants' hR hT hslot
    have hvH : v.val ∈ H (tr.time k) :=
      hvT.elim (fun h => h.2.1) fun h => not_not.1 fun hn => h ⟨hmemCV v hv, hn⟩
    refine finish v hv hvH fun j hj e hve he hs => ?_
    obtain ⟨-, hte⟩ := HVoteAt.ts_le_cast' D.hrun D.hnc hve
    rw [hs, hmeq] at hte
    exact (hinv.votes v.val j (by omega) e hve (by omega) (by omega)
      (Or.inl (by linarith))).voteCompat
  rcases le_or_gt m (D.j₀ + sp.k) with hmK | hmK
  · -- R-mid: `A₀` votes in slot `m` and extends `P`; the counted set is in
    -- `K m ∩ ((H z)ᶜ ∪ W)`, at the update's time `t_m + 6Δ ≤ z`
    have hkz : tr.time k ≤ D.z :=
      D.hzc _ (by rw [ht]; linarith [ts_le_ts (sp := sp) hmK]) hcall
    have hT : D.K.committee m ∩ D.A₀ ⊆ AC.voters {v | v ∈ (tr.projAC.state y k).pool m} := by
      rintro x ⟨hxK, hx⟩
      have hcm := honestCall_mono hcall (show sp.ts m + sp.Δ ≤ tr.time k by rw [ht]; linarith)
      obtain ⟨haw, hjn⟩ := holder_ready_at D hx (by omega) hmK hcm
      exact voter_of_ready D hy hu hm
        (D.hrun.antitone (D.hzc _ (by linarith [ts_le_ts (sp := sp) hmK]) hcm) (D.hA₀ hx)) hxK
        haw hjn
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants' hR hT
      (D.hopponentsK m (by omega) hmK
        (honestCall_mono hcall (show sp.ts m ≤ tr.time k by rw [ht]; linarith)))
    have hvz : v.val ∈ H D.z := by
      rcases hvT with h | h
      · exact D.hA₀ h.2
      · by_contra hn; exact h ⟨hmemCV v hv, Or.inl hn⟩
    refine finish v hv (D.hrun.antitone hkz hvz) fun j hj e hve he hs => ?_
    rcases hvT with hA | hQ
    · exact (hinv.votes v.val j (by omega) e hve (by omega) (by omega) (Or.inr hA.2)).voteCompat
    · exact hinv.voteCompat_of_not_opponent_at (by omega) hve (by omega)
        fun _ => ⟨hvz, fun h => hQ ⟨hmemCV v hv, Or.inr h⟩⟩
  · -- R-late: every slot-`m` vote is compatible with `P` (`late`); the committee members honest
    -- at the update and awake and joined at `t_m + Δ` reach it
    have hT : D.K.committee m ∩ {x | x ∈ H (tr.time k) ∧ tr.projAC.awake x (sp.ts m + sp.Δ) ∧
        AC.JoinedAt tr.projAC x (sp.ts m + sp.Δ)} ⊆
        AC.voters {v | v ∈ (tr.projAC.state y k).pool m} := fun x hx => by
      obtain ⟨hxK, hx, hwj⟩ := hx
      obtain ⟨hw, hj⟩ := (mem_awakeJoined_projAC' D.hrun).1 hwj
      exact voter_of_ready D hy hu hm (D.hrun.antitone (by rw [ht]; linarith) hx) hxK hw hj
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants' hR hT hslot
    have hvH : v.val ∈ H (tr.time k) :=
      hvT.elim (fun h => h.2.1) fun h => not_not.1 fun hn => h ⟨hmemCV v hv, hn⟩
    exact finish v hv hvH fun j hj e hve he hs => hinv.late v.val j (by omega) e hve (by omega)

end OutageVoteInv'

end Consensus.Goldilocks.Shadow.PU

end
