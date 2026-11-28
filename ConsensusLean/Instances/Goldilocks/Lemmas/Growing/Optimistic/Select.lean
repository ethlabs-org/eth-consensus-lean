module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Optimistic.Delivery
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic inclusion: every optimistic check of the window selects the proposal

Let `Q` be a set of slot-`p` committee members honest through `t_p + 2Δ`, at least three
quarters of the committee size, and let every slot-`p` vote of a node honest at `t_p + Δ` name
the proposal `P`. Then at every optimistic check of a node honest at its call, by `t_p + 2Δ`, with
`P` in the frame:

* every block with three quarters of the committee as optimistic voters lies below `P`
  (`optimistic_pass_anc`): its quorum meets `Q` (`quorums_meet`) in a member whose pool vote is
  genuine (`optimisticPoint_pool_voteU`), so names `P`;
* when the check sees `P` pass and no live lock conflicts with `P`, it selects `P`
  (`optimisticSelect_eq_proposal`).

Every step is proved. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams Vote Payload)

section Deepest

variable {n : Nat} {FGP : Type}

/-- A block of `S` above every block of `S` is its deepest block. -/
private theorem deepest_eq_of_anc {Φ : AC.Frm n FGP} (hΦ : FrameOK Φ) {S : Set (AC.Blk n FGP)}
    {P : AC.Blk n FGP} (hP : P ∈ S) (hPt : P ∈ Φ.tree) (hS : ∀ C ∈ S, Φ.Anc C P) :
    AC.deepest Φ S = some P := by
  have h : AC.IsDeepest Φ S P :=
    ⟨hP, fun C hC hne => Or.inl (AC.depth_lt_of_anc hΦ (hS C hC) hne hPt)⟩
  cases hd : AC.deepest Φ S with
  | none =>
    unfold AC.deepest at hd
    simp only [show ∃ B, AC.IsDeepest Φ S B from ⟨P, h⟩, ↓reduceDIte, reduceCtorEq] at hd
  | some D =>
    have h' := AC.deepest_mem hd
    by_contra hne
    have hne' : D ≠ P := fun h => hne (congrArg some h)
    rcases h.2 D h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 P h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

end Deepest

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- **A genuine pool vote at an optimistic point**: a vote of the pool of an optimistic point of a
node honest at its call, whose validator is honest then, was cast by it no later. -/
private theorem optimisticPoint_pool_vote_at {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i))
    {ℓ : ACLabel (goldilocksNode sp)} {A : AC.ACState sp.n}
    (hpt : AC.OptimisticPoint tr.projAC y i ℓ A) {σ : Nat} {v : Vote sp.n} (hv : v ∈ A.pool σ)
    (hvH : v.val ∈ H (tr.time i)) :
    v.slot = σ ∧ ∃ j ≤ i, ∃ e, AC.VoteAt tr.projAC v.val j e ∧ e.msg = v := by
  obtain ⟨hs, j, hj, e, hve, hev⟩ := AC.optimisticPoint_pool_voteU
    (acRun_upTo hrun hnc (hrun.time_nonneg i)).toU hy
    ((AC.upTo_optimisticPoint hrun.time_mono).mpr ⟨le_rfl, hpt⟩) hv hvH
  exact ⟨hs, j, hj, e, (ac_voteAt_upTo.mp hve).2, hev⟩

/-- **A0: every optimistic quorum of the window lies below the proposal.** At an optimistic point
of a node honest at its call, by `t_p + 2Δ`, with `P` in the frame, a block of the frame with
three quarters of the committee size as slot-`p` optimistic voters is an ancestor of `P`. -/
theorem optimistic_pass_anc {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hcs : 0 < sp.committeeSize) {p : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hU : Healing.Unanimous tr (H (sp.ts p + sp.Δ)) p P) {Q : Set (Fin sp.n)}
    (hQK : Q ⊆ K.committee p) (hQH : Q ⊆ H (sp.ts p + 2 * sp.Δ))
    (hQ : 3 * sp.committeeSize ≤ 4 * Q.ncard) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) (hti : tr.time i ≤ sp.ts p + 2 * sp.Δ)
    {ℓ : ACLabel (goldilocksNode sp)} {A : AC.ACState sp.n}
    (hpt : AC.OptimisticPoint tr.projAC y i ℓ A) (hP : P ∈ ℓ.frame.tree)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (h3 : 3 * sp.committeeSize ≤ 4 * (AC.optimisticVoters sp A ℓ.frame p B).ncard) :
    ℓ.frame.Anc B P := by
  have hsz := hKB.hsize p
  obtain ⟨w, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, hwQ⟩, -⟩ :=
    AC.quorums_meet (F := (∅ : Set (Fin sp.n))) (K.committee p) hsz
      (by rintro u ⟨v, hv, rfl, -⟩; exact hKB.hP.2 y i ℓ A hy hpt p v hv) hQK h3 hQ
      (by rw [Set.inter_empty, Set.ncard_empty, hsz]; omega)
  have hw2 := hQH hwQ
  obtain ⟨hvs, j, -, e, hve, rfl⟩ :=
    optimisticPoint_pool_vote_at hrun hnc hy hpt hv (hrun.antitone hti hw2)
  have hhead := hU _ (hrun.antitone (by linarith [sp.toParams.hΔ]) hw2) j e hve hvs
  obtain ⟨hΦ, -⟩ := frameIn_at hrun hnc hy hpt.1
  obtain rfl : R = P := hΦ.coherent.1 hR hP (hRr.trans hhead)
  exact hBR

/-- **A1: the optimistic check selects the proposal.** At an optimistic point of a node honest
at its call, at a time of `[t_p, t_p + 2Δ)` with `p > 0` and the switch on, joined, with `P` in the
frame passing the three-quarter test and no live lock conflicting with `P`, the check selects
`P`. -/
theorem optimisticSelect_eq_proposal {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hopt : sp.optimistic = true) {K : AC.CommitteeDict sp.n}
    (hKB : CommitteeFacts tr H K) (hcs : 0 < sp.committeeSize) {p : Nat} (hp : 0 < p)
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hU : Healing.Unanimous tr (H (sp.ts p + sp.Δ)) p P) {Q : Set (Fin sp.n)}
    (hQK : Q ⊆ K.committee p) (hQH : Q ⊆ H (sp.ts p + 2 * sp.Δ))
    (hQ : 3 * sp.committeeSize ≤ 4 * Q.ncard) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) (hti₀ : sp.ts p ≤ tr.time i) (hti : tr.time i < sp.ts p + 2 * sp.Δ)
    {ℓ : ACLabel (goldilocksNode sp)} {A : AC.ACState sp.n}
    (hpt : AC.OptimisticPoint tr.projAC y i ℓ A) (hj : AC.joined sp A (tr.time i))
    (hP : P ∈ ℓ.frame.tree)
    (hPass : 3 * sp.committeeSize ≤ 4 * (AC.optimisticVoters sp A ℓ.frame p P).ncard)
    (hlock : ¬ AC.conflictsWithLock sp A.locks ℓ.frame (tr.time i) P) :
    AC.optimisticSelect sp A ℓ.frame (tr.time i) = some P := by
  have hs : sp.slot (tr.time i) = p :=
    AC.CompatibleSides.slot_of_lt hti₀ (by linarith [sp.toParams.hΔ])
  unfold AC.optimisticSelect
  dsimp only
  have hc : ¬ (¬ AC.joined sp A (tr.time i) ∨ p = 0 ∨ sp.ts p + 2 * sp.Δ ≤ tr.time i ∨
      sp.optimistic = false) := by
    rintro (h | h | h | h)
    · exact h hj
    · omega
    · linarith
    · simp [hopt] at h
  rw [hs]
  simp only [hc, ↓reduceIte]
  obtain ⟨hΦ, -⟩ := frameIn_at hrun hnc hy hpt.1
  exact deepest_eq_of_anc hΦ ⟨hP, hPass, hlock⟩ hP fun C ⟨_, hC, _⟩ =>
    optimistic_pass_anc hrun hnc hKB hcs hU hQK hQH hQ hy hti.le hpt hP hC

end Consensus.Goldilocks.Compose.Growing

end
