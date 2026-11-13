module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers

public section

/-! # Goldilocks runs: the honest trees

The tree of an honest node only grows; its blocks are genesis and the blocks the node accepted, each
with its digest as root (from the wire, or made so by `propose_block`) and its slot's proposer (the
run's credential `LocalRun.proposerCredential`, or `Proposes` for the own block), and none with the
genesis root (genesis is held from the start). Under `NoColl` on the run, two such blocks with one
root are one block, so the honest blocks of a run are a coherent set. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {proposer : Nat → Fin P.n} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
  {ini : Fin P.n → A.State}

/-- **The tree of an honest node only grows.** -/
theorem tree_mono (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {k i : Nat} (hki : k ≤ i) : (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  induction i, hki using Nat.le_induction with
  | base => exact subset_rfl
  | succ i _ ih =>
    refine ih.trans ?_
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      exact (chain_fg y (.cons (h.cutLaw y hy i c hc) (.nil _)) (fg_reachable h hy i)).2.1
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

/-- **A block of an honest tree is genesis or was accepted by that node before.** -/
theorem tree_cases (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {X : A.Blk} (hX : X ∈ (tr.state y i).fg.tree) :
    X = P.genesisBlock A.genesisPayload ∨ ∃ k < i, tr.AcceptAt y k X := by
  induction i with
  | zero =>
    left
    change (tr.state y 0).fg.blocks X.root = some X at hX
    rw [Trace.state, h.init y hy] at hX
    change (if X.root = P.genesisRoot then some (P.genesisBlock A.genesisPayload) else none) =
      some X at hX
    split_ifs at hX
    exact (Option.some.inj hX).symm
  | succ i ih =>
    have old : X ∈ (tr.state y i).fg.tree →
        X = P.genesisBlock A.genesisPayload ∨ ∃ k < i + 1, tr.AcceptAt y k X := fun hX =>
      (ih hX).imp_right fun ⟨k, hk, hacc⟩ => ⟨k, by omega, hacc⟩
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := h.cutLaw y hy i c hc
      have hr := fg_reachable h hy i
      rw [tr.state_succ_of_call hc] at hX
      cases c with
      | ac ℓ => exact old (hlaw.2.2.1 ▸ hX)
      | fg ℓ =>
        cases ℓ with
        | block B acc =>
          cases acc with
          | true =>
            rw [(Store.tree_grows P _ _ _ hr).1 B _ hlaw.2.1] at hX
            rcases hX with rfl | hX
            exacts [Or.inr ⟨i, by omega, hc⟩, old hX]
          | false => exact old (hlaw.2 ▸ hX)
        | attestation a =>
          rw [hlaw.1, (Store.tree_grows P _ _ _ hr).2 a] at hX
          exact old hX
        | attest C s =>
          cases s with
          | none => exact old (hlaw.2 ▸ hX)
          | some a => exact old (hlaw.2.1 ▸ hX)
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩] at hX
      exact old hX

/-- **An accepted block has its digest as root, its slot's proposer, and a root not held
before** (so not the genesis root). -/
theorem accept_facts (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {k : Nat} {X : A.Blk} (hk : tr.AcceptAt y k X) :
    X.RootOk dg ∧ X.proposer = proposer X.slot ∧ (tr.state y k).fg.blocks X.root = none ∧
      X.root ≠ P.genesisRoot := by
  obtain ⟨pr, σ', -, hnew, -, -, hσ, -⟩ := Store.onBlock_eq_some (h.cutLaw y hy k _ hk).2.1
  refine ⟨?_, ?_, hnew, fun hg => ?_⟩
  · rcases blockCall_cases h hy hk with hg | ⟨j, x, -, -, -, d, p, -, rfl, -⟩
    · exact (h.wire y hy k _ _ hg).1
    · rfl
  · rcases blockCall_cases h hy hk with hg | ⟨j, x, -, -, hp, d, p, -, rfl, -⟩
    · exact h.proposerCredential y hy k _ _ hg
    · exact hp.2.2.symm
  · have hG := (Store.accepted_tree P _ _ _ (fg_reachable h hy k)).2.2.1
    change (tr.state y k).fg.blocks P.genesisRoot = some _ at hG
    rw [← hg, hnew] at hG
    cases hG

/-- `NoColl` on a smaller set. -/
theorem NoCollOn.mono {S S' : Set A.Blk} (h : NoCollOn dg S') (hS : S ⊆ S') : NoCollOn dg S :=
  fun B hB C hC => h B (hS hB) C (hS hC)

/-- **The blocks of an honest tree are genesis or occur in the run.** -/
theorem tree_subset_run (h : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    (i : Nat) :
    (tr.state y i).fg.tree ⊆ insert (P.genesisBlock A.genesisPayload) {B | tr.Occurs B} :=
  fun _ hX => (tree_cases h hy hX).imp_right fun ⟨k, _, hk⟩ => ⟨y, k, true, hk⟩

/-- **Under `NoColl`, blocks of honest trees with one root are one block.** -/
theorem tree_root_inj (h : Node.LocalRun proposer dg H sg tr ini) (hnc : NoCollRun dg tr)
    {y y' : Fin P.n}
    (hy : y ∈ H) (hy' : y' ∈ H) {i i' : Nat} {X X' : A.Blk} (hX : X ∈ (tr.state y i).fg.tree)
    (hX' : X' ∈ (tr.state y' i').fg.tree) (hr : X.root = X'.root) : X = X' := by
  rcases tree_cases h hy hX with rfl | ⟨k, -, hk⟩ <;>
    rcases tree_cases h hy' hX' with rfl | ⟨k', -, hk'⟩
  · rfl
  · exact absurd hr.symm (accept_facts h hy' hk').2.2.2
  · exact absurd hr (accept_facts h hy hk).2.2.2
  obtain ⟨hro, hpr, -⟩ := accept_facts h hy hk
  obtain ⟨hro', hpr', -⟩ := accept_facts h hy' hk'
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hnc X (Or.inr ⟨y, k, true, hk⟩) X' (Or.inr ⟨y', k', true, hk'⟩)
    (by rw [← hro, ← hro', hr])
  obtain ⟨r, pa, sl, pp, inp, fp, ap⟩ := X
  obtain ⟨r', pa', sl', pp', inp', fp', ap'⟩ := X'
  simp only at hr h₁ h₂ h₃ h₄ h₅ hpr hpr'
  subst hr h₁ h₂ h₃ h₄ h₅
  rw [hpr, hpr']

/-- **The honest blocks of a run are coherent** under `NoColl`. -/
theorem honest_blocks_coherent (h : Node.LocalRun proposer dg H sg tr ini)
    (hnc : NoCollRun dg tr) :
    Coherent (tr.HonestBlocks H) := by
  refine ⟨fun X ⟨y, hy, i, hX⟩ X' ⟨y', hy', i', hX'⟩ hr => tree_root_inj h hnc hy hy' hX hX' hr,
    fun Y ⟨y', hy', i', hY⟩ X ⟨y, hy, i, hX⟩ hp => ?_⟩
  rcases tree_cases h hy hX with rfl | ⟨k, hki, hk⟩
  · cases hp
  -- the parent of `X` is held where `X` is accepted
  obtain ⟨pr, -, hpar, -, hheld, -⟩ := Store.onBlock_eq_some (h.cutLaw y hy k _ hk).2.1
  rw [hp] at hpar
  obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hheld
  have hZr := (fg_reachable h hy k).blocks_root hZ
  have hZt : Z ∈ (tr.state y k).fg.tree := by
    change _ = _
    rw [hZr, hZ]
  cases Option.some.inj hpar
  obtain rfl : Z = Y := tree_root_inj h hnc hy hy' hZt hY hZr
  exact (Store.accepted_tree P _ _ _ (fg_reachable h hy i)).2.1.2 Z (tree_mono h hy hki.le hZt)
    X hX hp

end Consensus.Goldilocks.Compose

end
