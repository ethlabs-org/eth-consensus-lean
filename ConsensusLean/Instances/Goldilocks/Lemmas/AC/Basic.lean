module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry
public import Mathlib.Order.Preorder.Finite

public section

/-! # Goldilocks SA: shared helpers for the AC proofs

Blocks by root (`lookup`, `InTree`, `AncR`), ancestry in a frame, and the extended time line.
The viable ancestor of claims G0.4 (frame) (`viableAncestor_spec`, `viableAncestor_self`, for
every AC payload type) is proved here: `Lemmas.Common` cannot import `Spec.Frame`. A successful
optimistic selection is guarded by its slot and time and picks a block of the tree
(`optimisticSelect_guard`, `optimisticSelect_mem_tree`). -/

namespace Consensus.Goldilocks.SA

variable {n : Nat} {FGP : Type} {ACP : Type}

/-- The characterisation of a start up to the vote permission (`VoteStart`,
`Milestones/Spec/SA/Trace`). The AC invariants of the initial state that do not read `mayVote`
hold at every such start. -/
theorem voteStart_iff {g : Nat} {s : SAState n} :
    VoteStart g s ↔ ∃ m, s = { SAState.initial g with mayVote := m } :=
  Iff.rfl

/-- The pools of a start up to the vote permission are empty. -/
theorem VoteStart.pool {g : Nat} {s : SAState n} (h : VoteStart g s) (σ : Nat) :
    s.pool σ = [] := by
  obtain ⟨m, rfl⟩ := h
  rfl

/-- An AC run from the start `s₀` is a run of the AC whose initial state is `s₀`: the states
reachable from `s₀` are the reachable states of `{A with initial := s₀}`. -/
theorem _root_.Consensus.Goldilocks.ACInterface.reachableAtFrom_iff {P : Params}
    {A : ACInterface P FGP} {s₀ : A.State} {self : Fin P.n} {U : Set A.Blk} {s : A.State}
    {Φ : A.Frm} {t : Time} :
    A.ReachableAtFrom s₀ self U s Φ t ↔
      ({ A with initial := s₀ } : ACInterface P FGP).ReachableAt self U s Φ t := by
  constructor
  · intro h
    induction h with
    | init Φ hi hin => exact .init (A := { A with initial := s₀ }) Φ hi hin
    | step c _ ht hok ih =>
      cases c with
      | tick => exact .step (A := { A with initial := s₀ }) .tick ih ht hok
      | proposal => exact .step (A := { A with initial := s₀ }) .proposal ih ht hok
      | toFG => exact .step (A := { A with initial := s₀ }) .toFG ih ht hok
      | message m => exact .step (A := { A with initial := s₀ }) (.message m) ih ht hok
      | block B => exact .step (A := { A with initial := s₀ }) (.block B) ih ht hok
      | restart => exact .step (A := { A with initial := s₀ }) .restart ih ht hok
  · intro h
    refine ACInterface.ReachableAtFrom.rec (A := { A with initial := s₀ })
      (motive := fun s Φ t _ => A.ReachableAtFrom s₀ self U s Φ t)
      (fun Φ hi hin => .init (A := A) Φ hi hin) (fun c _ ht hok ih => ?_) h
    cases c with
    | tick => exact .step (A := A) .tick ih ht hok
    | proposal => exact .step (A := A) .proposal ih ht hok
    | toFG => exact .step (A := A) .toFG ih ht hok
    | message m => exact .step (A := A) (.message m) ih ht hok
    | block B => exact .step (A := A) (.block B) ih ht hok
    | restart => exact .step (A := A) .restart ih ht hok

/-- A call of `{A with initial := s₀}` as the same call of `A`. -/
def _root_.Consensus.Goldilocks.ACInterface.Call.ofStart {P : Params} {A : ACInterface P FGP}
    {s₀ : A.State} : ({ A with initial := s₀ } : ACInterface P FGP).Call → A.Call
  | .tick => .tick
  | .proposal => .proposal
  | .toFG => .toFG
  | .message m => .message m
  | .block B => .block B
  | .restart => .restart

/-- A call of `A` as the same call of `{A with initial := s₀}`. -/
def _root_.Consensus.Goldilocks.ACInterface.Call.toStart {P : Params} {A : ACInterface P FGP}
    {s₀ : A.State} : A.Call → ({ A with initial := s₀ } : ACInterface P FGP).Call
  | .tick => .tick
  | .proposal => .proposal
  | .toFG => .toFG
  | .message m => .message m
  | .block B => .block B
  | .restart => .restart

/-- Converting a call of `A` to the same call of `{A with initial := s₀}` and back returns the
original call. -/
theorem _root_.Consensus.Goldilocks.ACInterface.Call.ofStart_toStart {P : Params}
    {A : ACInterface P FGP} {s₀ : A.State} (c : A.Call) : (c.toStart (s₀ := s₀)).ofStart = c := by
  cases c <;> rfl

/-- The call law of `{A with initial := s₀}` is the call law of `A`. -/
theorem _root_.Consensus.Goldilocks.ACInterface.callOK_ofStart {P : Params}
    {A : ACInterface P FGP} {s₀ : A.State} {U : Set A.Blk} {Φ Φ' : A.Frm} {t : Time}
    {c : ({ A with initial := s₀ } : ACInterface P FGP).Call} :
    ({ A with initial := s₀ } : ACInterface P FGP).CallOK U Φ t c Φ' ↔
      A.CallOK U Φ t c.ofStart Φ' := by
  cases c <;> rfl

/-- A call of `{A with initial := s₀}` steps as the same call of `A`. -/
theorem _root_.Consensus.Goldilocks.ACInterface.step_ofStart {P : Params}
    {A : ACInterface P FGP} {s₀ : A.State} {self : Fin P.n} {s : A.State} {Φ : A.Frm} {t : Time}
    {c : ({ A with initial := s₀ } : ACInterface P FGP).Call} :
    ({ A with initial := s₀ } : ACInterface P FGP).step self s Φ t c =
      A.step self s Φ t c.ofStart := by
  cases c <;> rfl

/-- F.2 (b) for blocks of the SA (`Anc.total`). -/
theorem anc_total {S : Set (Blk n FGP)} {A A' C : Blk n FGP} (hS : Coherent S)
    (h : Anc S A C) (h' : Anc S A' C) : Anc S A A' ∨ Anc S A' A :=
  h.total hS h'

/-- An ancestor inside the tree of a block of the tree is in the tree. -/
theorem mem_of_anc {Φ : Frame n FGP ACP} {A B : Block n FGP ACP} (h : Φ.Anc A B)
    (hB : B ∈ Φ.tree) :
    A ∈ Φ.tree := by
  by_cases hAB : A = B
  · exact hAB ▸ hB
  · exact (Anc.mem h hAB).1

/-- **G0.4 (frame), the viable ancestor exists.** In a well-formed frame, a block of the tree has
a viable ancestor: the deepest (by slot) ancestor that is at or below `fc_root` or viable; `Φ.F`
is one, and the ancestors of a block form a chain. -/
theorem exists_isViableAncestor {Φ : Frame n FGP ACP} (hΦ : FrameOK Φ) {B : Block n FGP ACP}
    (hB : B ∈ Φ.tree) : ∃ A, Φ.IsViableAncestor B A := by
  have hfin : {A | Φ.Anc A B ∧ Φ.AncestorCandidate A}.Finite :=
    hΦ.finite.subset fun A hA => mem_of_anc hA.1 hB
  obtain ⟨A, ⟨hAB, hAc⟩, hmax⟩ := hfin.exists_maximalFor (fun A : Block n FGP ACP => A.slot) _
    ⟨Φ.F, hΦ.rooted.2 B hB, Or.inl hΦ.F_anc_fcRoot⟩
  refine ⟨A, hAB, hAc, fun A' hA'B hA'c => ?_⟩
  rcases hA'B.total hΦ.coherent hAB with h | h
  · exact h
  · by_cases hne : A = A'
    · exact hne ▸ Relation.ReflTransGen.refl
    · have hlt := (h.slot_le hΦ.coherent).2 hne
      exact absurd (hmax ⟨hA'B, hA'c⟩ (Nat.le_of_lt hlt)) (Nat.not_le.mpr hlt)

open Classical in
/-- `viableAncestor` returns the viable ancestor of a block of a well-formed frame. -/
theorem viableAncestor_spec {Φ : Frame n FGP ACP} (hΦ : FrameOK Φ) {B : Block n FGP ACP}
    (hB : B ∈ Φ.tree) :
    Φ.IsViableAncestor B (Φ.viableAncestor B) := by
  have h := exists_isViableAncestor hΦ hB
  unfold Frame.viableAncestor
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- **G0.4 (frame), self.** A block of the tree that is viable or at or below `fc_root` is its own
viable ancestor. -/
theorem viableAncestor_self {Φ : Frame n FGP ACP} (hΦ : FrameOK Φ) {B : Block n FGP ACP}
    (hB : B ∈ Φ.tree)
    (hc : B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot) : Φ.viableAncestor B = B := by
  obtain ⟨hAB, -, hmax⟩ := viableAncestor_spec hΦ hB
  exact Anc.antisymm hΦ.coherent hAB (hmax B Relation.ReflTransGen.refl hc.symm)

open Classical in
/-- `viableAncestor B` is an ancestor of `B` in the tree, in any frame. -/
theorem anc_viableAncestor (Φ : Frm n FGP) (B : Blk n FGP) : Φ.Anc (Φ.viableAncestor B) B := by
  unfold Frame.viableAncestor
  split_ifs with h
  · exact h.choose_spec.1
  · exact Relation.ReflTransGen.refl

/-- The viable ancestor of a block of a well-formed frame is in the tree, below the block. -/
theorem viableAncestor_anc {Φ : Frm n FGP} (hΦ : FrameOK Φ) {B : Blk n FGP} (hB : B ∈ Φ.tree) :
    Φ.viableAncestor B ∈ Φ.tree ∧ Φ.Anc (Φ.viableAncestor B) B :=
  ⟨mem_of_anc (viableAncestor_spec hΦ hB).1 hB, (viableAncestor_spec hΦ hB).1⟩

open Classical in
theorem deepest_mem {Φ : Frm n FGP} {S : Set (Blk n FGP)} {D : Blk n FGP}
    (h : deepest Φ S = some D) : IsDeepest Φ S D := by
  unfold deepest at h
  split_ifs at h with hS
  cases h
  exact hS.choose_spec

open Classical in
theorem lookup_eq_some {Φ : Frm n FGP} {r : Nat} {H : Blk n FGP} (h : lookup Φ r = some H) :
    H ∈ Φ.tree ∧ H.root = r := by
  unfold lookup at h
  split_ifs at h with hr
  cases h
  exact hr.choose_spec

open Classical in
theorem lookup_eq_none {Φ : Frm n FGP} {r : Nat} (h : lookup Φ r = none) : ¬ InTree Φ r := by
  unfold lookup at h
  split_ifs at h with hr
  exact hr

/-- A resolved vote (finite resolution time) has its head in the tree. -/
theorem inTree_of_resolutionTime_ne_top {A : SAState n} {Φ : Frm n FGP} {v : Vote n}
    (h : resolutionTime A Φ v ≠ ⊤) : InTree Φ v.head := by
  unfold resolutionTime at h
  split at h
  · exact absurd rfl h
  · rename_i H hH
    obtain ⟨hm, hr⟩ := lookup_eq_some hH
    exact ⟨H, hm, hr⟩

/-- In a rooted frame, every block of the tree is compatible with `Φ.F`. -/
theorem compatible_F {Φ : Frm n FGP} (hΦ : FrameOK Φ) {H : Blk n FGP} (hH : H ∈ Φ.tree) :
    Compatible Φ.tree H Φ.F :=
  Or.inr (hΦ.rooted.2 H hH)

/-- Ancestry inside a coherent `U` between two blocks of a well-formed frame tree contained in
`U` is ancestry inside the tree. -/
theorem anc_tree_of_anc_U {U : Set (Blk n FGP)} (hU : Coherent U) {Φ : Frm n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {B C : Blk n FGP} (hB : B ∈ Φ.tree)
    (h : Anc U B C) : C ∈ Φ.tree → Φ.Anc B C := by
  exact Frame.anc_tree_of_anc_U hU hΦ hΦU hB h

/-- In a well-formed frame, depth strictly increases along strict ancestry. -/
theorem depth_lt_of_anc {Φ : Frm n FGP} (hΦ : FrameOK Φ) {A B : Blk n FGP}
    (h : Φ.Anc A B) (hne : A ≠ B) (hB : B ∈ Φ.tree) : depth Φ A < depth Φ B := by
  refine Set.ncard_lt_ncard ⟨fun X hX => hX.trans h, fun hsub => hne ?_⟩
    (hΦ.finite.subset fun X hX => mem_of_anc hX hB)
  exact Anc.antisymm hΦ.coherent h (hsub (Relation.ReflTransGen.refl : Φ.Anc B B))

section Optimistic

variable {sp : SAParams}

open Classical in
/-- A successful optimistic selection at `t` is made by a joined node, in a slot `slot(t) > 0`,
before `t_{slot(t)} + 2Δ`. -/
theorem optimisticSelect_guard {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {B : Blk sp.n FGP} (h : optimisticSelect sp A Φ t = some B) :
    joined sp A t ∧ sp.slot t ≠ 0 ∧ t < sp.ts (sp.slot t) + 2 * sp.Δ := by
  unfold optimisticSelect at h
  dsimp only at h
  split_ifs at h with hc
  simp only [not_or, not_not, not_le] at hc
  exact hc

open Classical in
/-- The block of a successful optimistic selection is in the frame's tree. -/
theorem optimisticSelect_mem_tree {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {B : Blk sp.n FGP} (h : optimisticSelect sp A Φ t = some B) : B ∈ Φ.tree := by
  unfold optimisticSelect at h
  dsimp only at h
  split_ifs at h
  exact (deepest_mem h).1.1

end Optimistic

end Consensus.Goldilocks.SA

end
