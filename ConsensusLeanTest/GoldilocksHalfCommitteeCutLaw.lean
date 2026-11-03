module
public import ConsensusLeanTest.GoldilocksHalfCommitteeNode
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Trace
@[expose] public section

/-! # A computable mirror of the Goldilocks node: the cut law on data, checks along lists

Additions to the mirror (`GoldilocksHalfCommitteeNode`) for the concrete runs of
`GoldilocksHalfCommitteeRun`:

* `frag_init`: the initial node data is in the fragment (the base of `Frag` along a schedule);
* `postsD`: the node data after each cut of `execD`, and `chainOK_postsD`: the cut law's
  post-states (`Node.cutPost`) along the cuts of `Node.exec` are their interpretations, so every
  intermediate state of a run's group is the mirror's (`foldl_take_chainOK`);
* `allPre` and `scanOK`: Boolean checks along a list, with the earlier elements and with the
  latest wake of a node, that the kernel evaluates on a run's cuts (`allPre_spec`,
  `scanOK_spec`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA

namespace Fix

variable {X : Fix}

theorem frag_init (X : Fix) : X.Frag (NodeD.init X) :=
  ⟨⟨List.mem_singleton_self _, fun r hr => by rw [List.mem_singleton.1 hr]; exact valid_g,
    fun r hr hg => absurd (List.mem_singleton.1 hr) hg⟩, List.nodup_singleton _⟩

/-- The node data after each cut of `execD` (the cut law's post-states, on data). -/
def postsD (d : X.NodeD) (self : Fin X.sp.n) (t : Int) : X.EvD → List X.NodeD
  | .tick _ =>
    let r₁ := d.ac.onTick self d.fg.tree t
    let r₂ := r₁.1.toFG d.fg.tree t
    let d₂ : X.NodeD := ⟨d.fg, r₂.1, d.signed⟩
    match r₂.2 with
    | none => [⟨d.fg, r₁.1, d.signed⟩, d₂]
    | some _ =>
      match X.attestD d.signed self with
      | none => [⟨d.fg, r₁.1, d.signed⟩, d₂, d₂]
      | some a => [⟨d.fg, r₁.1, d.signed⟩, d₂, ⟨d.fg, r₂.1, true⟩, ⟨d.fg.onAtt a, r₂.1, true⟩]
  | .block r =>
    if slotT t < X.slotR r then []
    else
      match d.fg.onBlock r with
      | none => [d]
      | some fg' => [⟨fg', d.ac, d.signed⟩, ⟨fg', (d.ac.onBlk self fg'.tree t r).1, d.signed⟩]
  | .message v => [⟨d.fg, (d.ac.onMsg self d.fg.tree t v).1, d.signed⟩]
  | .attestation a => [⟨d.fg.onAtt a, d.ac, d.signed⟩]
  | .restart => [⟨d.fg, d.ac.restart d.fg.tree t, d.signed⟩]

end Fix

/-- A chain of steps: each element of `ss` is `f` of the previous one and the matching `c`. -/
def ChainOK {S C : Type} (f : S → C → S) : S → List C → List S → Prop
  | _, [], _ => True
  | s, c :: cs, s' :: ss => f s c = s' ∧ ChainOK f s' cs ss
  | _, _ :: _, [] => False

theorem foldl_take_chainOK {S C : Type} {f : S → C → S} :
    ∀ {s : S} {cs : List C} {ss : List S}, ChainOK f s cs ss →
      ∀ p ≤ cs.length, ∀ z, (cs.take p).foldl f s = (s :: ss).getD p z
  | _, [], _, _, p, hp, _ => by simp at hp; subst hp; rfl
  | _, _ :: _, [], h, _, _, _ => h.elim
  | s, c :: cs, s' :: ss, h, p, hp, z => by
    rcases p with _ | p
    · rfl
    · simp only [List.take_succ_cons, List.foldl_cons, h.1]
      simpa using foldl_take_chainOK h.2 p (by simpa using hp) z

namespace Fix

variable {X : Fix} (ro : ReplayOrder X.sp (List (FG.Att X.sp.n)))

theorem cutPost_ac (self : Fin X.sp.n) (t : Int) (d : X.NodeD) (c : CallD X) (M : List Nat)
    (ems : List X.EmD) :
    Node.cutPost self t (d.interp ro) ((CutD.ac c M ems).interp ro) =
      ⟨d.fg.interp, ((X.AC ro).step self d.ac.interp (X.frameOf M) t (c.interp ro)).1,
        X.recI d.signed⟩ := rfl

/-- The cut law along `execD`: the post-states of the cuts are the interpretations of
`postsD`. -/
theorem chainOK_postsD (hX : X.OK) (self : Fin X.sp.n) {d : X.NodeD} (hF : X.Frag d) {t : Int}
    (ht : 0 ≤ t) {e : X.EvD} (he : e.OK) :
    ChainOK (Node.cutPost self t) (d.interp ro) ((execD d self t e).2.map (CutD.interp ro))
      ((postsD d self t e).map (NodeD.interp ro)) := by
  cases e with
  | tick x =>
    simp only [execD, postsD]
    have h1 : Node.cutPost self t (d.interp ro) ((CutD.ac .tick d.fg.tree
        (d.ac.onTick self d.fg.tree t).2).interp ro) =
        NodeD.interp ro ⟨d.fg, (d.ac.onTick self d.fg.tree t).1, d.signed⟩ := by
      rw [cutPost_ac]
      simp only [CallD.interp, ACInterface.step, acOnTick_eq hX hF.1 hF.2, resI]; rfl
    have h2 : Node.cutPost self t (NodeD.interp ro ⟨d.fg, (d.ac.onTick self d.fg.tree t).1,
        d.signed⟩) ((CutD.ac .toFG d.fg.tree []).interp ro) = NodeD.interp ro
        ⟨d.fg, ((d.ac.onTick self d.fg.tree t).1.toFG d.fg.tree t).1, d.signed⟩ := by
      rw [cutPost_ac]
      simp only [CallD.interp, ACInterface.step, acToFG_eq hX hF.1, resF]; rfl
    cases hc : ((d.ac.onTick self d.fg.tree t).1.toFG d.fg.tree t).2 with
    | none => simp only; exact ⟨h1, h2, trivial⟩
    | some c =>
      cases ha : X.attestD d.signed self with
      | none => simp only; exact ⟨h1, h2, rfl, trivial⟩
      | some a =>
        simp only
        refine ⟨h1, h2, ?_, ?_, trivial⟩
        · change (⟨_, _, _⟩ : NodeState (X.AC ro)) = _
          simp only [NodeD.interp, attest_interp hX, ha, Option.map_some, Option.getD_some]
        · change (⟨_, _, _⟩ : NodeState (X.AC ro)) = _
          simp only [NodeD.interp, onAtt_interp]
  | block r =>
    have hr : r ∈ X.roots := he
    simp only [execD, postsD]
    split_ifs
    · trivial
    · cases h : d.fg.onBlock r with
      | none => exact ⟨rfl, trivial⟩
      | some fg' =>
        have hr1 : r ∉ d.fg.tree ∧ X.par r ∈ d.fg.tree := by
          unfold FGD.onBlock at h; split_ifs at h with hc
          exact not_or.1 hc |>.imp id not_not.1
        have hfg : fg' = ⟨r :: d.fg.tree, d.fg.atts⟩ := by
          unfold FGD.onBlock at h
          rw [ite_eq_right (by tauto)] at h
          exact (Option.some_injective _ h).symm
        have hM' : X.Closed fg'.tree := hfg ▸ closed_cons hF.1 hr hr1.2
        have hnd' : fg'.tree.Nodup := hfg ▸ List.nodup_cons.2 ⟨hr1.1, hF.2⟩
        refine ⟨?_, ?_, trivial⟩
        · change (⟨_, _, _⟩ : NodeState (X.AC ro)) = _
          simp only [NodeD.interp, onBlock_interp hX hF.1 hr, h, Option.map_some,
            Option.getD_some]
        · rw [cutPost_ac]
          simp only [CallD.interp, ACInterface.step, acOnBlock_eq hX hM' hnd' _ self t (Or.inr hr),
            resI]; rfl
  | message v =>
    refine ⟨?_, trivial⟩
    rw [cutPost_ac]
    simp only [CallD.interp, ACInterface.step, acOnMessage_eq hX hF.1 hF.2, resI]; rfl
  | attestation a =>
    refine ⟨?_, trivial⟩
    change (⟨_, _, _⟩ : NodeState (X.AC ro)) = _
    simp only [NodeD.interp, onAtt_interp]
  | restart =>
    refine ⟨?_, trivial⟩
    rw [cutPost_ac]
    simp only [CallD.interp, ACInterface.step, acRestart_eq hX hF.1 hF.2 ro self _ ht]; rfl

end Fix

theorem getD_map {α β : Type} (f : α → β) (l : List α) (p : Nat) (z : α) :
    (l.map f).getD p (f z) = f (l.getD p z) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]; cases l[p]? <;> rfl

/-! ## Checks along a list -/

/-- `P` at every element with the earlier ones (newest first). -/
def allPre {α : Type} (P : List α → α → Bool) : List α → List α → Bool
  | _, [] => true
  | acc, a :: as => P acc a && allPre P (a :: acc) as

theorem allPre_spec {α : Type} {P : List α → α → Bool} :
    ∀ {L acc : List α}, allPre P acc L = true →
      ∀ i (h : i < L.length), P ((L.take i).reverse ++ acc) L[i] = true
  | [], _, _, i, h => absurd h (Nat.not_lt_zero _)
  | a :: as, acc, hL, i, h => by
    simp only [allPre, Bool.and_eq_true] at hL
    rcases i with _ | i
    · simpa using hL.1
    · have := allPre_spec hL.2 i (by simpa using h)
      simpa using this

theorem mem_take_getElem {α : Type} {L : List α} {i : Nat} {a : α} (h : a ∈ L.take i) :
    ∃ j, ∃ hj : j < L.length, j < i ∧ L[j] = a := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_take] at hj
  exact ⟨j, by omega, by omega, by simp⟩

/-- A scan along a list with an accumulated wake `w` (updated by `wk` at each element): it succeeds
at the first element satisfying `P`, and fails at an element satisfying `Q` before it. -/
def scanOK {α : Type} (wk : Option Nat → α → Option Nat) (P Q : Option Nat → α → Bool) :
    List α → Option Nat → Bool
  | [], _ => true
  | a :: as, w =>
    if P (wk w a) a then true else if Q (wk w a) a then false else scanOK wk P Q as (wk w a)

/-- A successful scan: every element satisfying `Q` has an element at or before it satisfying
`P`, with the wakes accumulated up to each. -/
theorem scanOK_spec {α : Type} {wk : Option Nat → α → Option Nat} {P Q : Option Nat → α → Bool} :
    ∀ {L : List α} {w : Option Nat}, scanOK wk P Q L w = true → ∀ j (hj : j < L.length),
      Q ((L.take (j + 1)).foldl wk w) L[j] = true →
      ∃ i ≤ j, ∃ hi : i < L.length, P ((L.take (i + 1)).foldl wk w) L[i] = true
  | [], _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | a :: as, w, h, j, hj, hq => by
    simp only [scanOK] at h
    by_cases hp : P (wk w a) a = true
    · exact ⟨0, Nat.zero_le _, by simp, by simpa using hp⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      rcases j with _ | j
      · simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
          List.getElem_cons_zero] at hq
        simp only [hq, ↓reduceIte] at h; cases h
      · by_cases hq' : Q (wk w a) a = true
        · simp only [hq', ↓reduceIte] at h; cases h
        · simp only [hq', Bool.false_eq_true, ↓reduceIte] at h
          simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ] at hq
          obtain ⟨i, hi, hi', hpi⟩ := scanOK_spec h j (by simpa using hj) hq
          exact ⟨i + 1, by omega, by simpa using hi', by simpa using hpi⟩

end Consensus.Goldilocks.Test.HalfCommittee

end
