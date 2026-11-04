module
public import ConsensusLeanTest.GoldilocksConflictChains
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
@[expose] public section

/-! # Run-level rejection: two honest finalized tips conflict once the fault bound is dropped

Kind (r) for R.7 `FinalizedSafe` (`Regimes.FinalizedSafe`), with its other premises met, and
kind (a) for `FinalAccountable` and `NonFraming` on the same run (CONTRIBUTING "Statements").
The run `conflictRun` is a hand-built `GoldilocksRun` over the parameters of
`GoldilocksConflictChains` (`n = 6`, `q = 4`, `2q − n = 2`, `Δ = 2`, `t_s = 8s`, `k = c = 2`):

* validators `0, 1, 2, 3` are faulty (`f = 4 ≥ 2q − n`) and validator `0` proposes every slot;
  they sign both chains of `GoldilocksConflictChains`, so every quorum signer is faulty and no
  honest node signs anything;
* the honest validators `4` and `5` are awake at one odd (non-public) time each, `25` and `27`
  (after `t_3 = 24`), so neither ticks: each restarts and is delivered the three blocks of one
  chain, `4` chain A and `5` chain B. Every honest cut is a cut of the node's own handler
  (`Node.exec` of the restart and of each delivery, at consecutive indices), and every honest
  state is the one those handlers leave.

* `conflictRun_goldilocksRun`, `conflictRun_noColl`: the run is a `GoldilocksRun` with
  `NoCollRun` (the digest `dg6` is injective on the run's blocks).
* `conflicting_finalized`: node `4` finalizes the first block of chain A and node `5` the first
  block of chain B, and the two are incompatible among the honest blocks.
* `finalizedSafe_needs_fault_bound`: `FinalizedSafe` without its premise `f < 2q − n` is false;
  `conflictRun_faults` gives `f = 4` and `2q − n = 2` here.
* `conflictRun_accountable`: the proved `final_accountable` and `non_framing` on the run: at least
  `2q − n` validators are convicted from the chains the two honest readers hold, and no honest
  validator signs a slashable pair. -/

namespace Consensus.Goldilocks.ConflictRun

open FG

/-- `if_pos` for any decidability instance (`Trace.state` decides classically). -/
theorem ite_pos {α : Type*} {p : Prop} {d : Decidable p} (h : p) (a b : α) :
    @ite α p d a b = a := by simp [h]

/-- `if_neg` for any decidability instance. -/
theorem ite_neg {α : Type*} {p : Prop} {d : Decidable p} (h : ¬ p) (a b : α) :
    @ite α p d a b = b := by simp [h]

/-! ## The honest nodes' states -/

/-- The stores after `k` blocks of chain `c`. -/
def sF (c : Bool) : Nat → Store P6 (SA.Payload 6)
  | 0 => s₀
  | 1 => s₁ c
  | 2 => s₂ c
  | _ => s₃ c

theorem onBlock_sF (c : Bool) {k : Nat} (hk : k < 3) :
    (sF c k).onBlock (blk c (k + 1)) = some (sF c (k + 1)) := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · exact onBlock₁ c
  · exact onBlock₂ c
  · exact onBlock₃ c

/-- The initial node state. -/
noncomputable abbrev n₀ : NodeState Nd := Node.init Nd

/-- The state of node `v` (at time `T`) after its restart and `k` blocks of chain `c`. -/
noncomputable def stK (c : Bool) (v : Fin 6) (T : Time) : Nat → NodeState Nd
  | 0 => (Node.acCall v n₀ T .restart).1
  | k + 1 => (Node.acCall v { stK c v T k with fg := sF c (k + 1) } T (.block (blk c (k + 1)))).1

/-- The state between the FG and the AC cut of block `k + 1`. -/
noncomputable def mid (c : Bool) (v : Fin 6) (T : Time) (k : Nat) : NodeState Nd :=
  { stK c v T k with fg := sF c (k + 1) }

theorem stK_fg (c : Bool) (v : Fin 6) (T : Time) : ∀ k, (stK c v T k).fg = sF c k
  | 0 => rfl
  | _ + 1 => rfl

theorem slotOf_25 : P6.slotOf 25 = 3 := by decide

theorem slotOf_27 : P6.slotOf 27 = 3 := by decide

/-- A delivery of block `k + 1` of chain `c` at a time of slot `3`. -/
theorem onBlock_stK (c : Bool) (v : Fin 6) {T : Time} (hT : P6.slotOf T = 3) {k : Nat}
    (hk : k < 3) :
    Node.onBlock v (stK c v T k) T (blk c (k + 1)) =
      (stK c v T (k + 1), [.fg (.block (blk c (k + 1)) true),
        (Node.acCall v (mid c v T k) T (.block (blk c (k + 1)))).2]) := by
  have hs : ¬ P6.slotOf T < (blk c (k + 1)).slot := by
    rw [hT]; change ¬ 3 < k + 1; omega
  simp only [Node.onBlock, hs, ↓reduceIte, stK_fg, onBlock_sF c hk]
  rfl

/-! ## The run -/

/-- The honest validators. -/
def H : Set (Fin 6) := {4, 5}

/-- The restart cut of node `v` at time `T`. -/
noncomputable def rCut (v : Fin 6) (T : Time) : Cut Nd := (Node.acCall v n₀ T .restart).2

/-- The AC cut of block `k + 1` of chain `c` at node `v`. -/
noncomputable def aCut (c : Bool) (v : Fin 6) (T : Time) (k : Nat) : Cut Nd :=
  (Node.acCall v (mid c v T k) T (.block (blk c (k + 1)))).2

/-- The labels of one honest node's seven cuts, by local index: the restart, then for each block
its FG cut (odd index) and its AC cut (even index). -/
noncomputable def lab (c : Bool) (v : Fin 6) (T : Time) (m : Nat) : Option (Cut Nd) :=
  if m = 0 then some (rCut v T)
  else if m < 7 then
    if m % 2 = 1 then some (.fg (.block (blk c (m / 2 + 1)) true))
    else some (aCut c v T (m / 2 - 1))
  else none

/-- The post-states of one honest node's cuts, by local index. -/
noncomputable def pst (c : Bool) (v : Fin 6) (T : Time) (m : Nat) : NodeState Nd :=
  if m % 2 = 1 then mid c v T (m / 2) else stK c v T (m / 2)

/-- Cuts `0–6` are node `4`'s (chain A, time `25`), cuts `7–13` node `5`'s (chain B, time `27`).
-/
def sd (i : Nat) : Bool := decide (i < 7)

/-- The node of cut `i`. -/
def nd (i : Nat) : Fin 6 := if i < 7 then 4 else 5

/-- The time of cut `i`. -/
def tm (i : Nat) : Time := if i < 7 then 25 else 27

/-- The local index of cut `i` at its node. -/
def lc (i : Nat) : Nat := if i < 7 then i else i - 7

/-- The first cut of the group of cut `i` (its event id); cut `i` itself from `14` on. -/
def gs (i : Nat) : Nat := if i < 14 ∧ lc i ≠ 0 then i - (lc i - 1) % 2 else i

/-- The run: the restart and the three deliveries of node `4` at time `25`, then those of node
`5` at time `27`; nothing else. -/
noncomputable def conflictRun : GoldilocksTrace sp6 ro6 where
  init _ := n₀
  node := nd
  time := tm
  event := gs
  pos i := i - gs i
  label i := if i < 14 then lab (sd i) (nd i) (tm i) (lc i) else none
  post i := pst (sd i) (nd i) (tm i) (lc i)
  awake v t := (v = 4 ∧ t = 25) ∨ (v = 5 ∧ t = 27)

theorem lab_ne_none (c : Bool) (v : Fin 6) (T : Time) {m : Nat} (hm : m < 7) :
    lab c v T m ≠ none := by
  unfold lab; split_ifs <;> simp

theorem label_none {i : Nat} (hi : 14 ≤ i) : conflictRun.label i = none := by
  simp [conflictRun, show ¬ i < 14 by omega]

/-- The states of node `4`. -/
theorem state_y : ∀ i, conflictRun.state 4 i =
    if i = 0 then n₀ else pst true 4 25 (min i 7 - 1)
  | 0 => rfl
  | i + 1 => by
    rw [Trace.state, state_y i]
    by_cases hi : i < 7
    · have hl : conflictRun.label i ≠ none := by
        simp only [conflictRun, show i < 14 by omega, ↓reduceIte, lc, hi]
        exact lab_ne_none _ _ _ hi
      rw [ite_pos ⟨by simp [conflictRun, nd, hi], hl⟩]
      simp [conflictRun, sd, nd, tm, lc, hi]
    · have hn : ¬ (conflictRun.node i = 4 ∧ conflictRun.label i ≠ none) := by
        rintro ⟨h, -⟩
        simp [conflictRun, nd, hi] at h
      rw [ite_neg hn, ite_neg (by omega), ite_neg (by omega),
        show min (i + 1) 7 - 1 = min i 7 - 1 by omega]

/-- The states of node `5`. -/
theorem state_z : ∀ i, conflictRun.state 5 i =
    if i ≤ 7 then n₀ else pst false 5 27 (min i 14 - 8)
  | 0 => rfl
  | i + 1 => by
    rw [Trace.state, state_z i]
    by_cases hi : 7 ≤ i ∧ i < 14
    · have hl : conflictRun.label i ≠ none := by
        simp only [conflictRun, hi.2, ↓reduceIte, lc, show ¬ i < 7 by omega]
        exact lab_ne_none _ _ _ (by omega)
      rw [ite_pos ⟨by simp [conflictRun, nd, show ¬ i < 7 by omega], hl⟩, ite_neg (by omega)]
      simp [conflictRun, sd, nd, tm, lc, show ¬ i < 7 by omega,
        show min (i + 1) 14 - 8 = i - 7 by omega]
    · have hn : ¬ (conflictRun.node i = 5 ∧ conflictRun.label i ≠ none) := by
        rintro ⟨h, hl⟩
        by_cases h7 : i < 7
        · simp [conflictRun, nd, h7] at h
        · exact hl (label_none (by omega))
      rw [ite_neg hn]
      by_cases h7 : i < 7
      · rw [ite_pos (by omega), ite_pos (by omega)]
      · rw [ite_neg (by omega), ite_neg (by omega), show min (i + 1) 14 - 8 = min i 14 - 8 by omega]

/-! ## The groups -/

/-- The first cut of an event's handler names the event. -/
theorem exec_head (v : Fin 6) (st : NodeState Nd) (t : Time) (e : Node.Event Nd) :
    ∀ c ∈ (Node.exec (fun _ => v0) dg6 v st t e).2.head?,
      (e = .restart ∧ ∃ ℓ : ACLabel Nd, c = .ac ℓ ∧ ℓ.call = .restart) ∨
      (∃ x, e = .tick x ∧ ∃ ℓ : ACLabel Nd, c = .ac ℓ ∧ ℓ.call = .tick) ∨
      (∃ m, e = .message m ∧ ∃ ℓ : ACLabel Nd, c = .ac ℓ ∧ ℓ.call = .message m) ∨
      (∃ a, e = .attestation a ∧ c = .fg (.attestation a)) ∨
      (∃ B acc, e = .block B ∧ c = .fg (.block B acc)) := by
  intro c hc
  cases e with
  | block B =>
    simp only [Node.exec, Node.onBlock] at hc
    split_ifs at hc
    · simp at hc
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨B, ?_⟩)))
      cases h : st.fg.onBlock B <;> simp only [h, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hc <;> exact ⟨_, rfl, hc.symm⟩
  | tick x =>
    refine Or.inr (Or.inl ⟨x, rfl, ?_⟩)
    simp only [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep,
      Node.acCall, List.foldl_cons, List.foldl_nil, List.nil_append, List.cons_append,
      List.head?_cons, Option.mem_def, Option.some.injEq] at hc
    exact ⟨_, hc.symm, rfl⟩
  | message m =>
    refine Or.inr (Or.inr (Or.inl ⟨m, rfl, ?_⟩))
    simp only [Node.exec, Node.onMessage, Node.acCall, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hc
    exact ⟨_, hc.symm, rfl⟩
  | attestation a =>
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl, ?_⟩)))
    simp only [Node.exec, Node.onAttestation, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hc
    exact hc.symm
  | restart =>
    refine Or.inl ⟨rfl, ?_⟩
    simp only [Node.exec, Node.restart, Node.acCall, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hc
    exact ⟨_, hc.symm, rfl⟩

/-- The labelled cuts: the restart (local index `0`), an FG acceptance (odd) or an AC delivery
(even). -/
theorem label_cases {i : Nat} {c : Cut Nd} (h : conflictRun.label i = some c) :
    i < 14 ∧ lc i < 7 ∧ ((lc i = 0 ∧ c = rCut (nd i) (tm i)) ∨
      (lc i % 2 = 1 ∧ c = .fg (.block (blk (sd i) (lc i / 2 + 1)) true)) ∨
      (lc i ≠ 0 ∧ lc i % 2 = 0 ∧ c = aCut (sd i) (nd i) (tm i) (lc i / 2 - 1))) := by
  simp only [conflictRun] at h
  split_ifs at h with h14
  unfold lab at h
  split_ifs at h with h0 h7 hodd <;> obtain rfl := Option.some.inj h
  · exact ⟨h14, by omega, Or.inl ⟨h0, rfl⟩⟩
  · exact ⟨h14, h7, Or.inr (Or.inl ⟨hodd, rfl⟩)⟩
  · exact ⟨h14, h7, Or.inr (Or.inr ⟨h0, by omega, rfl⟩)⟩

theorem rCut_ac (v : Fin 6) (T : Time) : ∃ ℓ : ACLabel Nd, rCut v T = .ac ℓ ∧ ℓ.call = .restart :=
  ⟨_, rfl, rfl⟩

theorem aCut_ac (c : Bool) (v : Fin 6) (T : Time) (k : Nat) :
    ∃ ℓ : ACLabel Nd, aCut c v T k = .ac ℓ ∧ ℓ.call = .block (blk c (k + 1)) :=
  ⟨_, rfl, rfl⟩

/-- A group of the run starts at a restart (local index `0`) or at an FG acceptance (odd local
index), at the node and time of that cut. -/
theorem group_cases {v : Fin 6} {j : Nat} {t : Time} {e : Node.Event Nd}
    (hg : conflictRun.GroupAt (fun _ => v0) dg6 v j t e) :
    j < 14 ∧ lc j < 7 ∧ v = nd j ∧ t = tm j ∧
      ((lc j = 0 ∧ e = .restart) ∨ (lc j % 2 = 1 ∧ e = .block (blk (sd j) (lc j / 2 + 1)))) := by
  obtain ⟨hne, hk, -⟩ := hg
  have hlen := List.length_pos_iff.2 hne
  obtain ⟨hn, ht, -, -, hl⟩ := hk 0 hlen
  simp only [Nat.add_zero] at hn ht hl
  have hmem : (Node.exec (fun _ => v0) dg6 v (conflictRun.state v j) t e).2[0] ∈
      (Node.exec (fun _ => v0) dg6 v (conflictRun.state v j) t e).2.head? := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen]; rfl
  obtain ⟨h14, h7, hc⟩ := label_cases hl
  refine ⟨h14, h7, hn.symm, ht.symm, ?_⟩
  rcases exec_head v _ t e _ hmem with ⟨rfl, ℓ, hℓ, hcall⟩ | ⟨x, rfl, ℓ, hℓ, hcall⟩ |
      ⟨m, rfl, ℓ, hℓ, hcall⟩ | ⟨a, rfl, hℓ⟩ | ⟨B, acc, rfl, hℓ⟩ <;> rw [hℓ] at hc
  · rcases hc with ⟨h0, -⟩ | ⟨-, hc⟩ | ⟨-, -, hc⟩
    · exact Or.inl ⟨h0, rfl⟩
    · cases hc
    · obtain ⟨ℓ', h', hc'⟩ := aCut_ac (sd j) (nd j) (tm j) (lc j / 2 - 1)
      rw [h'] at hc; cases hc; rw [hcall] at hc'; cases hc'
  all_goals
    first
    | (rcases hc with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, -, hc⟩
       · obtain ⟨ℓ', h', hc'⟩ := rCut_ac (nd j) (tm j)
         rw [h'] at hc; cases hc; rw [hcall] at hc'; cases hc'
       · cases hc
       · obtain ⟨ℓ', h', hc'⟩ := aCut_ac (sd j) (nd j) (tm j) (lc j / 2 - 1)
         rw [h'] at hc; cases hc; rw [hcall] at hc'; cases hc')
    | (rcases hc with ⟨-, hc⟩ | ⟨hodd, hc⟩ | ⟨-, -, hc⟩
       · obtain ⟨ℓ', h', -⟩ := rCut_ac (nd j) (tm j)
         rw [h'] at hc; cases hc
       · first
         | (cases hc; exact Or.inr ⟨hodd, rfl⟩)
         | cases hc
       · obtain ⟨ℓ', h', -⟩ := aCut_ac (sd j) (nd j) (tm j) (lc j / 2 - 1)
         rw [h'] at hc; cases hc)

/-! ## The two sides -/

/-- The first cut of a side: `0` for node `4`, `7` for node `5`. -/
def bs (s : Bool) : Nat := if s then 0 else 7

/-- The node of a side. -/
def vs (s : Bool) : Fin 6 := if s then 4 else 5

/-- The time of a side. -/
def Ts (s : Bool) : Time := if s then 25 else 27

theorem side_eq (s : Bool) {m : Nat} (hm : m < 7) :
    nd (bs s + m) = vs s ∧ tm (bs s + m) = Ts s ∧ sd (bs s + m) = s ∧ lc (bs s + m) = m := by
  cases s
  · simp [nd, tm, sd, lc, bs, vs, Ts]
  · simp [nd, tm, sd, lc, bs, vs, Ts]; omega

theorem side_of {i : Nat} (hi : i < 14) : i = bs (sd i) + lc i := by
  by_cases h : i < 7
  · simp [bs, sd, lc, h]
  · simp [bs, sd, lc, h]; omega

theorem slotOf_Ts (s : Bool) : P6.slotOf (Ts s) = 3 := by
  cases s
  · exact slotOf_27
  · exact slotOf_25

theorem state_side (s : Bool) {m : Nat} (hm : m ≤ 7) :
    conflictRun.state (vs s) (bs s + m) = if m = 0 then n₀ else pst s (vs s) (Ts s) (m - 1) := by
  cases s
  · rw [show vs false = 5 from rfl, state_z]
    simp only [bs, Bool.false_eq_true, ↓reduceIte, Ts]
    by_cases h0 : m = 0
    · simp [h0]
    · rw [ite_neg (by omega), ite_neg h0, show min (7 + m) 14 - 8 = m - 1 by omega]
  · rw [show vs true = 4 from rfl, state_y]
    simp only [bs, ↓reduceIte, Ts, Nat.zero_add]
    by_cases h0 : m = 0
    · simp [h0]
    · rw [ite_neg h0, ite_neg h0, show min m 7 - 1 = m - 1 by omega]

theorem pst_even (c : Bool) (v : Fin 6) (T : Time) (k : Nat) : pst c v T (2 * k) = stK c v T k := by
  simp [pst]

theorem pst_odd (c : Bool) (v : Fin 6) (T : Time) (k : Nat) :
    pst c v T (2 * k + 1) = mid c v T k := by
  simp only [pst, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, ↓reduceIte]
  congr 1; omega

theorem label_side (s : Bool) {m : Nat} (hm : m < 7) :
    conflictRun.label (bs s + m) = lab s (vs s) (Ts s) m := by
  obtain ⟨hn, ht, hs, hl⟩ := side_eq s hm
  have h14 : bs s + m < 14 := by cases s <;> simp [bs] <;> omega
  simp only [conflictRun, h14, ↓reduceIte, hn, ht, hs, hl]

theorem gs_eq {i j : Nat} (h : gs i = j) (hj : j < 14) :
    i = j ∨ (i = j + 1 ∧ lc j % 2 = 1) := by
  simp only [gs, lc] at h ⊢
  split_ifs at h ⊢ <;> omega

/-- The restart group of a side. -/
theorem group_restart (s : Bool) :
    conflictRun.GroupAt (fun _ => v0) dg6 (vs s) (bs s) (Ts s) .restart ∧
      (Node.exec (fun _ => v0) dg6 (vs s) (conflictRun.state (vs s) (bs s)) (Ts s) .restart).2 =
        [rCut (vs s) (Ts s)] := by
  have hst : conflictRun.state (vs s) (bs s) = n₀ := by
    simpa using state_side s (m := 0) (by omega)
  have hcs : (Node.exec (fun _ => v0) dg6 (vs s) (conflictRun.state (vs s) (bs s)) (Ts s)
      .restart).2 = [rCut (vs s) (Ts s)] := by
    rw [hst]; rfl
  refine ⟨⟨by rw [hcs]; simp, fun k hk => ?_, fun i hi => ?_⟩, hcs⟩
  · rw [hcs] at hk
    obtain rfl : k = 0 := by simpa using hk
    obtain ⟨hn, ht, -, hl⟩ := side_eq s (m := 0) (by omega)
    refine ⟨hn, ht, rfl, ?_, ?_⟩
    · change bs s + 0 - gs (bs s + 0) = 0
      simp only [gs, hl]; simp
    · rw [label_side s (m := 0) (by omega)]; simp [hcs, lab]
  · rw [hcs]
    have hj : gs (bs s) = bs s := by
      have := (side_eq s (m := 0) (by omega)).2.2.2
      simp only [Nat.add_zero] at this
      simp [gs, this]
    have hbs : bs s < 14 := by cases s <;> simp [bs]
    have hi' : gs i = bs s := (show gs i = gs (bs s) from hi).trans hj
    rcases gs_eq hi' hbs with h | ⟨-, h⟩
    · simp; omega
    · have := (side_eq s (m := 0) (by omega)).2.2.2
      simp only [Nat.add_zero] at this
      omega

/-- The group of block `k + 1` of a side. -/
theorem group_block (s : Bool) {k : Nat} (hk : k < 3) :
    conflictRun.GroupAt (fun _ => v0) dg6 (vs s) (bs s + (2 * k + 1)) (Ts s)
        (.block (blk s (k + 1))) ∧
      (Node.exec (fun _ => v0) dg6 (vs s) (conflictRun.state (vs s) (bs s + (2 * k + 1))) (Ts s)
        (.block (blk s (k + 1)))).2 =
        [.fg (.block (blk s (k + 1)) true), aCut s (vs s) (Ts s) k] := by
  have hst : conflictRun.state (vs s) (bs s + (2 * k + 1)) = stK s (vs s) (Ts s) k := by
    rw [state_side s (by omega), ite_neg (by omega), show 2 * k + 1 - 1 = 2 * k by omega,
      pst_even]
  have hcs : (Node.exec (fun _ => v0) dg6 (vs s) (conflictRun.state (vs s) (bs s + (2 * k + 1)))
      (Ts s) (.block (blk s (k + 1)))).2 =
      [.fg (.block (blk s (k + 1)) true), aCut s (vs s) (Ts s) k] := by
    rw [hst]
    exact congrArg Prod.snd (onBlock_stK s (vs s) (slotOf_Ts s) hk)
  have hlc : ∀ m, m < 7 → lc (bs s + m) = m := fun m hm => (side_eq s hm).2.2.2
  have hbs : bs s ≤ 7 := by cases s <;> simp [bs]
  have hb14 : bs s + (2 * k + 1) < 14 := by omega
  have h2 := hlc _ (show 2 * k + 1 < 7 by omega)
  have hj : gs (bs s + (2 * k + 1)) = bs s + (2 * k + 1) := by
    simp only [gs, h2]; split_ifs <;> omega
  refine ⟨⟨by rw [hcs]; simp, fun k' hk' => ?_, fun i hi => ?_⟩, hcs⟩
  · have hk2 : k' < 2 := by rw [hcs] at hk'; simpa using hk'
    have hm : 2 * k + 1 + k' < 7 := by omega
    obtain ⟨hn, ht, -, -⟩ := side_eq s hm
    have h1 := hlc _ hm
    have hgs : gs (bs s + (2 * k + 1 + k')) = bs s + (2 * k + 1) := by
      simp only [gs, h1]; split_ifs <;> omega
    rw [Nat.add_assoc]
    refine ⟨hn, ht, ?_, ?_, ?_⟩
    · change gs (bs s + (2 * k + 1 + k')) = gs (bs s + (2 * k + 1))
      rw [hgs, hj]
    · change bs s + (2 * k + 1 + k') - gs (bs s + (2 * k + 1 + k')) = k'
      rw [hgs]; omega
    · rw [label_side s hm]
      simp only [hcs]
      rcases (show k' = 0 ∨ k' = 1 by omega) with rfl | rfl
      · simp only [lab, show 2 * k + 1 + 0 ≠ 0 by omega, ↓reduceIte, hm,
          show (2 * k + 1 + 0) % 2 = 1 by omega, show (2 * k + 1 + 0) / 2 = k by omega]
        rfl
      · simp only [lab, show 2 * k + 1 + 1 ≠ 0 by omega, ↓reduceIte, hm,
          show (2 * k + 1 + 1) % 2 = 0 by omega, show (2 * k + 1 + 1) / 2 - 1 = k by omega]
        rfl
  · rw [hcs]
    simp only [List.length_cons, List.length_nil]
    have hi' : gs i = bs s + (2 * k + 1) := (show gs i = gs (bs s + (2 * k + 1)) from hi).trans hj
    rcases gs_eq hi' hb14 with h | ⟨h, -⟩ <;> omega

/-! ## The calls -/

/-- Every cut of the run is a cut of one side, at that side's node and time. -/
theorem call_side {y : Fin 6} {i : Nat} {c : Cut Nd} (h : conflictRun.CallAt y i c) :
    i < 14 ∧ lc i < 7 ∧ y = vs (sd i) ∧ conflictRun.time i = Ts (sd i) ∧ i = bs (sd i) + lc i ∧
      conflictRun.label i = some c := by
  obtain ⟨h14, h7, -⟩ := label_cases h.2
  have hi := side_of h14
  obtain ⟨hn, ht, -, -⟩ := side_eq (sd i) h7
  rw [← hi] at hn ht
  exact ⟨h14, h7, h.1.symm.trans hn, ht, hi, h.2⟩

theorem H_side (s : Bool) : vs s ∈ H := by cases s <;> simp [vs, H]

theorem mem_H {y : Fin 6} (hy : y ∈ H) : y = 4 ∨ y = 5 := by simpa [H] using hy

theorem vs_inj {s s' : Bool} (h : vs s = vs s') : s = s' := by
  cases s <;> cases s' <;> simp_all [vs]

theorem acCall_cutStep (v : Fin 6) (st : NodeState Nd) (t : Time) (c : Nd.Call) :
    Node.CutStep v t st (Node.acCall v st t c).2 (Node.acCall v st t c).1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The cut law at every labelled cut. -/
theorem cutLaw {y : Fin 6} {i : Nat} {c : Cut Nd} (h : conflictRun.CallAt y i c) :
    Node.CutStep y (conflictRun.time i) (conflictRun.state y i) c (conflictRun.post i) := by
  obtain ⟨h14, h7, rfl, ht, hi, hl⟩ := call_side h
  set s := sd i
  set m := lc i
  have hpost : conflictRun.post i = pst s (vs s) (Ts s) m := by
    change pst (sd i) (nd i) (tm i) (lc i) = _
    rw [show nd i = vs s from h.1, show tm i = Ts s from ht]
  have hst : conflictRun.state (vs s) i = if m = 0 then n₀ else pst s (vs s) (Ts s) (m - 1) := by
    rw [hi]; exact state_side s h7.le
  rw [hi, label_side s h7] at hl
  rw [hst, hpost, ht]
  unfold lab at hl
  split_ifs at hl with h0 h7' <;> obtain rfl := Option.some.inj hl
  · rw [ite_pos h0, h0]
    exact acCall_cutStep _ _ _ _
  · obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    rw [ite_neg h0, hk, show 2 * k + 1 - 1 = 2 * k by omega, pst_even, pst_odd,
      show (2 * k + 1) / 2 + 1 = k + 1 by omega]
    refine ⟨?_, ?_, rfl, rfl⟩
    · rw [slotOf_Ts]; change k + 1 ≤ 3; omega
    · rw [stK_fg]; exact onBlock_sF s (by omega)
  · obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 2 := ⟨m / 2 - 1, by omega⟩
    rw [ite_neg h0, hk, show 2 * k + 2 - 1 = 2 * k + 1 by omega, pst_odd,
      show 2 * k + 2 = 2 * (k + 1) by omega, pst_even, show 2 * (k + 1) / 2 - 1 = k by omega]
    exact acCall_cutStep _ _ _ _

/-- Every labelled cut lies in the group of its side's restart or of one of its deliveries. -/
theorem grouped {y : Fin 6} {i : Nat} {c : Cut Nd} (h : conflictRun.CallAt y i c) :
    ∃ j e, conflictRun.InGroup (fun _ => v0) dg6 y j i (conflictRun.time i) e := by
  obtain ⟨h14, h7, rfl, ht, hi, -⟩ := call_side h
  set s := sd i
  set m := lc i
  rw [ht]
  by_cases h0 : m = 0
  · obtain ⟨hg, hcs⟩ := group_restart s
    exact ⟨bs s, .restart, hg, by omega, by rw [hcs]; simp; omega⟩
  · obtain ⟨k, hk, hmk⟩ : ∃ k, k < 3 ∧ (m = 2 * k + 1 ∨ m = 2 * k + 2) :=
      ⟨(m - 1) / 2, by omega, by omega⟩
    obtain ⟨hg, hcs⟩ := group_block s hk
    exact ⟨bs s + (2 * k + 1), .block (blk s (k + 1)), hg, by omega, by rw [hcs]; simp; omega⟩

/-- The groups of the run: a side's restart, at its first cut, or a delivery of one of its
blocks. -/
theorem group_side {y : Fin 6} {j : Nat} {t : Time} {e : Node.Event Nd}
    (hg : conflictRun.GroupAt (fun _ => v0) dg6 y j t e) :
    y = vs (sd j) ∧ t = Ts (sd j) ∧ j = bs (sd j) + lc j ∧
      ((lc j = 0 ∧ e = .restart) ∨ ∃ k < 3, e = .block (blk (sd j) (k + 1))) := by
  obtain ⟨h14, h7, hy, ht, he⟩ := group_cases hg
  have hi := side_of h14
  obtain ⟨hn, ht', -, -⟩ := side_eq (sd j) h7
  rw [← hi] at hn ht'
  refine ⟨hy.trans hn, ht.trans ht', hi, ?_⟩
  rcases he with h | ⟨hodd, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨lc j / 2, by omega, h⟩

theorem not_public_Ts (s : Bool) : ¬ P6.IsPublic (Ts s) := by
  cases s <;> simp only [Ts, Params.IsPublic] <;> decide

theorem restart_iff {y : Fin 6} {i : Nat} :
    conflictRun.RestartAt y i ↔ i < 14 ∧ lc i = 0 ∧ y = vs (sd i) := by
  constructor
  · rintro ⟨ℓ, hc, hr⟩
    obtain ⟨h14, h7, hy, -, hi, hl⟩ := call_side hc
    rw [hi, label_side _ h7] at hl
    unfold lab at hl
    refine ⟨h14, ?_, hy⟩
    split_ifs at hl with h0 h7'
    · exact h0
    · cases hl
    · obtain ⟨ℓ', h', hc'⟩ := aCut_ac (sd i) (vs (sd i)) (Ts (sd i)) (lc i / 2 - 1)
      rw [h'] at hl; cases hl; rw [hr] at hc'; cases hc'
  · rintro ⟨h14, h0, rfl⟩
    have hi := side_of h14
    obtain ⟨ℓ, hℓ, hr⟩ := rCut_ac (vs (sd i)) (Ts (sd i))
    refine ⟨ℓ, ⟨?_, ?_⟩, hr⟩
    · change nd i = _
      conv_lhs => rw [hi, h0]
      exact (side_eq (sd i) (m := 0) (by omega)).1
    · rw [hi, h0, label_side _ (m := 0) (by omega)]; simp [lab, hℓ]

theorem isCall_iff {y : Fin 6} {i : Nat} :
    conflictRun.IsCall y i ↔ i < 14 ∧ y = vs (sd i) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨h14, -, hy, -⟩ := call_side hc
    exact ⟨h14, hy⟩
  · rintro ⟨h14, rfl⟩
    have hi := side_of h14
    have h7 : lc i < 7 := by simp only [lc]; split_ifs <;> omega
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp
      (show conflictRun.label i ≠ none by
        rw [hi, label_side _ h7]; exact lab_ne_none _ _ _ h7)
    refine ⟨c, ?_, hc⟩
    change nd i = _
    conv_lhs => rw [hi]
    exact (side_eq (sd i) h7).1

theorem time_of_lt {i : Nat} (_hi : i < 14) : conflictRun.time i = Ts (sd i) := by
  change tm i = Ts (sd i)
  by_cases h : i < 7 <;> simp [tm, Ts, sd, h]

theorem awake_iff {y : Fin 6} {t : Time} :
    conflictRun.awake y t ↔ ∃ s, y = vs s ∧ t = Ts s := by
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨true, rfl, rfl⟩
    · exact ⟨false, rfl, rfl⟩
  · rintro ⟨s, rfl, rfl⟩
    cases s
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩

/-- A block call of the run is the acceptance of a block of its side's chain. -/
theorem blockCall_blk {y : Fin 6} {i : Nat} {B : Blk} {acc : Bool}
    (h : conflictRun.CallAt y i (.fg (.block B acc))) :
    ∃ k < 3, B = blk (sd i) (k + 1) ∧ acc = true := by
  obtain ⟨-, h7, -, -, hi, hl⟩ := call_side h
  rw [hi, label_side _ h7] at hl
  unfold lab at hl
  split_ifs at hl with h0 h7'
  · obtain ⟨ℓ, h', -⟩ := rCut_ac (vs (sd i)) (Ts (sd i))
    rw [h'] at hl; cases hl
  · cases hl; exact ⟨lc i / 2, by omega, rfl, rfl⟩
  · obtain ⟨ℓ, h', -⟩ := aCut_ac (sd i) (vs (sd i)) (Ts (sd i)) (lc i / 2 - 1)
    rw [h'] at hl; cases hl

/-- No cut of the run is an attestation call. -/
theorem not_attCall {y : Fin 6} {i : Nat} {a : Att 6} :
    ¬ conflictRun.CallAt y i (.fg (.attestation a)) := by
  intro h
  obtain ⟨-, h7, -, -, hi, hl⟩ := call_side h
  rw [hi, label_side _ h7] at hl
  unfold lab at hl
  split_ifs at hl
  · obtain ⟨ℓ, h', -⟩ := rCut_ac (vs (sd i)) (Ts (sd i))
    rw [h'] at hl; cases hl
  · cases hl
  · obtain ⟨ℓ, h', -⟩ := aCut_ac (sd i) (vs (sd i)) (Ts (sd i)) (lc i / 2 - 1)
    rw [h'] at hl; cases hl

/-- No cut of the run is an `ac_on_message` call. -/
theorem not_msgCall {y : Fin 6} {i : Nat} {m : Nd.Msg} : ¬ conflictRun.MsgCallAt y i m := by
  rintro ⟨ℓ, h, hm⟩
  obtain ⟨-, h7, -, -, hi, hl⟩ := call_side h
  rw [hi, label_side _ h7] at hl
  unfold lab at hl
  split_ifs at hl
  · obtain ⟨ℓ', h', hr⟩ := rCut_ac (vs (sd i)) (Ts (sd i))
    rw [h'] at hl; cases hl; rw [hr] at hm; cases hm
  · cases hl
  · obtain ⟨ℓ', h', hb⟩ := aCut_ac (sd i) (vs (sd i)) (Ts (sd i)) (lc i / 2 - 1)
    rw [h'] at hl; cases hl; rw [hb] at hm; cases hm

theorem signers_not_H {a : Att 6} {c : Bool} {k : Nat} (ha : a ∈ (blk c k).fgPayload) :
    a.val ∉ H := by
  have hv : a.val ∈ signers := by
    change a ∈ atts c k at ha
    unfold atts tvs at ha
    split at ha <;> (simp only [List.mem_map] at ha; obtain ⟨v, hv, rfl⟩ := ha; exact hv)
  simp [signers] at hv
  simp only [H, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hv with h | h | h | h <;> rw [h] <;> decide

theorem atts_wellFormed (c : Bool) {k : Nat} (hk : k < 3) :
    ∀ a ∈ (blk c (k + 1)).fgPayload, a.WellFormed := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> cases c <;> decide

/-! ## The run law -/

theorem conflictRun_localRun :
    Node.LocalRun (fun _ => v0) dg6 H (fun v : SA.Vote sp6.n => v.val) conflictRun where
  init _ _ := rfl
  grouped _ _ _ _ h := grouped h
  cutLaw _ _ _ _ h := cutLaw h
  wire y _ j t e hg := by
    obtain ⟨-, -, -, he⟩ := group_side hg
    rcases he with ⟨-, rfl⟩ | ⟨k, hk, rfl⟩
    · trivial
    · refine ⟨blk_rootOk _ (by simp; omega), atts_wellFormed _ hk, ?_⟩
      exact ⟨fun v hv => absurd hv List.not_mem_nil, fun v hv => absurd hv List.not_mem_nil⟩
  proposerCredential y _ j t B hg := by
    obtain ⟨-, -, -, he⟩ := group_side hg
    rcases he with ⟨-, h⟩ | ⟨k, -, h⟩
    · cases h
    · cases h; rfl
  time_nonneg i := by change (0 : Int) ≤ tm i; unfold tm; split_ifs <;> decide
  time_mono i j hij := by
    change tm i ≤ tm j; unfold tm; split_ifs <;> first | decide | omega
  finite T := (Set.finite_Iio 14).subset fun i hi => by
    by_contra h
    exact hi.1 (label_none (by simpa using h))
  phase_order y _ y' _ j j' t e e' hg hg' hlt := by
    obtain ⟨-, ht, hj, he⟩ := group_side hg
    obtain ⟨-, ht', hj', he'⟩ := group_side hg'
    have hs : sd j = sd j' := by
      have := ht.symm.trans ht'
      revert this
      cases sd j <;> cases sd j' <;> simp [Ts]
    rcases he' with ⟨h0, rfl⟩ | ⟨k, -, rfl⟩
    · exfalso; rw [hs] at hj; omega
    · rcases he with ⟨-, rfl⟩ | ⟨k', -, rfl⟩ <;> simp [Node.Event.phase]
  tick_public y _ j t h := by
    obtain ⟨x, hg⟩ := h
    obtain ⟨-, -, -, he⟩ := group_side hg
    rcases he with ⟨-, h⟩ | ⟨k, -, h⟩ <;> cases h
  tick_unique y _ j j' t h := by
    obtain ⟨x, hg⟩ := h
    obtain ⟨-, -, -, he⟩ := group_side hg
    rcases he with ⟨-, h⟩ | ⟨k, -, h⟩ <;> cases h
  tick_of_awake y _ t _ hp ha := by
    obtain ⟨s, -, rfl⟩ := awake_iff.1 ha
    exact absurd hp (not_public_Ts s)
  awake_in_horizon y _ t ha := by
    obtain ⟨s, -, rfl⟩ := awake_iff.1 ha
    have h7 : (0 : Nat) < 7 := by omega
    refine ⟨bs s + 0, Or.inl (by rw [label_side s h7]; exact lab_ne_none _ _ _ h7), ?_⟩
    rw [time_of_lt (by cases s <;> simp [bs]), (side_eq s h7).2.2.1]
  awake_of_call y _ i h := by
    obtain ⟨h14, rfl⟩ := isCall_iff.1 h
    exact awake_iff.2 ⟨sd i, rfl, time_of_lt h14⟩
  restart_of_sleep y _ i u hc hu hui hna hprev := by
    obtain ⟨h14, rfl⟩ := isCall_iff.1 hc
    refine restart_iff.2 ⟨h14, ?_, rfl⟩
    by_contra h0
    have hi := side_of h14
    have hb : bs (sd i) < 14 := by cases h : sd i <;> simp [bs]
    have hsb : sd (bs (sd i)) = sd i := by
      simpa using (side_eq (sd i) (m := 0) (by omega)).2.2.1
    have := hprev (bs (sd i)) (by omega) (isCall_iff.2 ⟨hb, by rw [hsb]⟩)
    rw [time_of_lt hb, hsb] at this
    rw [time_of_lt h14] at hui
    exact absurd (this.trans hui) (lt_irrefl _)
  restart_at_wake y _ u v _ huv _ hv := by
    obtain ⟨s, rfl, rfl⟩ := awake_iff.1 hv
    have hb : bs s < 14 := by cases s <;> simp [bs]
    have hs0 := side_eq s (m := 0) (by omega)
    simp only [Nat.add_zero] at hs0
    refine ⟨bs s, restart_iff.2 ⟨hb, hs0.2.2.2, by rw [hs0.2.2.1]⟩, ?_, ?_⟩ <;>
      rw [time_of_lt hb, hs0.2.2.1]
    exact huv
  sleep_of_restart y _ i h := by
    obtain ⟨h14, h0, rfl⟩ := restart_iff.1 h
    refine ⟨0, le_rfl, ?_, fun ha => ?_, fun j hj hc => ?_⟩
    · rw [time_of_lt h14]; cases sd i <;> decide
    · obtain ⟨s, -, h⟩ := awake_iff.1 ha
      cases s <;> simp [Ts] at h
    · obtain ⟨hj14, hy⟩ := isCall_iff.1 hc
      have := vs_inj hy
      have hi := side_of h14
      have hj' := side_of hj14
      rw [← this] at hj'
      omega
  block_unforgeable y _ i B h hB := by
    obtain ⟨acc, hc⟩ := h
    obtain ⟨k, -, rfl, -⟩ := blockCall_blk hc
    exact absurd hB (by simp [H, blk]; decide)
  att_unforgeable y _ i a h ha := by
    rcases h with h | ⟨B, ⟨acc, hc⟩, haB⟩
    · exact absurd h not_attCall
    · obtain ⟨k, -, rfl, -⟩ := blockCall_blk hc
      exact absurd ha (signers_not_H haB)
  msg_unforgeable y _ i m h _ := absurd h not_msgCall

/-- **The run** is a Goldilocks run. -/
theorem conflictRun_goldilocksRun : GoldilocksRun (fun _ => v0) dg6 H conflictRun where
  toLocalRun := conflictRun_localRun
  genesis_root_ok := (dg6_none _ _ _ _).symm
  carried_vote_unforgeable y _ i B h v hv := by
    obtain ⟨acc, hc⟩ := h
    obtain ⟨k, -, rfl, -⟩ := blockCall_blk hc
    exact absurd hv List.not_mem_nil

/-! ## Collision freedom -/

theorem rt_inj {c c' : Bool} {i i' : Nat} (hi : 1 ≤ i ∧ i ≤ 3) (hi' : 1 ≤ i' ∧ i' ≤ 3)
    (h : rt c i = rt c' i') : c = c' ∧ i = i' := by
  cases c <;> cases c' <;> simp only [rt, Bool.false_eq_true, ↓reduceIte] at h <;>
    first | exact ⟨rfl, by omega⟩ | omega

theorem occurs_blk {B : Blk} (h : conflictRun.Occurs B) : ∃ c, ∃ k < 3, B = blk c (k + 1) := by
  obtain ⟨y, i, acc, hc⟩ := h
  obtain ⟨k, hk, rfl, -⟩ := blockCall_blk hc
  exact ⟨_, k, hk, rfl⟩

/-- **`NoColl`**: the digest is injective on the run's blocks and genesis. -/
theorem conflictRun_noColl : Compose.NoCollRun dg6 conflictRun := by
  have hdg : ∀ B ∈ insert (P6.genesisBlock Nd.genesisPayload) {B | conflictRun.Occurs B},
      (B = G ∧ dg6 B.parent B.slot B.input B.fgPayload B.acPayload = 0) ∨
      ∃ c, ∃ k < 3, B = blk c (k + 1) ∧
        dg6 B.parent B.slot B.input B.fgPayload B.acPayload = rt c (k + 1) := by
    rintro B (rfl | hB)
    · exact Or.inl ⟨rfl, dg6_none _ _ _ _⟩
    · obtain ⟨c, k, hk, rfl⟩ := occurs_blk hB
      exact Or.inr ⟨c, k, hk, rfl, dg6_blk c (by simp; omega)⟩
  intro B hB C hC heq
  rcases hdg B hB with ⟨rfl, hb⟩ | ⟨c, k, hk, rfl, hb⟩ <;>
    rcases hdg C hC with ⟨rfl, hc⟩ | ⟨c', k', hk', rfl, hc⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [hb, hc] at heq; cases c' <;> simp [rt] at heq
  · rw [hb, hc] at heq; cases c <;> simp [rt] at heq
  · rw [hb, hc] at heq
    obtain ⟨rfl, h⟩ := rt_inj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ heq
    obtain rfl : k = k' := by omega
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The honest trees and the two finalized tips -/

theorem sF_blocks0 (c : Bool) (k : Nat) : (sF c k).blocks 0 = some G := by
  obtain ⟨h1, h2, h3, -⟩ := rt_ne c
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk
  · rfl
  · change (s₁ c).blocks 0 = _; rw [s₁_blocks]; simp [h1.symm]
  · change (s₂ c).blocks 0 = _; rw [s₂_blocks, s₁_blocks]; simp [h1.symm, h2.symm]
  · have : sF c k = s₃ c := by
      rcases k with _ | _ | _ | k <;> first | omega | rfl
    rw [this, s₃_blocks, s₂_blocks, s₁_blocks]; simp [h1.symm, h2.symm, h3.symm]

theorem pst_fg (c : Bool) (v : Fin 6) (T : Time) (m : Nat) : ∃ k, (pst c v T m).fg = sF c k := by
  unfold pst
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, stK_fg c v T _⟩

theorem state_fg {y : Fin 6} (hy : y ∈ H) (i : Nat) :
    ∃ c k, (conflictRun.state y i).fg = sF c k := by
  rcases mem_H hy with rfl | rfl
  · rw [state_y]; split_ifs
    · exact ⟨true, 0, rfl⟩
    · obtain ⟨k, hk⟩ := pst_fg true 4 25 (min i 7 - 1); exact ⟨true, k, hk⟩
  · rw [state_z]; split_ifs
    · exact ⟨true, 0, rfl⟩
    · obtain ⟨k, hk⟩ := pst_fg false 5 27 (min i 14 - 8); exact ⟨false, k, hk⟩

/-- The only honest block with the genesis root is genesis. -/
theorem honest_root0 {Z : Blk} (hZ : Z ∈ conflictRun.HonestBlocks H) (hr : Z.root = 0) : Z = G := by
  obtain ⟨y, hy, i, hZ⟩ := hZ
  obtain ⟨c, k, hk⟩ := state_fg hy i
  change (conflictRun.state y i).fg.blocks Z.root = some Z at hZ
  rw [hk, hr, sF_blocks0] at hZ
  exact (Option.some.inj hZ).symm

/-- Below the first block of a chain, among the honest blocks, there is only genesis. -/
theorem anc_blk1 {c : Bool} {X : Blk} (h : Anc (conflictRun.HonestBlocks H) X (blk c 1)) :
    X = blk c 1 ∨ X = G := by
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with he | ⟨Z, hXZ, hZ, -, hp⟩
  · exact Or.inl he.symm
  have hZr : Z.root = 0 := by
    simp only [blk, par, ↓reduceIte, Option.some.injEq] at hp; exact hp.symm
  obtain rfl := honest_root0 hZ hZr
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hXZ with he | ⟨W, -, -, -, hp'⟩
  · exact Or.inr he.symm
  · cases hp'

/-- The first blocks of the two chains are incompatible among the honest blocks. -/
theorem blk1_conflict :
    ¬ Compatible (conflictRun.HonestBlocks H) (blk true 1) (blk false 1) := by
  rintro (h | h) <;> rcases anc_blk1 h with h' | h' <;>
    exact absurd (congrArg Block.root h') (by decide)

theorem finalized_four : conflictRun.finalizedAt 4 7 = blk true 1 := by
  change (conflictRun.state 4 7).fg.F = _
  rw [state_y, ite_neg (by omega), show min 7 7 - 1 = 2 * 3 by rfl, pst_even, stK_fg]
  exact F_s₃ true

theorem finalized_five : conflictRun.finalizedAt 5 14 = blk false 1 := by
  change (conflictRun.state 5 14).fg.F = _
  rw [state_z, ite_neg (by omega), show min 14 14 - 8 = 2 * 3 by rfl, pst_even, stK_fg]
  exact F_s₃ false

/-- **The two honest finalized tips conflict.** -/
theorem conflicting_finalized :
    4 ∈ H ∧ 5 ∈ H ∧ conflictRun.finalizedAt 4 7 = blk true 1 ∧
      conflictRun.finalizedAt 5 14 = blk false 1 ∧
      ¬ Compatible (conflictRun.HonestBlocks H) (conflictRun.finalizedAt 4 7)
        (conflictRun.finalizedAt 5 14) := by
  refine ⟨by simp [H], by simp [H], finalized_four, finalized_five, ?_⟩
  rw [finalized_four, finalized_five]
  exact blk1_conflict

theorem H_compl : Hᶜ = ↑({0, 1, 2, 3} : Finset (Fin 6)) := by
  ext v; fin_cases v <;> simp [H]

/-- **The fault count**: `f = 4` faulty validators, against `2q − n = 2`: the fault bound
`f < 2q − n` of `FinalizedSafe` fails. -/
theorem conflictRun_faults :
    Hᶜ.ncard = 4 ∧ 2 * sp6.toParams.q - sp6.n = 2 ∧ ¬ Hᶜ.ncard < 2 * sp6.toParams.q - sp6.n := by
  have h : Hᶜ.ncard = 4 := by rw [H_compl, Set.ncard_coe_finset]; rfl
  have hq : 2 * sp6.toParams.q - sp6.n = 2 := rfl
  exact ⟨h, hq, by omega⟩

/-- (r) **`FinalizedSafe` needs its fault bound**: with the premise `f < 2q − n` dropped and every
other premise kept (a `GoldilocksRun` with `NoCollRun`), two honest finalized tips can conflict. -/
theorem finalizedSafe_needs_fault_bound :
    ¬ ∀ (sp : SA.SAParams) (ro : SA.ReplayOrder sp (List (Att sp.n)))
      (dg : Digest (List (Att sp.n)) (SA.Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
      GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
      ∀ y ∈ H, ∀ z ∈ H, ∀ i j,
        Compatible (tr.HonestBlocks H) (tr.finalizedAt y i) (tr.finalizedAt z j) := by
  intro h
  obtain ⟨h4, h5, -, -, hc⟩ := conflicting_finalized
  exact hc (h sp6 ro6 dg6 H conflictRun (fun _ => v0) conflictRun_goldilocksRun
    conflictRun_noColl 4 h4 5 h5 7 14)

/-- (a) **R.7 on the run**: the proved `final_accountable` convicts at least `2q − n = 2`
validators from the chains the two honest readers hold, and `non_framing` holds: no honest
validator signs a slashable pair. -/
theorem conflictRun_accountable :
    (∃ X₁ ∈ (conflictRun.state 4 7).fg.tree, ∃ X₂ ∈ (conflictRun.state 5 14).fg.tree,
      ∃ S : Finset (Fin 6), 2 ≤ S.card ∧
        ∀ v ∈ S, ∃ a ∈ Regimes.ChainAtts conflictRun 4 7 X₁ ∪ Regimes.ChainAtts conflictRun 5 14 X₂,
          ∃ b ∈ Regimes.ChainAtts conflictRun 4 7 X₁ ∪ Regimes.ChainAtts conflictRun 5 14 X₂,
            a.val = v ∧ slashable a b) ∧
    ∀ v ∈ H, ∀ k k' a b, conflictRun.SignAt v k a → conflictRun.SignAt v k' b →
      ¬ slashable a b := by
  obtain ⟨h4, h5, -, -, hc⟩ := conflicting_finalized
  refine ⟨?_, Regimes.non_framing sp6 ro6 dg6 H conflictRun (fun _ => v0)
    conflictRun_goldilocksRun⟩
  obtain ⟨X₁, hX₁, X₂, hX₂, S, hS, hv⟩ := Regimes.final_accountable sp6 ro6 dg6 H conflictRun
    (fun _ => v0) conflictRun_goldilocksRun conflictRun_noColl 4 h4 5 h5 7 14 hc
  exact ⟨X₁, hX₁, X₂, hX₂, S, (conflictRun_faults.2.1 ▸ hS), hv⟩

end Consensus.Goldilocks.ConflictRun

end
