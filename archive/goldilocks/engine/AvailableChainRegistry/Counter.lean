module
public import AvailableChainFramework
public import Mathlib.Tactic

@[expose] public section

namespace AvailableChain.Registry.Counter

open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Statements.Generic

/-- The chain of height `k`: a fixed block for every height. -/
def chain : Nat → Block
  | 0 => .genesis
  | k + 1 => .node (chain k) k (nodeRoot (chain k).root k k) k

/-- Each proposer proposes the next height; a node accepts exactly the next
height. Payload `k` depends on height `k - 1`. -/
def counter : ProtocolSpec 1 where
  State := Nat
  Label := Empty
  Payload := Nat
  init := 0
  clock := fun st _ => st
  actTime := fun ℓ => ℓ.elim
  duties := fun _ => []
  duties_spec := fun ℓ _ => ℓ.elim
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ ℓ => ℓ.elim
  proposalTime := fun s => s
  slotsAt := fun t => if 0 ≤ t then [t.toNat] else []
  slotsAt_spec := by
    intro s t
    change (s ∈ if 0 ≤ t then [t.toNat] else []) ↔ (s : Int) = t
    by_cases h : 0 ≤ t
    · simp only [ite_eq_left h, List.mem_singleton]
      have hc : (t.toNat : Int) = t := Int.toNat_of_nonneg h
      constructor
      · intro he
        rw [he]
        exact hc
      · intro he
        exact_mod_cast (hc.trans he.symm).symm
    · simp only [ite_eq_right h, List.not_mem_nil, false_iff]
      intro he
      exact h (he ▸ Int.natCast_nonneg s)
  slotsAt_nodup := by intro t; split_ifs <;> simp
  propose := fun st _ => some (st + 1)
  gossip := fun _ _ => []
  process := fun st o => if o.payload = st + 1 then st + 1 else st
  wellFormed := fun _ => true
  depsPresent := fun st o => decide (o.payload ≤ st + 1)
  processed := fun st o => decide (o.payload ≤ st)
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

def counterIface : Interface counter where
  confirmed := fun st => chain st
  stable := fun st => chain st
  block := fun k => some (chain k)
  opening := fun _ => True

section Mono

variable {V : Type} [DecidableEq V]

/-- The height of a node in a world: its state, as a number. -/
def height (w : World V counter) (v : V) : Nat := w v

/-- `process` returns the state or the state plus one. -/
theorem process_ge (a : Nat) (o : counter.Object) : a ≤ counter.process a o := by
  simp only [counter]
  split_ifs <;> omega

/-- A step does not decrease the height of a node. -/
theorem step_mono (w : World V counter) (e : Event V counter.Object) (u : V) :
    height w u ≤ height (World.step w e) u := by
  unfold height
  cases e with
  | tick v t =>
    by_cases h : u = v
    · subst h
      simp only [World.step, Function.update_self]
      exact le_refl _
    · simp only [World.step, Function.update_of_ne h]
      exact le_refl _
  | deliver v o t =>
    by_cases h : u = v
    · subst h
      simp only [World.step, Function.update_self]
      exact process_ge _ o
    · simp only [World.step, Function.update_of_ne h]
      exact le_refl _

/-- A step is monotone in the world. -/
theorem step_le {w w' : World V counter} (h : ∀ u, height w u ≤ height w' u)
    (e : Event V counter.Object) (u : V) :
    height (World.step w e) u ≤ height (World.step w' e) u := by
  unfold height at h ⊢
  cases e with
  | tick v t =>
    by_cases hu : u = v
    · subst hu
      simp only [World.step, Function.update_self]
      exact h u
    · simp only [World.step, Function.update_of_ne hu]
      exact h u
  | deliver v o t =>
    by_cases hu : u = v
    · subst hu
      have hu := h u
      simp only [World.step, Function.update_self]
      have key : ∀ a b p : ℕ, a ≤ b →
          (if p = a + 1 then a + 1 else a) ≤ (if p = b + 1 then b + 1 else b) := by
        intro a b p hab; split_ifs <;> omega
      exact key _ _ _ hu
    · simp only [World.step, Function.update_of_ne hu]
      exact h u

/-- The fold over a sublist gives a smaller height at every node. -/
theorem foldl_sublist {l₁ l₂ : List (Event V counter.Object)} (hl : l₁.Sublist l₂) :
    ∀ w w' : World V counter, (∀ u, height w u ≤ height w' u) →
      ∀ u, height (l₁.foldl World.step w) u ≤ height (l₂.foldl World.step w') u := by
  induction hl with
  | slnil => intro w w' h; exact h
  | cons a _ ih =>
    intro w w' h
    exact ih w (World.step w' a) (fun u => le_trans (h u) (step_mono w' a u))
  | cons_cons a _ ih =>
    intro w w' h
    exact ih (World.step w a) (World.step w' a) (step_le h a)

/-- The height of a node only grows along the event list. -/
theorem stateBefore_mono (rho : Run V counter) {i j : Nat} (hij : i ≤ j) (v : V) :
    height (Run.stateBefore counter rho i) v ≤ height (Run.stateBefore counter rho j) v :=
  foldl_sublist (List.take_sublist_take_left hij) _ _ (fun _ => le_refl _) v

end Mono

theorem counter_hooks : HooksSound counter := by
  refine ⟨fun _ _ h => by simp [counter] at h, ?_, ?_, ?_, fun _ _ _ h => Or.inl h⟩
  · intro V _ _ E rho _ v o i j _ h; simp [counter] at h
  · intro V _ _ E rho _ v o i j hij h
    exact decide_eq_true (inst := Nat.decLe _ _)
      (Nat.le_trans (of_decide_eq_true (inst := Nat.decLe _ _) h) (stateBefore_mono rho hij v))
  · intro V _ _ E rho _ v o i j hij h
    exact decide_eq_true (inst := Nat.decLe _ _)
      (Nat.le_trans (of_decide_eq_true (inst := Nat.decLe _ _) h)
        (Nat.add_le_add_right (stateBefore_mono rho hij v) 1))

def counterInst : Instance where
  n := 1
  P := counter
  Δ := 1
  Δ_pos := by decide
  iface := counterIface
  hooks := counter_hooks

end AvailableChain.Registry.Counter

end
