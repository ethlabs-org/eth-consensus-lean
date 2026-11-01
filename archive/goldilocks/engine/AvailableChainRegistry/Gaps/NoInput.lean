module
public import AvailableChainFramework
public import AvailableChainKit.Roots
public import Mathlib.Tactic

@[expose] public section

/-! KNOWN GAP I1 (design §12). This protocol reads no input and still passes
the core floor. The floor is too weak until engine v2 gives the proposer a
run-chosen input (plan 2). A run input alone is not enough (Astra A05). Plan 2
also needs a floor claim that binds the proposal to the input, and a
refutation of `clockChain` as its regression test (see below). The explorer
stays off until then. The registry marks these rows `KNOWN-GAP` (Task 0,
`gapsPrefix`).

`clockChain` reads no delivered object. Its state is the largest tick time so
far. Its two outputs are the chain of all slots up to that time, and its
proposal for slot `s` is the block of slot `s`, which every node can compute.
Every node ticks at every public time, so every honest read at `s` holds the
block of slot `s`: inclusion holds at `D = 0`.

The gap does not depend on `excludes := true`. With `excludes := false` the
same protocol still passes (reasoned, not compiled; plan 1b compiles it
against Candidate × Eligible). Its witness run then needs delivery events for
broadcast. Thus plan 2 cannot close I1 by an exclusion rule.

This module does not fix the gap. Plan 2 fixes it with a run-chosen proposer
input AND a floor claim that binds the proposal to that input. A run input
alone is not sufficient, because a protocol can ignore it. The regression test
of plan 2 is a refutation of this protocol (lifted to v2) against that claim.
This v1 certificate stays valid as a record of the gap. -/

namespace AvailableChain.Registry.Gaps.NoInput

open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Statements.Generic AvailableChain.Framework.Catalog

/-- The block of slot `k` on the clock chain. -/
def clockBlock : Nat → Block
  | 0 => .genesis
  | k + 1 => .node (clockBlock k) (k + 1) (nodeRoot (clockBlock k).root (k + 1) 0) 0

/-- A protocol that reads no input (design §12, I1): it excludes every
object, and its outputs depend on the clock only. -/
def clockChain : ProtocolSpec 1 where
  State := Time
  Label := Empty
  Payload := Nat
  init := 0
  clock := fun st t => max st t
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
  propose := fun _ s => some s
  gossip := fun _ _ => []
  process := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => true
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

def clockIface : Interface clockChain where
  confirmed := fun st => clockBlock st.toNat
  stable := fun st => clockBlock st.toNat
  block := fun k => some (clockBlock k)
  opening := fun _ => True

theorem clockHooks : HooksSound clockChain := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro st o _; rfl
  · intro V _ _ E rho _ v o i j _ _; rfl
  · intro V _ _ E rho _ v o i j _ h; simp [clockChain] at h
  · intro V _ _ E rho _ v o i j _ _; rfl
  · intro st o o' h; exact Or.inl h

def clockInst : Instance where
  n := 1
  P := clockChain
  Δ := 1
  Δ_pos := zero_lt_one
  iface := clockIface
  hooks := clockHooks

/-! ### Monotone states -/

section Mono

variable {V : Type} [DecidableEq V]

/-- The state of a node in a world: its largest tick time so far, or `0`. -/
def now (w : World V clockChain) (v : V) : Int := w v

/-- A step does not decrease the state of a node. -/
theorem step_mono (w : World V clockChain) (e : Event V clockChain.Object) (u : V) :
    now w u ≤ now (World.step w e) u := by
  unfold now
  cases e with
  | tick v t =>
    by_cases h : u = v
    · subst h
      simp only [World.step, Function.update_self]
      exact le_max_left _ _
    · simp only [World.step, Function.update_of_ne h]
      exact le_refl _
  | deliver v o t =>
    by_cases h : u = v
    · subst h
      simp only [World.step, Function.update_self]
      exact le_refl _
    · simp only [World.step, Function.update_of_ne h]
      exact le_refl _

/-- A step is monotone in the world. -/
theorem step_le {w w' : World V clockChain} (h : ∀ u, now w u ≤ now w' u)
    (e : Event V clockChain.Object) (u : V) :
    now (World.step w e) u ≤ now (World.step w' e) u := by
  unfold now at h ⊢
  cases e with
  | tick v t =>
    by_cases hu : u = v
    · subst hu
      simp only [World.step, Function.update_self]
      exact max_le_max (h u) (le_refl _)
    · simp only [World.step, Function.update_of_ne hu]
      exact h u
  | deliver v o t =>
    by_cases hu : u = v
    · subst hu
      simp only [World.step, Function.update_self]
      exact h u
    · simp only [World.step, Function.update_of_ne hu]
      exact h u

/-- The fold over a sublist gives a smaller state at every node. -/
theorem foldl_sublist {l₁ l₂ : List (Event V clockChain.Object)} (hl : l₁.Sublist l₂) :
    ∀ w w' : World V clockChain, (∀ u, now w u ≤ now w' u) →
      ∀ u, now (l₁.foldl World.step w) u ≤ now (l₂.foldl World.step w') u := by
  induction hl with
  | slnil => intro w w' h; exact h
  | cons a _ ih =>
    intro w w' h
    exact ih w (World.step w' a) (fun u => le_trans (h u) (step_mono w' a u))
  | cons_cons a _ ih =>
    intro w w' h
    exact ih (World.step w a) (World.step w' a) (step_le h a)

/-- After a list that holds a tick of `v` at `t`, the state of `v` is at
least `t`. -/
theorem tick_le {l : List (Event V clockChain.Object)} {v : V} {t : Time}
    (h : Event.tick v t ∈ l) (w : World V clockChain) :
    t ≤ now (l.foldl World.step w) v := by
  have hs := foldl_sublist (List.singleton_sublist.mpr h) w w (fun _ => le_refl _) v
  refine le_trans ?_ hs
  simp only [List.foldl_cons, List.foldl_nil, World.step, now, Function.update_self]
  exact le_max_right (α := Int) _ _

/-- Reads only grow with time, in every run: the events up to `t` are a
sublist of the events up to `t'`. -/
theorem readAt_mono (rho : Run V clockChain) {t t' : Time} (h : t ≤ t') (v : V) :
    now (Run.readAt clockChain rho t) v ≤ now (Run.readAt clockChain rho t') v :=
  foldl_sublist
    (List.monotone_filter_right _ (fun _ he =>
      decide_eq_true (le_trans (of_decide_eq_true he) h)))
    _ _ (fun _ => le_refl _) v

end Mono

/-! ### Blocks -/

theorem clockBlock_depth : ∀ m : Nat, (clockBlock m).depth = m
  | 0 => rfl
  | m + 1 => by simp [clockBlock, Block.depth, clockBlock_depth m]

/-- Distinct slots give distinct blocks. -/
theorem clockBlock_injective {i j : Nat} (h : clockBlock i = clockBlock j) : i = j := by
  simpa [clockBlock_depth] using congrArg Block.depth h

theorem preceq_refl (B : Block) : Block.Preceq B B := by
  cases B <;> simp [Block.Preceq, Block.preceq]

theorem preceq_node {B p : Block} (s : Slot) (r_s : BlockId) (x : Nat) (h : Block.Preceq B p) :
    Block.Preceq B (.node p s r_s x) := by
  simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  exact Or.inr h

theorem clockBlock_preceq : ∀ {a b : Nat}, a ≤ b → Block.Preceq (clockBlock a) (clockBlock b)
  | a, 0, h => by
    obtain rfl : a = 0 := by omega
    exact preceq_refl _
  | a, b + 1, h => by
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact preceq_node _ _ _ (clockBlock_preceq (by omega))
    · obtain rfl : a = b + 1 := by omega
      exact preceq_refl _

theorem preceq_clockBlock {B : Block} :
    ∀ {p : Nat}, Block.Preceq B (clockBlock p) → ∃ j, B = clockBlock j
  | 0, h => ⟨0, by simpa [Block.Preceq, Block.preceq, clockBlock] using h⟩
  | p + 1, h => by
    simp only [Block.Preceq, clockBlock, Block.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨p + 1, h⟩
    · exact preceq_clockBlock h

theorem blockInRun_clock {V : Type} [DecidableEq V] {E : Env V}
    {rho : Run V clockChain} {B : Block} (hB : BlockInRun E clockIface rho B) :
    ∃ j, B = clockBlock j := by
  rcases hB with hB | ⟨v, o, t, tip, _, htip, hpre⟩
  · exact ⟨0, hB⟩
  · have : tip = clockBlock o.payload := (Option.some.inj htip).symm
    subst this
    exact preceq_clockBlock hpre

/-- Roots are computed from block content, so they are injective in every run. -/
theorem clock_rootInjective {V : Type} [DecidableEq V] (E : Env V)
    (rho : Run V clockChain) : RootInjective E clockIface rho :=
  by
    intro A B hA hB hr
    obtain ⟨i, rfl⟩ := blockInRun_clock hA
    obtain ⟨j, rfl⟩ := blockInRun_clock hB
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => simp [clockBlock, Block.root, nodeRoot, genesisRoot] at hr
    | succ i =>
      cases j with
      | zero => simp [clockBlock, Block.root, nodeRoot, genesisRoot] at hr
      | succ j =>
        simp only [clockBlock, Block.root, nodeRoot, BlockId.mk.injEq,
          Nat.add_right_cancel_iff] at hr
        have hs := (epair_inj (epair_inj hr).2).1
        exact congrArg clockBlock hs

/-! ### Safety, prefix and inclusion -/

/-- Every read is `clockBlock m` for some `m`, so reads agree; the state only
grows with time, so reads only extend. -/
theorem clock_safe (W : Validators) (rho : Run W.V clockChain) (t₀ : Time) :
    SafeFrom clockChain rho clockIface.confirmed t₀ := by
  constructor
  · intro u _ v _ t t' _ _ _ _
    change Block.compatible (clockBlock (now (Run.readAt clockChain rho t) u).toNat)
      (clockBlock (now (Run.readAt clockChain rho t') v).toNat) = true
    unfold Block.compatible
    rw [Bool.or_eq_true]
    rcases Nat.le_total (now (Run.readAt clockChain rho t) u).toNat
      (now (Run.readAt clockChain rho t') v).toNat with h | h
    · exact Or.inl (clockBlock_preceq h)
    · exact Or.inr (clockBlock_preceq h)
  · intro v _ t t' _ htt' _
    exact clockBlock_preceq (Int.toNat_le_toNat (readAt_mono rho htt' v))

/-- Inclusion at `D = 0`. The honest awake proposer of `s` ticks at `s` and
emits the block of slot `s`. Every honest node ticks at `s`, so its read at `s`
is at least the block of slot `s`. -/
theorem clock_included (W : Validators) (E : Env W.V) (hΔ : E.Δ = 1)
    (rho : Run W.V clockChain) (t₀ : Time)
    (hs : SleepyRegime clockChain E clockIface rho t₀) :
    IncludedFrom clockChain E clockIface rho clockIface.confirmed t₀ 0 := by
  intro s _ hprop hsh
  obtain ⟨hph, hpa⟩ := hprop
  have hsched := hs.execution.toScheduleWellFormed
  have hs0 : (0 : Time) ≤ s := Int.natCast_nonneg s
  change (s : Time) + 0 ≤ rho.horizon at hsh
  have hsH : (s : Time) ≤ rho.horizon := by linarith
  have hpub : PublicTime E (s : Time) := ⟨s, by rw [hΔ, mul_one]⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hsched.tick_total _ hph s hpub hs0 hsH)
  refine ⟨clockBlock s, ⟨hph, s, rfl, i, hi, ?_⟩, ?_⟩
  · change E.awake (rho.proposerOf s) (s : Time) = true at hpa
    simp [Run.emittedAt, hpa, clockChain]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  · intro w hw
    change Block.Preceq (clockBlock s)
      (clockBlock (now (Run.readAt clockChain rho ((s : Time) + 0)) w).toNat)
    apply clockBlock_preceq
    have htw : Event.tick w (s : Time) ∈
        rho.events.filter (fun e => decide (e.time ≤ (s : Time) + 0)) :=
      List.mem_filter.mpr ⟨hsched.tick_total w hw s hpub hs0 hsH,
        decide_eq_true (by simp [Event.time])⟩
    have hle := tick_le htw World.init
    have := Int.toNat_le_toNat hle
    simpa [Run.readAt] using this

/-! ### The witness run -/

def clockEnv : Env (Fin 1) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := le_rfl
  awake := fun _ _ => true

/-- One validator, a tick at every integer time `0 … N`, no delivery. -/
def clockRun (N : Nat) : Run (Fin 1) clockChain where
  honest := Finset.univ
  horizon := N
  events := (List.range (N + 1)).map (fun (k : Nat) => .tick 0 (k : Time))
  seatOf := fun ℓ => ℓ.elim
  proposerOf := fun _ => 0

private theorem no_delivery (N i : Nat) (v : Fin 1) (o : clockChain.Object) (t : Time) :
    (clockRun N).events[i]? ≠ some (.deliver v o t) := by
  intro h
  have hm : Event.deliver v o t ∈ (clockRun N).events :=
    List.mem_iff_getElem?.2 ⟨i, h⟩
  simp [clockRun, List.mem_map] at hm

theorem clockExecution (N : Nat) : ExecutionValid clockChain clockEnv (clockRun N) := by
  refine { horizon_nonneg := Int.natCast_nonneg N
           sorted := ?_
           nodup := ?_
           in_horizon := ?_
           honest_only := fun _ _ => Finset.mem_univ _
           tick_public := ?_
           tick_total := ?_
           wire := fun i v o t h => (no_delivery N i v o t h).elim
           deps := fun i v o t h => (no_delivery N i v o t h).elim
           fresh := fun i v o t h => (no_delivery N i v o t h).elim
           unforgeable := fun v o t ⟨i, hi⟩ => (no_delivery N i v o t hi).elim
           carried := fun v o t ⟨i, hi⟩ => (no_delivery N i v o t hi).elim }
  · simp only [clockRun, List.pairwise_map]
    apply List.Pairwise.imp _ List.pairwise_lt_range
    intro a b hab
    change toLex ((a : Time), 0) ≤ toLex ((b : Time), 0)
    apply Prod.Lex.toLex_le_toLex.mpr
    exact Or.inl (show (a : Time) < b by exact_mod_cast hab)
  · apply List.Nodup.map (fun a b h => by cases h; rfl) List.nodup_range
  · intro e he
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
    have hk' : k ≤ N := by have := List.mem_range.mp hk; omega
    exact ⟨Int.natCast_nonneg k, show (k : Time) ≤ (N : Time) by exact_mod_cast hk'⟩
  · intro v t h
    obtain ⟨k, _, hk⟩ := List.mem_map.mp h
    cases hk
    exact ⟨k, (mul_one _).symm⟩
  · intro v _ t ⟨j, hj⟩ _ hle
    have htj : t = j := hj.trans (mul_one _)
    subst htj
    have hjN : j ≤ N := by exact_mod_cast (show (j : Time) ≤ (N : Time) from hle)
    obtain rfl : v = 0 := Subsingleton.elim _ _
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩

/-- `excludes` is always true, so no delivery obligation applies. -/
theorem clockSynchrony (N : Nat) : PartialSynchrony clockChain clockEnv (clockRun N) := by
  constructor
  · intro v _ o t _ w _ _ hex
    simp [clockChain] at hex
  · intro v _ i o t _ w _ _ _ hex
    simp [clockChain] at hex

theorem clockSleepy (N : Nat) :
    SleepyRegime clockChain clockEnv clockIface (clockRun N) 0 := by
  refine { execution := clockExecution N
           rootInjective := clock_rootInjective _ _
           partialSynchrony := clockSynchrony N
           gst_zero := rfl
           start_zero := rfl
           participation := ?_ }
  intro t _ _
  simp [AwakeMajority, faulty, awakeAt, clockRun, clockEnv]

/-- The Sleepy regime of the clock chain has runs of every horizon. -/
theorem sleepyInhabited (H : Time) :
    ∃ (W : Validators) (E : Env W.V) (rho : Run W.V clockInst.P) (t₀ : Time),
      E.Δ = clockInst.Δ ∧ H ≤ rho.horizon ∧ sleepy clockInst W E rho t₀ :=
  ⟨⟨Fin 1, inferInstance, inferInstance⟩, clockEnv, clockRun H.toNat, 0, rfl,
    Int.self_le_toNat H, clockSleepy H.toNat⟩

/-! ### The four certificates and the candidate -/

def certSafeConfirmed : Cert safeConfirmed clockInst where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    obtain ⟨W, E, rho, t₀, hΔ, hH, hs⟩ := sleepyInhabited H
    exact ⟨W, ⟨E, rho⟩, t₀, hΔ, hH, hs, trivial⟩
  proof := by
    intro W x _ t₀ _
    exact clock_safe W x.rho t₀

def certSafeStable : Cert safeStable clockInst where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    obtain ⟨W, E, rho, t₀, hΔ, hH, hs⟩ := sleepyInhabited H
    exact ⟨W, ⟨E, rho⟩, t₀, hΔ, hH, hs, trivial⟩
  proof := by
    intro W x _ t₀ _
    exact clock_safe W x.rho t₀

/-- The two outputs are equal. -/
def certPrefix : Cert prefixOrder clockInst where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    exact ⟨⟨Fin 1, inferInstance, inferInstance⟩, ⟨clockEnv, clockRun H.toNat⟩, (), rfl,
      Int.self_le_toNat H, trivial, trivial⟩
  proof := by
    intro W x _ _ _
    exact ⟨fun v _ t => preceq_refl _⟩

/-- The trigger slot `s = (max H 1).toNat` is at least `H` and positive (I2:
the trigger is late). -/
private theorem slot_late (H : Time) :
    H ≤ ((max H 1).toNat : Time) ∧ (0 : Time) < ((max H 1).toNat : Time) :=
  ⟨le_trans (le_max_left _ _) (Int.self_le_toNat _),
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (Int.self_le_toNat _))⟩

def certIncluded : Cert includedConfirmed clockInst where
  const := (0 : Time)
  valid := le_rfl
  inhabited := by
    intro H
    obtain ⟨hH, hpos⟩ := slot_late H
    refine ⟨⟨Fin 1, inferInstance, inferInstance⟩,
      ⟨clockEnv, clockRun (max H 1).toNat⟩, (0 : Time), rfl, hH,
      clockSleepy (max H 1).toNat, (max H 1).toNat, hpos, hH,
      ⟨Finset.mem_univ _, rfl⟩, ?_⟩
    change ((max H 1).toNat : Time) + 0 ≤ ((max H 1).toNat : Time)
    rw [add_zero]
  proof := by
    intro W x hΔ t₀ hs
    exact clock_included W x.E hΔ x.rho t₀ hs

/-- KNOWN GAP I1: the clock chain passes the core floor at `D = 0`. -/
noncomputable def clockCandidate : Candidate clockInst where
  shared := (0 : Time)
  valid := le_rfl
  certs := by
    classical
    intro e he
    exact if h1 : e = ⟨safeConfirmed, fun _ => ()⟩ then
        (by subst h1; exact ⟨certSafeConfirmed, rfl⟩)
      else if h2 : e = ⟨safeStable, fun _ => ()⟩ then
        (by subst h2; exact ⟨certSafeStable, rfl⟩)
      else if h3 : e = ⟨prefixOrder, fun _ => ()⟩ then
        (by subst h3; exact ⟨certPrefix, rfl⟩)
      else (by
        have h4 : e = ⟨includedConfirmed, fun D => D⟩ := by
          rcases List.mem_cons.1 he with h | he; · exact absurd h h1
          rcases List.mem_cons.1 he with h | he; · exact absurd h h2
          rcases List.mem_cons.1 he with h | he; · exact absurd h h3
          exact List.mem_singleton.1 he
        subst h4; exact ⟨certIncluded, rfl⟩)

end AvailableChain.Registry.Gaps.NoInput

end
