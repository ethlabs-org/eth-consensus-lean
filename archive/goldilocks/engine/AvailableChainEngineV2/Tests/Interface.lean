module
public import AvailableChainEngineV2.Conditions.Delivery
public import AvailableChainEngineV2.Conditions.Interface
public import AvailableChainEngineV2.Laws.Outputs
public import AvailableChainEngineV2.Tests.Laws

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

/-! Tests of the interface, the output reader, the outputs law and the delivery
conditions (plan 2a, Task 5). A proposal duty is a one-seat label, and a
two-seat label cannot be one. Two slots never share a proposal duty, so a spec
with one label has no `Interface`. `OutputsFactor` with `base := id` holds by
`rfl`, and it fails for an output that reads the own record. Broadcast in
`HealthyPrefixDelivery` includes the emitting node. -/

namespace AvailableChain.V2.Tests

open AvailableChain AvailableChain.V2

/-! ### Specs with slot-indexed proposal labels -/

/-- The duties of `slotSpec`: slot `t` at a time `t ≥ 0`. -/
def dutiesS (t : Time) : List Slot := if 0 ≤ t then [t.toNat] else []

theorem dutiesS_spec (s : Slot) (t : Time) : s ∈ dutiesS t ↔ (s : Time) = t := by
  unfold dutiesS
  by_cases h : 0 ≤ t
  · simp only [h, ite_true, List.mem_singleton]
    constructor
    · rintro rfl; exact Int.toNat_of_nonneg h
    · rintro rfl; exact (Int.toNat_natCast s).symm
  · simp only [h, ite_false, List.not_mem_nil, false_iff]
    rintro rfl; exact h (Int.natCast_nonneg s)

theorem dutiesS_nodup (t : Time) : (dutiesS t).Nodup := by
  unfold dutiesS
  split_ifs <;> simp

/-- Labels are slots; label `s` is due at time `s`. `sts` gives the seats, `sv`
the self-visibility of every label, and the own record adds `rec`. The clock
keeps the state, `act` adds the input to the state, a delivery sets the state
to the payload, and a restart restores 0. -/
abbrev slotSpec (sts : Slot → Nat) (sv : Bool) (rec : Nat) : ProtocolSpec Nat where
  State := Nat
  Label := Slot
  seats := sts
  Payload := Nat
  Durable := Unit
  init := 0
  clock := fun s _ => s
  actTime := fun s => (s : Time)
  duties := dutiesS
  duties_spec := dutiesS_spec
  duties_nodup := dutiesS_nodup
  act := fun s _ x => some (s + x)
  gossip := fun _ _ => []
  process := fun _ o => o.payload
  selfVisible := fun _ => sv
  recordOwn := fun s _ => s + rec
  durable := fun _ => ()
  restore := fun _ _ => 0
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

/-- Every label has one seat; nothing is self-visible; the own record is inert. -/
abbrev specS : ProtocolSpec Nat := slotSpec (fun _ => 1) false 0
/-- Label `0` has two seats, every other label one. -/
abbrev specS2 : ProtocolSpec Nat := slotSpec (fun s => if s = 0 then 2 else 1) false 0
/-- Every label is self-visible, and the own record adds 10. -/
abbrev specSR : ProtocolSpec Nat := slotSpec (fun _ => 1) true 10

/-! ### `Interface` with a one-seat proposal label -/

/-- Slot `s` proposes with label `s`. The confirmed output names the state. -/
def IS : Interface specS where
  confirmed := fun st => .node .genesis 1 (nodeRoot Block.genesis.root 1 st) st
  stable := fun _ => .genesis
  block := fun p => some (.node .genesis 1 (nodeRoot Block.genesis.root 1 p) p)
  opening := fun _ => True
  propLabel := id
  propLabel_single := fun _ => rfl
  propLabel_injective := Function.injective_id

/-- Validator 1 holds every seat and ticks at time 3; its input is `100 * v`. -/
def rhoP : Run (Fin 2) specS where
  honest := ∅
  horizon := 3
  events := [.tick 1 3]
  seatOf := fun _ _ => 1
  input := fun v _ => 100 * v.val

example : proposalTime IS 7 = 7 := rfl
example : propSeat IS 3 = ⟨0, by decide⟩ := rfl
-- In `rhoP`, validator 1 holds every seat, so it is the proposer.
example : proposerOf rhoP IS 7 = 1 := rfl
-- The proposal of slot 3 is the object that `rhoP` emits at time 3: the
-- post-clock state 0 plus the input 100 of validator 1.
example : Run.emitsAt (envAwake _) rhoP 0 = [⟨.seat 3 ⟨0, by decide⟩, 100⟩] := rfl
example : (⟨.seat (IS.propLabel 3) (propSeat IS 3), 100⟩ : specS.Object) ∈
    Run.emitsAt (envAwake _) rhoP 0 := by
  rw [show Run.emitsAt (envAwake _) rhoP 0 = [⟨.seat 3 ⟨0, by decide⟩, 100⟩] from rfl]
  exact List.mem_singleton_self _
example (i : Fin (specS.seats (IS.propLabel 7))) :
    Run.holder rhoP (.seat (IS.propLabel 7) i) = some 1 :=
  holder_propLabel rhoP IS 7 i

/-- Slot `s` proposes with label `s + 1`, which has one seat in `specS2`. -/
def IS2 : Interface specS2 where
  confirmed := fun _ => .genesis
  stable := fun _ => .genesis
  block := fun _ => none
  opening := fun _ => True
  propLabel := fun s => s + 1
  propLabel_single := fun _ => by simp
  propLabel_injective := fun _ _ h => Nat.add_right_cancel h

example : proposalTime IS2 4 = 5 := rfl
-- Label `0` has two seats: it is not a proposal duty.
example : ¬ ∃ I : Interface specS2, I.propLabel 0 = 0 := by
  rintro ⟨I, h⟩
  have h1 := I.propLabel_single 0
  rw [h] at h1
  exact absurd h1 (by decide)

-- Two slots never share a proposal duty.
example {In : Type} (P : ProtocolSpec In) : ¬ ∃ I : Interface P, I.propLabel 0 = I.propLabel 1 :=
  fun ⟨I, h⟩ => absurd (I.propLabel_injective h) (by decide)
-- A spec with a constant proposal label (one label, `specB`) has no `Interface`.
example : IsEmpty (Interface specB) :=
  ⟨fun I => absurd (I.propLabel_injective (a₁ := 0) (a₂ := 1) rfl) (by decide)⟩

/-! ### The output reader and roots -/

/-- `rhoB` on `specS`: a delivery at time 4, then a restart and a tick at time 5. -/
def rhoS : Run Unit specS where
  honest := ∅
  horizon := 5
  events := [.deliver () ⟨.none, 1⟩ 4, .restart () 5, .tick () 5]
  seatOf := fun _ _ => ()
  input := fun _ _ => 0

-- At time 4 the delivery set the state to 1; at time 5 the restart restored 0,
-- and the tick kept it.
example : outputAt (envAwake _) rhoS IS.confirmed () 4 = .node .genesis 1 (nodeRoot
    Block.genesis.root 1 1) 1 := rfl
example : outputAt (envAwake _) rhoS IS.confirmed () 5 = .node .genesis 1 (nodeRoot
    Block.genesis.root 1 0) 0 := rfl
/-- ROOT-DIGEST W3: the interface names only genesis and constructed children. -/
theorem interface_root_scope : RootInjective (envAwake _) IS rhoS := by
  have scope (B : Block) (hB : BlockInRun (envAwake _) IS rhoS B) :
      B = .genesis ∨ ∃ x, B = .node .genesis 1 (nodeRoot genesisRoot 1 x) x := by
    rcases hB with rfl | ⟨v, o, t, tip, _, hb, hp⟩
    · exact Or.inl rfl
    · have he : Block.node .genesis 1 (nodeRoot genesisRoot 1 o.payload) o.payload = tip :=
        Option.some.inj hb
      subst tip
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hp
      rcases hp with hp | hp
      · exact Or.inr ⟨o.payload, hp⟩
      · exact Or.inl hp
  intro B C hB hC hr
  rcases scope B hB with rfl | ⟨x, rfl⟩ <;>
    rcases scope C hC with rfl | ⟨y, rfl⟩
  · rfl
  · have h := congrArg BlockId.value hr
    change 0 = epair 0 (epair 1 y) + 1 at h
    omega
  · have h := congrArg BlockId.value hr
    change epair 0 (epair 1 x) + 1 = 0 at h
    omega
  · have h := congrArg BlockId.value hr
    change epair 0 (epair 1 x) + 1 = epair 0 (epair 1 y) + 1 at h
    have he := (epair_inj (epair_inj (Nat.add_right_cancel h)).2).2
    subst y
    rfl

#print axioms interface_root_scope
-- The block of the delivered payload at time 4 is in the run.
example : BlockInRun (envAwake _) IS rhoS (.node .genesis 1 (nodeRoot Block.genesis.root 1 1) 1) :=
  Or.inr ⟨(), ⟨.none, 1⟩, 4, _, Or.inl ⟨0, rfl⟩, rfl, by decide⟩

/-! ### `OutputsFactor` -/

/-- `specS` with every label in `ap` and `fresh`. The base is the whole state. -/
def isoS : Isolation specS ⟨fun _ => True, fun _ => True, fun _ => False⟩ where
  Base := Nat
  base := id
  clockB := fun b _ => b
  clock_base := fun _ _ => rfl
  processB := fun _ o => o.payload
  process_base := fun _ _ => rfl
  recordOwn_base := fun _ _ => rfl
  actB := fun b _ x => some (b + x)
  act_base := fun _ _ _ _ => rfl
  gossipB := fun _ _ => []
  gossip_base := fun _ _ => rfl
  depsB := fun _ _ => true
  processedB := fun _ _ => false
  excludesB := fun _ _ => false
  handlesB := fun _ o o' => o = o'
  hooks_base := fun _ _ _ => ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl⟩
  separation := fun _ _ => rfl

/-- With `base := id` (`isoS`), the factors are the getters. -/
def outS : OutputsFactor IS isoS where
  confirmedB := IS.confirmed
  confirmed_base := fun _ => rfl
  stableB := IS.stable
  stable_base := fun _ => rfl

example (st : Nat) : IS.confirmed (tick (envAwake _) rhoS st () 5).1 =
    IS.confirmed (specS.clock st 5) :=
  outS.confirmed_tick _ _ _ _ _

/-- `specSR` with a confirmed output that names the state. -/
def IA : Interface specSR where
  confirmed := fun st => .node .genesis 1 (nodeRoot Block.genesis.root 1 st) st
  stable := fun _ => .genesis
  block := fun _ => none
  opening := fun _ => True
  propLabel := id
  propLabel_single := fun _ => rfl
  propLabel_injective := Function.injective_id

/-- Every label of `specSR` in `linked` (self-visible labels are allowed). The
base is trivial; the hooks of `specSR` are constant. -/
def isoSR : Isolation specSR ⟨fun _ => False, fun _ => False, fun _ => True⟩ where
  Base := Unit
  base := fun _ => ()
  clockB := fun _ _ => ()
  clock_base := fun _ _ => rfl
  processB := fun _ _ => ()
  process_base := fun _ _ => rfl
  recordOwn_base := fun _ _ => rfl
  actB := fun _ _ _ => none
  act_base := fun _ _ _ h => h.elim
  gossipB := fun _ _ => []
  gossip_base := fun _ _ => rfl
  depsB := fun _ _ => true
  processedB := fun _ _ => false
  excludesB := fun _ _ => false
  handlesB := fun _ o o' => o = o'
  hooks_base := fun _ _ _ => ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl⟩
  separation := fun _ h => h.elim (fun h => h.elim) (fun h => h.elim)

-- The own record of `specSR` changes the state, and so `confirmed`.
example : IA.confirmed (specSR.recordOwn 0 ⟨.none, 0⟩) = .node .genesis 1 (nodeRoot
    Block.genesis.root 1 10) 10 := rfl
-- The base of `isoSR` is trivial, but `confirmed` reads the state, which the
-- own record changes: there is no `OutputsFactor` value.
example : IsEmpty (OutputsFactor IA isoSR) := by
  refine ⟨fun h => ?_⟩
  have h0 := h.confirmed_base 0
  have h1 := h.confirmed_base 10
  rw [show isoSR.base 10 = isoSR.base 0 from rfl, ← h0] at h1
  exact absurd h1 (by decide)

/-! ### Delivery conditions -/

-- With no honest node, both conditions hold.
example : PartialSynchrony (envAwake _) rhoR :=
  ⟨fun _ hv => absurd hv (Finset.notMem_empty _),
    fun _ hv => absurd hv (Finset.notMem_empty _)⟩
example : HealthyPrefixDelivery (envAwake _) rhoR 10 :=
  ⟨fun _ hv => absurd hv (Finset.notMem_empty _),
    fun _ hv => absurd hv (Finset.notMem_empty _)⟩

-- With horizon 2, validator 0 emits at time 1 and never gets the object.
-- The deadline is within the run, so healthy-prefix delivery fails.
example : ¬ HealthyPrefixDelivery (envAwake _) { rhoNoSD with horizon := 2 } 2 := by
  intro h
  have hs := h.broadcast 0 (by decide) oSD 1
    ⟨0, rfl, List.mem_singleton_self _⟩ 0 (by decide) 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro u _ _; rfl) rfl
  rcases hs with ⟨k, _, hk⟩ | ⟨_, _, _, j, _, hj, _⟩
  · exact Bool.false_ne_true hk
  · match j, hj with
    | 0, hj => simp [rhoNoSD, rhoSD] at hj
    | _ + 1, hj => simp [rhoNoSD, rhoSD] at hj

end AvailableChain.V2.Tests

end
