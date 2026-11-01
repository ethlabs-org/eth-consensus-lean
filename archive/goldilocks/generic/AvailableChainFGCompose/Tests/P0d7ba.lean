module
public import AvailableChainFGCompose.Proofs.Finality.Kernel

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d7ba
open AvailableChain.SimplexFG AvailableChain.KitFG

/-! P0d7b-a G0 (bounded models). (A) exact terminal timing; (B) the kernel premise boundary
with the horizon exactly at the deadline; (C) one kernel-shaped opening/middle/terminal
chain under the shared window fold; (D) an interface execution whose terminal receipt uses
the kernel's exact `a₀` and deadline, with `KernelRunFacts` proved on it. (D) is an
interface model, not an ExecutionValid FG-SA or PC-SA run. -/

/-! (A) Timing: Δ = 1, R = 4, ΔF = 1, so κ = 2; opening round 1, terminal action q = 3. -/

private abbrev kT : FGTiming where
  delta := 1
  roundSlots := 4
  proposal s := 4 * (s : Time) * 1
  vote s := 4 * (s : Time) * 1 + 1
  early s := 4 * (s : Time) * 1 + 2 * 1
  freeze s := 4 * (s : Time) * 1 + 3 * 1
  release s := 4 * (s : Time) * 1 + 5 * 1
  gate s := 4 * (s : Time) * 1 + 6 * 1
  action r := 4 * ((r * 4 : Nat) : Time) * 1 + 6 * 1

private theorem kL : FGTimingLaws kT where
  delta_pos := by decide
  rounds := by decide
  proposal_eq _ := rfl
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private theorem kKappa : kappaF kT 1 = 2 := by decide

private theorem kBound : LivenessBoundW kT 1 := ⟨by rw [kKappa]; decide⟩

/-- Every premise of `kernel_terminal_bounds_W` at q = 3, GST = 0. -/
private theorem kTerminal_premises_sat :
    LivenessBoundW kT 1 ∧ (0 : Time) ≤ 1 ∧ (0 : Time) ≤ kT.action 3 :=
  ⟨kBound, by decide, by decide⟩

/-- POSITIVE: the generic terminal bounds at q = 3. -/
private theorem kTerminal :
    max (kT.action 3) 0 + 1 ≤ kT.proposal (3 * kT.roundSlots + kappaF kT 1) ∧
      kT.proposal (3 * kT.roundSlots + kappaF kT 1) + kT.delta = kernelDeadlineW kT 1 3 ∧
      kT.proposal (3 * kT.roundSlots + kappaF kT 1) < kT.action (3 + 1) :=
  kernel_terminal_bounds_W kT kL 3 kTerminal_premises_sat.1 kTerminal_premises_sat.2.1
    kTerminal_premises_sat.2.2

/-- The returned values: terminal slot 14 read at 56, deadline 57, actions 54 and 70. -/
private theorem kTerminalInspected :
    3 * kT.roundSlots + kappaF kT 1 = 14 ∧ kT.proposal 14 = 56 ∧
      kernelDeadlineW kT 1 3 = 57 ∧ kT.action 3 = 54 ∧ kT.action 4 = 70 := by
  rw [kKappa]
  decide

/-- R = 2 and ΔF = 9 give κ = 4 > R. -/
private abbrev kTWide : FGTiming :=
  { kT with roundSlots := 2, action := fun r => 4 * ((r * 2 : Nat) : Time) * 1 + 6 * 1 }

/-- NEGATIVE (κ ≤ R): without the liveness bound the terminal read is not before the
next action, so the anchor-cap cut of the kernel fails. -/
private theorem kWideRejected :
    ¬ LivenessBoundW kTWide 9 ∧
      kTWide.action (3 + 1) ≤ kTWide.proposal (3 * kTWide.roundSlots + kappaF kTWide 9) := by
  have hk : kappaF kTWide 9 = 4 := by decide
  refine ⟨fun h => ?_, ?_⟩
  · have := h.kappa_le_R
    rw [hk] at this
    exact absurd this (by decide)
  · rw [hk]
    decide

/-! (B) The kernel premise boundary. Honest slots are the positive slots; the service starts
at 0; the horizon is exactly the deadline 57. -/

private abbrev kSP : FGServicePoint := ⟨⟨0, 0, 0, 0, 0, .genesis⟩, 0, .genesis, 0⟩

private abbrev kH (s : Slot) : Prop := 0 < s

/-- POSITIVE (premises_sat): every field, with the horizon covering the deadline. -/
private theorem kPrem : KernelPrem_W kT 1 57 kSP ⟨1⟩ kH 1 1 8 2 where
  bound := kBound
  window := by
    rw [Gen.Pure.FGoodE_W_def, kKappa]
    exact ⟨by decide, by decide, ⟨10, by decide, by decide, by decide⟩, by decide⟩
  start := by decide
  hhor := by rw [kTerminalInspected.2.2.1]
  honest_quorum := le_rfl
  timeout_eq := rfl
  capacity_ge := le_rfl

/-- NEGATIVE (terminal receipt horizon): one unit short of the deadline. -/
private theorem kHorizonShort : ¬ KernelPrem_W kT 1 56 kSP ⟨1⟩ kH 1 1 8 2 := by
  intro h
  have := h.hhor
  rw [kTerminalInspected.2.2.1] at this
  exact absurd this (by decide)

/-- NEGATIVE (independent FG quorum): honest FG weight 1 below the quorum 2. -/
private theorem kQuorumShort : ¬ KernelPrem_W kT 1 57 kSP ⟨1⟩ kH 2 1 8 2 :=
  fun h => absurd h.honest_quorum (by decide)

/-- NEGATIVE (terminal carrier slot): the other three window slots stay honest. -/
private theorem kTerminalSlotMissing :
    ¬ KernelPrem_W kT 1 57 kSP ⟨1⟩ (fun s => 0 < s ∧ s ≠ 14) 1 1 8 2 := by
  intro h
  have hw := h.window
  rw [Gen.Pure.FGoodE_W_def, kKappa] at hw
  exact absurd hw.2.2.2 (by decide)

/-- NEGATIVE (service start): a start after the opening period. -/
private theorem kLateStart :
    ¬ KernelPrem_W kT 1 57 ⟨⟨0, 0, 0, 0, 0, .genesis⟩, 0, .genesis, 17⟩ ⟨1⟩ kH 1 1 8 2 := by
  intro h
  have := h.start
  exact absurd this (by decide)

/-! (C) One kernel-shaped chain, d = 2: opening A₀ at slot 4 (height 2), fresh U at slot 6
(height 3), B at slot 8 (T_h = U), middle carrier X_D at slot 10 (J = U, h_j = 3, retained
key (3, U)), terminal X at slot 14 with one signed row whose finality pair is (3, U). -/

private abbrev kE : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev kCfg : FGConfig := ⟨8⟩
private abbrev kA : FGBlock (Fin 1) :=
  .node .genesis 4 ⟨4⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private abbrev kU : FGBlock (Fin 1) := .node kA 6 ⟨6⟩ 0 [⟨0, .vote 2 ⟨4⟩ false, none⟩]
private abbrev kB : FGBlock (Fin 1) := .node kU 8 ⟨8⟩ 0 []
private abbrev kD : FGBlock (Fin 1) := .node kB 10 ⟨10⟩ 0 [⟨0, .vote 3 ⟨6⟩ false, none⟩]
private abbrev kXrow : Row (Fin 1) := ⟨0, .vote 4 ⟨10⟩ false, some ⟨3, ⟨6⟩⟩⟩
private abbrev kX : FGBlock (Fin 1) := .node kD 14 ⟨14⟩ 0 [kXrow]

private abbrev kH' : FGHeightView (Fin 1) := KitFG.Window.certificateHeight kE kCfg 2

/-- POSITIVE: the chain is nonempty and has exactly the kernel's height relations: strict
fresh extension A₀ → U, B and X_D below the pending key, and terminal finality U. -/
private theorem kChain :
    FGBlock.Preceq kA kU ∧ kA ≠ kU ∧ (kH' kA).h = 2 ∧ (kH' kU).h = 2 + 1 ∧
      (kH' kU).T_h = kU ∧ (kH' kB).h = 2 + 1 ∧ (kH' kB).T_h = kU ∧
      FGBlock.Preceq kD kX.parent ∧ (kH' kD).h = 2 + 2 ∧ (kH' kD).J = kU ∧
      (kH' kD).h_j = 2 + 1 ∧ (SimplexFG.Window.derive kE kCfg 2 kD).h_F < 2 + 1 ∧
      KitFG.Window.RetainedW kE kCfg 2 kD (2 + 1) kU ∧
      (SimplexFG.Window.derive kE kCfg 2 kX).F = kU := by
  refine ⟨by decide, by decide, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  unfold KitFG.Window.RetainedW
  decide +kernel

/-- NEGATIVE (one witness tuple): the same row naming another pair (3, A₀) or no finality
pair leaves F at genesis; only the fixed (d + 1, U) tuple finalizes U. -/
private theorem kOtherTuple :
    (SimplexFG.Window.derive kE kCfg 2
      (.node kD 14 ⟨14⟩ 0 [⟨0, .vote 4 ⟨10⟩ false, some ⟨3, ⟨4⟩⟩⟩])).F = .genesis ∧
    (SimplexFG.Window.derive kE kCfg 2
      (.node kD 14 ⟨14⟩ 0 [⟨0, .vote 4 ⟨10⟩ false, none⟩])).F = .genesis := by
  decide +kernel

/-! (D) Interface execution: deliveries of A₀, U, B, X_D at their proposal reads and of X at
time 56 (`late`: 57 = the kernel deadline). GST is 56; the node is awake from GST and ticks
at every public time from 56 to the horizon 60. The store is the shared window store and
every delivery runs `SimplexFG.Window.on_block`. -/

private def kErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (kErase p) s r (encFGBody x rs)

private abbrev kP : V2.ProtocolSpecD Unit where
  State := SimplexFG.Store (Fin 1)
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := FGBlock (Fin 1)
  Durable := SimplexFG.Store (Fin 1)
  init := SimplexFG.Store.init
  clock st _ := st
  actTime s := (s : Time)
  duties t := if 0 ≤ t then [t.toNat] else []
  duties_spec s t := by
    split
    · next ht =>
      simp only [List.mem_singleton]
      constructor
      · intro hs; subst s; exact Int.toNat_of_nonneg ht
      · intro hs; subst t; simp
    · next ht =>
      constructor
      · intro hm; cases hm
      · intro hs; exact False.elim (ht (hs ▸ Int.natCast_nonneg s))
  duties_nodup t := by split <;> simp
  act _ _ _ := none
  gossip _ _ := []
  process st o := SimplexFG.Window.on_block kE kCfg 2 st o.payload
  selfVisible _ := true
  recordOwn st _ := st
  durable st := st
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private noncomputable abbrev kObj (B : FGBlock (Fin 1)) : kP.Object := ⟨.none, B⟩
private abbrev kEnv : Generic.Env Unit :=
  ⟨1, by decide, 56, by decide, fun _ t => decide (56 ≤ t)⟩

private noncomputable abbrev kRun (late : Bool) : V2.D.Run Unit kP where
  honest := {()}
  horizon := 60
  events := [.deliver () (kObj kA) 16, .deliver () (kObj kU) 24, .deliver () (kObj kB) 32,
    .deliver () (kObj kD) 40, .tick () 56] ++
    (if late then [.tick () 57, .deliver () (kObj kX) 57] else
      [.deliver () (kObj kX) 56, .tick () 57]) ++ [.tick () 58, .tick () 59, .tick () 60]
  seatOf _ _ := ()
  input _ _ := ()

private noncomputable abbrev kR : FGCoreReads kP 1 Unit Unit Unit where
  core st := ⟨(), st, [], []⟩
  erase := kErase
  source _ := none
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ o := some o.payload

private noncomputable abbrev kS : FGSafetyReads kP 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode _ := kObj .genesis
  decode := some
  decodeObject _ := none
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (none, ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis

private theorem kSchedule (late : Bool) : V2.D.ScheduleWellFormed kEnv (kRun late) := by
  refine ⟨by cases late <;> decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases late <;> decide
  · cases late <;> decide
  · cases late <;> decide
  · cases late <;> decide
  · intro v t h
    have ht : t = 56 ∨ t = 57 ∨ t = 58 ∨ t = 59 ∨ t = 60 := by
      cases late <;> simp at h <;> omega
    rcases ht with rfl | rfl | rfl | rfl | rfl
    exacts [⟨56, by norm_num⟩, ⟨57, by norm_num⟩, ⟨58, by norm_num⟩, ⟨59, by norm_num⟩,
      ⟨60, by norm_num⟩]
  · intro v _ t ⟨k, hk⟩ _ h60 ha
    have h56 : 56 ≤ t := by simpa using ha
    subst hk
    have hk56' : (56 : Int) ≤ k := by simpa using h56
    have hk60' : (k : Int) ≤ 60 := by simpa using h60
    have hk56 : 56 ≤ k := by exact_mod_cast hk56'
    have hk60 : k ≤ 60 := by exact_mod_cast hk60'
    cases v
    interval_cases k <;> cases late <;> decide

/-- POSITIVE (premises_sat, BaseSet replacement): every field of `KernelRunFacts` on the
exact run, with ΔF = 1. -/
private theorem kRunFacts (late : Bool) : KernelRunFacts kS kEnv (kRun late) kE 1 where
  schedule := kSchedule late
  fault_weight := by
    have hf : historyFaulty kS (kRun late) = ∅ := by
      ext i
      simp [historyFaulty, safetyHolder]
    rw [hf]
    decide
  deltaF := le_rfl
  linked := fun i j _ => Subsingleton.elim i j
  awake _ _ _ h _ := decide_eq_true h

private def kReady (late : Bool) (i : Nat) (x : Unit) (W : FGBlock (Fin 1)) (t : Time) :
    Prop :=
  ∃ o, (kRun late).events[i]? = some (.deliver x o t) ∧ o.payload = W ∧
    ¬ (W ∈ (V2.D.Run.stateBefore kEnv (kRun late) i x).TF ∨
      W.parent ∉ (V2.D.Run.stateBefore kEnv (kRun late) i x).TF ∨
      FGBlock.preceq (V2.D.Run.stateBefore kEnv (kRun late) i x).F W = false ∨
      W.slot ≤ W.parent.slot)

private abbrev kBlocks : Finset (FGBlock (Fin 1)) := {.genesis, kA, kU, kB, kD, kX}

private theorem kNonempty : ¬ kE.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

private theorem kClosed : ∀ B ∈ kBlocks, B.parent ∈ kBlocks := by decide

private theorem kRoots (st : SimplexFG.Store (Fin 1)) (B : FGBlock (Fin 1))
    (hst : st.TF ⊆ kBlocks) (hB : B ∈ kBlocks) : StoreStepRoots st B := by
  have hsub : insert B st.TF ⊆ kBlocks := Finset.insert_subset hB hst
  intro X Y ⟨W, hW, hXW⟩ ⟨W', hW', hYW'⟩ hr
  have hX := KitFG.ancestor_closed_of_parent_closed kBlocks kClosed W (hsub hW) X hXW
  have hY := KitFG.ancestor_closed_of_parent_closed kBlocks kClosed W' (hsub hW') Y hYW'
  exact (by decide : ∀ X ∈ kBlocks, ∀ Y ∈ kBlocks, X.root = Y.root → X = Y) X hX Y hY hr

private theorem kEvents (late : Bool) (i : Nat) (e : V2.Event Unit kP.Object)
    (he : (kRun late).events[i]? = some e) :
    (∃ v o t, e = .deliver v o t ∧ o.payload ∈ kBlocks) ∨ ∃ v t, e = .tick v t := by
  have hm := List.mem_of_getElem? he
  cases late <;> simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact Or.inr ⟨_, _, rfl⟩
    | exact Or.inl ⟨_, _, _, rfl, by decide⟩

private theorem kTickSame (late : Bool) (st : kP.State) (v : Unit) (t : Time) :
    (V2.D.tick kEnv (kRun late) st v t).1 = st := by
  simp [V2.D.tick]

private theorem kOnBlockTF (st : SimplexFG.Store (Fin 1)) (B : FGBlock (Fin 1)) :
    (SimplexFG.Window.on_block kE kCfg 2 st B).TF ⊆ insert B st.TF := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [KitFG.Window.window_on_block_of_refused kE kCfg 2 st B hc]
    exact Finset.subset_insert _ _
  · rw [KitFG.Window.window_on_block_of_accepted kE kCfg 2 st B hc,
      KitFG.Window.window_update_finality_TF]

/-- Every reachable store has the window invariant and stays inside the six blocks. -/
private theorem kReach (late : Bool) (i : Nat) (x : Unit) :
    FGStoreInvariant (KitFG.Window.certificateHeight kE kCfg 2)
      (KitFG.Window.certificateFinality kE kCfg 2)
      (V2.D.Run.stateBefore kEnv (kRun late) i x) ∧
    (V2.D.Run.stateBefore kEnv (kRun late) i x).TF ⊆ kBlocks := by
  induction i with
  | zero =>
    refine ⟨KitFG.Window.windowStoreInvariant_init kE kCfg 2, ?_⟩
    change ({.genesis} : Finset (FGBlock (Fin 1))) ⊆ kBlocks
    decide
  | succ i ih =>
    cases he : (kRun late).events[i]? with
    | none =>
      have hlen : (kRun late).events.length ≤ i := by
        by_contra hn
        exact absurd (List.getElem?_eq_getElem (Nat.lt_of_not_ge hn)) (by rw [he]; simp)
      have hs : V2.D.Run.stateBefore kEnv (kRun late) (i + 1) =
          V2.D.Run.stateBefore kEnv (kRun late) i := by
        unfold V2.D.Run.stateBefore
        rw [List.take_of_length_le (by omega), List.take_of_length_le hlen]
      rw [hs]
      exact ih
    | some e =>
      rw [V2.D.Run.stateBefore_succ kEnv (kRun late) he]
      rcases kEvents late i e he with ⟨v, o, t, rfl, ho⟩ | ⟨v, t, rfl⟩
      · cases v
        cases x
        simp only [V2.D.World.step, Function.update_self]
        refine ⟨KitFG.Window.windowStoreInvariant_on_block kE kCfg 2 kNonempty (by decide) _ _
          ih.1 (kRoots _ _ ih.2 ho), ?_⟩
        intro B hB
        rcases Finset.mem_insert.mp (kOnBlockTF _ _ hB) with h | h
        · exact h ▸ ho
        · exact ih.2 h
      · cases v
        cases x
        simp only [V2.D.World.step, Function.update_self, kTickSame]
        exact ih

private noncomputable abbrev kO : FGObservationReads kR where
  height := KitFG.Window.certificateHeight kE kCfg 2
  finality := KitFG.Window.certificateFinality kE kCfg 2
  controls _ := ⟨.genesis, 0, 0, .genesis, false⟩
  viable _ X := X

/-- The produced selected-step equation: the checked delivery runs `on_block`. -/
private theorem kStep (late : Bool) :
    AcceptStep_W kR kEnv (kRun late) kE kCfg 2 (kReady late) := by
  intro i x W t _hx ⟨o, he, ho, hc⟩
  have hreach := kReach late i x
  refine ⟨?_, ?_⟩
  · rw [V2.D.Run.stateBefore_succ kEnv (kRun late) he]
    cases x
    simp only [V2.D.World.step, Function.update_self]
    change SimplexFG.Window.on_block kE kCfg 2 _ o.payload = _
    rw [ho]
    exact KitFG.Window.window_on_block_of_accepted kE kCfg 2 _ W hc
  · have hpar : W.parent ∈ (V2.D.Run.stateBefore kEnv (kRun late) i x).TF := by
      simp only [not_or, not_not] at hc
      exact hc.2.1
    have hclosed : ∀ B ∈ insert W (V2.D.Run.stateBefore kEnv (kRun late) i x).TF,
        B.parent ∈ insert W (V2.D.Run.stateBefore kEnv (kRun late) i x).TF := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact Finset.mem_insert_of_mem hpar
      · exact Finset.mem_insert_of_mem (hreach.1.closed B hB)
    have L := KitFG.Window.windowCertificateLaws kE kCfg 2 kNonempty (by decide)
    have hFW : FGBlock.Preceq (SimplexFG.Window.derive kE kCfg 2 W).F W :=
      KitFG.preceq_trans (L.finalized_preceq_justified W)
        (KitFG.preceq_trans (L.height.justified_preceq_entry W) (L.height.entry_preceq W))
    exact KitFG.ancestor_closed_of_parent_closed _ hclosed W (Finset.mem_insert_self _ _) _ hFW

private theorem kDurable : FGFinalityDurableLaws kR :=
  ⟨fun _ => ⟨fun _ _ h => h, fun st o h => KitFG.preceq_trans h
    (KitFG.Window.window_on_block_F_mono kE kCfg 2 st o.payload), fun _ _ h => h⟩,
    fun _ _ => rfl⟩

private theorem kReady5 : kReady false 5 () kX 56 :=
  ⟨kObj kX, rfl, rfl, by decide +kernel⟩

/-- The kernel's selected receipt: index 5 at the terminal read 56, `a₀ = 56`, strictly
before the kernel deadline 57. -/
private def kDelivery :
    BlockDelivery_W kR kEnv (kRun false) (kReady false) kX kU 56 (kernelDeadlineW kT 1 3) where
  selected _ _ := ⟨5, 56⟩
  witness x _ := by
    cases x
    rw [kTerminalInspected.2.2.1]
    exact ⟨rfl, by decide, Or.inr ⟨le_rfl, kReady5⟩⟩

private theorem kStored5 : (V2.D.Run.stateBefore kEnv (kRun false) 5 ()).J = kU ∧
    (V2.D.Run.stateBefore kEnv (kRun false) 5 ()).F = .genesis := by decide +kernel

private theorem kFinal : (SimplexFG.Window.derive kE kCfg 2 kX).F = kU := by decide +kernel

private theorem kGuards : AcceptGuards_W kR kEnv (kRun false) kE kCfg 2 (kReady false) kX kU
    56 (kernelDeadlineW kT 1 3) kDelivery where
  finCmp x hx := by
    cases x
    dsimp only
    intro _
    exact receipt_finCmp_of_block kR kEnv (kRun false) kE kCfg 2 kNonempty (by decide) kO rfl
      (· ∈ kBlocks) (fun C W hC hW => (by decide +kernel : ∀ C ∈ kBlocks, ∀ W ∈ kBlocks,
        FGBlock.compatible (KitFG.Window.certificateFinality kE kCfg 2 C).F
          (KitFG.Window.certificateFinality kE kCfg 2 W).F = true) C hC W hW)
      5 () (kReach false 5 ()).1
      (fun C hC _ => (kReach false 5 ()).2 hC) kX kU (by rw [kFinal]; exact preceq_refl _)
      (by decide)
  jPath x hx := by
    cases x
    dsimp only
    intro _ _
    exact receipt_jPath_of_cached_anchor kR kEnv (kRun false) kE kCfg 2 5 () kX kU
      kStored5.1 (by decide)
  cap x hx := by
    cases x
    dsimp only
    intro _ _
    exact (by decide +kernel : (receiptInsert_W kR kEnv (kRun false) kE kCfg 2 5 () kX).h_max ≤
      (SimplexFG.Window.derive kE kCfg 2 kX).h + 1)

private def kAccept : AcceptPrem_W kR kEnv (kRun false) kE kCfg 2 (kReady false) kX kU 56
    (kernelDeadlineW kT 1 3) where
  schedule := kSchedule false
  finalized := by rw [kFinal]; exact preceq_refl _
  deliver := kDelivery
  guards := kGuards
  horizon := by rw [kTerminalInspected.2.2.1]; decide

/-- POSITIVE: the terminal receipt at the kernel's `a₀` is accepted strictly before the
kernel deadline (the kernel's final `acceptBefore_W` step). -/
private theorem kAccepted :
    AcceptsFinalBefore kR kEnv (kRun false) () kU (kernelDeadlineW kT 1 3) :=
  acceptBefore_W kR kEnv (kRun false) kE kCfg 2 kNonempty (by decide) kDurable
    (kReady false) (kStep false) (fun i x _ => (kReach false i x).1) kX kU 56 _ kAccept ()
    (Finset.mem_singleton_self _)

/-- The returned acceptance is the actual store finality U before the deadline. -/
private theorem kAcceptedInspected :
    (V2.D.Run.stateBeforeTime kEnv (kRun false) 57 ()).F = kU ∧
      FGBlock.Preceq kU (V2.D.Run.stateBeforeTime kEnv (kRun false) 57 ()).F := by
  have h := kAccepted
  rw [kTerminalInspected.2.2.1] at h
  exact ⟨by decide +kernel, h⟩

/-- NEGATIVE (strict terminal receipt): the same receipt at the deadline 57 itself is not an
acceptance before the deadline, so no acceptance premise exists for it. -/
private theorem kLateRejected :
    ¬ AcceptsFinalBefore kR kEnv (kRun true) () kU (kernelDeadlineW kT 1 3) ∧
      ∀ (ready : Nat → Unit → FGBlock (Fin 1) → Time → Prop),
        AcceptStep_W kR kEnv (kRun true) kE kCfg 2 ready →
        IsEmpty (AcceptPrem_W kR kEnv (kRun true) kE kCfg 2 ready kX kU 56
          (kernelDeadlineW kT 1 3)) := by
  have hnot : ¬ AcceptsFinalBefore kR kEnv (kRun true) () kU (kernelDeadlineW kT 1 3) := by
    intro h
    rw [kTerminalInspected.2.2.1] at h
    have hF : (V2.D.Run.stateBeforeTime kEnv (kRun true) 57 ()).F = .genesis := by
      decide +kernel
    change FGBlock.Preceq kU (V2.D.Run.stateBeforeTime kEnv (kRun true) 57 ()).F at h
    rw [hF] at h
    exact absurd h (by decide)
  refine ⟨hnot, fun ready step => ⟨fun h => hnot ?_⟩⟩
  exact acceptBefore_W kR kEnv (kRun true) kE kCfg 2 kNonempty (by decide) kDurable ready
    step (fun i x _ => (kReach true i x).1) kX kU 56 _ h () (Finset.mem_singleton_self _)

#print axioms kTerminal
#print axioms kTerminalInspected
#print axioms kWideRejected
#print axioms kPrem
#print axioms kHorizonShort
#print axioms kQuorumShort
#print axioms kTerminalSlotMissing
#print axioms kLateStart
#print axioms kChain
#print axioms kOtherTuple
#print axioms kRunFacts
#print axioms kStep
#print axioms kAccepted
#print axioms kAcceptedInspected
#print axioms kLateRejected

end AvailableChain.FGCompose.Tests.P0d7ba
end
