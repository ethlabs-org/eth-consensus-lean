module
public import ConsensusLeanTest.Goldilocks.AC.Base
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.TickRun
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial

@[expose] public section

/-! # An infinite standalone SA execution with trivial frames

Kind (b) healing witness, with one honest validator and `k = c = 2`. Every public time has
a tick. At each positive slot start the validator proposes and accepts the block made from
the actual returned head and payload. No assumption is made about the chosen head or locks.
The FG frame is supplied directly: all accepted blocks remain viable, rooted at genesis.
-/

namespace Consensus.Goldilocks.SA.Test.SAHealing

open Consensus.Goldilocks.Witness

/-- The four kinds of reserved cuts. -/
inductive Kind where
  | tick | proposal | block | idle
  deriving DecidableEq

/-- Four cuts per public time, with proposal/acceptance only at positive slot starts. -/
def kind (i : Nat) : Kind :=
  if i % 4 = 0 then .tick
  else if 16 ≤ i ∧ i % 16 = 1 then .proposal
  else if 16 ≤ i ∧ i % 16 = 2 then .block
  else .idle

/-- The state, accepted tree, and block waiting for the next acceptance cut. -/
structure Config where
  state : SAState sp1.n
  tree : Set (Blk sp1.n Unit)
  pending : Blk sp1.n Unit

/-- Every accepted block is viable; the finalized and fork-choice roots stay at genesis. -/
def frame (T : Set (Blk sp1.n Unit)) : Frm sp1.n Unit := ⟨T, g, g, T⟩

/-- The actual proposal result, with a total default that will never be used. -/
noncomputable def proposalData (i : Nat) (C : Config) :
    DutyHead sp1.n Unit (Payload sp1.n) × Payload sp1.n :=
  (acProposal sp1 C.state (frame C.tree) (i / 4 : Nat)).2.getD (⟨g, g, C.tree⟩, [], [])

/-- Fresh root and slot, with the parent and payload returned by the SA. -/
noncomputable def madeBlock (i : Nat) (C : Config) : Blk sp1.n Unit :=
  ⟨i / 16, some (proposalData i C).1.head.root, i / 16, v0, 0, (),
    (proposalData i C).2⟩

/-- One reserved cut, executing the real handler. -/
noncomputable def next (i : Nat) (C : Config) : Config :=
  match kind i with
  | .tick => { C with state := (acOnTick sp1 v0 C.state (frame C.tree) (i / 4 : Nat)).1 }
  | .proposal => { C with
      state := (acProposal sp1 C.state (frame C.tree) (i / 4 : Nat)).1
      pending := madeBlock i C }
  | .block =>
    { C with tree := insert C.pending C.tree
             state := (acOnBlock sp1 v0 C.state (frame (insert C.pending C.tree))
               (i / 4 : Nat) C.pending).1 }
  | .idle => C

/-- Configuration before cut `i`. -/
noncomputable def config : Nat → Config
  | 0 => ⟨SAState.initial 0, {g}, g⟩
  | i + 1 => next i (config i)

/-- The frame at a cut includes the block being accepted at that cut. -/
noncomputable def cutFrame (i : Nat) : Frm sp1.n Unit :=
  frame (if kind i = .block then insert (config i).pending (config i).tree else (config i).tree)

/-- Only ticks, proposals and own blocks are called. -/
noncomputable def call (i : Nat) : Option GA1.Call :=
  match kind i with
  | .tick => some .tick
  | .proposal => some .proposal
  | .block => some (.block (config i).pending)
  | .idle => none

/-- The infinite component trace, including the handlers' actual emission read points. -/
noncomputable def run : SATrace sp1 Unit ro1 where
  init _ := SAState.initial 0
  node _ := v0
  time i := (i / 4 : Nat)
  event i := i / 4
  pos i := i % 4
  label i := (call i).map fun c =>
    ⟨c, cutFrame i, (GA1.step v0 (config i).state (cutFrame i) (i / 4 : Nat) c).2⟩
  post i := (config (i + 1)).state
  awake _ t := 0 ≤ t

/-- The block accepted in positive slot `s`. Slot zero is unused. -/
noncomputable def block (s : Nat) : Blk sp1.n Unit := (config (16 * s + 2)).pending

/-- The universe of blocks of this execution. -/
noncomputable def blocks : Set (Blk sp1.n Unit) :=
  {B | ∃ i, B ∈ (config i).tree}

theorem kind_tick (i : Nat) : kind i = .tick ↔ i % 4 = 0 := by
  unfold kind
  split_ifs <;> simp_all

theorem kind_proposal (i : Nat) : kind i = .proposal ↔ 16 ≤ i ∧ i % 16 = 1 := by
  unfold kind
  split_ifs <;> simp_all
  omega

theorem kind_block (i : Nat) : kind i = .block ↔ 16 ≤ i ∧ i % 16 = 2 := by
  unfold kind
  split_ifs <;> simp_all
  omega

theorem kind_proposal_slot {s : Nat} (hs : 0 < s) : kind (16 * s + 1) = .proposal :=
  (kind_proposal _).2 ⟨by omega, by omega⟩

theorem kind_block_slot {s : Nat} (hs : 0 < s) : kind (16 * s + 2) = .block :=
  (kind_block _).2 ⟨by omega, by omega⟩

theorem eq_zero (y : Fin sp1.n) : y = v0 := Subsingleton.elim _ _

theorem state_eq (y : Fin sp1.n) : ∀ i, run.state y i = (config i).state
  | 0 => rfl
  | i + 1 => by
    rw [eq_zero y]
    rw [Trace.state, state_eq v0 i]
    cases hk : kind i <;>
      simp [run, call, hk, config, next]

theorem callAt_iff {i : Nat} {ℓ : ACLabel GA1} : run.CallAt v0 i ℓ ↔
    call i = some ℓ.call ∧ ℓ.frame = cutFrame i ∧
      ℓ.emits = (GA1.step v0 (config i).state (cutFrame i) (i / 4 : Nat) ℓ.call).2 := by
  simp only [Trace.CallAt, run, true_and, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨hc, rfl, rfl⟩
  · rintro ⟨hc, hf, he⟩
    exact ⟨ℓ.call, hc, by cases ℓ; simp_all⟩

theorem exec {i : Nat} {ℓ : ACLabel GA1} (hc : run.CallAt v0 i ℓ) :
    GA1.step v0 (run.state v0 i) ℓ.frame (run.time i) ℓ.call = (run.post i, ℓ.emits) := by
  obtain ⟨hc, hf, he⟩ := callAt_iff.1 hc
  rw [state_eq, hf, he]
  change GA1.step v0 (config i).state (cutFrame i) (i / 4 : Nat) ℓ.call = _
  cases hk : kind i <;> simp only [call, hk, Option.some.injEq, reduceCtorEq] at hc
  all_goals rw [← hc]
  all_goals simp [GA1, goldilocksSA, ACInterface.step, cutFrame, config, next, hk, run]

theorem call_no_restart {i : Nat} {ℓ : ACLabel GA1} (hc : run.CallAt v0 i ℓ) :
    ℓ.call ≠ .restart := by
  have h := (callAt_iff.1 hc).1
  cases hk : kind i <;> simp [call, hk] at h <;> simp [← h]

theorem restartTime (i : Nat) : (config i).state.restartTime = ⊥ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases hk : kind i
    all_goals simp only [config, next, hk]
    case idle => exact ih
    all_goals
      have h := step_restartTime (sp := sp1) (ro := ro1) v0 (config i).state
        (frame (if kind i = .block then insert (config i).pending (config i).tree
          else (config i).tree)) (i / 4 : Nat)
      first
      | simpa only [hk, reduceCtorEq, ite_false, ACInterface.step, goldilocksSA] using
          (h .tick (by simp)).trans ih
      | simpa only [hk, reduceCtorEq, ite_false, ACInterface.step, goldilocksSA] using
          (h .proposal (by simp)).trans ih
      | simpa only [hk, ite_true, ACInterface.step, goldilocksSA] using
          (h (.block (config i).pending) (by simp)).trans ih

theorem joined_config (i : Nat) : joined sp1 (config i).state (i / 4 : Nat) := by
  simp [joined, restartTime]

theorem proposal_some (i : Nat) :
    (acProposal sp1 (config i).state (frame (config i).tree) (i / 4 : Nat)).2 =
      some (proposalData i (config i)) := by
  simp only [proposalData, acProposal, joined_config, not_true_eq_false, ite_false,
    Option.getD_some]

theorem block_eq {s : Nat} (hs : 0 < s) :
    block s = madeBlock (16 * s + 1) (config (16 * s + 1)) := by
  change (config ((16 * s + 1) + 1)).pending = _
  simp [config, next, kind_proposal_slot hs]

theorem block_slot {s : Nat} (hs : 0 < s) : (block s).slot = s := by
  rw [block_eq hs]
  simp [madeBlock]
  omega

theorem block_root {s : Nat} (hs : 0 < s) : (block s).root = s := by
  rw [block_eq hs]
  simp [madeBlock]
  omega

theorem config_tree_step (i : Nat) : (config (i + 1)).tree =
    if kind i = .block then insert (config i).pending (config i).tree else (config i).tree := by
  cases hk : kind i <;> simp [config, next, hk]

theorem tree_history (i : Nat) : (config i).tree =
    insert g {B | ∃ s : Nat, 0 < s ∧ 16 * s + 2 < i ∧ B = block s} := by
  induction i with
  | zero => ext B; simp [config]
  | succ i ih =>
    rw [config_tree_step, ih]
    by_cases hb : kind i = .block
    · rw [ite_eq_left hb]
      obtain ⟨hi, hm⟩ := (kind_block i).1 hb
      have hs : 0 < i / 16 := by omega
      have he : i = 16 * (i / 16) + 2 := by omega
      have hp : (config i).pending = block (i / 16) :=
        congrArg (fun k => (config k).pending) he
      rw [hp]
      ext B
      simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (rfl | rfl | ⟨s, hs, hlt, rfl⟩)
        · exact Or.inr ⟨_, hs, by omega, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨s, hs, by omega, rfl⟩
      · rintro (rfl | ⟨s, hs', hlt, rfl⟩)
        · exact Or.inr (Or.inl rfl)
        · by_cases he' : 16 * s + 2 = i
          · left; congr 1; omega
          · exact Or.inr (Or.inr ⟨s, hs', by omega, rfl⟩)
    · rw [ite_eq_right hb]
      have hn := mt (kind_block i).2 hb
      ext B
      simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (rfl | ⟨s, hs, hlt, rfl⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨s, hs, by omega, rfl⟩
      · rintro (rfl | ⟨s, hs, hlt, rfl⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨s, hs, by omega, rfl⟩

theorem blocks_eq : blocks = insert g {B | ∃ s : Nat, 0 < s ∧ B = block s} := by
  ext B
  constructor
  · rintro ⟨i, hB⟩
    rw [tree_history] at hB
    rcases hB with rfl | ⟨s, hs, -, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · exact ⟨0, by simp [config]⟩
    · refine ⟨16 * s + 3, ?_⟩
      rw [tree_history]
      exact Set.mem_insert_of_mem _ ⟨s, hs, by omega, rfl⟩

theorem tree_mono {i j : Nat} (hij : i ≤ j) : (config i).tree ⊆ (config j).tree := by
  rw [tree_history, tree_history]
  rintro B (rfl | ⟨s, hs, hi, rfl⟩)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨s, hs, by omega, rfl⟩

theorem root_eq_slot {B : Blk sp1.n Unit} (hB : B ∈ blocks) : B.root = B.slot := by
  rw [blocks_eq] at hB
  rcases hB with rfl | ⟨s, hs, rfl⟩
  · rfl
  · rw [block_root hs, block_slot hs]

theorem roots_injective : Set.InjOn Block.root blocks := by
  intro B hB C hC he
  rw [blocks_eq] at hB hC
  rcases hB with rfl | ⟨s, hs, rfl⟩ <;>
    rcases hC with rfl | ⟨t, ht, rfl⟩
  · rfl
  · have := block_root ht; change 0 = _ at he; omega
  · have := block_root hs; change _ = 0 at he; omega
  · rw [block_root hs, block_root ht] at he
    rw [he]

theorem tree_slot_lt {s : Nat} (hs : 0 < s) {B : Blk sp1.n Unit}
    (hB : B ∈ (config (16 * s + 2)).tree) : B.slot < s := by
  rw [tree_history] at hB
  rcases hB with rfl | ⟨r, hr, hi, rfl⟩
  · exact hs
  · rw [block_slot hr]; omega

theorem proposal_head_mem {i : Nat} (hf : FrameOK (frame (config i).tree)) :
    (proposalData i (config i)).1.head ∈ (config i).tree := by
  simp only [proposalData, acProposal, joined_config, not_true_eq_false, ite_false,
    Option.getD_some]
  exact getHead_mem hf (fun _ h => h.1) _ _ _ _

/-- Finite, rooted frames and parent roots strictly below the child slot. -/
theorem config_good (i : Nat) : FrameOK (frame (config i).tree) ∧
    ∀ B ∈ (config i).tree, ∀ r, B.parent = some r → r < B.slot := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero =>
      refine ⟨frameOK_Φ₀, ?_⟩
      intro B hB r hr
      have : B = g := Set.mem_singleton_iff.1 hB
      subst B
      cases hr
    | succ i =>
      obtain ⟨hf, hp⟩ := ih i (by omega)
      by_cases hb : kind i = .block
      · obtain ⟨hi, hm⟩ := (kind_block i).1 hb
        let s := i / 16
        have hs : 0 < s := by dsimp [s]; omega
        have he : i = 16 * s + 2 := by dsimp [s]; omega
        have htree : (config i).tree = (config (16 * s + 1)).tree := by
          rw [he]
          change (config ((16 * s + 1) + 1)).tree = _
          simp [config, next, kind_proposal_slot hs]
        have hprev := (ih (16 * s + 1) (by omega)).1
        let D := (proposalData (16 * s + 1) (config (16 * s + 1))).1.head
        have hd : D ∈ (config i).tree := by rw [htree]; exact proposal_head_mem hprev
        have hpend : (config i).pending = block s := by rw [he]; rfl
        have hparent : (block s).parent = some D.root := by rw [block_eq hs]; rfl
        have hbelow : D.root < (block s).slot := by
          rw [root_eq_slot ⟨i, hd⟩, block_slot hs]
          exact tree_slot_lt hs (he ▸ hd)
        have hnext : (config (i + 1)).tree = insert (block s) (config i).tree := by
          rw [config_tree_step, ite_eq_left hb, hpend]
        have hp' : ∀ B ∈ (config (i + 1)).tree, ∀ r, B.parent = some r → r < B.slot := by
          rw [hnext]
          rintro B (rfl | hB) r hr
          · rw [hparent] at hr
            exact (Option.some.inj hr) ▸ hbelow
          · exact hp B hB r hr
        have hc : Coherent (config (i + 1)).tree := by
          refine ⟨fun B hB C hC h => roots_injective ⟨_, hB⟩ ⟨_, hC⟩ h, ?_⟩
          intro B hB C hC h
          rw [← root_eq_slot ⟨_, hB⟩]
          exact hp' C hC B.root h
        have hroot : ∀ B ∈ (config (i + 1)).tree, Anc (config (i + 1)).tree g B := by
          rw [hnext]
          rintro B (rfl | hB)
          · exact (Anc.mono (Set.subset_insert _ _) (hf.rooted.2 D hd)).tail
              ⟨Set.mem_insert_of_mem _ hd, Set.mem_insert _ _, hparent⟩
          · exact Anc.mono (Set.subset_insert _ _) (hf.rooted.2 B hB)
        have hg : g ∈ (config (i + 1)).tree := tree_mono (by omega) hf.rooted.1
        refine ⟨?_, hp'⟩
        exact ⟨by rw [hnext]; exact hf.finite.insert _, hc, ⟨hg, hroot⟩,
          hg, Relation.ReflTransGen.refl, le_rfl, hroot⟩
      · have ht : (config (i + 1)).tree = (config i).tree := by
          rw [config_tree_step, ite_eq_right hb]
        rw [ht]
        exact ⟨hf, hp⟩

theorem coherent_blocks : Coherent blocks := by
  refine ⟨roots_injective, ?_⟩
  rintro B hB C ⟨i, hC⟩ hp
  rw [← root_eq_slot hB]
  exact (config_good i).2 C hC B.root hp

theorem cutFrame_eq (i : Nat) : cutFrame i = frame (config (i + 1)).tree := by
  rw [config_tree_step]
  rfl

theorem frameOK_cut (i : Nat) : FrameOK (cutFrame i) := by
  rw [cutFrame_eq]
  exact (config_good _).1

theorem frameIn_cut (i : Nat) : GA1.FrameIn blocks (cutFrame i) :=
  ⟨frameOK_cut i, fun _ h => ⟨i + 1, by simpa only [cutFrame_eq, frame] using h⟩⟩

theorem slot_time (i : Nat) : sp1.slot (i / 4 : Nat) = i / 16 := by
  apply slot_of_mem sp1
  · change 4 * ((i / 16 : Nat) : Int) ≤ ((i / 4 : Nat) : Int)
    omega
  · change ((i / 4 : Nat) : Int) < 4 * (((i / 16 : Nat) : Int) + 1)
    omega

theorem slotOK (i : Nat) : SAPool.SlotOK sp1 (config i).state := by
  induction i with
  | zero => intro σ v hv; simp [config, SAState.initial] at hv
  | succ i ih =>
    cases hk : kind i <;> simp only [config, next, hk]
    · exact SAPool.acOnTick_slot sp1 v0 _ _ _ ih
    · exact SAPool.slot_of_pool_eq sp1 (SAPool.acProposal_pool sp1 _ _ _) ih
    · exact SAPool.acOnBlock_slot sp1 v0 _ _ _ _ ih
    · exact ih

theorem proposal_payload (i : Nat) : (proposalData i (config i)).2 =
    voteViewList (config i).state (frame (config i).tree)
      ((sp1.slot (i / 4 : Nat) : Int) - 1) ⊤ := by
  simp only [proposalData, acProposal, joined_config, not_true_eq_false, ite_false,
    Option.getD_some]

theorem block_valid {s : Nat} (hs : 0 < s) : validPayload (block s) := by
  rw [block_eq hs]
  change (∀ v ∈ (proposalData (16 * s + 1) (config (16 * s + 1))).2.1,
    v.slot + 1 = (16 * s + 1) / 16) ∧
    ∀ v ∈ (proposalData (16 * s + 1) (config (16 * s + 1))).2.2,
      v ∈ (proposalData (16 * s + 1) (config (16 * s + 1))).2.1
  rw [proposal_payload]
  have hslot : sp1.slot ((16 * s + 1) / 4 : Nat) = s := by rw [slot_time]; omega
  rw [hslot]
  refine ⟨?_, ?_⟩
  · intro v hv
    simp only [voteViewList, List.mem_filter, SAState.poolAt] at hv
    split_ifs at hv with hn
    · simp at hv
    · have h := slotOK (16 * s + 1) _ v hv.1
      omega
  · intro v hv
    exact (List.mem_filter.1 hv).1

theorem block_parent {s : Nat} (hs : 0 < s) :
    ∃ D ∈ (config (16 * s + 2)).tree, (block s).parent = some D.root ∧ D.slot < s := by
  let D := (proposalData (16 * s + 1) (config (16 * s + 1))).1.head
  have hd : D ∈ (config (16 * s + 2)).tree :=
    tree_mono (by omega) (proposal_head_mem (config_good _).1)
  exact ⟨D, hd, by rw [block_eq hs]; rfl, tree_slot_lt hs hd⟩

theorem block_cut {i : Nat} (hi : kind i = .block) :
    ∃ s : Nat, 0 < s ∧ i = 16 * s + 2 ∧ (config i).pending = block s := by
  obtain ⟨hi, hm⟩ := (kind_block i).1 hi
  have he : i = 16 * (i / 16) + 2 := by omega
  exact ⟨i / 16, by omega, he, congrArg (fun k => (config k).pending) he⟩

theorem frame_step {i : Nat} (hi : kind i = .block) :
    FrameStep (frame (config i).tree) (config i).pending (cutFrame i) := by
  obtain ⟨s, hs, he, hp⟩ := block_cut hi
  obtain ⟨D, hd, hparent, hslot⟩ := block_parent hs
  have ht : (cutFrame i).tree = insert (block s) (config i).tree := by
    simp [cutFrame, hi, hp, frame]
  have hf := frameOK_cut i
  refine ⟨?_, ?_, Relation.ReflTransGen.refl, ?_, ?_⟩
  · change (config i).pending ∉ (config i).tree
    rw [hp, he]
    intro hb
    have := tree_slot_lt hs hb
    rw [block_slot hs] at this
    omega
  · exact ⟨D, he ▸ hd, hp ▸ hparent⟩
  · have hroot := hf.rooted.2 (block s) (by rw [ht]; exact Set.mem_insert _ _)
    simpa only [cutFrame, hi, ite_true, frame, hp] using hroot
  · change (cutFrame i).tree = {X | X ∈ insert (config i).pending (config i).tree ∧
      Anc (insert (config i).pending (config i).tree) g X}
    rw [hp]
    ext X
    constructor
    · intro hx
      exact ⟨ht ▸ hx, by simpa only [cutFrame, hi, ite_true, frame, hp] using hf.rooted.2 X hx⟩
    · exact fun hx => ht ▸ hx.1

theorem callOK {i : Nat} {ℓ : ACLabel GA1} (hc : run.CallAt v0 i ℓ) :
    GA1.CallOK blocks (frame (config i).tree) (run.time i) ℓ.call ℓ.frame := by
  obtain ⟨hc, hf, -⟩ := callAt_iff.1 hc
  rw [hf]
  refine ⟨frameIn_cut i, ?_⟩
  cases hk : kind i <;> simp only [call, hk, Option.some.injEq, reduceCtorEq] at hc
  all_goals rw [← hc]
  · simp [cutFrame, hk]
  · simp [cutFrame, hk]
  · obtain ⟨s, hs, he, hp⟩ := block_cut hk
    refine ⟨frame_step hk, hp ▸ block_valid hs, ?_⟩
    change (config i).pending.slot ≤ sp1.slot (i / 4 : Nat)
    rw [hp, block_slot hs, slot_time, he]
    omega

theorem call_exists {i : Nat} {c : GA1.Call} (hc : call i = some c) :
    ∃ ℓ, run.CallAt v0 i ℓ ∧ ℓ.call = c := by
  refine ⟨⟨c, cutFrame i, (GA1.step v0 (config i).state (cutFrame i) (i / 4 : Nat) c).2⟩,
    callAt_iff.2 ⟨hc, rfl, rfl⟩, rfl⟩

theorem tree_noCall {a b : Nat} (hab : a ≤ b) (hn : run.NoCallBetween v0 a b) :
    (config b).tree = (config a).tree := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hi : kind b ≠ .block := by
      intro hb
      obtain ⟨ℓ, hc, -⟩ := call_exists
        (show call b = some (.block (config b).pending) by simp [call, hb])
      exact hn b hab (by omega) ℓ hc
    rw [config_tree_step, ite_eq_right hi]
    exact ih (fun k hak hkb => hn k hak (by omega))

/-- All calls obey the actual SA transition, frame, time and wake contracts. -/
theorem localRun : ACLocalRun GA1 Set.univ blocks run where
  coherent := coherent_blocks
  init _ _ := rfl
  exec i ℓ hc _ := exec ⟨rfl, hc⟩
  frameLaw y _ i ℓ hc := by
    rw [eq_zero y] at hc ⊢
    rcases run.noCall_or_lastCall v0 i with hn | ⟨j, hj, ℓ', hc', hn⟩
    · refine Or.inl ⟨hn, frame {g}, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
      · exact ⟨frameOK_Φ₀, fun _ h => ⟨0, h⟩⟩
      · have ht := tree_noCall (Nat.zero_le i) hn
        simpa only [ht, config] using callOK hc
    · refine Or.inr ⟨j, ℓ', hj, hc', hn, ?_⟩
      have ht := tree_noCall (by omega : j + 1 ≤ i) hn
      have hf := (callAt_iff.1 hc').2.1
      rw [hf, cutFrame_eq, ← ht]
      exact callOK hc
  time_nonneg i := Int.natCast_nonneg _
  time_mono := fun i j hij => by change ((i / 4 : Nat) : Int) ≤ ((j / 4 : Nat) : Int); omega
  awake_of_call _ _ i _ _ := Int.natCast_nonneg _
  restart_of_sleep _ _ _ _ u _ hu _ hn _ := False.elim (hn hu)
  restart_at_wake _ _ u _ hu _ hn _ := False.elim (hn hu)
  sleep_of_restart y _ _ _ hc hr := by
    rw [eq_zero y] at hc
    exact False.elim (call_no_restart hc hr)

theorem accept_iff (i : Nat) (B : Blk sp1.n Unit) :
    run.AcceptAt v0 i B ↔ ∃ s : Nat, 0 < s ∧ i = 16 * s + 2 ∧ B = block s := by
  constructor
  · rintro ⟨ℓ, hc, he⟩
    have h := (callAt_iff.1 hc).1
    rw [he] at h
    have hk : kind i = .block := by cases hk : kind i <;> simp_all [call]
    have hp : (config i).pending = B := by simpa only [call, hk, Option.some.injEq,
      ACInterface.Call.block.injEq] using h
    obtain ⟨s, hs, hi, hb⟩ := block_cut hk
    exact ⟨s, hs, hi, hp ▸ hb⟩
  · rintro ⟨s, hs, rfl, rfl⟩
    exact call_exists (by simp only [call, kind_block_slot hs, block])

theorem proposal_iff {i : Nat} {ℓ : ACLabel GA1} (hc : run.CallAt v0 i ℓ) :
    ℓ.call = .proposal ↔ ∃ s : Nat, 0 < s ∧ i = 16 * s + 1 := by
  have h := (callAt_iff.1 hc).1
  constructor
  · intro hp
    rw [hp] at h
    have hk : kind i = .proposal := by cases hk : kind i <;> simp_all [call]
    obtain ⟨hi, hm⟩ := (kind_proposal i).1 hk
    exact ⟨i / 16, by omega, by omega⟩
  · rintro ⟨s, hs, rfl⟩
    simpa only [call, kind_proposal_slot hs, Option.some.injEq] using h.symm

theorem trivialFrames : TrivialFrames run Set.univ := by
  intro y _ i ℓ hc
  rw [eq_zero y] at hc ⊢
  rw [(callAt_iff.1 hc).2.1, cutFrame_eq]
  refine ⟨rfl, rfl, rfl, ?_⟩
  change (config (i + 1)).tree = insert g {B | ∃ k ≤ i, run.AcceptAt v0 k B}
  rw [tree_history]
  ext B
  simp only [Set.mem_insert_iff, Set.mem_ofPred_eq, accept_iff]
  constructor
  · rintro (rfl | ⟨s, hs, hi, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨16 * s + 2, by omega, s, hs, rfl, rfl⟩
  · rintro (rfl | ⟨k, hk, s, hs, rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨s, hs, by omega, rfl⟩

theorem honestProposal {s : Nat} (hs : 0 < s) : HonestProposal run v0 s (block s) := by
  obtain ⟨ℓ, hc, hcall⟩ := call_exists
    (show call (16 * s + 1) = some .proposal by simp [call, kind_proposal_slot hs])
  have hf : ℓ.frame = frame (config (16 * s + 1)).tree := by
    rw [(callAt_iff.1 hc).2.1]
    simp [cutFrame, kind_proposal_slot hs]
  refine ⟨16 * s + 1, ℓ, (proposalData (16 * s + 1) (config (16 * s + 1))).1,
    (proposalData (16 * s + 1) (config (16 * s + 1))).2, hc, hcall, ?_, ?_, ?_,
    block_slot hs, ?_, ?_, 16 * s + 2, by omega, (accept_iff _ _).2 ⟨s, hs, rfl, rfl⟩, ?_⟩
  · rw [state_eq, hf]
    exact proposal_some _
  · change ((16 * s + 1) / 4 : Nat) = (4 * (s : Int))
    omega
  · rw [block_eq hs]; rfl
  · rw [block_eq hs]; rfl
  · rw [block_eq hs]; rfl
  · change ((16 * s + 2) / 4 : Nat) = (4 * (s : Int))
    omega

theorem pool_mono {i j : Nat} (hij : i ≤ j) (σ : Nat) :
    (config i).state.pool σ ⊆ (config j).state.pool σ := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ h => h
  | succ j _ ih =>
    refine List.Subset.trans ih ?_
    cases hk : kind j <;> simp only [config, next, hk]
    · exact SAPool.acOnTick_pool_mono sp1 v0 _ _ _ σ
    · rw [SAPool.acProposal_pool]
    · exact SAPool.acOnBlock_pool_mono sp1 v0 _ _ _ _ σ
    · exact fun _ h => h

theorem payload_in_pool {s : Nat} (hs : 0 < s) {v : Vote sp1.n}
    (hv : v ∈ blockVotes (block s)) : v ∈ (config (16 * s + 1)).state.pool v.slot := by
  rw [block_eq hs] at hv
  change v ∈ (proposalData (16 * s + 1) (config (16 * s + 1))).2.1 at hv
  rw [proposal_payload] at hv
  simp only [voteViewList, List.mem_filter, SAState.poolAt] at hv
  split_ifs at hv with hn
  · simp at hv
  · have hslot := slotOK (16 * s + 1) _ v hv.1
    rw [hslot]
    exact hv.1

theorem pending_in_pool {i : Nat} (hi : kind i = .block) {v : Vote sp1.n}
    (hv : v ∈ blockVotes (config i).pending) : v ∈ (config i).state.pool v.slot := by
  obtain ⟨s, hs, he, hp⟩ := block_cut hi
  rw [hp] at hv
  exact pool_mono (by omega) _ (payload_in_pool hs hv)

theorem voteAt_of_mem {i : Nat} {c : GA1.Call} {e : Em sp1 Unit}
    (hc : call i = some c)
    (he : e ∈ (GA1.step v0 (config i).state (cutFrame i) (i / 4 : Nat) c).2) :
    VoteAt run v0 i e :=
  ⟨⟨c, cutFrame i, (GA1.step v0 (config i).state (cutFrame i) (i / 4 : Nat) c).2⟩,
    callAt_iff.2 ⟨hc, rfl, rfl⟩, he⟩

/-- A newly held vote is exactly a vote emitted at this cut. -/
theorem pool_step {i σ : Nat} {v : Vote sp1.n} (hv : v ∈ (config (i + 1)).state.pool σ) :
    v ∈ (config i).state.pool σ ∨ ∃ e, VoteAt run v0 i e ∧ e.msg = v := by
  have hσ := slotOK (i + 1) σ v hv
  cases hk : kind i <;> simp only [config, next, hk] at hv
  · rcases SAPool.acOnTick_pool sp1 v0 _ _ _ σ v hv with h | ⟨e, he, hm⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, voteAt_of_mem (c := .tick) (by simp [call, hk])
        (by simpa only [GA1, goldilocksSA, ACInterface.step, cutFrame, hk, reduceCtorEq,
          ite_false] using he), hm⟩
  · rw [SAPool.acProposal_pool] at hv
    exact Or.inl hv
  · rcases SAPool.acOnBlock_pool sp1 v0 _ _ _ _ σ v hv with h | h | ⟨e, he, hm⟩
    · exact Or.inl h
    · exact Or.inl (hσ ▸ pending_in_pool hk h)
    · exact Or.inr ⟨e, voteAt_of_mem (c := .block (config i).pending) (by simp [call, hk])
        (by simpa only [GA1, goldilocksSA, ACInterface.step, cutFrame, hk, ite_true] using he), hm⟩
  · exact Or.inl hv

theorem pool_emitted (i : Nat) (σ : Nat) (v : Vote sp1.n)
    (hv : v ∈ (config i).state.pool σ) : ∃ j < i, ∃ e, VoteAt run v0 j e ∧ e.msg = v := by
  induction i with
  | zero => simp [config, SAState.initial] at hv
  | succ i ih =>
    rcases pool_step hv with hv | ⟨e, he, hm⟩
    · obtain ⟨j, hj, e, he, hm⟩ := ih hv
      exact ⟨j, by omega, e, he, hm⟩
    · exact ⟨i, by omega, e, he, hm⟩

theorem no_message {i : Nat} {ℓ : ACLabel GA1} (hc : run.CallAt v0 i ℓ) (v : Vote sp1.n) :
    ℓ.call ≠ .message v := by
  have h := (callAt_iff.1 hc).1
  cases hk : kind i <;> simp [call, hk] at h <;> simp [← h]

/-- The execution also satisfies honest vote and block provenance. -/
theorem acRun : ACRun (fun _ => v0) run Set.univ blocks where
  stock := rfl
  localRun := localRun
  honest := {
    pool_vote := by
      intro y _ i σ v hv _
      rw [state_eq] at hv
      rw [eq_zero v.val]
      exact pool_emitted i σ v hv
    message_vote := by
      intro y _ i ℓ v hc hm _
      rw [eq_zero y] at hc
      exact False.elim (no_message hc v hm)
    carried_vote := by
      intro y _ i ℓ hc B hB v hv _
      rw [eq_zero y] at hc
      rw [eq_zero v.val]
      rw [(callAt_iff.1 hc).2.1, cutFrame_eq] at hB
      change B ∈ (config (i + 1)).tree at hB
      rw [tree_history] at hB
      rcases hB with rfl | ⟨s, hs, hi, rfl⟩
      · simp [blockVotes, g] at hv
      · obtain ⟨j, hj, e, he, hm⟩ := pool_emitted _ _ _ (payload_in_pool hs hv)
        exact ⟨j, by omega, e, he, hm⟩
    proposer := fun B _ _ => eq_zero B.proposer
    one_block := by
      rintro B C ⟨y, hy, i, ℓ, hc, hB⟩ ⟨z, hz, j, ℓ', hc', hC⟩ _ _ hs
      have hBU := (frameIn_of_callAt localRun hy hc).2 hB
      have hCU := (frameIn_of_callAt localRun hz hc').2 hC
      exact roots_injective hBU hCU ((root_eq_slot hBU).trans (hs.trans (root_eq_slot hCU).symm)) }

theorem sendOrAdmit {i : Nat} {v : Vote sp1.n} (h : run.SendOrAdmit v0 i v) :
    ∃ e, VoteAt run v0 i e ∧ e.msg = v := by
  obtain ⟨ℓ, hc, h | ⟨-, hnot, hhold⟩⟩ := h
  · obtain ⟨e, he, hm⟩ := h
    exact ⟨e, ⟨ℓ, hc, he⟩, hm⟩
  · change v ∉ (run.state v0 i).pool v.slot at hnot
    rw [state_eq] at hnot
    exact (pool_step hhold).resolve_left hnot

theorem lastWake (y : Fin sp1.n) : ∀ i, run.lastWake y i = ⊥
  | 0 => by
    have hn : ¬ run.RestartAt y 0 := by
      rintro ⟨ℓ, hc, hr⟩
      rw [eq_zero y] at hc
      exact call_no_restart hc hr
    simp [ACTrace.lastWake, hn]
  | i + 1 => by
    have hn : ¬ run.RestartAt y (i + 1) := by
      rintro ⟨ℓ, hc, hr⟩
      rw [eq_zero y] at hc
      exact call_no_restart hc hr
    simp [ACTrace.lastWake, hn, lastWake y i]

theorem deadline (y : Fin sp1.n) (i : Nat) (t : Time) : run.deadline y i t = t + 1 := by
  simp only [ACTrace.deadline, lastWake]
  rfl

theorem healthy : HealthyAC run Set.univ blocks 0 := by
  refine ⟨?_, ?_, fun _ _ _ ht => ht, by simp⟩
  · intro x _ i m hm y _ j ℓ hc hd
    rw [eq_zero x] at hm
    rw [eq_zero y] at hc ⊢
    obtain ⟨e, he, rfl⟩ := sendOrAdmit hm
    rw [deadline, max_eq_left (localRun.time_nonneg i)] at hd
    have hij : i ≤ j := by
      change ((i / 4 : Nat) : Int) + 1 ≤ ((j / 4 : Nat) : Int) at hd
      omega
    obtain ⟨ℓ', hc', hem⟩ := he
    refine ⟨i, hij, le_rfl, ⟨ℓ', hc', Or.inr ⟨e, hem, rfl⟩⟩, ?_⟩
    rw [deadline, max_eq_left (localRun.time_nonneg i)]
    change ((i / 4 : Nat) : Int) < ((i / 4 : Nat) : Int) + 1
    omega
  · intro x _ i B hB _ y _ j ℓ hc hd _
    rw [eq_zero x] at hB
    rw [eq_zero y] at hc ⊢
    rw [deadline] at hd
    have hij : i ≤ j := by
      change ((i / 4 : Nat) : Int) + 1 ≤ ((j / 4 : Nat) : Int) at hd
      omega
    refine ⟨i, hij, hB, ?_⟩
    rw [deadline]
    change ((i / 4 : Nat) : Int) < ((i / 4 : Nat) : Int) + 1
    omega

theorem catchAC : CatchAC run Set.univ blocks 0 (2 * sp1.Δ) := by
  intro _ _ i _ _ ht
  change run.time i < max 0 0 at ht
  exact False.elim ((not_lt_of_ge (localRun.time_nonneg i)) (by simpa only [max_self] using ht))

theorem driven : Driven (fun _ => v0) run Set.univ where
  blocks := by
    intro y _ i B hb _
    rw [eq_zero y] at hb
    obtain ⟨s, hs, rfl, rfl⟩ := (accept_iff _ _).1 hb
    obtain ⟨D, hd, hp, hlt⟩ := block_parent hs
    refine ⟨eq_zero _, ?_, D, hp, ?_, ?_⟩
    · change (block s).slot ≤ sp1.slot ((16 * s + 2) / 4 : Nat)
      rw [block_slot hs, slot_time]; omega
    · rw [block_slot hs]; exact hlt
    · rw [tree_history] at hd
      rcases hd with rfl | ⟨r, hr, hi, rfl⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨16 * r + 2, hi, ?_⟩
        rw [eq_zero y]
        exact (accept_iff _ _).2 ⟨r, hr, rfl, rfl⟩
  honest_slot := by
    intro y _ i B hb _ _
    rw [eq_zero y] at hb
    obtain ⟨s, hs, -, rfl⟩ := (accept_iff _ _).1 hb
    rw [block_slot hs]
    exact honestProposal hs
  tick := by
    intro y _ t ht _ _
    rw [eq_zero y]
    obtain ⟨ℓ, hc, hk⟩ := call_exists (show call (4 * t.toNat) = some .tick by
      simp [call, kind])
    refine ⟨4 * t.toNat, ℓ, hc, hk, ?_⟩
    change ((4 * t.toNat / 4 : Nat) : Int) = t
    simp [Int.toNat_of_nonneg ht]
  proposal := by
    intro s hs p _ hp _ _
    rw [hp]
    obtain ⟨ℓ, hc, hk⟩ := call_exists
      (show call (16 * s + 1) = some .proposal by simp [call, kind_proposal_slot hs])
    refine ⟨16 * s + 1, ℓ, hc, hk, ?_, fun _ => ⟨block s, honestProposal hs⟩⟩
    change ((16 * s + 1) / 4 : Nat) = (4 * (s : Int))
    omega
  tick_first := by
    rintro y _ i _ ℓ _ hc _ _ _ ⟨m, hm⟩
    rw [eq_zero y] at hc
    exact False.elim (no_message hc m hm)
  proposal_first := by
    intro y _ i j ℓ ℓ' hc hc' hp ht hm
    rw [eq_zero y] at hc hc'
    obtain ⟨s, hs, rfl⟩ := (proposal_iff hc').1 hp
    rcases hm with ⟨m, hm⟩ | ⟨B, hb⟩
    · exact False.elim (no_message hc m hm)
    · obtain ⟨r, hr, rfl, -⟩ := (accept_iff _ _).1 ⟨ℓ, hc, hb⟩
      change (((16 * r + 2) / 4 : Nat) : Int) = (((16 * s + 1) / 4 : Nat) : Int) at ht
      omega

/-- One infinite live run satisfies all standalone healing premises together. -/
theorem standaloneRun : StandaloneRun run Set.univ blocks (fun _ => v0) 0 :=
  ⟨⟨acRun, driven, healthy, catchAC, rfl⟩, trivialFrames⟩

/-- Every interval of length four from GST contains a positive honest proposer slot. -/
theorem proposerBound : PropAC (sp := sp1) (fun _ => v0) Set.univ 0 4 := by
  intro t ht
  simp only [gbar, max_self] at ht
  have hnat : (t.toNat : Int) = t := Int.toNat_of_nonneg ht
  refine ⟨t.toNat / 4 + 1, by omega, ?_, ?_, Set.mem_univ _⟩
  · change t ≤ 4 * ((t.toNat / 4 + 1 : Nat) : Int)
    dsimp only [Time] at *
    omega
  · change 4 * ((t.toNat / 4 + 1 : Nat) : Int) ≤ t + 4
    dsimp only [Time] at *
    omega

/-- Each positive slot has an actual vote, independently of the healing conclusions. -/
theorem vote_each_slot {s : Nat} (hs : 0 < s) :
    ∃ i e, VoteAt run v0 i e ∧ e.msg.slot = s :=
  honest_votes_in_slot standaloneRun.toHealthyBase
    (by change max 0 0 + 4 * (1 : Int) ≤ 4 * (s : Int); omega) v0 (Set.mem_univ _)

/-- Kind (b): one live execution, all standalone premises, and infinitely many actual duties. -/
theorem live_run_witness : ∃ (tr : SATrace sp1 Unit ro1) (U : Set (Blk sp1.n Unit)),
    StandaloneRun tr Set.univ U (fun _ => v0) 0 ∧
    PropAC (sp := sp1) (fun _ => v0) Set.univ 0 4 ∧
    ∀ s : Nat, 0 < s → ∃ P : Blk sp1.n Unit, HonestProposal tr v0 s P ∧
      ∃ i e, VoteAt tr v0 i e ∧ e.msg.slot = s :=
  ⟨run, blocks, standaloneRun, proposerBound,
    fun s hs => ⟨block s, honestProposal hs, vote_each_slot hs⟩⟩

end Consensus.Goldilocks.SA.Test.SAHealing

end
