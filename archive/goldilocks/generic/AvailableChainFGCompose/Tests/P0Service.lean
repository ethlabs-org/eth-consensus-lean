module
public import AvailableChainFGCompose.Proofs.ServiceTransport
public import AvailableChainFGCompose.Proofs.SourceHead
public import Mathlib.Tactic.NormNum -- shake: keep (axioms)

set_option linter.privateModule false

public section

namespace AvailableChain.FGCompose.Tests.P0Service
open AvailableChain.SimplexFG AvailableChain.KitFG

-- These are inhabited interface models, not protocol execution fixtures.
private def c2Q : Block := .node .genesis 2 ⟨1⟩ 0
private def c2Other : Block := .node (.node .genesis 1 ⟨7⟩ 0) 2 ⟨8⟩ 0
private def c2Opening : Block := .node c2Q 6 ⟨2⟩ 0
private def c2Clock : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6

private def c2Reset : FGResetHistory := ⟨0, 6, 0, 0, 0, c2Q⟩
private def c2Early : FGServicePoint := ⟨c2Reset, 2, c2Q, 8⟩
private def c2Late : FGServicePoint := ⟨c2Reset, 3, c2Q, 12⟩

private theorem c2TwoSeeds : c2Early.reset = c2Late.reset ∧
    c2Early.seedSlot ≠ c2Late.seedSlot ∧ c2Early.serviceStart ≠ c2Late.serviceStart := by
  exact ⟨rfl, by decide, by decide⟩

private theorem c2EarlyStart : FGServiceStartLaws c2Clock 0 30 30
    (· = c2Reset) (fun reset _ seed => reset = c2Reset ∧ seed = c2Q) c2Early := by
  constructor <;> first | rfl | exact ⟨rfl, rfl⟩ | decide

private theorem c2LateStart : FGServiceStartLaws c2Clock 0 30 30
    (· = c2Reset) (fun reset _ seed => reset = c2Reset ∧ seed = c2Q) c2Late := by
  constructor <;> first | rfl | exact ⟨rfl, rfl⟩ | decide

private theorem c2RejectLateOpening : ¬ KernelPrem_W c2Clock 0 100
    c2Late ⟨1⟩ (fun _ => True) 1 1 4 2 := by
  intro h
  have hb := service_start_before_opening c2Clock h
  norm_num [c2Late, c2Clock, FGCompose.P] at hb

private def c2ExactOnly : FGACServiceReads Unit where
  honest _ := True
  proposal s B := s = 2 ∧ B = c2Q
  proposalTime := c2Clock.proposal
  voteTime := c2Clock.vote
  gateTime := c2Clock.gate
  gateLabel q := q * 2
  actionHeadLabel q := q * 2 + 1
  actionTime := c2Clock.action
  proposalScope _ _ := True
  sourceScope _ _ _ := False
  headScope _ _ := True
  gateScope _ _ := True
  actionScope _ _ := False
  headAtLabel _ s := some (if s = 2 then c2Q else .genesis)
  actionHead _ _ := none
  gate _ s := some (some (if s = 2 then c2Q else .genesis))
  source _ _ := none
  parent _ := some .genesis
  gateFloor _ _ := some .genesis
  frame _ _ _ := False
  below := Block.Preceq

private theorem c2ExactPositive : c2ExactOnly.headAtLabel () 2 = some c2Q ∧
    c2ExactOnly.gate () 2 = some (some c2Q) ∧ c2Q ≠ .genesis := by decide

private theorem c2ExactRejectsLater : ¬ FGACServiceLaws c2ExactOnly c2Early 0 100 := by
  intro h
  have hf := h.proposal_later_head 2 c2Q () 3 .genesis
    ⟨rfl, rfl⟩ trivial (by decide) trivial trivial (by decide) (by decide) (by decide)
  exact (by decide : ¬ Block.Preceq c2Q .genesis) hf

private theorem c2DistinctPools : c2ExactOnly.gateLabel 1 = 2 ∧
    c2ExactOnly.actionHeadLabel 1 = 3 ∧
    c2ExactOnly.headAtLabel () (c2ExactOnly.gateLabel 1) ≠
      c2ExactOnly.headAtLabel () (c2ExactOnly.actionHeadLabel 1) := by decide

private theorem c2NextVoteBeforeAction : c2Clock.vote (1 * c2Clock.roundSlots + 1) <
    c2Clock.action 1 := by decide

private theorem c2NestedOptions : (none : Option (Option Block)) ≠ some none := by decide

-- A suffix source and proposal are inhabited. The earlier source is on another branch.
private def c2Suffix : FGACServiceReads Unit where
  honest _ := True
  proposal s B := s = 6 ∧ B = c2Opening
  proposalTime := c2Clock.proposal
  voteTime := c2Clock.vote
  gateTime := c2Clock.gate
  gateLabel q := q * 2
  actionHeadLabel q := q * 2 + 1
  actionTime := c2Clock.action
  proposalScope _ _ := True
  sourceScope _ _ _ := True
  headScope _ _ := True
  gateScope _ _ := True
  actionScope _ _ := True
  headAtLabel _ _ := some c2Q
  actionHead _ _ := some (some c2Q)
  gate _ _ := some (some c2Q)
  source _ r := some (some (if r = 0 then c2Other else c2Q))
  parent _ := some c2Q
  gateFloor _ _ := some .genesis
  frame _ _ _ := True
  below := Block.Preceq

private theorem c2SuffixSource (r : Nat) (h : InSuffix c2Late 100 (c2Suffix.actionTime r)) :
    c2Suffix.source () r = some (some c2Q) := by
  have hr : r ≠ 0 := by
    intro he
    subst r
    have := h.1
    norm_num [c2Late, c2Suffix, c2Clock] at this
  simp [c2Suffix, hr]

private theorem c2SuffixChain : ∀ x y r q C D,
    c2Suffix.honest x → c2Suffix.honest y →
    InSuffix c2Late 100 (c2Suffix.actionTime r) →
    InSuffix c2Late 100 (c2Suffix.actionTime q) →
    c2Suffix.source x r = some (some C) → c2Suffix.source y q = some (some D) →
    Block.Compatible C D := by
  intro x y r q C D _ _ hr hq hc hd
  cases x; cases y
  rw [c2SuffixSource r hr] at hc
  rw [c2SuffixSource q hq] at hd
  cases Option.some.inj (Option.some.inj hc)
  cases Option.some.inj (Option.some.inj hd)
  change (c2Q.preceq c2Q || c2Q.preceq c2Q) = true
  decide

private theorem c2SuffixParent : ∀ x r C s Q,
    c2Suffix.source x r = some (some C) →
    InSuffix c2Late 100 (c2Suffix.actionTime r) → c2Suffix.proposal s Q →
    c2Suffix.below C Q.parent := by
  intro x r C s Q hc hr hQ
  cases x
  rw [c2SuffixSource r hr] at hc
  cases Option.some.inj (Option.some.inj hc)
  obtain ⟨_, rfl⟩ := hQ
  change Block.Preceq c2Q c2Q
  decide

private theorem c2HistoryFailure :
    c2Suffix.source () 0 = some (some c2Other) ∧
    c2Suffix.source () 1 = some (some c2Q) ∧
    InSuffix c2Late 100 (c2Suffix.actionTime 1) ∧
    c2Suffix.proposal 6 c2Opening ∧
    c2Suffix.actionTime 0 < c2Late.serviceStart ∧
    ¬ c2Suffix.below c2Other c2Opening.parent := by
  dsimp [c2Suffix, InSuffix, c2Late, c2Clock]
  decide

-- Height 3 is assigned to the earlier row; the opening has height 2.
-- Thus suffix-only transfer cannot supply the causal row-height cap.
private theorem c2HistoryRowFailure : ¬ (3 : Nat) ≤ 2 := by decide

private noncomputable abbrev c2HistoryProtocol : V2.ProtocolSpecD Unit where
  State := Time
  Label := Nat
  Duty := Nat
  signLabel s := s
  seats _ := 1
  Payload := Block × NamedHeightPair
  Durable := Time
  init := 0
  clock _ t := t
  actTime s := (s : Time)
  duties t := if 0 ≤ t then [t.toNat] else []
  duties_spec s t := by
    split
    · next ht =>
      simp only [List.mem_singleton]
      constructor
      · intro hs
        subst s
        exact Int.toNat_of_nonneg ht
      · intro hs
        subst t
        simp
    · next ht =>
      constructor
      · intro hm
        cases hm
      · intro hs
        exact False.elim (ht (hs ▸ Int.natCast_nonneg s))
  duties_nodup t := by split <;> simp
  act _ s _ := some (c2Opening, if s = 6 then .vote 3 ⟨8⟩ false else .empty)
  gossip _ _ := []
  process st _ := st
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

private noncomputable def c2HistoryInterface : V2.D.Interface c2HistoryProtocol where
  confirmed _ := .genesis
  stable _ := .genesis
  block B := some B.1
  opening _ := True
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * a = 4 * b at h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h

private def c2HistoryEnv : Generic.Env Unit := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private noncomputable def c2HistoryRun : V2.D.Run Unit c2HistoryProtocol where
  honest := {()}
  horizon := 100
  events := [.tick () 6, .tick () 14, .tick () 24]
  seatOf _ _ := ()
  input _ _ := ()
private def c2BadFG : FGBlock (Fin 1) := .node .genesis 1 ⟨8⟩ 0 []
private def c2GoodFG : FGBlock (Fin 1) := .node .genesis 2 ⟨1⟩ 0 []
private noncomputable def c2HistoryCore :
    FGCoreReads c2HistoryProtocol 1 Unit Unit Unit where
  core _ := ⟨(), ⟨{.genesis, c2BadFG, c2GoodFG}, .genesis, .genesis, 0, 3⟩, [], []⟩
  erase B := if B = c2BadFG then c2Other else c2Q
  source t := some (if t = 6 then c2BadFG else c2GoodFG)
  headVote _ _ := c2Q
  finalityHead _ := some c2GoodFG
  proposalFG _ _ := some c2GoodFG
private noncomputable def c2HistoryObs : FGObservationReads c2HistoryCore where
  height B := ⟨.genesis, 0, if B = c2BadFG then 3 else 2, B, ∅, ∅, 0, .genesis⟩
  finality _ := ⟨.genesis, 0⟩
  controls _ := ⟨.genesis, 0, 0, .genesis, false⟩
  viable _ X := X
private def c2HistoryClock : FGTiming := c2Clock

private theorem c2HistoryProposal :
    HonestProposal c2HistoryEnv c2HistoryRun c2HistoryInterface 6 c2Opening := by
  constructor
  · change 0 < (6 : Nat) ∧ () ∈ ({()} : Finset Unit)
    simp
  · refine ⟨⟨.seat 24 0, (c2Opening, .empty)⟩, ?_, rfl⟩
    change ∃ i, c2HistoryRun.events[i]? = some (.tick () 24) ∧
      (⟨.seat 24 0, (c2Opening, .empty)⟩ : c2HistoryProtocol.Object) ∈
        V2.D.Run.emitsAt c2HistoryEnv c2HistoryRun i
    exact ⟨2, rfl, by decide +kernel⟩

private theorem c2HistoryRejectsTransfer :
    ¬ FGHistoricalHighTransfer c2HistoryCore c2HistoryObs c2HistoryClock
      c2HistoryEnv c2HistoryRun c2HistoryInterface c2Late 100 := by
  intro h
  have bad := h () 0 c2BadFG (by simp [c2HistoryRun])
    (by rfl) (by decide +kernel) (by decide)
    6 c2Opening c2HistoryProposal (by decide) (by decide)
  exact (by decide +kernel : ¬ Block.Preceq (c2HistoryCore.erase c2BadFG)
    c2Opening.parent) bad

private theorem c2HistoryHeightWitness :
    (postClock c2HistoryEnv c2HistoryRun () (c2HistoryClock.action 0)).map
      c2HistoryCore.source = some (some c2BadFG) ∧
    c2HistoryClock.action 0 < c2Late.serviceStart ∧
    ¬ (c2HistoryObs.height c2BadFG).h ≤ (c2HistoryObs.height c2GoodFG).h := by
  exact ⟨rfl, by decide, by decide +kernel⟩

-- The suffix laws use the same actual source, reset, timing, and horizon as history.
private theorem c2ActualSuffixSource (r : Nat) (C : FGBlock (Fin 1))
    (ht : InSuffix c2Late 100 (c2HistoryClock.action r))
    (hs : (postClock c2HistoryEnv c2HistoryRun () (c2HistoryClock.action r)).map
      c2HistoryCore.source = some (some C)) : C = c2GoodFG := by
  obtain ⟨nd, hnd, hs⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨i, _, hc⟩ := postClock_tick c2HistoryEnv c2HistoryRun hnd
  have hn : nd ≠ 6 := by
    intro hn
    have ht' : (12 : Time) ≤ c2HistoryClock.action r := ht.1
    have he : c2HistoryClock.action r = 6 := hc.trans hn
    rw [he] at ht'
    contradiction
  change some (if nd = 6 then c2BadFG else c2GoodFG) = some C at hs
  simp only [hn, ↓reduceIte] at hs
  exact (Option.some.inj hs).symm

private theorem c2ActualSuffixChain (r q : Nat) (C D : FGBlock (Fin 1))
    (hr : InSuffix c2Late 100 (c2HistoryClock.action r))
    (hq : InSuffix c2Late 100 (c2HistoryClock.action q))
    (hc : (postClock c2HistoryEnv c2HistoryRun () (c2HistoryClock.action r)).map
      c2HistoryCore.source = some (some C))
    (hd : (postClock c2HistoryEnv c2HistoryRun () (c2HistoryClock.action q)).map
      c2HistoryCore.source = some (some D)) :
    Block.Compatible (c2HistoryCore.erase C) (c2HistoryCore.erase D) := by
  rw [c2ActualSuffixSource r C hr hc, c2ActualSuffixSource q D hq hd]
  change (c2Q.preceq c2Q || c2Q.preceq c2Q) = true
  decide

private theorem c2ActualSuffixParent (r : Nat) (C : FGBlock (Fin 1))
    (hr : InSuffix c2Late 100 (c2HistoryClock.action r))
    (hc : (postClock c2HistoryEnv c2HistoryRun () (c2HistoryClock.action r)).map
      c2HistoryCore.source = some (some C)) :
    Block.Preceq (c2HistoryCore.erase C) c2Opening.parent := by
  rw [c2ActualSuffixSource r C hr hc]
  decide +kernel

private theorem c2ActualSuffixInhabited :
    (postClock c2HistoryEnv c2HistoryRun () (c2HistoryClock.action 1)).map
      c2HistoryCore.source = some (some c2GoodFG) ∧
    InSuffix c2Late 100 (c2HistoryClock.action 1) ∧
    HonestProposal c2HistoryEnv c2HistoryRun c2HistoryInterface 6 c2Opening ∧
    1 * c2HistoryClock.roundSlots + 2 ≤ 6 := by
  exact ⟨rfl, by constructor <;> decide, c2HistoryProposal, by decide⟩

private noncomputable def c2HistoricalRow : c2HistoryProtocol.Object :=
  ⟨.seat 6 0, (c2Opening, .vote 3 c2BadFG.root false)⟩

private noncomputable def c2HistorySafety :
    FGSafetyReads c2HistoryProtocol 1 c2HistoryProtocol.Object where
  proposalErase o := some o.payload.1
  proposalRows _ := []
  encode := id
  decode o := some ⟨0, o.payload.2, none⟩
  decodeObject o := some ⟨0, o.payload.2, none⟩
  fgLabel := 6
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some c2BadFG, ⟨3, c2BadFG.root, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis

-- This is the signed wire emitted at tick 0, with the source read at action 0.
private theorem c2HistoricalRowOrigin :
    HonestRowAt c2HistorySafety c2HistoryEnv c2HistoryRun c2HistoryClock
      0 () 0 c2HistoricalRow ∧
    actionSourceFG c2HistoryCore c2HistoryEnv c2HistoryRun c2HistoryClock () 0 =
      some (some c2BadFG) ∧
    namedEntry c2HistoricalRow.payload.2 =
      some ((c2HistoryObs.height c2BadFG).h, (c2HistoryObs.height c2BadFG).T_h.root) := by
  refine ⟨⟨by simp [c2HistoryRun], rfl, ?_⟩, rfl, ?_⟩
  · decide +kernel
  · decide +kernel

private theorem c2ActualRowCapFailure :
    ∃ h e, HonestRowAt c2HistorySafety c2HistoryEnv c2HistoryRun c2HistoryClock
      0 () 0 c2HistoricalRow ∧
      actionSourceFG c2HistoryCore c2HistoryEnv c2HistoryRun c2HistoryClock () 0 =
        some (some c2BadFG) ∧
      namedEntry c2HistoricalRow.payload.2 = some (h, e) ∧
      h = (c2HistoryObs.height c2BadFG).h ∧
      c2HistoryClock.action 0 < c2Late.serviceStart ∧
      ¬ h ≤ (c2HistoryObs.height c2GoodFG).h := by
  exact ⟨_, _, c2HistoricalRowOrigin.1, c2HistoricalRowOrigin.2.1,
    c2HistoricalRowOrigin.2.2, rfl, by decide, by decide +kernel⟩

-- The PC leaf split has no gap: old shield rows, rows in [d_s,R_s), and suffix rows.
private theorem c2ShieldSplit (shield start t : Time) (_hs : shield ≤ start)
    (old gap suffix : Prop) (hOld : t < shield → old)
    (hGap : shield ≤ t → t < start → gap) (hSuffix : start ≤ t → suffix) :
    old ∨ gap ∨ suffix := by
  by_cases ht : t < shield
  · exact Or.inl (hOld ht)
  · by_cases hu : t < start
    · exact Or.inr (Or.inl (hGap (le_of_not_gt ht) hu))
    · exact Or.inr (Or.inr (hSuffix (le_of_not_gt hu)))

-- Conditional PC leaf test. The selected source determines a nonempty row entry.
-- OldShield and fresh-slot order are leaves; row caps and entry equality are results.
private def c2PCRow (H : FGHeightView (Fin 1)) (C : FGBlock (Fin 1)) : Row (Fin 1) :=
  ⟨0, .vote (H C).h (H C).T_h.root false, none⟩

private structure c2PCLeaves (H : FGHeightView (Fin 1)) (M : Nat)
    (Cstar X A : FGBlock (Fin 1)) (source : Time → Option (FGBlock (Fin 1))) : Prop where
  reset_height : (H Cstar).h = M + 1
  reset_transfer : FGBlock.Preceq Cstar X.parent
  seed_parent : FGBlock.Preceq X A.parent
  parent_path : ∀ B : FGBlock (Fin 1), FGBlock.Preceq B.parent B
  shield : ∀ t C, source t = some C → t < 10 → (H X).h ≤ (H C).h →
    FGBlock.Preceq (H C).T_h X ∨ FGBlock.Preceq X (H C).T_h
  fresh_slot : ∀ t C, source t = some C → t < 10 → (H C).T_h.slot < X.slot
  slot_order : ∀ t C, source t = some C → t < 10 →
    FGBlock.Preceq X (H C).T_h → X.slot ≤ (H C).T_h.slot
  historical_transfer : ∀ t C, source t = some C → 10 ≤ t → t < 30 →
    M + 1 ≤ (H C).h → FGBlock.Preceq C A.parent

private theorem c2PCSemanticCap (Ef : Electorate (Fin 1)) (H : FGHeightView (Fin 1))
    (laws : FGHeightLaws Ef H) (M : Nat) (Cstar X A C : FGBlock (Fin 1))
    (source : Time → Option (FGBlock (Fin 1)))
    (leaves : c2PCLeaves H M Cstar X A source) (t : Time)
    (selected : source t = some C) (earlier : t < 30) :
    namedEntry (c2PCRow H C).height_pair = some ((H C).h, (H C).T_h.root) ∧
    M + 1 ≤ (H A).h ∧ (H C).h ≤ (H A).h ∧
    ((H C).h = (H A).h → (H C).T_h = (H A).T_h) := by
  have hXA := preceq_trans leaves.seed_parent (leaves.parent_path A)
  have hCX := preceq_trans leaves.reset_transfer (leaves.parent_path X)
  have hseed : M + 1 ≤ (H X).h := by
    rw [← leaves.reset_height]
    exact laws.h_mono hCX
  have hopen := laws.h_mono hXA
  refine ⟨rfl, hseed.trans hopen, ?_⟩
  by_cases hold : t < 10
  · by_cases hhigh : (H X).h ≤ (H C).h
    · have hentry : FGBlock.Preceq (H C).T_h X := by
        rcases leaves.shield t C selected hold hhigh with h | h
        · exact h
        · exact False.elim ((Nat.not_le_of_lt (leaves.fresh_slot t C selected hold))
            (leaves.slot_order t C selected hold h))
      have hEA := preceq_trans hentry hXA
      have hcap := laws.h_mono hEA
      rw [laws.entry_same_height] at hcap
      refine ⟨hcap, ?_⟩
      intro heq
      have he := laws.entry_plateau hEA ((laws.entry_same_height C).trans heq)
      simpa only [laws.entry_idem] using he
    · exact ⟨(le_of_not_ge hhigh).trans hopen, fun heq =>
        False.elim (hhigh (heq.symm ▸ hopen))⟩
  · by_cases hhigh : M + 1 ≤ (H C).h
    · have hCA := preceq_trans
        (leaves.historical_transfer t C selected (le_of_not_gt hold) earlier hhigh)
        (leaves.parent_path A)
      exact ⟨laws.h_mono hCA, laws.entry_plateau hCA⟩
    · have hlt := (Nat.lt_of_not_ge hhigh).trans_le (hseed.trans hopen)
      exact ⟨hlt.le, fun heq => False.elim ((Nat.ne_of_lt hlt) heq)⟩

private def c2PCSources (old boundary gap suffix : FGBlock (Fin 1))
    (t : Time) : Option (FGBlock (Fin 1)) :=
  some (if t = 9 then old else if t = 10 then boundary else if t = 15 then gap else suffix)

-- Four nonempty source/row cases share the reset, seed, opening, and horizon.
-- In particular the boundary and gap sources are high, before the start at 20.
private theorem c2PCIntervals (Ef : Electorate (Fin 1)) (H : FGHeightView (Fin 1))
    (laws : FGHeightLaws Ef H) (M : Nat) (Cstar X A old boundary gap suffix : FGBlock (Fin 1))
    (leaves : c2PCLeaves H M Cstar X A (c2PCSources old boundary gap suffix))
    (high : ∀ C ∈ [boundary, gap, suffix], M + 1 ≤ (H C).h) :
    (∀ C ∈ [boundary, gap, suffix], M + 1 ≤ (H C).h) ∧
    ∀ t ∈ ([9, 10, 15, 25] : List Time), ∃ C,
      c2PCSources old boundary gap suffix t = some C ∧
      namedEntry (c2PCRow H C).height_pair = some ((H C).h, (H C).T_h.root) ∧
      M + 1 ≤ (H A).h ∧ (H C).h ≤ (H A).h ∧
      ((H C).h = (H A).h → (H C).T_h = (H A).T_h) := by
  refine ⟨high, ?_⟩
  intro t ht
  let C := if t = 9 then old else if t = 10 then boundary else if t = 15 then gap else suffix
  refine ⟨C, rfl, c2PCSemanticCap Ef H laws M Cstar X A C
    (c2PCSources old boundary gap suffix) leaves t rfl ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> norm_num

private theorem c2OldShieldRowCap : (9 : Time) < 10 ∧ (9 : Time) < 20 := by norm_num
private theorem c2AtShieldRow : (10 : Time) ≤ 10 ∧ (10 : Time) < 20 := by norm_num
private theorem c2GapRowCap : (10 : Time) ≤ 15 ∧ (15 : Time) < 20 := by norm_num
private theorem c2SuffixRowCap : (20 : Time) ≤ 25 ∧ (25 : Time) < 30 := by norm_num

#print axioms c2HistoricalRowOrigin
#print axioms c2PCSemanticCap
#print axioms c2PCIntervals
#print axioms c2AtShieldRow

#print axioms c2TwoSeeds
#print axioms c2EarlyStart
#print axioms c2LateStart
#print axioms c2RejectLateOpening
#print axioms c2ExactPositive
#print axioms c2ExactRejectsLater
#print axioms c2DistinctPools
#print axioms c2NextVoteBeforeAction
#print axioms c2NestedOptions
#print axioms c2SuffixChain
#print axioms c2SuffixParent
#print axioms c2HistoryFailure
#print axioms c2HistoryRowFailure
#print axioms c2HistoryRejectsTransfer
#print axioms c2HistoryHeightWitness
#print axioms c2ShieldSplit
#print axioms c2GapRowCap
#print axioms c2OldShieldRowCap
#print axioms c2SuffixRowCap
#print axioms c2ActualSuffixChain
#print axioms c2ActualSuffixParent
#print axioms c2ActualSuffixInhabited
#print axioms c2ActualRowCapFailure

end AvailableChain.FGCompose.Tests.P0Service
end
