module
public import AvailableChainFGCompose.Statements.FinalityKernel
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (causal laws)
public import AvailableChainFGCompose.Proofs.Finality.RecordInv -- shake: keep (client laws)
public import AvailableChainFGCompose.Proofs.Timing -- shake: keep (clock tactic context)
public import AvailableChainFGCompose.Proofs.Healing.ResetCut -- shake: keep (clock laws)

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The supplied clock places the action six delays after its opening. -/
theorem kmid_actionTime_eq (T : FGTiming) (L : FGTimingLaws T) (r : Nat) :
    T.action r = 4 * T.delta * ((r * T.roundSlots : Nat) : Time) + 6 * T.delta := by
  rw [L.action_eq, L.gate_eq, L.proposal_eq]
  ring

/-- Positive slot duration orders the actual actions. -/
theorem kmid_action_strictMono (T : FGTiming) (L : FGTimingLaws T) :
    StrictMono T.action := by
  intro m n hmn
  rw [kmid_actionTime_eq T L, kmid_actionTime_eq T L]
  have hR : 0 < T.roundSlots := by have := L.rounds; omega
  have hΔ : 0 < 4 * T.delta := mul_pos (by decide) L.delta_pos
  have hmul := Nat.mul_lt_mul_of_pos_right hmn hR
  exact Int.add_lt_add_right (mul_lt_mul_of_pos_left (Int.ofNat_lt.mpr hmul) hΔ) _

/-- The slot clock preserves a non-strict slot bound. -/
theorem kmid_slot_scale_le (T : FGTiming) (L : FGTimingLaws T)
    {a b : Nat} (h : a ≤ b) : 4 * T.delta * (a : Time) ≤ 4 * T.delta * (b : Time) := by
  have hd := L.delta_pos
  have hab : (a : Time) ≤ b := by exact_mod_cast h
  nlinarith

/-- The slot clock preserves a strict slot bound. -/
theorem kmid_slot_scale_lt (T : FGTiming) (L : FGTimingLaws T)
    {a b : Nat} (h : a < b) : 4 * T.delta * (a : Time) < 4 * T.delta * (b : Time) := by
  have hd := L.delta_pos
  have hab : (a : Time) < b := by exact_mod_cast h
  nlinarith

/-- The defined integer ceiling covers the row delay. -/
theorem kmid_kappa_cover (T : FGTiming) (L : FGTimingLaws T)
    (ΔF : Time) (hF : 0 ≤ ΔF) :
    6 * T.delta + ΔF ≤ 4 * T.delta * (kappaF T ΔF : Time) := by
  have hd : 0 < 4 * T.delta := by have := L.delta_pos; linarith
  have hn : 0 ≤ 6 * T.delta + ΔF + 4 * T.delta - 1 := by
    have hd1 : (1 : Time) ≤ T.delta := L.delta_pos
    linarith
  delta kappaF
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)]
  have hhi := Int.lt_ediv_add_one_mul_self (6 * T.delta + ΔF + 4 * T.delta - 1) hd
  nlinarith

/-- A round period is the clock of its first slot. -/
theorem kmid_period_eq (T : FGTiming) (r : Nat) :
    (r : Time) * FGCompose.P T = 4 * T.delta * ((r * T.roundSlots : Nat) : Time) := by
  unfold FGCompose.P
  push_cast
  ring

/-- An erased path lifts through the supplied, proved erasure equation. -/
theorem kmid_lift_preceq {n : Nat} (erase : FGBlock (Fin n) → Block)
    (reflect : ∀ A B, Block.Preceq (erase A) (erase B) → FGBlock.Preceq A B)
    {A B : FGBlock (Fin n)} (h : Block.Preceq (erase A) (erase B)) : FGBlock.Preceq A B :=
  reflect A B h

/-- The parent belongs to the same FG path. -/
theorem kmid_parent_preceq {n : Nat} (B : FGBlock (Fin n)) : FGBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact preceq_refl _
  | node P s root x rs => exact preceq_parent_node P s root x rs

/-- Slots are monotone on an actual increasing parent path. -/
theorem kmid_slot_le_of_preceq {n : Nat} {W X : FGBlock (Fin n)} (hX : SlotChain X)
    (hW : FGBlock.Preceq W X) : W.slot ≤ X.slot := by
  induction X with
  | genesis => rw [preceq_genesis.mp hW]
  | node P s root x rs ih =>
    by_cases he : W = .node P s root x rs
    · rw [he]
    · have hWP := preceq_parent_of_preceq_node hW he
      have hP : SlotChain P := fun Z hZ hg =>
        hX Z (preceq_trans hZ (preceq_parent_node P s root x rs)) hg
      have hlt := hX (.node P s root x rs) (preceq_refl _) (by intro h; cases h)
      exact (ih hP hWP).trans (le_of_lt hlt)

/-- A strict ancestor has a smaller slot. -/
theorem kmid_slot_lt_of_strict {n : Nat} {W X : FGBlock (Fin n)} (hX : SlotChain X)
    (hW : FGBlock.Preceq W X) (hne : W ≠ X) : W.slot < X.slot := by
  cases X with
  | genesis => exact (hne (preceq_genesis.mp hW)).elim
  | node P s root x rs =>
    have hWP := preceq_parent_of_preceq_node hW hne
    have hP : SlotChain P := fun Z hZ hg =>
      hX Z (preceq_trans hZ (preceq_parent_node P s root x rs)) hg
    have hlt := hX (.node P s root x rs) (preceq_refl _) (by intro h; cases h)
    exact (kmid_slot_le_of_preceq hP hWP).trans_lt hlt


/-- Kernel bounds use the same service start and the original row-delay budget. -/
theorem kmid_kernel_bounds (T : FGTiming) (L : FGTimingLaws T)
    {ΔF horizon gst : Time} {sp : FGServicePoint} {pt : KernelPt}
    (bound : LivenessBoundW T ΔF)
    (start : sp.serviceStart ≤ (pt.r : Time) * FGCompose.P T)
    (deadline : kernelDeadlineW T ΔF (pt.r + 2) ≤ horizon)
    (hF : 0 ≤ ΔF) (hreset : T.proposal (sp.reset.sStar + 2) ≤ sp.serviceStart)
    (hGST : gst ≤ sp.serviceStart) :
    0 ≤ ΔF ∧ 2 ≤ kappaF T ΔF ∧ kappaF T ΔF ≤ T.roundSlots ∧ 2 ≤ T.roundSlots ∧
      sp.reset.sStar + 2 ≤ pt.r * T.roundSlots ∧
      gst ≤ T.proposal (pt.r * T.roundSlots) ∧ T.action (pt.r + 2) ≤ horizon := by
  have hd := L.delta_pos
  have hcover := kmid_kappa_cover T L ΔF hF
  have hk : 2 ≤ kappaF T ΔF := by
    by_contra hn
    have hcast : (kappaF T ΔF : Time) ≤ 1 := by exact_mod_cast (show _ ≤ 1 by omega)
    nlinarith
  rw [kmid_period_eq] at start
  have hstart : sp.serviceStart ≤ T.proposal (pt.r * T.roundSlots) := by
    rw [L.proposal_eq]
    nlinarith [start]
  refine ⟨hF, hk, bound.kappa_le_R, L.rounds, ?_, hGST.trans hstart, ?_⟩
  · by_contra hn
    have hlt := kmid_slot_scale_lt T L (Nat.lt_of_not_ge hn)
    rw [L.proposal_eq] at hreset hstart
    nlinarith
  · have hhor := deadline
    unfold kernelDeadlineW betaF at hhor
    rw [kmid_period_eq] at hhor
    rw [kmid_actionTime_eq T L]
    have hcast : (2 : Time) ≤ kappaF T ΔF := by exact_mod_cast hk
    nlinarith

/-- A window slot remains inside the finite run horizon. -/
theorem kmid_slot_horizon (T : FGTiming) (L : FGTimingLaws T) {q s : Nat} {horizon : Time}
    (ha : T.action (q + 2) ≤ horizon) (hs : s ≤ (q + 2) * T.roundSlots) :
    T.proposal s ≤ horizon ∧ T.vote s ≤ horizon ∧ T.gate s ≤ horizon := by
  have hle := kmid_slot_scale_le T L hs
  rw [kmid_actionTime_eq T L] at ha
  rw [L.vote_eq, L.gate_eq, L.proposal_eq]
  have hd := L.delta_pos
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The opening GST bound extends to every later window slot. -/
theorem kmid_slot_gst (T : FGTiming) (L : FGTimingLaws T) {q s : Nat} {gst : Time}
    (hG : gst ≤ T.proposal (q * T.roundSlots)) (hs : q * T.roundSlots ≤ s) :
    gst ≤ T.proposal s := by
  have hle := kmid_slot_scale_le T L hs
  rw [L.proposal_eq] at hG ⊢
  nlinarith

/-- A label vote is strictly before the corresponding action. -/
theorem kmid_vote_lt_action (T : FGTiming) (L : FGTimingLaws T)
    {s : Slot} {r : Nat} (h : s ≤ r * T.roundSlots) : T.vote s < T.action r := by
  have hle := kmid_slot_scale_le T L h
  rw [L.vote_eq, L.proposal_eq, kmid_actionTime_eq T L]
  have hd := L.delta_pos
  nlinarith

/-- A proposal read is no later than its covering action. -/
theorem kmid_proposal_le_action (T : FGTiming) (L : FGTimingLaws T)
    {s : Slot} {r : Nat} (h : s ≤ r * T.roundSlots) : T.proposal s ≤ T.action r := by
  have hle := kmid_slot_scale_le T L h
  rw [L.proposal_eq, kmid_actionTime_eq T L]
  have hd := L.delta_pos
  nlinarith

/-- The same κ bound covers row delivery before the selected carrier. -/
theorem kmid_batch_horizon (T : FGTiming) (L : FGTimingLaws T) {ΔF gst horizon : Time}
    (hF : 0 ≤ ΔF) {q r s : Nat} (ha : T.action (q + 2) ≤ horizon)
    (hG : gst ≤ T.action r) (hs : r * T.roundSlots + kappaF T ΔF ≤ s)
    (hs' : s ≤ (q + 2) * T.roundSlots) :
    max (T.action r) gst + ΔF ≤ T.proposal s ∧ T.proposal s ≤ horizon := by
  refine ⟨?_, (kmid_slot_horizon T L ha hs').1⟩
  rw [max_eq_left hG, kmid_actionTime_eq T L, L.proposal_eq]
  have hcov := kmid_kappa_cover T L ΔF hF
  have hle := kmid_slot_scale_le T L hs
  push_cast at hle ⊢
  nlinarith

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

/-- Every actual row retains its action tick. -/
theorem kmid_event_time {j r : Nat} {z : V} {a : Wire}
    (hj : HonestRowAt S E rho T j z r a) : eventTime rho j = some (T.action r) := by
  unfold eventTime
  rw [hj.2.1]
  rfl

/-- The selected named source fixes the emitted row height, for either sign. -/
theorem kmid_row_source_height (hnames : HighRecordNames R S O T E rho D)
    {j : Nat} {x : V} {r : Nat} {a : Wire} {h : Nat}
    (ha : HonestRowAt S E rho T j x r a) (hh : historyRowHeight S D a = some h) :
    ∃ C, actionSourceFG R E rho T x r = some (some C) ∧ h = (O.height C).h := by
  unfold historyRowHeight at hh
  cases hp : D.heightPair a with
  | empty => simp only [hp] at hh; contradiction
  | vote y U timeout =>
    rw [hp] at hh
    obtain rfl := Option.some.inj hh
    obtain ⟨C, hC, he⟩ := hnames j x r a (y, U) ha (by rw [hp]; rfl)
    exact ⟨C, hC, congrArg Prod.fst he⟩

/-- Equal action sources give the same row height. -/
theorem kmid_rows_at_source (hnames : HighRecordNames R S O T E rho D)
    (r : Nat) (X : FGBlock (Fin n))
    (hsrc : ∀ x ∈ rho.honest, actionSourceFG R E rho T x r = some (some X)) :
    ∀ j x a h, HonestRowAt S E rho T j x r a → historyRowHeight S D a = some h →
      h = (O.height X).h := by
  intro j x a h ha hh
  obtain ⟨C, hC, he⟩ := kmid_row_source_height R S O T E rho D hnames ha hh
  obtain rfl := Option.some.inj (Option.some.inj (hC.symm.trans (hsrc x ha.1)))
  exact he

include L in
/-- Earlier high sources transfer without a service-start lower bound. -/
theorem kmid_rows_below_opening (sp : FGServicePoint) (horizon : Time)
    (history : FGHistoricalHighTransfer R O T E rho I sp horizon)
    (hnames : HighRecordNames R S O T E rho D)
    (height : FGHeightLaws Ef O.height)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (q : Nat) (A₀ : FGBlock (Fin n))
    (hA : HonestProposal E rho I (q * T.roundSlots) (R.erase A₀))
    (hhor : T.action q ≤ horizon) (hprop : T.proposal (q * T.roundSlots) ≤ horizon)
    (hhigh : sp.reset.M + 1 ≤ (O.height A₀).h) :
    ∀ j x r a h, r < q → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h ≤ (O.height A₀).h := by
  intro j x r a h hr ha hh
  obtain ⟨C, hC, rfl⟩ := kmid_row_source_height R S O T E rho D hnames ha hh
  by_cases highC : sp.reset.M + 1 ≤ (O.height C).h
  · have hgap : r * T.roundSlots + 2 ≤ q * T.roundSlots := by
      have hh := Nat.mul_le_mul_right T.roundSlots (Nat.succ_le_of_lt hr)
      have hR := L.rounds
      rw [Nat.succ_mul] at hh
      omega
    have hp := history x r C ha.1 hC highC
      (((kmid_action_strictMono T L).monotone hr.le).trans hhor)
      _ _ hA hprop hgap
    rw [← parent] at hp
    exact (height.h_mono (reflect C A₀.parent hp)).trans
      (height.h_mono (kmid_parent_preceq A₀))
  · omega

/-- Seed height and its actual parent path give the opening height. -/
theorem middle_seed_opening_height (sp : FGServicePoint) (X A₀ : FGBlock (Fin n))
    (b : Nat) (cutoff : Time) (seed : HighRecordSeedLeaves R S O T E rho D sp X b cutoff)
    (height : FGHeightLaws Ef O.height)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (seed_parent : Block.Preceq (R.erase X) (R.erase A₀).parent) :
    sp.reset.M + 1 ≤ b ∧ b ≤ (O.height A₀).h := by
  rw [← parent] at seed_parent
  refine ⟨seed.2.2.1, ?_⟩
  rw [← seed.2.1]
  exact (height.h_mono (reflect X A₀.parent seed_parent)).trans
    (height.h_mono (kmid_parent_preceq A₀))

include L in
/-- The shield stops at its cutoff. All rows from that cutoff use historical transfer. -/
theorem middle_shield_rows_below_opening (sp : FGServicePoint) (horizon : Time)
    (X A₀ : FGBlock (Fin n)) (b : Nat) (cutoff : Time)
    (seed : HighRecordSeedLeaves R S O T E rho D sp X b cutoff)
    (seed_parent : Block.Preceq (R.erase X) (R.erase A₀).parent)
    (history : FGHistoricalHighTransfer R O T E rho I sp horizon)
    (hnames : HighRecordNames R S O T E rho D)
    (height : FGHeightLaws Ef O.height)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (q : Nat) (hA : HonestProposal E rho I (q * T.roundSlots) (R.erase A₀))
    (hhor : T.action q ≤ horizon) (hprop : T.proposal (q * T.roundSlots) ≤ horizon) :
    sp.reset.M + 1 ≤ b ∧ b ≤ (O.height A₀).h ∧
    ∀ j x r a h, r < q → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h ≤ (O.height A₀).h := by
  obtain ⟨hhigh, hcap⟩ := middle_seed_opening_height R S O T E rho D Ef
    sp X A₀ b cutoff seed height reflect parent seed_parent
  refine ⟨hhigh, hcap, ?_⟩
  intro j x r a h hr ha hh
  by_cases hold : T.action r < cutoff
  · unfold historyRowHeight at hh
    cases hp : D.heightPair a with
    | empty => simp only [hp] at hh; contradiction
    | vote y U timeout =>
      rw [hp] at hh
      obtain rfl := Option.some.inj hh
      exact ((seed.2.2.2.2 j x r a y U timeout ha hold hp).1).trans hcap
  · exact kmid_rows_below_opening R S O T L E rho I D Ef sp horizon history hnames
      height reflect parent q A₀ hA hhor hprop (hhigh.trans hcap) j x r a h hr ha hh

/-- A decoded matching height retains the exact signed row height. -/
theorem kmid_matching_height {u : Row (Fin n)} {a : Wire} {y : Nat} {root : BlockId}
    (ha : S.decode a = some u) (hm : u.height_pair.matchesEntry y root = true) :
    historyRowHeight S D a = some y := by
  unfold historyRowHeight
  rw [D.decode_height a u ha]
  cases hp : u.height_pair with
  | empty => simp only [hp, NamedHeightPair.matchesEntry] at hm; contradiction
  | vote h U timeout =>
    have hh : h = y := by
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      exact hm.1
    exact congrArg some hh

/-- A seat outside the actual faulty-seat set has an honest holder. -/
theorem kmid_honest_seat (u : Row (Fin n))
    (hf : u.signer ∉ historyFaulty S rho) : safetyHolder S rho u.signer ∈ rho.honest := by
  classical
  delta historyFaulty at hf
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    not_not] using hf

omit [DecidableEq V] in
/-- Event phases put every tick at the cut before its read-phase endpoint. -/
theorem kmid_tick_lt_afterTicks (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t' t : Time} (hi : rho.events[i]? = some (.tick v t')) (ht : t' ≤ t) :
    i < afterTicksIdx rho t := tick_lt_afterTicks E rho hs hi ht

/-- Sources remain held before the clock reads their own action. -/
theorem kmid_source_held_at_tick (CL : FGCoreLaws R) (hs : V2.D.ScheduleWellFormed E rho)
    {x : V} {r : Nat} {C : FGBlock (Fin n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG R E rho T x r = some (some C)) :
    ∃ i, rho.events[i]? = some (.tick x (T.action r)) ∧
      i < afterTicksIdx rho (T.action r) ∧ HeldAt R E rho i x C := by
  unfold actionSourceFG postClock preTick at hsrc
  cases hi : V2.D.Run.tickIdx? rho x (T.action r) with
  | none => simp only [hi, Option.map_none] at hsrc; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hsrc
    have hj := V2.D.Run.tickIdx?_spec hi
    have hm := CL.source_mem _ C hsrc
    rw [CL.clock_fg] at hm
    exact ⟨i, hj, kmid_tick_lt_afterTicks E rho hs hj le_rfl, hx, hm⟩

/-- An actual HEAD read supplies every raw carrier before a later cut. -/
theorem kmid_chainRows_of_head (CL : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (hs : V2.D.ScheduleWellFormed E rho) (restore : FGTreeRestoreLaws R)
    {v : Slot} {X : FGBlock (Fin n)} (x : V) (hx : x ∈ rho.honest)
    (hh : headAtLabel R E rho T x v = some (R.erase X))
    (cut : Time) (hcut : T.vote v < cut) : ChainRowsBefore R E rho X cut :=
  chainRows_of_head_all R E rho CL HL hs restore hx hh cut hcut

/-- The same read remains held through every later cut, including restarts. -/
theorem kmid_head_held_from (CL : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (hs : V2.D.ScheduleWellFormed E rho) (keep : FGTreeKeepLaws R)
    {v : Slot} {X : FGBlock (Fin n)} (x : V)
    (hh : headAtLabel R E rho T x v = some (R.erase X))
    (k : Nat) (t : Time) (ht : T.vote v ≤ t) (hk : afterTicksIdx rho t ≤ k) :
    X ∈ (R.core (V2.D.Run.stateBefore E rho k x)).fg.TF :=
  head_held_from_all R E rho CL HL hs keep hh k t ht hk

/-- The semantic source equation and injective erasure identify the full FG body. -/
theorem kmid_source_of_exact (CL : FGCoreLaws R)
    {x : V} {r : Nat} {X : FGBlock (Fin n)}
    (hex : (actionSourceFG R E rho T x r).map (Option.map R.erase) =
      some (some (R.erase X))) :
    actionSourceFG R E rho T x r = some (some X) := by
  cases hsrc : actionSourceFG R E rho T x r with
  | none => simp only [hsrc, Option.map_none] at hex; contradiction
  | some v =>
    cases v with
    | none =>
      simp only [hsrc, Option.map_some, Option.map_none, Option.some.injEq] at hex
      cases hex
    | some C =>
      simp only [hsrc, Option.map_some, Option.some.injEq] at hex
      rw [CL.erase_inj hex]

omit [DecidableEq V] in
/-- Deliveries strictly before the read-phase cut have a strictly earlier time. -/
theorem kmid_delivery_before_afterTicks (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {t t' : Time} {x : V} {o : P.Object}
    (hk : k < afterTicksIdx rho t) (he : rho.events[k]? = some (.deliver x o t')) :
    t' < t := by
  have hf := V2.D.Engine.filter_eq_take hs (cutPred t) (fun e f hk hf =>
    decide_eq_true (hk.trans (of_decide_eq_true hf)))
  have hm : (V2.Event.deliver x o t' : V2.Event V P.Object) ∈
      rho.events.filter (cutPred t) := by
    rw [hf]
    apply List.mem_of_getElem? (i := k)
    change (rho.events.take (afterTicksIdx rho t))[k]? = some _
    rw [List.getElem?_take_of_lt hk]
    exact he
  have hkey : toLex (t', (2 : Nat)) ≤ toLex (t, (1 : Nat)) :=
    of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨_, h⟩
  · exact h
  · omega

variable (hc : FGCertificateLaws Ef O.height O.finality)
variable (horigin : RawHistoryOrigin R S E rho T D)

include hc horigin in
/-- Actual signed origins rule out a crossing above the earlier row cap. -/
theorem kmid_held_height_le
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt S E rho T j z r a →
      historyRowHeight S D a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin n)) (hheld : HeldAt R E rho i x B)
    (hbefore : ∀ k o t, k < i → rho.events[k]? = some (.deliver x o t) → t < cut) :
    (O.height B).h ≤ m + 1 := by
  by_contra hn
  obtain ⟨C, _hCB, _hC, Q, hQ, hw⟩ := hc.height.height_crossing
    B (m + 1) (by simp only [Height]; omega) (by simp only [Height] at *; omega)
  obtain ⟨seat, hseat, hf⟩ := honest_in_quorum Ef (historyFaulty S rho) hQ hweight
  obtain ⟨W, u, hWB, hu, hsign, hm⟩ := hw seat hseat
  have hhonest := kmid_honest_seat S rho u (hsign ▸ hf)
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ :=
    horigin i x B hheld u (mem_chainRows_of_carrier hWB hu)
  obtain ⟨hb, hrt⟩ := he _ ⟨u.signer, har, rfl⟩ hhonest
  obtain ⟨j, _hji, hj⟩ := hb
  have bound := hrows j _ r a (m + 1) (T.action r) hj
    (kmid_matching_height S D ha hm) (kmid_event_time S T E rho hj)
    (hrt.trans_lt (hbefore k o t hki hk))
  omega

include hc horigin in
/-- The cap includes every read up to the cut, but excludes same-time deliveries. -/
theorem kmid_held_cap_afterTicks (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt S E rho T j z r a →
      historyRowHeight S D a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin n))
    (hcut : i ≤ afterTicksIdx rho cut) (hheld : HeldAt R E rho i x B) :
    (O.height B).h ≤ m + 1 :=
  kmid_held_height_le R S O T E rho D Ef hc horigin hweight m cut hrows i x B hheld
    (fun _ _ _ hki hk => kmid_delivery_before_afterTicks E rho hs (hki.trans_le hcut) hk)

include hc horigin in
/-- A positive finality certificate also needs an earlier honest signed row. -/
theorem kmid_held_finality_afterTicks (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q) (y : Nat) (cut : Time) (hy : 0 < y)
    (hrows : ∀ j z r a f t, HonestRowAt S E rho T j z r a →
      historyFinHeight S D a = some f → eventTime rho j = some t → t < cut → f < y)
    (i : Nat) (x : V) (W : FGBlock (Fin n))
    (hcut : i ≤ afterTicksIdx rho cut) (hheld : HeldAt R E rho i x W) :
    (O.finality W).h_F < y := by
  by_contra hn
  have hF : y ≤ (O.finality W).h_F := Nat.le_of_not_gt hn
  let origin := fun u : Row (Fin n) => ∃ j z r a t,
    HonestRowAt S E rho T j z r a ∧ S.decode a = some u ∧
      eventTime rho j = some t ∧ t < cut
  obtain ⟨u, _hu, _hf, ho, hp⟩ := finalityCap_row_of_certificate Ef O.height O.finality hc
    (historyFaulty S rho) hweight y W origin (by
      intro u hu hf
      have hhonest := kmid_honest_seat S rho u hf
      obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ := horigin i x W hheld u hu
      obtain ⟨hb, hrt⟩ := he _ ⟨u.signer, har, rfl⟩ hhonest
      obtain ⟨j, _hji, hj⟩ := hb
      exact ⟨j, _, r, a, T.action r, hj, ha, kmid_event_time S T E rho hj,
        hrt.trans_lt (kmid_delivery_before_afterTicks E rho hs (hki.trans_le hcut) hk)⟩) hy hF
  obtain ⟨j, z, r, a, t, hj, ha, ht, hlt⟩ := ho
  have hfin : historyFinHeight S D a = some (O.finality W).h_F := by
    unfold historyFinHeight
    rw [D.decode_finality a u ha, hp]
    rfl
  exact (Nat.not_lt.mpr hF) (hrows j z r a _ t hj hfin ht hlt)

/-- The emitted wire and actual client effect share the same action index. -/
theorem kmid_row_action (cfg : FGConfig)
    (emission : HighRecordEmission S T E rho Ef cfg)
    {j : Nat} {x : V} {r : Nat} {a : Wire} {u : Row (Fin n)}
    (ha : HonestRowAt S E rho T j x r a) (decode : S.decode a = some u) :
    rho.events[j]? = some (.tick x (T.action r)) ∧
      (createRowOnce Ef cfg (S.record (V2.D.Run.stateBefore E rho j x)) u.signer
        (S.inputs (P.clock (V2.D.Run.stateBefore E rho j x) (T.action r))).1
        (S.inputs (P.clock (V2.D.Run.stateBefore E rho j x) (T.action r))).2).1 = some u :=
  ⟨ha.2.1, emission j x r a u ha decode⟩

/-- The actual client filters a finality pair strictly below the height pair. -/
theorem kmid_row_fin_lt (cfg : FGConfig)
    (emission : HighRecordEmission S T E rho Ef cfg)
    (decoded : ∀ j x r a, HonestRowAt S E rho T j x r a → ∃ u, S.decode a = some u)
    {j : Nat} {x : V} {r : Nat} {a : Wire} (ha : HonestRowAt S E rho T j x r a) :
    ∃ h, historyRowHeight S D a = some h ∧ ∀ f, historyFinHeight S D a = some f → f < h := by
  obtain ⟨u, hu⟩ := decoded j x r a ha
  have he := (kmid_row_action S T E rho Ef cfg emission ha hu).2
  obtain ⟨h, root, tm, _hp, hroweq, _, _, _⟩ := createRowOnce_released Ef cfg _ _ _ _ he
  refine ⟨h, ?_, ?_⟩
  · unfold historyRowHeight
    rw [D.decode_height a u hu, hroweq]
  · intro f hf
    unfold historyFinHeight at hf
    rw [D.decode_finality a u hu, hroweq] at hf
    change ((finality_pair _ _).filter (fun p => decide (p.height < h))).map (·.height) =
      some f at hf
    obtain ⟨fp, hfp, hfe⟩ := Option.map_eq_some_iff.mp hf
    have hlt := of_decide_eq_true (Option.filter_eq_some_iff.mp hfp).2
    rw [← hfe]
    exact hlt

include L in
/-- All rows through Q give the strict next-action cut. -/
theorem kmid_rows_cut (m Q : Nat)
    (hrow : ∀ j x r a h, r ≤ Q → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h ≤ m) :
    (∀ j x r a h t, HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → m + 1 ≤ h →
      eventTime rho j = some t → T.action (Q + 1) ≤ t) ∧
    (∀ j z r a h t, HonestRowAt S E rho T j z r a →
      historyRowHeight S D a = some h → eventTime rho j = some t →
      t < T.action (Q + 1) → h ≤ m) := by
  have key : ∀ j x r a h t, HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → eventTime rho j = some t →
      t < T.action (Q + 1) → h ≤ m := by
    intro j x r a h t ha hh ht hlt
    have he := Option.some.inj ((kmid_event_time S T E rho ha).symm.trans ht)
    have hr := (kmid_action_strictMono T L).lt_iff_lt.mp (he ▸ hlt)
    exact hrow j x r a h (by omega) ha hh
  refine ⟨?_, key⟩
  intro j x r a h t ha hh hm ht
  by_contra hn
  have := key j x r a h t ha hh ht (lt_of_not_ge hn)
  omega

include L in
/-- The client height filter turns the same row cut into a finality cut. -/
theorem kmid_fin_cut (cfg : FGConfig)
    (emission : HighRecordEmission S T E rho Ef cfg)
    (decoded : ∀ j x r a, HonestRowAt S E rho T j x r a → ∃ u, S.decode a = some u)
    (m Q : Nat)
    (hrow : ∀ j x r a h, r ≤ Q → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h ≤ m) :
    (∀ j x r a f t, HonestRowAt S E rho T j x r a →
      historyFinHeight S D a = some f → m ≤ f →
      eventTime rho j = some t → T.action (Q + 1) ≤ t) ∧
    (∀ j z r a f t, HonestRowAt S E rho T j z r a →
      historyFinHeight S D a = some f → eventTime rho j = some t →
      t < T.action (Q + 1) → f < m) := by
  have hcut := (kmid_rows_cut S T L E rho D m Q hrow).2
  have key : ∀ j z r a f t, HonestRowAt S E rho T j z r a →
      historyFinHeight S D a = some f → eventTime rho j = some t →
      t < T.action (Q + 1) → f < m := by
    intro j z r a f t ha hf ht hlt
    obtain ⟨h, hh, hlt'⟩ := kmid_row_fin_lt S T E rho D Ef cfg emission decoded ha
    exact (hlt' f hf).trans_le (hcut j z r a h t ha hh ht hlt)
  refine ⟨?_, key⟩
  intro j x r a f t ha hf hm ht
  by_contra hn
  have := key j x r a f t ha hf ht (lt_of_not_ge hn)
  omega

/-- Linked unit-weight FG seats transfer the faulty-node cardinality bound. -/
theorem kmid_faulty_weight [Fintype V]
    (linked : Function.Injective (safetyHolder S rho))
    (unit : ∀ i, Ef.weight i = 1)
    (fault : (Gen.V2.Duty.faulty rho).card < Ef.q) :
    Ef.weightOf (historyFaulty S rho) < Ef.q := by
  classical
  have hsub : (historyFaulty S rho).image (safetyHolder S rho) ⊆
      Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have hc : (historyFaulty S rho).card ≤ (Gen.V2.Duty.faulty rho).card :=
    (Finset.card_image_of_injective _ linked).symm.trans_le (Finset.card_le_card hsub)
  have hw : Ef.weightOf (historyFaulty S rho) = (historyFaulty S rho).card := by
    delta Electorate.weightOf
    simp only [unit, Finset.sum_const, smul_eq_mul, mul_one]
  rw [hw]
  exact hc.trans_lt fault

/-- The parent fold changes the slot and preserves both height-entry fields. -/
theorem kmid_parentFold_height (Ef : Electorate (Fin n)) (cfg : FGConfig) (K : Nat)
    (s : Slot) (H : FGBlock (Fin n)) :
    (KitFG.Window.parentState Ef cfg K H s).h =
      (KitFG.Window.certificateHeight Ef cfg K H).h ∧
    (KitFG.Window.parentState Ef cfg K H s).T_h =
      (KitFG.Window.certificateHeight Ef cfg K H).T_h := ⟨rfl, rfl⟩

/-- A valid stored height row on a plateau lies above its named entry. -/
theorem kmid_rows_above_entry (cfg : FGConfig) (K : Nat)
    (height : FGHeightLaws Ef O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (nd : P.State) (closed : ∀ B ∈ (R.core nd).fg.TF, B.parent ∈ (R.core nd).fg.TF)
    (roots : ViewRootInj (R.core nd).fg.TF)
    (validRows : ∀ W ∈ (R.core nd).fg.TF, ∀ row ∈ W.rows,
      SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K W.parent) row = true)
    (k : RowKind) (y : Nat) (U B : FGBlock (Fin n)) (hB : B ∈ (R.core nd).fg.TF)
    (hBh : (O.height B).h = y) (hUB : FGBlock.Preceq U B) :
    ∀ i W, FGBlock.Preceq W B → (∃ row ∈ W.rows, RowNames k row i y U) →
      FGBlock.Preceq U W.parent := by
  intro i W hWB ⟨row, hrow, hnames⟩
  have hW := ancestor_closed_of_parent_closed _ closed B hB W hWB
  cases W with
  | genesis => exact (List.not_mem_nil hrow).elim
  | node Q t root x rs =>
    have hv := validRows _ hW row hrow
    have hpair : ∃ timeout, row.height_pair = .vote y U.root timeout := by
      obtain ⟨_, hk⟩ := hnames
      cases k with
      | target => exact ⟨_, hk⟩
      | progress => exact hk
    obtain ⟨timeout, hp⟩ := hpair
    have hQB := preceq_trans (preceq_parent_node Q t root x rs) hWB
    have hQh : (O.height Q).h ≤ y := hBh ▸ height.h_mono hQB
    have hdh : (SimplexFG.Window.derive Ef cfg K Q).h = (O.height Q).h := by
      rw [height_eq]; rfl
    have hdT : (SimplexFG.Window.derive Ef cfg K Q).T_h = (O.height Q).T_h := by
      rw [height_eq]; rfl
    rw [SimplexFG.Window.r6w_def] at hv
    rcases Bool.or_eq_true_iff.mp hv with hm | hm
    · rw [SimplexFG.Window.heightMatch_def, hp] at hm
      simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      have hroot : U.root = (O.height Q).T_h.root := hdT ▸ hm.2
      have hU : U = (O.height Q).T_h := roots _ _ ⟨B, hB, hUB⟩
        ⟨B, hB, preceq_trans (height.entry_preceq Q) hQB⟩ hroot
      change FGBlock.Preceq U Q
      rw [hU]
      exact height.entry_preceq Q
    · rw [SimplexFG.Window.staleUseful_def, hp] at hm
      cases hf : row.finality_pair with
      | none => rw [hf] at hm; cases hm
      | some fp =>
        rw [hf] at hm
        have hb := (Bool.and_eq_true_iff.mp hm).1
        have hlt : y < (SimplexFG.Window.derive Ef cfg K Q).h := (of_decide_eq_true hb).2
        rw [hdh] at hlt
        simp only [Height] at hQh hlt
        omega

/-- Construct the batch from actual matching rows and exact parent-read effects. -/
theorem kmid_batchPrem {Body : Type} (cfg : FGConfig) (K : Nat)
    (height : FGHeightLaws Ef O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (decodeProposal : P.Object → Option (Slot × Body))
    (bodyErase : Body → Block) (bodyRows : Body → List Wire)
    (blockWireRows : P.State → List Wire)
    (parentFG : P.State → Block → Option (FGBlock (Fin n)))
    (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
    (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)
    (valid : Wire → Bool) (ΔF : Time)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (linked : Function.Injective (safetyHolder S rho))
    (quorum : Ef.q ≤ Ef.weightOf (Finset.univ \ historyFaulty S rho))
    (deltaF : E.Δ ≤ ΔF) (receipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (q y : Nat) (U X : FGBlock (Fin n))
    (horizon : max (T.action q) E.t_GST + ΔF ≤ T.proposal X.slot ∧
      T.proposal X.slot ≤ rho.horizon)
    (carrier : ∃ rows, HonestCarrier E rho I
      (kernelCarrier decodeProposal bodyErase bodyRows) X.slot (R.erase X) rows ∧
      X.rows = rows.filterMap S.decode)
    (nd : P.State) (hnd : proposalStateAt E rho I X.slot = some nd)
    (lookup : parentFG nd (R.erase X).parent = some X.parent)
    (hparTF : X.parent ∈ (R.core nd).fg.TF)
    (closed : ∀ B ∈ (R.core nd).fg.TF, B.parent ∈ (R.core nd).fg.TF)
    (roots : ViewRootInj (R.core nd).fg.TF)
    (validRows : ∀ W ∈ (R.core nd).fg.TF, ∀ row ∈ W.rows,
      SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K W.parent) row = true)
    (parentEq : parentHeight nd X.slot X.parent =
      ((O.height X.parent).h, (O.height X.parent).T_h.root))
    (matchValid : ∀ a, valid a = true →
      namedEntry (D.heightPair a) = some (parentHeight nd X.slot X.parent) →
      validFor nd X.slot X.parent a = true)
    (after : q * T.roundSlots + 2 ≤ X.slot) (entry : EntryAt O.height U y)
    (path : FGBlock.Preceq U X.parent) (hpar : (O.height X.parent).h = y)
    (rows : ∀ x ∈ rho.honest, ∃ j r a, r ≤ q ∧ HonestRowAt S E rho T j x r a ∧
      RowComplete S rho D.signer valid x a ∧ NamesEntry (pair := D.heightPair) .target a y U) :
    BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
      parentFG parentHeight validFor ΔF .target q y U X := by
  classical
  have hT : (O.height X.parent).T_h = U :=
    ((height.entry_plateau path (entry.1.trans hpar.symm)).symm.trans entry.2)
  refine ⟨hs, hweight, deltaF, receipt, horizon, carrier, after, ?_, entry, path, ?_⟩
  · refine ⟨Finset.univ \ historyFaulty S rho, ?_, quorum, ?_⟩
    · intro i hi
      have hn : i ∉ historyFaulty S rho := (Finset.mem_sdiff.mp hi).2
      delta historyFaulty at hn
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        not_not] using hn
    · intro i hi
      have honest : safetyHolder S rho i ∈ rho.honest := by
        have hn : i ∉ historyFaulty S rho := (Finset.mem_sdiff.mp hi).2
        delta historyFaulty at hn
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
          not_not] using hn
      obtain ⟨j, r, a, hr, ha, hcomp, hnames⟩ := rows _ honest
      obtain ⟨i', hauth, hseat⟩ := hcomp.2
      obtain rfl := linked hseat
      have hmatch : namedEntry (D.heightPair a) = some (parentHeight nd X.slot X.parent) := by
        rw [parentEq, hpar, hT]
        change D.heightPair a = .vote y U.root false at hnames
        rw [hnames]
        rfl
      exact ⟨j, r, a, T.action r, hr, ha, hauth, hnames, kmid_event_time S T E rho ha,
        rfl, ⟨nd, X.parent, hnd, lookup, matchValid a hcomp.1 hmatch⟩,
        ⟨nd, X.parent, hnd, lookup, hmatch⟩⟩
  · intro i _ W hW hrow
    exact kmid_rows_above_entry R O Ef cfg K height height_eq nd closed roots validRows
      .target y U X.parent hparTF hpar path i W hW hrow

end AvailableChain.FGCompose
end
