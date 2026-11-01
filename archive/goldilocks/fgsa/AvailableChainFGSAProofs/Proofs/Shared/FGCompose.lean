module
public import AvailableChainFGCompose.Statements.ChannelLaws
public import AvailableChainFGCompose.Proofs.SourceHead
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGSARun.Proofs.FGSource
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import AvailableChainFGSAClaims.Statements.Fold
public import AvailableChainFGSA.Proofs.Head

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
def fgsaCoreReads (p : Params) {In : Type} (c : AppCodec In) :
  FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }
theorem fgsaCoreReads_def (p : Params) {In : Type} (c : AppCodec In) : fgsaCoreReads p c =
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none } := by
  rfl
theorem fgsa_eventReads_eq_compose {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) :
    (@cutPred V In P t = @FGCompose.cutPred V In P t) ∧
    afterTicksIdx rho t = FGCompose.afterTicksIdx rho t ∧ timeIdx rho t = FGCompose.timeIdx rho t ∧
    afterTicks E rho t = FGCompose.afterTicks E rho t ∧
    preTick E rho x t = FGCompose.preTick E rho x t ∧
    postClock E rho x t = FGCompose.postClock E rho x t ∧
    postTick E rho x t = FGCompose.postTick E rho x t :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem fgsa_chainRows_eq_compose (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (X : FGBlock (Fin p.n)) (cut : Time) :
    ChainRowsBefore p c E rho X cut =
      FGCompose.ChainRowsBefore (fgsaCoreReads p c) E rho X cut := by
  rw [fgsaCoreReads_def]
  rfl
theorem fgsaCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (fgsaCoreReads p c) where
  clock_fg nd t := FGSA.clock_fg p nd.st t
  clock_proposals nd t := FGSA.clock_proposals p nd.st t
  clock_rowPool nd t := FGSA.clock_rowPool p nd.st t
  process_tf nd o := (FGSA.process_cumulative p nd.st (toWire p o)).1
  process_proposals nd o := (FGSA.process_cumulative p nd.st (toWire p o)).2.2.2.2.1
  process_rowPool nd o := (FGSA.process_cumulative p nd.st (toWire p o)).2.2.2.2.2
  own_core nd o := rfl
  source_mem nd C h := by
    change FGSA.fgSource p nd.st = some C at h
    change C ∈ nd.st.fg.TF
    have hsource : FGSA.fgSource p nd.st = jointSource p nd.st := by
      rw [jointSource_def, domainR_def, frameR_def, treeT_def]
      change FGSA.deepest ((FGSA.fullTree p nd.st).filter _) =
        FGSA.deepest ((FGSA.fullTree p nd.st).filter _)
      apply congrArg (FGSA.deepest (n := p.n))
      apply Finset.filter_congr
      intro B _
      rw [sourceCandidates_def, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
        Finset.mem_filter, List.mem_toFinset]
      cases leaseOf nd.st (eraseFG B) <;> rfl
    rw [hsource, jointSource_def] at h
    have hm := (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ h).1).1
    rw [domainR_def, KitFG.mem_filteredFromView, treeT_def] at hm
    exact hm.1
  erase_inj := eraseFG_injective
theorem fgsaHeadLaws (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    FGCompose.FGHeadLaws (fgsaCoreReads p c) E rho where
  head_mem i x t s := by
    have hinv := (storeBundle_postClock E rho i x t).cstore
    have hm := headVote_stored p _ hinv s
    obtain ⟨B, hB, hBe⟩ := (hinv.baseTree _).mp hm
    exact ⟨B, hB, hBe⟩
  parent_closed i x B hB := (cstoreInv_stateBefore E rho i x).fg.closed B hB

open Gen.Pure

private def p0c1_observations (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0c1_selection (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSelectionReads (fgsa p c) p.n where
  select nd := (FGSA.fgSource p nd.st, fgBlockOf nd.st (fgHead p nd.st))
  clientInputs nd := fgInputs p nd.st

private def p0c1_deeper (a b : Block) : Block :=
  if a.depth < b.depth || (a.depth == b.depth && a.root < b.root) then b else a

private theorem p0c1_deeper_depth (a b : Block) :
    a.depth ≤ (p0c1_deeper a b).depth ∧ b.depth ≤ (p0c1_deeper a b).depth := by
  unfold p0c1_deeper
  split
  · next h =>
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact ⟨Nat.le_of_lt (of_decide_eq_true h), le_rfl⟩
    · exact ⟨(beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1).le, le_rfl⟩
  · next h =>
    have hn : ¬ a.depth < b.depth := by
      intro hab
      exact h (by simp only [hab, decide_true, Bool.true_or])
    exact ⟨le_rfl, Nat.le_of_not_gt hn⟩

private theorem p0c1_fold_depth (xs : List Block) (init : Block) :
    init.depth ≤ (xs.foldl p0c1_deeper init).depth ∧
      ∀ b ∈ xs, b.depth ≤ (xs.foldl p0c1_deeper init).depth := by
  induction xs generalizing init with
  | nil => exact ⟨le_rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons x xs ih =>
    obtain ⟨hi, hb⟩ := ih (p0c1_deeper init x)
    refine ⟨(p0c1_deeper_depth init x).1.trans hi, ?_⟩
    intro b hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (p0c1_deeper_depth init b).2.trans hi
    · exact hb b hm


private theorem p0c1_fold_covers (xs : List Block) (init B : Block) (hB : B ∈ xs)
    (hinit : Block.Compatible init B)
    (hxs : ∀ b ∈ xs, Block.Compatible b B) :
    Block.Preceq B (xs.foldl (fun a b =>
      if a.depth < b.depth || (a.depth == b.depth && a.root < b.root) then b else a) init) := by
  change Block.Preceq B (xs.foldl p0c1_deeper init)
  have hdepth := (p0c1_fold_depth xs init).2 B hB
  have hmem := foldl_select_mem (fun (a b : Block) =>
    a.depth < b.depth || (a.depth == b.depth && a.root < b.root)) xs init
  change xs.foldl p0c1_deeper init = init ∨ xs.foldl p0c1_deeper init ∈ xs at hmem
  have hcompat : Block.Compatible (xs.foldl p0c1_deeper init) B := by
    rcases hmem with he | hm
    · rw [he]; exact hinit
    · exact hxs _ hm
  rcases Bool.or_eq_true_iff.mp hcompat with h | h
  · have he := prefix_eq_of_depth _ _ h hdepth
    rw [he]
    exact block_preceq_refl _
  · exact h


private theorem p0c1_liveRoot_of_lease (p : Params) (st : State p.n) {B : Block}
    (hBS : Block.Preceq B st.base.stableRecord)
    (hbelow : LeaseBelowOutputStore p st) {dl : Time}
    (hlease : FGSA.leaseOf st B = some dl) (hlive : st.base.now < dl)
    (hdom : ∃ β ∈ FGSA.fullTree p st, eraseFG β = B) :
    Block.Preceq B (FGSA.liveRoot p st) := by
  obtain ⟨β, hβ, hβB⟩ := hdom
  have hZB : Block.Preceq (eraseFG (FGSA.controls p st).Z) B := by
    rw [← hβB]
    exact eraseFG_preceq
      ((KitFG.mem_filteredFromView (heightView p) _ _ β).mp hβ).2.2.1
  obtain ⟨row, hfind, hdl⟩ := Option.map_eq_some_iff.mp hlease
  have hrow := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  have hkey : row.1 = B := beq_iff_eq.mp hp
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ β ∈ FGSA.fullTree p st, eraseFG β = row.1)
    then some row.1 else none)
  have hBm : B ∈ targets := by
    apply List.mem_filterMap.mpr
    refine ⟨row, hrow, ?_⟩
    have htime : st.base.now < row.2.2 := hdl ▸ hlive
    have hdB : ∃ β ∈ FGSA.fullTree p st, eraseFG β = B := ⟨β, hβ, hβB⟩
    simp only [htime, decide_true, hkey, hdB, Bool.and_self, ite_true]
  change Block.Preceq B (targets.foldl p0c1_deeper (eraseFG (FGSA.controls p st).Z))
  apply p0c1_fold_covers targets _ B hBm
  · exact block_compatible_of_common hZB (block_preceq_refl B)
  · intro b hb
    obtain ⟨row, hr, he⟩ := List.mem_filterMap.mp hb
    split at he
    · next hc =>
      have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
      have hbe : row.1 = b := Option.some.inj he
      rw [← hbe]
      exact block_compatible_of_common (hbelow row hr hl) hBS
    · cases he


private theorem p0c1_source_head (p : Params) (st : State p.n)
    (hReach : Reachable p st) {C H : FGBlock (Fin p.n)}
    (hC : FGSA.fgSource p st = some C) (hH : fgBlockOf st (fgHead p st) = some H) :
    FGBlock.Preceq C H := by
  have hmem := Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hC).1
  have hguard := Bool.and_eq_true_iff.mp hmem.2
  have hlive := hguard.2
  cases hl : leaseOf st (eraseFG C) with
  | none => simp only [hl, Bool.false_eq_true] at hlive
  | some dl =>
    simp only [hl, decide_eq_true_eq] at hlive
    have hbelow := leaseBelowOutputStore_of_reachable p st hReach
    obtain ⟨row, hfind, hdl⟩ := Option.map_eq_some_iff.mp hl
    have hp := List.find?_some hfind
    have hkey : row.1 = eraseFG C := beq_iff_eq.mp hp
    have hCS : Block.Preceq (eraseFG C) st.base.stableRecord := by
      rw [← hkey]
      exact hbelow row (List.mem_of_find?_eq_some hfind) (hdl ▸ hlive)
    have hroot := p0c1_liveRoot_of_lease p st hCS hbelow hl hlive ⟨C, hmem.1, rfl⟩
    have hhead : Block.Preceq (liveRoot p st) (fgHead p st) :=
      liveRoot_preceq_headInTree p st _ _ _
    have hHe := ((fgBlockOf_spec p st (storeBundle_of_reachable p st hReach).cstore
      (fgHead p st) H).mp hH).2
    exact eraseFG_preceq_iff.mp (hHe ▸ block_preceq_trans hroot hhead)

private theorem p0c1_selection_laws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSelectionLaws (fgsaCoreReads p c) (p0c1_observations p c)
      (p0c1_selection p c) (fun nd => Reachable p nd.st) (Window.headFields p p.K_W) where
  source_eq _ _ := rfl
  head_eq _ _ := rfl
  head_held nd hReach := by
    have hinv := (storeBundle_of_reachable p nd.st hReach).cstore
    obtain ⟨H, hm, he⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
    exact ⟨H, (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hm, he⟩, hm⟩
  source_viable nd C _ hC := by
    exact (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hC).1).1
  source_head nd C H hReach he := by
    exact p0c1_source_head p nd.st hReach (congrArg Prod.fst he) (congrArg Prod.snd he)
  client_eq nd H _ hH := by
    change (fgSource p nd.st, _) = (fgSource p nd.st, Window.headFields p p.K_W H)
    change fgBlockOf nd.st (fgHead p nd.st) = some H at hH
    simp only [hH]

private theorem p0c1_action_selection_laws (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hvalid : V2.D.ExecutionValid E rho) :
    FGCompose.FGActionSelectionLaws E rho (p0c1_selection p c) p.actionTime
      (fun x r _ => x ∈ rho.honest ∧ E.awake x (p.actionTime r) = true)
      (fun _ _ nd => joinedNow p nd.st = true) where
  nonempty_joined x r nd C hread _ hC := by
    obtain ⟨pre, hpre, rfl⟩ := Option.map_eq_some_iff.mp hread
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hpre
    have ht := V2.D.Run.tickIdx?_spec hi
    cases hj : joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
        (p.actionTime r)).st with
    | true => rfl
    | false =>
      have hn := fgsa_fgAction_unjoined_source_none E rho hvalid ht hj
      change FGSA.fgSource p _ = some C at hC
      rw [hn] at hC
      cases hC

#print axioms p0c1_source_head
#print axioms p0c1_selection_laws
#print axioms p0c1_action_selection_laws

private def p0c1_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0c1_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (p0c1_timing p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private abbrev p0c1_safety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut
private theorem p0c1_order_laws (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    FGCompose.FGRunOrderLaws E rho (fgsaCoreReads p c) := by
  constructor
  change RMonoAll p c E rho
  intro i j x _ hij
  let a := storeAt p c E rho i x
  apply V2.D.Engine.stateBefore_stable_restore (P := fgsa p c)
    (fun nd => FGBlock.Preceq a.fg.F nd.st.fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤ lexKey (nd.st.fg.h_j, nd.st.fg.J) ∧
      a.fg.h_max ≤ nd.st.fg.h_max)
    ?_ ?_ (fun _ _ h => h) E rho hij x ?_
    ⟨KitFG.preceq_refl _, le_rfl, le_rfl⟩
  · intro nd t h
    change FGBlock.Preceq a.fg.F (clock p nd.st t).fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤ lexKey ((clock p nd.st t).fg.h_j, (clock p nd.st t).fg.J) ∧
      a.fg.h_max ≤ (clock p nd.st t).fg.h_max
    rw [clock_fg]
    exact h
  · intro nd o h
    exact ⟨KitFG.preceq_trans h.1 (process_F_mono p nd.st (toWire p o)),
      le_trans h.2.1 (process_pair_mono p nd.st (toWire p o)),
      le_trans h.2.2 (process_hmax_mono p nd.st (toWire p o))⟩
  · intro nd t h
    change FGBlock.Preceq a.fg.F (acRestart p nd.st t).fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤
        lexKey ((acRestart p nd.st t).fg.h_j, (acRestart p nd.st t).fg.J) ∧
      a.fg.h_max ≤ (acRestart p nd.st t).fg.h_max
    rwa [acRestart_fg]


private theorem p0c1_observation_laws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (fgsaCoreReads p c) (p0c1_observations p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private theorem p0c1_client_laws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSelectionClientLaws (p0c1_selection p c) (p0c1_safety p c) :=
  ⟨fun _ => rfl⟩

private abbrev p0c1_signer {n : Nat} (a : RowWire n) : Option (Fin n) :=
  match a.auth with
  | .seat .fg i => some i
  | _ => none

private abbrev p0c1_carrier (p : Params) (o : Obj p) (_ : Slot) (Q : Block)
    (rows : List (RowWire p.n)) : Prop :=
  ∃ N, o.payload = .proposal N ∧ N.erase = Q ∧ N.rows = rows

private abbrev p0c1_stored_carrier (p : Params) (nd : Node p) (B : FGBlock (Fin p.n))
    (wire : RowWire p.n) : Prop :=
  ∃ s N, N.erase = eraseFG B ∧
    (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals ∧ wire ∈ N.rows

private abbrev p0c1_source_service (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (y : V) (r : Nat) (C : FGBlock (Fin p.n)) : Prop :=
  ∃ G, gateResult p c E rho y (r * p.R) = some (some G) ∧
    Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C)

section P0c1Channels
variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
variable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem p0c1_certified_eq (W : FGBlock (Fin p.n)) :
    FGCompose.certified (fgsaCoreReads p c) (p0c1_observations p c) W = certified p W := rfl

private theorem p0c1_entry_below_eq (e : Height × BlockId) (W : FGBlock (Fin p.n)) :
    FGCompose.EntryBelow (fgsaCoreReads p c) (p0c1_observations p c) e W =
      EntryBelow p e W := rfl

private theorem p0c1_named_entry_eq (e : NamedHeightPair) :
    FGCompose.namedEntry e = namedEntry e := by cases e <;> rfl

omit [DecidableEq V] in
private theorem p0c1_row_signer_eq (a : RowWire p.n) (x : V) :
    FGCompose.RowSigner (p0c1_safety p c) rho p0c1_signer a x = RowSigner p c rho a x := by
  rw [RowSigner_def]
  dsimp only [FGCompose.RowSigner]
  simp only [FGCompose.safetyHolder_def]
  dsimp only [p0c1_safety, p0c1_signer]
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => simp
  | proposer s => simp
  | seat label i =>
    cases label <;> simp
    rfl

private theorem p0c1_honest_row_eq (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (p0c1_safety p c) E rho (p0c1_timing p) j y r a =
      HonestRowAt p c E rho j y r a := rfl

private theorem p0c1_honest_row_before_eq (j : Nat) (y : V) (r : Nat)
    (a : RowWire p.n) :
    FGCompose.HonestRowBefore (p0c1_safety p c) E rho (p0c1_timing p) j y r a =
      HonestRowBefore p c E rho j y r a := rfl

omit [DecidableEq V] in
private theorem p0c1_row_complete_eq (x : V) (a : RowWire p.n) :
    FGCompose.RowComplete (p0c1_safety p c) rho p0c1_signer RowWire.valid x a =
      RowComplete p c rho x a := by
  change (_ ∧ _) = (_ ∧ _)
  rw [p0c1_row_signer_eq]

private theorem p0c1_held_eq (i : Nat) (x : V) (W : FGBlock (Fin p.n)) :
    FGCompose.HeldAt (fgsaCoreReads p c) E rho i x W = HeldAt p c E rho i x W := rfl

private theorem p0c1_block_before_eq (i : Nat) (W : FGBlock (Fin p.n)) :
    FGCompose.BlockInRunBefore (fgsaCoreReads p c) E rho i W =
      BlockInRunBefore p c E rho i W := rfl

private theorem p0c1_honest_proposal_eq (s : Slot) (Q : Block) :
    FGCompose.HonestProposal E rho (fgsaInterface p c) s Q =
      HonestProposal E rho (fgsaInterface p c) s Q := rfl

private theorem p0c1_honest_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c) (p0c1_carrier p) s Q rows =
      HonestCarrier p c E rho s Q rows := by
  rw [HonestCarrier_def]
  dsimp only [FGCompose.HonestCarrier, p0c1_carrier]
  rw [p0c1_honest_proposal_eq]
  simp only [exists_and_left]
  rfl

private theorem p0c1_action_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (p0c1_timing p) x r =
      actionSourceFG p c E rho x r := rfl

private theorem p0c1_action_triple_eq (x : V) (r : Nat) :
    FGCompose.actionTriple E rho (p0c1_timing p) (p0c1_selection p c) x r =
      actionTriple p c E rho x r := rfl

private theorem p0c1_head_label_eq (x : V) (s : Slot) :
    FGCompose.headAtLabel (fgsaCoreReads p c) E rho (p0c1_timing p) x s =
      headAtLabel p c E rho x s := rfl

private theorem p0c1_proposal_state_eq (s : Slot) :
    (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st =
      proposalStateAt p c E rho s := rfl

private theorem p0c1_proposal_head_eq (s : Slot) :
    FGCompose.proposalHeadAt E rho (fgsaInterface p c)
      (fun nd s => proposerHead p nd.st s) s = proposalHeadAt p c E rho s := rfl

private theorem p0c1_row_held_eq (nd : Node p) (a : RowWire p.n) :
    FGCompose.rowHeld (fgsaCoreReads p c) (fun nd => FGSA.blockWireRows nd.st) nd a =
      rowHeld p nd.st a := rfl

private theorem p0c1_held_before_eq (x : V) (a : RowWire p.n) (d : Time) :
    FGCompose.HeldBefore (fgsaCoreReads p c) E rho
      (fun nd => FGSA.blockWireRows nd.st) x a d = HeldBefore p c E rho x a d := rfl

private theorem p0c1_held_proposal_eq (s : Slot) (a : RowWire p.n) :
    FGCompose.heldAtProposal (fgsaCoreReads p c) E rho (fgsaInterface p c)
      (fun nd => FGSA.blockWireRows nd.st) s a = heldAtProposal p c E rho s a := by
  apply propext
  constructor
  · rintro ⟨nd, hread, hrow⟩
    exact ⟨nd.st, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hrow⟩
  · rintro ⟨st, hread, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, hnd, hrow⟩

private theorem p0c1_parent_chain_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.onParentChain E rho (fgsaInterface p c)
      (fun nd => FGSA.chainWireRows nd.st) s Q a = onParentChain p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, hread, hrow⟩
    exact ⟨nd.st, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hrow⟩
  · rintro ⟨st, hread, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, hnd, hrow⟩

private theorem p0c1_valid_parent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.ValidForParent E rho (fgsaInterface p c) (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) s Q a =
      ValidForParent p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, H, hread, hparent, hrow⟩
    exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · rintro ⟨st, H, hread, hparent, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, H, hnd, hparent, hrow⟩

private theorem p0c1_height_match_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.HeightMatch E rho (fgsaInterface p c)
      (fun a : RowWire p.n => namedEntry a.payload.height_pair)
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root)) s Q a =
      HeightMatch p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, H, hread, hparent, hrow⟩
    exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · rintro ⟨st, H, hread, hparent, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, H, hnd, hparent, hrow⟩

private theorem p0c1_crossing_eq :
    FGCompose.RXing (fgsaCoreReads p c) E rho (p0c1_observations p c) =
      RXing p c E rho := rfl

private theorem p0c1_cap_eq :
    FGCompose.RCap (fgsaCoreReads p c) (p0c1_safety p c) E rho (p0c1_observations p c)
      (p0c1_timing p) (fun a : RowWire p.n => namedEntry a.payload.height_pair)
      (fun nd => FGSA.chainWireRows nd.st) = RCap p c E rho := rfl

private theorem p0c1_strat_eq :
    FGCompose.RStrat (fgsaCoreReads p c) (p0c1_safety p c) E rho (p0c1_observations p c)
      (p0c1_timing p) (fun a : RowWire p.n => namedEntry a.payload.height_pair) =
      RStrat p c E rho := rfl

private theorem p0c1_qc_origin_eq :
    FGCompose.RQCOrigin (fgsaCoreReads p c) (p0c1_safety p c) E rho
      (p0c1_observations p c) (p0c1_timing p) (p0c1_stored_carrier p)
      (p0c1_source_service p c E rho) p.E = RQCOrigin p c E rho := by
  rw [RQCOrigin_def]
  dsimp only [FGCompose.RQCOrigin, p0c1_stored_carrier, p0c1_source_service]
  simp only [exists_and_left]
  rfl


private theorem p0c1_action_head_erasure (x : V) (r : Nat) :
    (FGCompose.actionHead (fgsaCoreReads p c) E rho (p0c1_timing p) x r).bind
      (fun h => h.map eraseFG) = actionHead p c E rho x r := by
  cases hr : postClock E rho x (p.actionTime r) with
  | none =>
    change ((postClock E rho x (p.actionTime r)).map _).bind _ =
      (postClock E rho x (p.actionTime r)).map _
    rw [hr]
    rfl
  | some nd =>
    obtain ⟨i, _, he⟩ := FGCompose.postClock_tick E rho hr
    have hReach : Reachable p nd.st := he ▸ reachable_postClock E rho i x (p.actionTime r)
    obtain ⟨H, hH, _⟩ := (p0c1_selection_laws p c).head_held nd hReach
    have hblock := ((fgBlockOf_spec p nd.st
      (storeBundle_of_reachable p nd.st hReach).cstore _ H).mp hH).2
    change ((postClock E rho x (p.actionTime r)).map
      (fun nd => fgBlockOf nd.st (fgHead p nd.st))).bind (fun h => h.map eraseFG) =
        (postClock E rho x (p.actionTime r)).map (fun nd => fgHead p nd.st)
    rw [hr]
    change (fgBlockOf nd.st (fgHead p nd.st)).map eraseFG = some (fgHead p nd.st)
    change fgBlockOf nd.st (fgHead p nd.st) = some H at hH
    rw [hH, Option.map_some, hblock]

private theorem p0c1_slot_start_eq (z : Int) :
    FGCompose.slotStartZ (p0c1_timing p) z = slotStartZ p z := rfl

private theorem p0c1_slot_at_eq (t : Time) :
    FGCompose.slotAt (p0c1_timing p) t = slotAt p t := rfl

end P0c1Channels

#print axioms p0c1_deeper_depth
#print axioms p0c1_fold_depth
#print axioms p0c1_fold_covers
#print axioms p0c1_liveRoot_of_lease
#print axioms p0c1_timing_laws
#print axioms p0c1_order_laws
#print axioms p0c1_observation_laws
#print axioms p0c1_client_laws
#print axioms p0c1_certified_eq
#print axioms p0c1_entry_below_eq
#print axioms p0c1_named_entry_eq
#print axioms p0c1_row_signer_eq
#print axioms p0c1_honest_row_eq
#print axioms p0c1_honest_row_before_eq
#print axioms p0c1_row_complete_eq
#print axioms p0c1_held_eq
#print axioms p0c1_block_before_eq
#print axioms p0c1_honest_proposal_eq
#print axioms p0c1_honest_carrier_eq
#print axioms p0c1_action_source_eq
#print axioms p0c1_action_triple_eq
#print axioms p0c1_head_label_eq
#print axioms p0c1_proposal_state_eq
#print axioms p0c1_proposal_head_eq
#print axioms p0c1_row_held_eq
#print axioms p0c1_held_before_eq
#print axioms p0c1_held_proposal_eq
#print axioms p0c1_parent_chain_eq
#print axioms p0c1_valid_parent_eq
#print axioms p0c1_height_match_eq
#print axioms p0c1_crossing_eq
#print axioms p0c1_cap_eq
#print axioms p0c1_strat_eq
#print axioms p0c1_qc_origin_eq
#print axioms p0c1_action_head_erasure
#print axioms p0c1_slot_start_eq
#print axioms p0c1_slot_at_eq

end AvailableChain.FGSA.Run

end
