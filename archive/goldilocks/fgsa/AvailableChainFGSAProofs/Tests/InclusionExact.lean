module
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposal
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalHistory -- shake: keep (axioms)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedReflect -- shake: keep (X=Q example)
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalRetained

set_option linter.privateModule false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100

namespace AvailableChain.FGSA.Run.Tests.InclusionExact

open AvailableChain.SimplexFG

-- Schedule-only fixture: Delta = 1; node 1 sleeps at the slot-1 HEAD time.
public abbrev params : Params :=
  ⟨⟨1, 2, 2, 0, by decide, by decide, by decide, by decide⟩,
    2, 0, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩
public abbrev env : Generic.Env (Fin 2) :=
  ⟨1, by decide, 0, le_rfl, fun x t => !decide (x = 1 ∧ t = 5)⟩
public abbrev mkRun (es : List (V2.Event (Fin 2) (fgsa params unitCodec).Object)) :
    V2.D.Run (Fin 2) (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := 5
  events := es
  seatOf := fun l j => match l with | .base _ => j | .prop _ => 0
  input := fun _ _ => ()
public abbrev events : List (V2.Event (Fin 2) (fgsa params unitCodec).Object) :=
  (List.range 6).foldl (fun es n =>
    let r := mkRun (es ++ [.tick 0 n, .tick 1 n])
    let objects := V2.D.Run.emitsAt env r es.length ++
      V2.D.Run.emitsAt env r (es.length + 1)
    es ++ [.tick 0 n, .tick 1 n] ++
      objects.flatMap (fun o => [.deliver 0 o n, .deliver 1 o n])) []
public abbrev run := mkRun events

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The finite schedule keeps both same-time ticks before each delivery. -/
public theorem iexact_schedule : V2.D.ScheduleWellFormed env run where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by decide +kernel
  honest_only := by decide +kernel
  tick_public := by
    intro x t ht
    have hall : ∀ e ∈ run.events, 0 ≤ e.time := by decide +kernel
    have hn : 0 ≤ t := hall _ ht
    exact ⟨t.toNat, by simp [Int.toNat_of_nonneg hn]⟩
  tick_total := by
    intro x _ t _ ht hh _
    change t ≤ 5 at hh
    interval_cases t <;> fin_cases x <;> decide +kernel

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The finite test run has no restart event. -/
public theorem noRestart : V2.D.NoRestart run := by
  intro i x t hi
  have hall : ∀ e ∈ run.events,
      (match e with | .restart _ _ => true | _ => false) = false := by decide +kernel
  exact Bool.noConfusion (hall _ (List.mem_of_getElem? hi))

public abbrev proposalIdx : Nat := run.events.findIdx (fun e => e == .tick 0 4)
public abbrev proposal : (fgsa params unitCodec).Object :=
  (V2.D.Run.emitsAt env run proposalIdx)[0]'(by decide +kernel)
public abbrev block : Block :=
  ((fgsaInterface params unitCodec).block proposal.payload).getD .genesis

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The test block has an actual honest slot-1 proposal emission. -/
public theorem honestProposal :
    HonestProposal env run (fgsaInterface params unitCodec) 1 block := by
  constructor
  · rw [Gen.V2.Duty.HonestSlot_def]
    exact ⟨by decide, Finset.mem_univ _⟩
  · refine ⟨proposal, ⟨proposalIdx, ?_, ?_⟩, ?_⟩
    · decide +kernel
    · exact List.getElem_mem _
    · decide +kernel

-- The positive slot-1 test has a real, non-genesis honest proposal.
/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The emitted test proposal is a non-genesis block. -/
public theorem proposal_nonGenesis : block ≠ .genesis := by decide +kernel

-- Each node accepted the proposal at time 4, strictly before the vote at 5.
/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
Both honest nodes accept the test proposal strictly before vote time. -/
public theorem receipt (x : Fin 2) :
    ∃ o i t, (fgsaInterface params unitCodec).block o.payload = some block ∧
      t < SA.voteTime params.toParams 1 ∧ V2.D.Run.acceptsAt env run i x o t := by
  let i := run.events.findIdx (fun e => e == .deliver x proposal 4)
  refine ⟨proposal, i, 4, ?_, by decide, ?_⟩
  · decide +kernel
  · refine ⟨⟨proposal, ?_, Or.inl rfl⟩, ?_, ?_⟩
    all_goals fin_cases x <;> decide +kernel

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
Both scheduled readers compute the test proposal as their HEAD. -/
public theorem headLabel (x : Fin 2) :
    headAtLabel params unitCodec env run x 1 = some block := by
  fin_cases x <;> decide +kernel

-- Both the awake and asleep readers compute the same strict-before HEAD.
/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The strict-before clocked read includes the sleeping reader. -/
public theorem strictHead (x : Fin 2) :
    FGSA.headVote params ((fgsa params unitCodec).clock
      (V2.D.Run.stateBeforeTime env run (SA.voteTime params.toParams 1) x)
      (SA.voteTime params.toParams 1)).st 1 = block :=
  by fin_cases x <;> decide +kernel

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The sleeping honest reader emits no object at vote time. -/
public theorem asleep_silent : ∀ o, ¬ V2.D.Run.emits env run 1 o
    (SA.voteTime params.toParams 1) :=
  inclusion_sleep_silence env run 1 1 (Finset.mem_univ _) (by decide)

-- This schedule-only fixture includes a sleeping tick for deterministic read tests.
example : .tick 1 (SA.voteTime params.toParams 1) ∈ run.events ∧
    env.awake 1 (SA.voteTime params.toParams 1) = false := by decide +kernel
example : (Gen.V2.Duty.faulty run).card <
    (Gen.V2.Duty.awakeHonest env run (SA.voteTime params.toParams 1)).card := by decide

-- A real HEAD delivery at vote time is after all same-time ticks.
public abbrev voteIdx : Nat := run.events.findIdx (fun e => e == .tick 0 5)
public abbrev headObject : (fgsa params unitCodec).Object :=
  (V2.D.Run.emitsAt env run voteIdx)[0]'(by decide +kernel)
public abbrev deliveryIdx : Nat := run.events.findIdx
  (fun e => e == .deliver 1 headObject 5)
example : run.events[deliveryIdx]? = some (.deliver 1 headObject 5) ∧
    V2.D.Run.idxBefore run 5 ≤ voteIdx ∧ voteIdx < deliveryIdx := by decide +kernel
example : afterTicksIdx run 5 ≤ deliveryIdx ∧ deliveryIdx < timeIdx run 5 := by
  decide +kernel

-- The strict-before read excludes any delivery at the read time.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p}
    {d : Time} (hi : rho.events[i]? = some (.deliver x o d)) :
    ¬ i < V2.D.Run.idxBefore rho d := by
  intro h
  exact (lt_irrefl d) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp h)

-- The same strict boundary applies to an I-GATE delivery at the gate time.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {s : Slot}
    (hi : rho.events[i]? = some (.deliver x o (SA.gateTime p.toParams s))) :
    ¬ i < V2.D.Run.idxBefore rho (SA.gateTime p.toParams s) := by
  intro h
  exact (lt_irrefl _) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp h)

-- A delivery at vote time cannot supply an acceptance strictly before it.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i : Nat} {x : V} {o : Obj p} {s : Slot}
    (hi : rho.events[i]? = some (.deliver x o (SA.voteTime p.toParams s))) :
    ¬ ∃ t, t < SA.voteTime p.toParams s ∧ V2.D.Run.acceptsAt E rho i x o t := by
  rintro ⟨t, ht, ⟨⟨parent, he, _⟩, _⟩⟩
  rw [hi] at he
  have heq : SA.voteTime p.toParams s = t := (V2.Event.deliver.inj (Option.some.inj he)).2.2
  exact (lt_irrefl t) (heq ▸ ht)

-- DeltaF = 3 is independent of the block/HEAD delay Delta = 1.
example : fgsaDelay (p := params) 1 3 proposal = 1 ∧
    fgsaDelay (p := params) 1 3 headObject = 1 := by decide +kernel
example (body : RowPayload) :
    fgsaDelay 1 3 (ofRow params ⟨.seat .fg 0, body⟩) = 3 := rfl

-- The old-child reflection route permits a rival at X = the stored parent Q.
example {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Kc C : Block)
    (hcut : Block.Preceq (RetainedWalk.z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))) Kc)
    (hKQ : Block.Preceq Kc N.erase.parent) (hp : C.parent? = some N.erase.parent)
    (hold : C.slot < s + 1)
    (hm : C ∈ RetainedWalk.T p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hw : ReflectedDomainWitness p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) C) :
    C ∈ RetainedWalk.S p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1))) :=
  fgsa_walkRun_reflected_old_child (hroots := hroots) E rho hE hN hDelta s hSync hx hy hip hih hseat
    N hem Kc N.erase.parent C hcut hKQ (Gen.Pure.block_preceq_refl _)
    hp hold hm hw

#print axioms AvailableChain.FGSA.Run.Tests.InclusionExact.receipt
#print axioms AvailableChain.FGSA.Run.Tests.InclusionExact.strictHead
#print axioms AvailableChain.FGSA.Run.Tests.InclusionExact.asleep_silent
#print axioms AvailableChain.FGSA.Run.Tests.InclusionExact.honestProposal
#print axioms AvailableChain.FGSA.Run.inclusion_acceptance_of_stored
#print axioms AvailableChain.FGSA.Run.inclusion_receipt_of_compatible
#print axioms AvailableChain.FGSA.Run.inclusion_proposal_receipt
#print axioms AvailableChain.FGSA.Run.inclusion_head_read
#print axioms AvailableChain.FGSA.Run.inclusion_sleep_silence
#print axioms AvailableChain.FGSA.Run.inclusion_comparison_prefix

/-! ### r2: G1 producer, E1 compatibility, E2 -/

-- Slot 1: no gate result exists before v_1, so the comparison prefix is genesis.
/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT r2, R3.
Class (iii). DC: INTENTIONAL.
The test run has no genuine comparison result before the slot-1 vote. -/
public theorem slot1_no_result {r : Slot} {B : Block}
    (h : (r, B) ∈ cleanResults params unitCodec env run
      (V2.D.Run.idxBefore run (SA.voteTime params.toParams 1))) : False := by
  have := (inclusion_results_before iexact_schedule 1 (fun j hj e he =>
    ((Gen.V2.Duty.index_lt_idxBefore_iff iexact_schedule he _).mp hj).le) h).2
  simp only [Slot] at this
  omega

example : ∀ D, BelowLabel params unitCodec env run
    (V2.D.Run.idxBefore run (SA.voteTime params.toParams 1)) (1 - 2) D → D = .genesis := by
  rintro D (h | ⟨r, B, hB, _, _⟩)
  · exact h
  · exact (slot1_no_result hB).elim

-- In every run, a comparison result read at v_s has label at most s − 2.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (s r : Slot) (B : Block)
    (h : (r, B) ∈ cleanResults p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s))) :
    r + 2 ≤ s :=
  (inclusion_results_before hs s (fun _ hj _ he =>
    ((Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mp hj).le) h).2

-- The HEAD and proposal ticks are off the gate times: the tick is the pre-gate tick.
example (st : State params.n) :
    clock params st (SA.voteTime params.toParams 1) =
      clockPre params st (SA.voteTime params.toParams 1) := by
  apply inclusion_clock_offGate
  intro r h
  change 4 * 1 * (r : Int) + 6 * 1 = 4 * 1 * ((1 : Nat) : Int) + 1 at h
  omega
example (st : State params.n) :
    clock params st (SA.proposalTime params.toParams 1) =
      clockPre params st (SA.proposalTime params.toParams 1) := by
  apply inclusion_clock_offGate
  intro r h
  change 4 * 1 * (r : Int) + 6 * 1 = 4 * 1 * ((1 : Nat) : Int) at h
  omega

-- Without leases the live root is the FG root, so the root bound suffices.
example (p : Params) (st : State p.n) (D : Block)
    (hz : Block.Preceq (eraseFG (controls p st).Z) D) (h0 : st.base.obligations = []) :
    Block.Preceq (liveRoot p st) D :=
  inclusion_liveRoot_le p st D hz (by simp [h0])

-- One vote per seat is not a cap.
example : GridCO.equivocates
    [baseVote (⟨.seat (.head 0) (0 : Fin 2), genesisRoot⟩ : HeadWire 2)] 0 = false :=
  inclusion_no_equivocation _ 0 _ (fun _ ho _ => List.mem_singleton.mp ho)

-- O-CLOSE shape: the ExactProposalPrem fields and the field-level Clean binders give E1, E2 and E3
-- inline, for joined honest readers with local service.
example {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (pt : PtSP)
    (hset : CleanSet p c E rho ΔF) (hInputs : InclusionReceiverInputs E rho)
    (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.voteTime p.toParams pt.s ≤ rho.horizon)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hstrat : RStrat p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) :
    (∀ x, headReader p E rho x pt.s (SA.voteTime p.toParams pt.s) →
      ∃ o i t, (fgsaInterface p c).block o.payload = some pt.P ∧
      t < SA.voteTime p.toParams pt.s ∧ V2.D.Run.acceptsAt E rho i x o t) ∧
    (∀ x ∈ rho.honest, joinedAt p E rho x pt.s (SA.voteTime p.toParams pt.s) →
      FGSA.headVote p ((fgsa p c).clock
      (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams pt.s) x)
      (SA.voteTime p.toParams pt.s)).st pt.s = pt.P) ∧
    (∀ x ∈ rho.honest, E.awake x (SA.voteTime p.toParams pt.s) = false →
      ∀ o, ¬ V2.D.Run.emits E rho x o (SA.voteTime p.toParams pt.s)) :=
  ⟨inclusion_exact_receipt (_hstrat :=
    hstrat) E rho ΔF hset hInputs hstore hframe hsrc hordered hnonempty
      htransfer hleases hrows pt hprop hhor,
    inclusion_exact_head (hstrat :=
    hstrat) E rho ΔF hset hInputs hstore hframe hsrc hordered hnonempty
      htransfer hleases hrows pt hprop hhor,
    inclusion_sleep_silence E rho pt.s⟩

/-- The last HEAD is at the horizon. Service for it cannot have a later deadline. -/
public theorem horizon_head_has_no_early_service :
    ¬ Nonempty (FreshHeadService env run 1 (0 : Fin 2) genesisRoot 6 0) := by
  rintro ⟨h⟩
  have hl := h.later
  have hh := h.horizon
  change 5 < h.dl 5 at hl
  change h.dl 5 ≤ 5 at hh
  exact (not_lt_of_ge hh) hl

/-- A tick before the reader vote cannot satisfy the relay scope's index bound. -/
public theorem early_tick_has_no_relay_scope {i : Nat}
    (hi : run.events[i]? = some (.tick 0 2)) :
    ¬ HeadRelayServiceScope env run 0 (0 : Fin 2) genesisRoot 5 i 0 := by
  intro h
  have hil := (Gen.V2.Duty.index_lt_idxBefore_iff iexact_schedule hi 5).mpr (by decide)
  exact (not_lt_of_ge h.index) hil

#print axioms AvailableChain.FGSA.Run.Tests.InclusionExact.horizon_head_has_no_early_service
#print axioms AvailableChain.FGSA.Run.Tests.InclusionExact.early_tick_has_no_relay_scope

#print axioms AvailableChain.FGSA.Run.Tests.InclusionExact.slot1_no_result
#print axioms AvailableChain.FGSA.Run.inclusion_retained_reads
#print axioms AvailableChain.FGSA.Run.inclusion_exact_compat
#print axioms AvailableChain.FGSA.Run.inclusion_exact_receipt
#print axioms AvailableChain.FGSA.Run.inclusion_exact_head

end AvailableChain.FGSA.Run.Tests.InclusionExact
