module
public import AvailableChainPCSAProofs
public meta import AvailableChainPCSAProofs -- shake: keep (closed run evaluation)

@[expose] public section

/-! Pending HEAD cutoff counterexamples. Delta is 2, cut is 18,
and the label-1 gate is at 20. The same run is also clean to cut 12,
which puts the HEAD at 18 strictly past that cut. Five honest nodes vote 3 for X and 2 for Y.
A faulty slot-2 proposal Z arrives only at node 3 at time 17. It carries
one faulty label-1 HEAD for Y. Its relay deadline 19 is after the cut.
Node 0's gate has 3 X supporters among 5 voters. Node 3's next vote has
6 voters, so neither old child is eligible; it chooses current proposal Z.
The actual engine and all finite run/prefix checks are evaluated below. -/

open AvailableChain AvailableChain.PCSA AvailableChain.PCSA.Run AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run.Tests.PendingHeadCounterexample
abbrev p : Params :=
  { Δ := 2, n := 6, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide,
    digest := fun d => ⟨d.app + 1⟩ }
def X : NamedProposal 6 := namedProposal p .genesis 1 0 [] [] [] none
def Y : NamedProposal 6 := namedProposal p .genesis 1 1 [] [] [] none
def faultyY : HeadWire 6 := ⟨.seat (.head 1) 5, Y.root⟩
def Z : NamedProposal 6 := namedProposal p .genesis 2 2 [faultyY] [faultyY] [] none
def prop (s : Nat) (N : NamedProposal 6) : Obj p :=
  ⟨.seat (.prop s) ⟨0, by change 0 < 1; decide⟩, .proposal N⟩
def head (s : Nat) (i : Fin 6) (root : BlockId) : Obj p :=
  ⟨.seat (.base (.head s)) i, .head root⟩
def ack (s : Nat) (i : Fin 6) (root : BlockId) : Obj p :=
  ⟨.seat (.base (.ack s)) i, .ack root⟩
def pcObj (C : PC 6) : Obj p := ⟨.none, .pc C⟩
def E : Generic.Env (Fin 6) :=
  { Δ := 2, Δ_pos := by decide, t_GST := 24, t_GST_nonneg := by decide,
    awake := fun v _ => decide (v ≠ 5) }
def seats : (l : RunLabel) → Fin (RunLabel.seats p l) → Fin 6
  | .prop _, _ => 5
  | .base _, i => i

def honestNodes : List (Fin 6) := [0, 1, 2, 3, 4]
def onX : List (Fin 6) := [0, 1, 2]
def onY : List (Fin 6) := [3, 4]
def deliveries (t : Nat) : List (V2.Event (Fin 6) (Obj p)) :=
  match t with
  | 2 => honestNodes.flatMap (fun i =>
      honestNodes.map (fun v => .deliver v (head 0 i Block.genesis.root) 2))
  | 4 => honestNodes.flatMap (fun i =>
      honestNodes.map (fun v => .deliver v (ack 0 i Block.genesis.root) 4))
  | 9 => onX.map (fun v => .deliver v (prop 1 X) 9) ++
      onY.map (fun v => .deliver v (prop 1 Y) 9)
  | 10 => onY.map (fun v => .deliver v (prop 1 X) 10) ++
      onX.map (fun v => .deliver v (prop 1 Y) 10) ++
      honestNodes.flatMap (fun i => honestNodes.map (fun v =>
        .deliver v (head 1 i (if i.val < 3 then X.root else Y.root)) 10))
  | 17 => [.deliver 3 (prop 2 Z) 17]
  | _ => []
def rho : V2.D.Run (Fin 6) (pcsaWith .idle p unitCodec) :=
  { honest := {0, 1, 2, 3, 4}, horizon := 20,
    events := (List.range 21).flatMap (fun (t : Nat) =>
      (if t % 2 == 0 then honestNodes.map (fun v => V2.Event.tick v (t : Int)) else []) ++
        deliveries t),
    seatOf := seats, input := fun _ _ => () }
/-- Every fresh HEAD and ack committee uses the same identity map. -/
theorem fresh_committees :
    V2.D.CStar (pcsaFamilies p unitCodec).fresh rho := by
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | fg => exact hl.elim
    | head s => exact Function.bijective_id
    | ack s => exact Function.bijective_id

/-- The FG committee is fixed and linked. -/
theorem linked_committee :
    V2.D.Linked (pcsaFamilies p unitCodec).linked rho := by
  refine ⟨6, Equiv.refl (Fin 6), ?_⟩
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | head s => exact hl.elim
    | ack s => exact hl.elim
    | fg => exact ⟨rfl, fun _ => rfl⟩

/-- One faulty seat: `a = 1 < q_A = 3`. -/
theorem faults_below_qa : FaultsBelowQA p unitCodec rho := by
  rw [FaultsBelowQA_def]
  decide

abbrev node0 : Node p := ⟨initial p.n, RecordOnce.initial⟩
abbrev world (w : Array (Node p)) : Fin 6 → Node p := fun x => w.getD x.val node0
abbrev Run6 := V2.D.Run (Fin 6) (pcsaWith .idle p unitCodec)
abbrev FixtureEvent := V2.Event (Fin 6) (Obj p)
instance : DecidableEq (pcsaWith .idle p unitCodec).Object :=
  inferInstanceAs (DecidableEq (Obj p))
instance : DecidableEq FixtureEvent :=
  inferInstanceAs (DecidableEq (V2.Event (Fin 6) (Obj p)))
instance : BEq FixtureEvent := ⟨fun x y => decide (x = y)⟩

def cachedStep (r : Run6) (w : Array (Node p)) (e : V2.Event (Fin 6) (Obj p)) :
    Array (Node p) :=
  Array.ofFn (V2.D.World.step E r (world w) e)

/-- Materializing a finite world preserves the actual engine step at each node. -/
theorem cachedStep_exact (r : Run6) (w : Array (Node p)) (e : V2.Event (Fin 6) (Obj p))
    (x : Fin 6) : world (cachedStep r w e) x = V2.D.World.step E r (world w) e x := by
  have h (f : Fin 6 → Node p) : (Array.ofFn f).getD x.val node0 = f x := by
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_ofFn]; exact x.isLt)]
    exact Array.getElem_ofFn _
  exact h (V2.D.World.step E r (world w) e)

/-- Cached folds have the same semantics as the engine's event fold. -/
theorem cachedFold_exact (r : Run6) (es : List (V2.Event (Fin 6) (Obj p)))
    (w : Array (Node p)) :
    world (es.foldl (cachedStep r) w) = es.foldl (V2.D.World.step E r) (world w) := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih, funext (cachedStep_exact r w e)]
    rfl

def trace (r : Run6) : Array (Array (Node p)) :=
  (r.events.scanl (cachedStep r) (Array.replicate 6 node0)).toArray

def atIndex (tr : Array (Array (Node p))) (i : Nat) (x : Fin 6) : Node p :=
  world (tr.getD i #[]) x

def beforeTick (r : Run6) (tr : Array (Array (Node p))) (x : Fin 6) (t : Time) : Node p :=
  atIndex tr ((r.tickIdx? x t).getD 0) x

def readTick (r : Run6) (tr : Array (Array (Node p))) (x : Fin 6) (t : Time) : State 6 :=
  clock p (beforeTick r tr x t).st t

/-- Every cached trace entry is the exact event-indexed engine state. -/
theorem atIndex_trace_exact (r : Run6) (i : Nat) (hi : i ≤ r.events.length) (x : Fin 6) :
    atIndex (trace r) i x = V2.D.Run.stateBefore E r i x := by
  have hb : i < (trace r).size := by
    change i < (r.events.scanl (cachedStep r) (Array.replicate 6 node0)).toArray.size
    erw [List.size_toArray, List.length_scanl]
    exact Nat.lt_succ_of_le hi
  have hentry : (trace r).getD i #[] =
      (r.events.take i).foldl (cachedStep r) (Array.replicate 6 node0) := by
    rw [← Array.getElem_eq_getD (h := hb)]
    change (r.events.scanl (cachedStep r) (Array.replicate 6 node0)).toArray[i] = _
    erw [List.getElem_toArray, List.getElem_scanl]
    rfl
  have hinit : world (Array.replicate 6 node0) =
      (V2.D.World.init : V2.D.World (Fin 6) (pcsaWith .idle p unitCodec)) := by
    funext y
    change (Array.replicate 6 node0).getD y.val node0 = node0
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_replicate]; exact y.isLt),
      Array.getElem_replicate]
  change world ((trace r).getD i #[]) x = _
  erw [hentry, cachedFold_exact, hinit]
  rfl
/-- The cached HEAD read is exactly the claim reader whenever its tick exists. -/
theorem head_reader_eq_cached (r : Run6) (x : Fin 6) (s : Slot) (k : Nat)
    (hk : r.tickIdx? x (SA.voteTime p.toParams s) = some k) :
    voteHeadAt p unitCodec E r x s =
      some (headVote p (readTick r (trace r) x (SA.voteTime p.toParams s)) s) := by
  have hb : k ≤ r.events.length := Nat.le_of_lt
    (List.getElem?_eq_some_iff.mp (V2.D.Run.tickIdx?_spec hk)).1
  rw [pcsa_voteHeadAt_def, pcsa_postClock_def, pcsa_preTick_def, hk]
  delta readTick beforeTick
  rw [hk]
  change some (headVote p (clock p (V2.D.Run.stateBefore E r k x).st
    (SA.voteTime p.toParams s)) s) =
    some (headVote p (clock p (atIndex (trace r) k x).st (SA.voteTime p.toParams s)) s)
  erw [atIndex_trace_exact r k hb x]
/-- The cached raw gate read is exactly the claim reader whenever its tick exists. -/
theorem result_reader_eq_cached (r : Run6) (x : Fin 6) (s : Slot) (k : Nat)
    (hk : r.tickIdx? x (SA.gateTime p.toParams s) = some k) :
    gateResultAt p unitCodec E r x s = some
      (SA.Root.confirmationFrom p.toParams
        (eraseFG (readTick r (trace r) x (SA.gateTime p.toParams s)).fg.F)
        (actView (readTick r (trace r) x (SA.gateTime p.toParams s))) s) := by
  have hb : k ≤ r.events.length := Nat.le_of_lt
    (List.getElem?_eq_some_iff.mp (V2.D.Run.tickIdx?_spec hk)).1
  rw [pcsa_gateResultAt_def, pcsa_gateInAt_def, pcsa_preTick_def, hk]
  delta readTick beforeTick
  rw [hk]
  erw [atIndex_trace_exact r k hb x]
  exact congrArg some (pcsa_clock_confirmation_eq_pre p
    (V2.D.Run.stateBefore E r k x).st (SA.gateTime p.toParams s) s).symm

/-- The store after every event with time `≤ t` (`readAt`). -/
def readAtNode (r : Run6) (tr : Array (Array (Node p))) (x : Fin 6) (t : Time) : State 6 :=
  (atIndex tr (r.events.filter (fun e => decide (e.time ≤ t))).length x).st

/-- The signed objects that an object carries. A carried PC object has no
signer. -/
def carriedObjects (o : Obj p) : List (Obj p) :=
  match o.payload with
  | .proposal N => N.raw.map (ofHead p) ++ N.support.map (ofHead p) ++
      N.rows.map (ofRow p) ++ N.pcAcks.map (ofAck p)
  | .pc C => C.acks.map (ofAck p)
  | _ => []

/-- The signature check enumerates every signed object in the carries
relation; the other carried objects are PC objects, with no holder. -/
theorem carriedObjects_signed (o u : Obj p) :
    (pcsaWith .idle p unitCodec).carries o u → u ∈ carriedObjects o ∨ u.auth = .none := by
  change carriesS p o u → _
  delta carriesS carriedObjects
  rintro (h | ⟨C, rfl, -⟩)
  · left
    revert h
    cases o.payload <;> simp only [List.mem_append, List.not_mem_nil, imp_self]
    all_goals tauto
  · right
    rfl

/-- The carried PC test of `carriesS`. -/
def carriesPC (o : Obj p) (C : PC 6) : Bool :=
  match o.payload with
  | .ack _ => (C.acks.map (ofAck p)).contains o
  | .proposal N => (C.slot == N.erase.slot && C.target.root == N.erase.root) ||
      N.pc.any (fun d => d.slot == C.slot && d.target.root == C.target.root)
  | .pc c => c.slot == C.slot && c.target.root == C.target.root
  | _ => false

/-- The PCs that the call of `o` installs. -/
def installedBy (st : State 6) (o : Obj p) : List (PC 6) :=
  (PCSA.process p st (toWire p o)).pcs.filter (fun C => !st.pcs.contains C)

def handlesTest (st : State 6) (o u : Obj p) : Bool :=
  decide (o = u) || (match (toWire p o).decode with
  | some (.block s N) => namedParentHeld st N &&
      (match parentFG st N.erase with
      | some P => blockAccepted p st s N P &&
          (N.raw.map (ofHead p) ++ N.rows.map (ofRow p) ++ N.pcAcks.map (ofAck p)).contains u
      | none => false)
  | some (.pc C) => (C.acks.map (ofAck p)).contains u
  | _ => false) || (installedBy st o).any (fun C => decide (u = pcObj C) && carriesPC o C)

/-- A PC object is carried exactly when the carried PC test passes. -/
theorem carriesS_pcObj (o : Obj p) (C : PC 6) :
    carriesS p o (pcObj C) ↔ carriesPC o C = true := by
  delta carriesS carriesPC
  constructor
  · rintro (h | ⟨C', hC, h⟩)
    · exfalso
      revert h
      cases o.payload <;> simp only [List.mem_map, imp_self]
      all_goals first
        | (rintro (⟨a, -, ha⟩ | ⟨a, -, ha⟩ | ⟨a, -, ha⟩ | ⟨a, -, ha⟩) <;>
            cases congrArg (fun x : Obj p => x.payload) ha)
        | (rintro ⟨a, -, ha⟩; cases congrArg (fun x : Obj p => x.payload) ha)
    · cases hC
      revert h
      cases o.payload <;> simp [Option.any_eq_true]
  · intro h
    right
    refine ⟨C, rfl, ?_⟩
    revert h
    cases o.payload <;> simp [Option.any_eq_true]

/-- The finite handles test is the model's complete handles relation. -/
theorem handlesTest_exact (st : State 6) (o u : Obj p) :
    handlesS p st o u ↔ handlesTest st o u = true := by
  delta handlesS handlesTest
  simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc]
  refine or_congr Iff.rfl (or_congr ?_ ?_)
  · cases h : (toWire p o).decode with
    | none => simp only [Bool.false_eq_true]
    | some d =>
      cases d <;> simp only [Bool.false_eq_true]
      · rename_i s N
        cases hp : parentFG st N.erase with
        | none => simp only [Bool.and_false, Bool.false_eq_true, reduceCtorEq, false_and,
            exists_false, and_false]
        | some P =>
          simp only [Option.some.injEq, exists_eq_left', Bool.and_eq_true,
            List.contains_iff_mem, List.mem_append]
          tauto
      · simp only [List.contains_iff_mem]
  · constructor
    · rintro ⟨hc, C, rfl, h1, h2⟩
      refine List.any_eq_true.mpr ⟨C, List.mem_filter.mpr ⟨h1, by simpa using h2⟩, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨rfl, (carriesS_pcObj o C).mp hc⟩
    · intro h
      obtain ⟨C, hC, h'⟩ := List.any_eq_true.mp h
      rw [Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨rfl, hc⟩ := h'
      obtain ⟨h1, h2⟩ := List.mem_filter.mp hC
      exact ⟨(carriesS_pcObj o C).mpr hc, C, rfl, h1, by simpa using h2⟩

-- All acceptance handles are the parent, a carried object or an installed PC.
def handledObjects (st : State 6) (o : Obj p) : List (Obj p) :=
  (o :: carriedObjects o ++ (installedBy st o).map pcObj).filter (fun u => handlesTest st o u)

def emitted (r : Run6) (tr : Array (Array (Node p))) (i : Nat) : List (Obj p) :=
  match r.events[i]? with
  | some (.tick x t) => (V2.D.tick E r (atIndex tr i x) x t).2
  | _ => []

def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"Pending HEAD counterexample: {label} failed")
  IO.println s!"Pending HEAD counterexample: {label}: PASS"

/-- The healthy acceptance relay with cut `b₀`: every object accepted before
the cut is handled within `Δ = 2` at every honest node that has not
processed it. -/
def relayOK (r : Run6) (b₀ : Time) : Bool :=
  let es : Array FixtureEvent := r.events.toArray
  let tr := trace r
  let hs := honestNodes
  let is := List.range es.size
  let handlesBy := fun x o t => is.any (fun j =>
    match es.getD j (.tick 0 0) with
    | .deliver y a u => x == y && decide (t ≤ u ∧ u < t + E.Δ) &&
        handlesTest (atIndex tr j x).st a o
    | _ => false)
  let excluded := fun x o t =>
    let k := (es.toList.takeWhile (fun e => decide (e.time < t + E.Δ))).length
    excludesS p (atIndex tr k x).st o
  is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver y o t => (handledObjects (atIndex tr i y).st o).all (fun a =>
        if !processedS p (atIndex tr i y).st a && processedS p (atIndex tr (i + 1) y).st a then
          hs.all (fun x =>
            if !processedS p (atIndex tr (i + 1) x).st a && decide (t + E.Δ ≤ b₀) &&
                !excluded x a t then
              handlesBy x a t else true)
        else true)
    | _ => true)

/-- The delivery-premise checks of `Clean₂` with cut `b₀` (strict delivery
within `Δ = 2` of every emission and every acceptance before the cut, and
`a < h_j` for every label with `e_j ≤ b₀`). -/
def cleanChecks (rho : Run6) (b₀ : Time) : IO Unit := do
  let es : Array FixtureEvent := rho.events.toArray
  let tr := trace rho
  let hs := honestNodes
  let is := List.range es.size
  let emissions := is.flatMap (fun i =>
    let e := es.getD i (.tick 0 0)
    (emitted rho tr i).map (fun o => (e.node, o, e.time)))
  let handlesBy := fun x o t => is.any (fun j =>
    match es.getD j (.tick 0 0) with
    | .deliver y a u => x == y && decide (t ≤ u ∧ u < t + E.Δ) &&
        handlesTest (atIndex tr j x).st a o
    | _ => false)
  let excluded := fun x o t =>
    let k := (es.toList.takeWhile (fun e => decide (e.time < t + E.Δ))).length
    excludesS p (atIndex tr k x).st o
  require s!"healthy broadcast to b₀ = {b₀}" (emissions.all (fun row =>
    let (_, o, t) := row
    hs.all (fun x => if decide (t + E.Δ ≤ b₀) && !excluded x o t then handlesBy x o t else true)))
  require s!"healthy acceptance relay to b₀ = {b₀}" (relayOK rho b₀)
  require s!"labels a < h_j for e_j ≤ b₀ = {b₀}" ((List.range 5).all (fun j =>
    if decide (SA.earlyTime p.toParams j ≤ b₀) then
      decide (1 < (hs.filter (fun x => E.awake x (SA.voteTime p.toParams j) &&
        E.awake x (SA.earlyTime p.toParams j))).length)
    else true))
  require s!"cut 0 ≤ b₀ ≤ horizon = {b₀}" (decide (0 ≤ b₀ ∧ b₀ ≤ rho.horizon))

def auditRun (rho : Run6) : IO Unit := do
  let es : Array FixtureEvent := rho.events.toArray
  let tr := trace rho
  let hs := honestNodes
  let is := List.range es.size
  let states := List.range tr.size
  let emissions := is.flatMap (fun i =>
    let e := es.getD i (.tick 0 0)
    (emitted rho tr i).map (fun o => (e.node, o, e.time)))
  let hasEmission := fun u o t =>
    emissions.any (fun row => row.1 = u && row.2.1 == o && row.2.2 ≤ t)
  require "schedule" (decide ((rho.events : List FixtureEvent).Nodup) &&
    (es.toList.zip (es.toList.drop 1)).all (fun ef => decide (ef.1.key ≤ ef.2.key)) &&
    es.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ 20) && hs.contains e.node &&
      match e with | .restart .. => false | .tick _ t => decide (t % 2 = 0) | _ => true) &&
    (List.range 21).all (fun t => if t % 2 == 0 then
      hs.all (fun x => es.contains (.tick x (t : Int))) else true) )
  require "wire/dependencies/freshness" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver x o _ => (pcsaWith .idle p unitCodec).wellFormed o &&
        depsS p (atIndex tr i x).st o && !processedS p (atIndex tr i x).st o
    | _ => true))
  require "direct signatures" (es.all (fun e =>
    match e with
    | .deliver _ o t => hs.all (fun u =>
        if rho.holder o.auth == some u then hasEmission u o t else true)
    | _ => true))
  require "carried signatures" (es.all (fun e =>
    match e with
    | .deliver _ o t => (carriedObjects o).all (fun a => hs.all (fun u =>
        if rho.holder a.auth == some u then hasEmission u a t else true))
    | _ => true))
  let bodies := [.genesis, X, Y, Z]
  require "named root collision freedom" (
    es.all (fun e => match e with
      | .deliver _ o _ => match o.payload with
        | .proposal X => bodies.contains X
        | _ => true
      | _ => true) &&
    states.all (fun i => hs.all (fun x => (atIndex tr i x).st.namedBodies.all bodies.contains)) &&
    bodies.all (fun X => bodies.contains X.parent) &&
    bodies.all (fun X => bodies.all (fun Y => if X.root == Y.root then X == Y else true)))
  require "all emitted proposals are in the named scope" (emissions.all (fun row =>
    match row.2.1.payload with | .proposal N => bodies.contains N | _ => true))
  require "no PC is installed" (states.all (fun i => hs.all (fun x =>
    (atIndex tr i x).st.pcs.isEmpty)))
  require "stage-one frame" (states.all (fun i => hs.all (fun x =>
    let st := (atIndex tr i x).st
    st.fg.F == .genesis && (controls p st).Z == .genesis && (controls p st).lo == 0)))
  cleanChecks rho 12
  cleanChecks rho 18

def audit : IO Unit := do
  auditRun rho
  let tr := trace rho
  let v := readTick rho tr 3 18
  let g := readTick rho tr 0 20
  let H := headVote p v 2
  let R := SA.Root.confirmationFrom p.toParams (eraseFG g.fg.F) (actView g) 1
  require "both exact claim readers have their ticks"
    ((rho.tickIdx? 3 18).isSome && (rho.tickIdx? 0 20).isSome)
  require "cut and duty times" (decide (SA.earlyTime p.toParams 1 = 12 ∧
    SA.voteTime p.toParams 2 = 18 ∧ SA.gateTime p.toParams 1 = 20 ∧ (17 : Time) + E.Δ > 18))
  require "source denominator is 5 and X support is 3" (decide
    (GridCO.voterCount (GridCO.lateVotes p.toParams.engine (actView g) 1) = 5 ∧
      SA.Root.prefixSupport p.toParams (actView g) 1 X.erase = 3))
  require "target has 6 voters and X is ineligible" (decide
    (GridCO.voterCount (headVotes p v 2) = 6) &&
    !eligible p v (headVotes p v 2) (headSupport p v 2) X.erase)
  require "HEAD at node 3, label 2, is Z" (H == Z.erase)
  require "result at node 0, label 1, is X" (R == some X.erase)
  require "past-cut HEAD timing" (decide ((12 : Time) < SA.voteTime p.toParams 2 ∧
    SA.earlyTime p.toParams 1 ≤ 12))
  require "X is not a prefix of Z" (!Block.preceq X.erase H)
  IO.println s!"Pending HEAD counterexample: events={rho.events.length}; honest=5; faults=1;
    cuts=12,18"

#eval audit
#print axioms fresh_committees
#print axioms linked_committee
#print axioms faults_below_qa
#print axioms cachedStep_exact
#print axioms cachedFold_exact
#print axioms atIndex_trace_exact
#print axioms head_reader_eq_cached
#print axioms result_reader_eq_cached
#print axioms carriedObjects_signed
#print axioms carriesS_pcObj
#print axioms handlesTest_exact
end AvailableChain.PCSA.Run.Tests.PendingHeadCounterexample
end
