module
public import AvailableChainPCSAProofs
public meta import AvailableChainPCSAProofs -- shake: keep (closed run evaluation)

@[expose] public section

/-! Regression for the PC relay (pcsa34-r4.3 §5.2.3): an honest node relays a
PC it installs as a whole certificate. The run is the ARM relay run. Four
honest nodes and one faulty seat 4 (`a = 1 < q_A = 3`). Seat 4 proposes `B`
at slot 1, and the five HEADs of slot 1 are on `B`. Only nodes 0 and 1 are
awake at `e_1`, so only they ack `B`. Seat 4 acks `B` to nodes 0 and 1, and
acks two unresolved roots to nodes 2 and 3 first. Nodes 0 and 1 assemble
`PC(1, B)` at `T = e_1 = 6`; the ack call that installs it handles the PC
object, so the healthy acceptance relay obliges a delivery of `PC(1, B)` to
nodes 2 and 3 within `Δ`. The run delivers it at `6`. `poolAck` refuses the
relayed faulty ack at nodes 2 and 3 (seat cap), but the whole PC pools its
acks raw, so nodes 2 and 3 install `PC(1, B)` at `6` and their strong output
is `B` from then on. A control without the PC deliveries fails the healthy
acceptance relay check: the relay obligation is in the model.
Fabricated target: in a second run, seat 4's ack on `B` reaches nodes 0 and
1 only inside a faulty PC whose target `T' ≠ B` has the root and slot of `B`.
The PC call pools the ack raw and installs `PC(1, B)` (collection resolves
the root to `B`). The PC tests of `carriesS` read the target root, so that
call handles `PC(1, B)` and the relay obliges its delivery to nodes 2 and 3;
an exact-target test would not.
Carried PC: at node 2 of the control run without the relay (it holds `B` and
the acks of seats 0 and 1, and no PC), a slot-2 proposal that carries the
faulty PC on `T'` completes the ack quorum, so its call installs `PC(1, B)`
and handles its object. Controls: a carried PC with another slot, or with
another root, is not carried and does not install `PC(1, B)`.
This is a Lean run witness checked by evaluation over the actual engine. -/

open AvailableChain AvailableChain.PCSA AvailableChain.PCSA.Run AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run.Tests.PcRelayRegression
abbrev p : Params :=
  { Δ := 1, n := 5, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide,
    digest := fun d => if d.slot = 1 then ⟨1⟩ else ⟨3⟩ }
def B : NamedProposal 5 := namedProposal p .genesis 1 0 [] [] [] none
def prop (s : Nat) (N : NamedProposal 5) : Obj p :=
  ⟨.seat (.prop s) ⟨0, by change 0 < 1; decide⟩, .proposal N⟩
def head (s : Nat) (i : Fin 5) (root : BlockId) : Obj p :=
  ⟨.seat (.base (.head s)) i, .head root⟩
def ack (s : Nat) (i : Fin 5) (root : BlockId) : Obj p :=
  ⟨.seat (.base (.ack s)) i, .ack root⟩
def r1 : BlockId := ⟨99⟩
def r2 : BlockId := ⟨100⟩
/-- `PC(1, B)` as nodes 0 and 1 assemble it: the first ack of each seat on
`B`, in receipt order. -/
def pcB : PC 5 :=
  ⟨1, B.erase, [⟨.seat (.ack 1) 0, B.root⟩, ⟨.seat (.ack 1) 1, B.root⟩,
    ⟨.seat (.ack 1) 4, B.root⟩]⟩
def pcObj (C : PC 5) : Obj p := ⟨.none, .pc C⟩
/-- A fabricated target: the slot and root of `B`, another body. -/
def fakeB : Block := .node .genesis 1 B.root 77777
/-- A faulty PC on `fakeB` with the acks of `pcB`. -/
def pcFake : PC 5 := ⟨1, fakeB, pcB.acks⟩
/-- A slot-2 proposal on `B` that carries the PC `d`. -/
def N2 (d : PC 5) : NamedProposal 5 := namedProposal p B 2 0 [] [] [] (some d)
/-- Mismatched slot: a slot-2 PC on a target with the root of `B`. -/
def pcSlot : PC 5 :=
  ⟨2, .node B.erase 2 B.root 88888, [⟨.seat (.ack 2) 0, B.root⟩, ⟨.seat (.ack 2) 1, B.root⟩,
    ⟨.seat (.ack 2) 4, B.root⟩]⟩
/-- Mismatched root: a slot-1 PC on a target with another root. -/
def pcRoot : PC 5 :=
  ⟨1, .node .genesis 1 ⟨55⟩ 55555, [⟨.seat (.ack 1) 0, ⟨55⟩⟩, ⟨.seat (.ack 1) 1, ⟨55⟩⟩,
    ⟨.seat (.ack 1) 4, ⟨55⟩⟩]⟩
def E : Generic.Env (Fin 5) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 20, t_GST_nonneg := by decide,
    awake := fun v t =>
      if v = 0 ∨ v = 1 then decide (t = 1 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 9 ∨ t = 10)
      else decide (t = 5) }
def seats : (l : RunLabel) → Fin (RunLabel.seats p l) → Fin 5
  | .prop _, _ => 4
  | .base _, i => i

def honestNodes : List (Fin 5) := [0, 1, 2, 3]
def ackers : List (Fin 5) := [0, 1]
def others : List (Fin 5) := [2, 3]
def allSeats : List (Fin 5) := [0, 1, 2, 3, 4]

def deliveries (fake relay : Bool) (t : Nat) : List (V2.Event (Fin 5) (Obj p)) :=
  match t with
  | 1 => ackers.flatMap (fun i =>
      honestNodes.map (fun v => .deliver v (head 0 i Block.genesis.root) 1))
  | 4 => honestNodes.map (fun v => .deliver v (prop 1 B) 4)
  | 5 => allSeats.flatMap (fun i => honestNodes.map (fun v => .deliver v (head 1 i B.root) 5))
  | 6 => others.flatMap (fun v => [.deliver v (ack 1 4 r1) 6, .deliver v (ack 1 4 r2) 6]) ++
      ackers.flatMap (fun i => honestNodes.map (fun v => .deliver v (ack 1 i B.root) 6)) ++
      (if fake then ackers.map (fun v => .deliver v (pcObj pcFake) 6)
        else ackers.map (fun v => .deliver v (ack 1 4 B.root) 6)) ++
      others.map (fun v => .deliver v (ack 1 4 B.root) 6) ++
      ackers.flatMap (fun v => [.deliver v (ack 1 4 r1) 6, .deliver v (ack 1 4 r2) 6]) ++
      (if relay then others.map (fun v => .deliver v (pcObj pcB) 6) else [])
  | 9 => ackers.flatMap (fun i => honestNodes.map (fun v => .deliver v (head 2 i B.root) 9))
  | _ => []
def runWith (fake relay : Bool) : V2.D.Run (Fin 5) (pcsaWith .idle p unitCodec) :=
  { honest := {0, 1, 2, 3}, horizon := 14,
    events := (List.range 15).flatMap (fun (t : Nat) =>
      honestNodes.map (fun v => V2.Event.tick v (t : Int)) ++ deliveries fake relay t),
    seatOf := seats, input := fun _ _ => () }
/-- The run with the PC relayed. -/
def rho : V2.D.Run (Fin 5) (pcsaWith .idle p unitCodec) := runWith false true
/-- The control run without the PC deliveries. -/
def rhoNoRelay : V2.D.Run (Fin 5) (pcsaWith .idle p unitCodec) := runWith false false
/-- The fabricated-target run with the PC relayed. -/
def rhoFake : V2.D.Run (Fin 5) (pcsaWith .idle p unitCodec) := runWith true true
/-- The fabricated-target control run without the PC deliveries. -/
def rhoFakeNoRelay : V2.D.Run (Fin 5) (pcsaWith .idle p unitCodec) := runWith true false

/-- Every fresh HEAD and ack committee uses the same identity map. -/
theorem fresh_committees (fake relay : Bool) :
    V2.D.CStar (pcsaFamilies p unitCodec).fresh (runWith fake relay) := by
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | fg => exact hl.elim
    | head s => exact Function.bijective_id
    | ack s => exact Function.bijective_id

/-- The FG committee is fixed and linked. -/
theorem linked_committee (fake relay : Bool) :
    V2.D.Linked (pcsaFamilies p unitCodec).linked (runWith fake relay) := by
  refine ⟨5, Equiv.refl (Fin 5), ?_⟩
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | head s => exact hl.elim
    | ack s => exact hl.elim
    | fg => exact ⟨rfl, fun _ => rfl⟩

/-- One faulty seat: `a = 1 < q_A = 3`. -/
theorem faults_below_qa (fake relay : Bool) : FaultsBelowQA p unitCodec (runWith fake relay) := by
  rw [FaultsBelowQA_def]
  cases fake <;> cases relay <;> decide

abbrev node0 : Node p := ⟨initial p.n, RecordOnce.initial⟩
abbrev world (w : Array (Node p)) : Fin 5 → Node p := fun x => w.getD x.val node0
abbrev Run5 := V2.D.Run (Fin 5) (pcsaWith .idle p unitCodec)
abbrev FixtureEvent := V2.Event (Fin 5) (Obj p)
instance : DecidableEq (pcsaWith .idle p unitCodec).Object :=
  inferInstanceAs (DecidableEq (Obj p))
instance : DecidableEq FixtureEvent :=
  inferInstanceAs (DecidableEq (V2.Event (Fin 5) (Obj p)))
instance : BEq FixtureEvent := ⟨fun x y => decide (x = y)⟩

def cachedStep (r : Run5) (w : Array (Node p)) (e : V2.Event (Fin 5) (Obj p)) :
    Array (Node p) :=
  Array.ofFn (V2.D.World.step E r (world w) e)

/-- Materializing a finite world preserves the actual engine step at each node. -/
theorem cachedStep_exact (r : Run5) (w : Array (Node p)) (e : V2.Event (Fin 5) (Obj p))
    (x : Fin 5) : world (cachedStep r w e) x = V2.D.World.step E r (world w) e x := by
  have h (f : Fin 5 → Node p) : (Array.ofFn f).getD x.val node0 = f x := by
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_ofFn]; exact x.isLt)]
    exact Array.getElem_ofFn _
  exact h (V2.D.World.step E r (world w) e)

/-- Cached folds have the same semantics as the engine's event fold. -/
theorem cachedFold_exact (r : Run5) (es : List (V2.Event (Fin 5) (Obj p)))
    (w : Array (Node p)) :
    world (es.foldl (cachedStep r) w) = es.foldl (V2.D.World.step E r) (world w) := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih, funext (cachedStep_exact r w e)]
    rfl

def trace (r : Run5) : Array (Array (Node p)) :=
  r.events.foldl (fun acc e =>
    acc.push (cachedStep r (acc.getD (acc.size - 1) #[]) e)) #[Array.replicate 5 node0]

def atIndex (tr : Array (Array (Node p))) (i : Nat) (x : Fin 5) : Node p :=
  world (tr.getD i #[]) x

def beforeTick (r : Run5) (tr : Array (Array (Node p))) (x : Fin 5) (t : Time) : Node p :=
  atIndex tr ((r.tickIdx? x t).getD 0) x

def readTick (r : Run5) (tr : Array (Array (Node p))) (x : Fin 5) (t : Time) : State 5 :=
  clock p (beforeTick r tr x t).st t

/-- The store after every event with time `≤ t` (`readAt`). -/
def readAtNode (r : Run5) (tr : Array (Array (Node p))) (x : Fin 5) (t : Time) : State 5 :=
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
def carriesPC (o : Obj p) (C : PC 5) : Bool :=
  match o.payload with
  | .ack _ => (C.acks.map (ofAck p)).contains o
  | .proposal N => (C.slot == N.erase.slot && C.target.root == N.erase.root) ||
      N.pc.any (fun d => d.slot == C.slot && d.target.root == C.target.root)
  | .pc c => c.slot == C.slot && c.target.root == C.target.root
  | _ => false

/-- The exact-target PC test (43733fe), for the control. -/
def carriesPCExact (o : Obj p) (C : PC 5) : Bool :=
  match o.payload with
  | .ack _ => (C.acks.map (ofAck p)).contains o
  | .proposal N => C.target == N.erase ||
      N.pc.any (fun d => d.slot == C.slot && d.target == C.target)
  | .pc c => c.slot == C.slot && c.target == C.target
  | _ => false

/-- The PCs that the call of `o` installs. -/
def installedBy (st : State 5) (o : Obj p) : List (PC 5) :=
  (PCSA.process p st (toWire p o)).pcs.filter (fun C => !st.pcs.contains C)

def handlesTest (st : State 5) (o u : Obj p) : Bool :=
  decide (o = u) || (match (toWire p o).decode with
  | some (.block s N) => namedParentHeld st N &&
      (match parentFG st N.erase with
      | some P => blockAccepted p st s N P &&
          (N.raw.map (ofHead p) ++ N.rows.map (ofRow p) ++ N.pcAcks.map (ofAck p)).contains u
      | none => false)
  | some (.pc C) => (C.acks.map (ofAck p)).contains u
  | _ => false) || (installedBy st o).any (fun C => decide (u = pcObj C) && carriesPC o C)

/-- A PC object is carried exactly when the carried PC test passes. -/
theorem carriesS_pcObj (o : Obj p) (C : PC 5) :
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
theorem handlesTest_exact (st : State 5) (o u : Obj p) :
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
def handledObjects (st : State 5) (o : Obj p) : List (Obj p) :=
  (o :: carriedObjects o ++ (installedBy st o).map pcObj).filter (fun u => handlesTest st o u)

def emitted (r : Run5) (tr : Array (Array (Node p))) (i : Nat) : List (Obj p) :=
  match r.events[i]? with
  | some (.tick x t) => (V2.D.tick E r (atIndex tr i x) x t).2
  | _ => []

def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"PC relay regression: {label} failed")
  IO.println s!"PC relay regression: {label}: PASS"

/-- The healthy acceptance relay with cut `b₀`: every object accepted before
the cut is handled within `Δ = 1` at every honest node that has not
processed it. -/
def relayOK (r : Run5) (b₀ : Time) : Bool :=
  let es : Array FixtureEvent := r.events.toArray
  let tr := trace r
  let hs := honestNodes
  let is := List.range es.size
  let handlesBy := fun x o t => is.any (fun j =>
    match es.getD j (.tick 0 0) with
    | .deliver y a u => x == y && decide (t ≤ u ∧ u < t + 1) &&
        handlesTest (atIndex tr j x).st a o
    | _ => false)
  let excluded := fun x o t =>
    let k := (es.toList.takeWhile (fun e => decide (e.time < t + 1))).length
    excludesS p (atIndex tr k x).st o
  is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver y o t => (handledObjects (atIndex tr i y).st o).all (fun a =>
        if !processedS p (atIndex tr i y).st a && processedS p (atIndex tr (i + 1) y).st a then
          hs.all (fun x =>
            if !processedS p (atIndex tr (i + 1) x).st a && decide (t + 1 ≤ b₀) &&
                !excluded x a t then
              handlesBy x a t else true)
        else true)
    | _ => true)

/-- The delivery-premise checks of `Clean₂` with cut `b₀` (strict delivery
within `Δ = 1` of every emission and every acceptance before the cut, and
`a < h_j` for every label with `e_j ≤ b₀`). -/
def cleanChecks (rho : Run5) (b₀ : Time) : IO Unit := do
  let es : Array FixtureEvent := rho.events.toArray
  let tr := trace rho
  let hs := honestNodes
  let is := List.range es.size
  let emissions := is.flatMap (fun i =>
    let e := es.getD i (.tick 0 0)
    (emitted rho tr i).map (fun o => (e.node, o, e.time)))
  let handlesBy := fun x o t => is.any (fun j =>
    match es.getD j (.tick 0 0) with
    | .deliver y a u => x == y && decide (t ≤ u ∧ u < t + 1) &&
        handlesTest (atIndex tr j x).st a o
    | _ => false)
  let excluded := fun x o t =>
    let k := (es.toList.takeWhile (fun e => decide (e.time < t + 1))).length
    excludesS p (atIndex tr k x).st o
  require s!"healthy broadcast to b₀ = {b₀}" (emissions.all (fun row =>
    let (_, o, t) := row
    hs.all (fun x => if decide (t + 1 ≤ b₀) && !excluded x o t then handlesBy x o t else true)))
  require s!"healthy acceptance relay to b₀ = {b₀}" (relayOK rho b₀)
  require s!"labels a < h_j for e_j ≤ b₀ = {b₀}" ((List.range 5).all (fun j =>
    if decide (SA.earlyTime p.toParams j ≤ b₀) then
      decide (1 < (hs.filter (fun x => E.awake x (SA.voteTime p.toParams j) &&
        E.awake x (SA.earlyTime p.toParams j))).length)
    else true))
  require s!"cut 0 ≤ b₀ ≤ horizon = {b₀}" (decide (0 ≤ b₀ ∧ b₀ ≤ rho.horizon))

def auditRun (rho : Run5) : IO Unit := do
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
    es.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ 14) && hs.contains e.node &&
      match e with | .restart .. => false | _ => true) &&
    (List.range 15).all (fun t => hs.all (fun x => es.contains (.tick x (t : Int)))) )
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
  let bodies := [.genesis, B]
  require "named root collision freedom" (
    es.all (fun e => match e with
      | .deliver _ o _ => match o.payload with
        | .proposal X => bodies.contains X
        | _ => true
      | _ => true) &&
    states.all (fun i => hs.all (fun x => (atIndex tr i x).st.namedBodies.all bodies.contains)) &&
    bodies.all (fun X => bodies.contains X.parent) &&
    bodies.all (fun X => bodies.all (fun Y => if X.root == Y.root then X == Y else true)))
  require "stage-one frame" (states.all (fun i => hs.all (fun x =>
    let st := (atIndex tr i x).st
    st.fg.F == .genesis && (controls p st).Z == .genesis && (controls p st).lo == 0)))
  cleanChecks rho 9
  cleanChecks rho 10

def audit : IO Unit := do
  auditRun rho
  let es : Array FixtureEvent := rho.events.toArray
  let tr := trace rho
  let is := List.range es.size
  require "v = 0 holds PC(1, B) at T = 6, as assembled" (
    (readAtNode rho tr 0 6).pcs == [pcB] && strong (readAtNode rho tr 0 6) == B.erase)
  require "the ack call of v = 0 that installs PC(1, B) handles and accepts the PC object" (
    is.any (fun i => match es.getD i (.tick 0 0) with
      | .deliver 0 o 6 => handlesTest (atIndex tr i 0).st o (pcObj pcB) &&
          !processedS p (atIndex tr i 0).st (pcObj pcB) &&
          processedS p (atIndex tr (i + 1) 0).st (pcObj pcB)
      | _ => false))
  require "y = 2 refuses the relayed faulty ack through the seat cap" (
    is.any (fun i => es.getD i (.tick 0 0) == .deliver 2 (ack 1 4 B.root) 6 &&
      seatAcks (atIndex tr i 2).st 1 4 == [r1, r2] &&
      !(atIndex tr (i + 1) 2).st.ackPool.contains ⟨.seat (.ack 1) 4, B.root⟩))
  require "y = 2 and y = 3 install PC(1, B) within Δ of T = 6" (others.all (fun y =>
    (readAtNode rho tr y 6).pcs.any (fun C => C.slot == 1 && C.target == B.erase)))
  require "C8 conclusion holds at y = 2, 3 from T + Δ to the horizon" (others.all (fun y =>
    (List.range 8).all (fun j => Block.preceq B.erase (strong (readAtNode rho tr y (7 + j))))))
  require "control: without the PC deliveries the acceptance relay fails" (
    !relayOK rhoNoRelay 9 && !relayOK rhoNoRelay 10)
  IO.println s!"PC relay regression: events={es.size}; honest=4; faults=1"

def auditFake : IO Unit := do
  auditRun rhoFake
  let es : Array FixtureEvent := rhoFake.events.toArray
  let tr := trace rhoFake
  let is := List.range es.size
  require "fake: T' ≠ B with the slot and root of B, and PC(T') is well formed" (
    fakeB != B.erase && fakeB.root == B.erase.root && fakeB.slot == B.erase.slot &&
      pcFake.wellFormed)
  require "fake: v = 0 holds PC(1, B), not PC(1, T'), at T = 6" (
    (readAtNode rhoFake tr 0 6).pcs == [pcB] && strong (readAtNode rhoFake tr 0 6) == B.erase)
  require "fake: the PC call of v = 0 installs PC(1, B) and handles and accepts its object" (
    is.any (fun i => match es.getD i (.tick 0 0) with
      | .deliver 0 o 6 => o == pcObj pcFake &&
          handlesTest (atIndex tr i 0).st o (pcObj pcB) &&
          !processedS p (atIndex tr i 0).st (pcObj pcB) &&
          processedS p (atIndex tr (i + 1) 0).st (pcObj pcB)
      | _ => false))
  require "fake: the PC object of T' is not accepted at v = 0" (
    !processedS p (readAtNode rhoFake tr 0 14) (pcObj pcFake))
  require "fake control: the exact-target test does not carry PC(1, B)" (
    !carriesPCExact (pcObj pcFake) pcB && carriesPC (pcObj pcFake) pcB)
  require "fake: y = 2 refuses the relayed faulty ack through the seat cap" (
    is.any (fun i => es.getD i (.tick 0 0) == .deliver 2 (ack 1 4 B.root) 6 &&
      seatAcks (atIndex tr i 2).st 1 4 == [r1, r2] &&
      !(atIndex tr (i + 1) 2).st.ackPool.contains ⟨.seat (.ack 1) 4, B.root⟩))
  require "fake: y = 2 and y = 3 install PC(1, B) within Δ of T = 6" (others.all (fun y =>
    (readAtNode rhoFake tr y 6).pcs.any (fun C => C.slot == 1 && C.target == B.erase)))
  require "fake: C8 conclusion holds at y = 2, 3 from T + Δ to the horizon" (others.all (fun y =>
    (List.range 8).all (fun j =>
      Block.preceq B.erase (strong (readAtNode rhoFake tr y (7 + j))))))
  require "fake control: without the PC deliveries the acceptance relay fails" (
    !relayOK rhoFakeNoRelay 9 && !relayOK rhoFakeNoRelay 10)
  IO.println s!"PC relay regression (fabricated target): events={es.size}"

def auditCarry : IO Unit := do
  let tr := trace rhoNoRelay
  let st := readAtNode rhoNoRelay tr 2 9
  require "carry: y = 2 holds B and no PC at t = 9 without the relay" (
    st.pcs.isEmpty && st.base.blocks.contains B.erase)
  let o := prop 2 (N2 pcFake)
  require "carry: the slot-2 proposal carrying PC(T') is accepted" (
    processedS p (PCSA.process p st (toWire p o)) o)
  require "carry: its call installs PC(1, B) and handles the PC object" (
    installedBy st o == [pcB] && handlesTest st o (pcObj pcB))
  require "carry control: the exact-target test does not carry PC(1, B)" (
    !carriesPCExact o pcB && carriesPC o pcB)
  for (label, d) in [("slot", pcSlot), ("root", pcRoot)] do
    let o := prop 2 (N2 d)
    require s!"carry control ({label}): the carried PC is well formed and accepted" (
      d.wellFormed && processedS p (PCSA.process p st (toWire p o)) o)
    require s!"carry control ({label}): PC(1, B) is not carried, installed or handled" (
      !carriesPC o pcB && !(installedBy st o).contains pcB && !handlesTest st o (pcObj pcB))

#eval audit
#eval auditFake
#eval auditCarry
#print axioms cachedStep_exact
#print axioms carriedObjects_signed
#print axioms carriesS_pcObj
#print axioms handlesTest_exact
#print axioms cachedFold_exact
#print axioms fresh_committees
#print axioms linked_committee
#print axioms faults_below_qa

end AvailableChain.PCSA.Run.Tests.PcRelayRegression
end
