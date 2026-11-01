module
public import AvailableChainPCSAProofs
public meta import AvailableChainPCSAProofs -- shake: keep (closed run evaluation)

@[expose] public section

/-! Regression for Formation whole-PC relay (pcsa34-r4.3 §5.2.3).
The old schedule has a PC at node 6 that other honest nodes do not hold.
It fails the current F1 acceptance relay check and is a negative control.
A repaired schedule delivers the complete PC before the slot-4 proposal.
The honest proposer then chooses B as the parent and carries the old PC.
Six honest nodes vote on its child. All seven honest nodes ack it at e_4,
including node 6, which is asleep at v_4. The current PC and source follow.
Both schedules use the actual engine and the corrected F4 condition.
This test does not assert a kernel theorem of negated FormationClaim. -/

open AvailableChain AvailableChain.PCSA AvailableChain.PCSA.Run AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run.Tests.FormationAckCounterexample
abbrev p : Params :=
  { Δ := 1, n := 8, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide,
    digest := fun d => if d.slot = 1 then ⟨1⟩ else if d.slot = 3 then ⟨2⟩ else ⟨3⟩ }
def B : NamedProposal 8 := namedProposal p .genesis 1 0 [] [] [] none
def A : NamedProposal 8 := namedProposal p .genesis 3 0 [] [] [] none
def prop (s : Nat) (N : NamedProposal 8) : Obj p :=
  ⟨.seat (.prop s) ⟨0, by change 0 < 1; decide⟩, .proposal N⟩
def head (s : Nat) (i : Fin 8) (N : NamedProposal 8) : Obj p :=
  ⟨.seat (.base (.head s)) i, .head N.root⟩
def ack (s : Nat) (i : Fin 8) (root : BlockId) : Obj p :=
  ⟨.seat (.base (.ack s)) i, .ack root⟩
def E : Generic.Env (Fin 8) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 15, t_GST_nonneg := by decide,
    awake := fun v t =>
      if v = 6 then decide (t = 6 ∨ t = 18)
      else if v = 5 then decide (t = 13 ∨ t = 17 ∨ t = 18)
      else if v = 0 then decide (t = 5 ∨ t = 13 ∨ t = 16 ∨ t = 17 ∨ t = 18)
      else decide (t = 5 ∨ ((v = 1 ∨ v = 2) ∧ t = 6) ∨ t = 13 ∨ t = 17 ∨ t = 18) }
def seats : (l : RunLabel) → Fin (RunLabel.seats p l) → Fin 8
  | .prop s, _ => if s = 4 then 0 else 7
  | .base _, i => i

def honestNodes : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6]
def participants : List (Fin 8) := [0, 1, 2, 3, 4, 5]
def firstHeads : List (Fin 8) := [0, 1, 2, 3, 4, 7]
def firstAcks : List (Fin 8) := [1, 2, 6]
def raw3 : List (HeadWire 8) := participants.map (fun i => ⟨.seat (.head 3) i, A.root⟩)
def N : NamedProposal 8 := namedProposal p A 4 0 raw3 raw3 [] none
def C : PC 8 := ⟨1, B.erase,
  [⟨.seat (.ack 1) 1, B.root⟩, ⟨.seat (.ack 1) 2, B.root⟩,
   ⟨.seat (.ack 1) 6, B.root⟩, ⟨.seat (.ack 1) 7, B.root⟩]⟩
def oldPC : Obj p := ⟨.none, .pc C⟩

def deliveries (t : Nat) : List (V2.Event (Fin 8) (Obj p)) :=
  match t with
  | 4 => honestNodes.map (fun v => .deliver v (prop 1 B) 4) ++
      participants.flatMap (fun v =>
        [.deliver v (ack 1 7 ⟨99⟩) 4, .deliver v (ack 1 7 ⟨100⟩) 4])
  | 5 => firstHeads.flatMap (fun i => honestNodes.map (fun v => .deliver v (head 1 i B) 5))
  | 6 => firstAcks.flatMap (fun i => honestNodes.map (fun v => .deliver v (ack 1 i B.root) 6)) ++
      ([6, 0, 1, 2, 3, 4, 5] : List (Fin 8)).map (fun v => .deliver v (ack 1 7 B.root) 6)
  | 12 => honestNodes.map (fun v => .deliver v (prop 3 A) 12)
  | 13 => participants.flatMap (fun i => honestNodes.map (fun v => .deliver v (head 3 i A) 13))
  | 15 => [.deliver 6 (ack 1 7 ⟨99⟩) 15, .deliver 6 (ack 1 7 ⟨100⟩) 15]
  | 16 => honestNodes.map (fun v => .deliver v (prop 4 N) 16)
  | 17 => participants.flatMap (fun i => honestNodes.map (fun v => .deliver v (head 4 i N) 17))
  | 18 => participants.flatMap (fun i => honestNodes.map (fun v => .deliver v (ack 4 i N.root) 18))
  | _ => []
def rho : V2.D.Run (Fin 8) (pcsaWith .idle p unitCodec) :=
  { honest := {0, 1, 2, 3, 4, 5, 6}, horizon := 22,
    events := (List.range 23).flatMap (fun (t : Nat) =>
      honestNodes.map (fun v => V2.Event.tick v (t : Int)) ++ deliveries t),
    seatOf := seats, input := fun _ _ => () }

/-- Every fresh HEAD and ack committee uses the same identity map. -/
theorem fresh_committees : V2.D.CStar (pcsaFamilies p unitCodec).fresh rho := by
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | fg => exact hl.elim
    | head s => exact Function.bijective_id
    | ack s => exact Function.bijective_id

/-- The FG committee is fixed and linked. -/
theorem linked_committee : V2.D.Linked (pcsaFamilies p unitCodec).linked rho := by
  refine ⟨8, Equiv.refl (Fin 8), ?_⟩
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | head s => exact hl.elim
    | ack s => exact hl.elim
    | fg => exact ⟨rfl, fun _ => rfl⟩

abbrev node0 : Node p := ⟨initial p.n, RecordOnce.initial⟩
abbrev world (w : Array (Node p)) : Fin 8 → Node p := fun x => w.getD x.val node0

def cachedStep (w : Array (Node p)) (e : V2.Event (Fin 8) (Obj p)) : Array (Node p) :=
  Array.ofFn (V2.D.World.step E rho (world w) e)

/-- Materializing a finite world preserves the actual engine step at each node. -/
theorem cachedStep_exact (w : Array (Node p)) (e : V2.Event (Fin 8) (Obj p)) (x : Fin 8) :
    world (cachedStep w e) x = V2.D.World.step E rho (world w) e x := by
  have h (f : Fin 8 → Node p) : (Array.ofFn f).getD x.val node0 = f x := by
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_ofFn]; exact x.isLt)]
    exact Array.getElem_ofFn _
  exact h (V2.D.World.step E rho (world w) e)

/-- Cached folds have the same semantics as the engine's event fold. -/
theorem cachedFold_exact (es : List (V2.Event (Fin 8) (Obj p))) (w : Array (Node p)) :
    world (es.foldl cachedStep w) = es.foldl (V2.D.World.step E rho) (world w) := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih, funext (cachedStep_exact w e)]
    rfl

def trace : Array (Array (Node p)) :=
  rho.events.foldl (fun acc e =>
    acc.push (cachedStep (acc.getD (acc.size - 1) #[]) e)) #[Array.replicate 8 node0]

def atIndex (tr : Array (Array (Node p))) (i : Nat) (x : Fin 8) : Node p :=
  world (tr.getD i #[]) x

def beforeTick (tr : Array (Array (Node p))) (x : Fin 8) (t : Time) : Node p :=
  atIndex tr ((rho.tickIdx? x t).getD 0) x

def readTick (tr : Array (Array (Node p))) (x : Fin 8) (t : Time) : State 8 :=
  clock p (beforeTick tr x t).st t

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

abbrev FixtureEvent := V2.Event (Fin 8) (Obj p)
instance : DecidableEq (pcsaWith .idle p unitCodec).Object :=
  inferInstanceAs (DecidableEq (Obj p))
instance : DecidableEq FixtureEvent :=
  inferInstanceAs (DecidableEq (V2.Event (Fin 8) (Obj p)))
instance : BEq FixtureEvent := ⟨fun x y => decide (x = y)⟩

def pcObj (C : PC 8) : Obj p := ⟨.none, .pc C⟩

/-- The carried PC test of `carriesS`. -/
def carriesPC (o : Obj p) (C : PC 8) : Bool :=
  match o.payload with
  | .ack _ => (C.acks.map (ofAck p)).contains o
  | .proposal N => (C.slot == N.erase.slot && C.target.root == N.erase.root) ||
      N.pc.any (fun d => d.slot == C.slot && d.target.root == C.target.root)
  | .pc c => c.slot == C.slot && c.target.root == C.target.root
  | _ => false

/-- The PCs that the call of `o` installs. -/
def installedBy (st : State 8) (o : Obj p) : List (PC 8) :=
  (PCSA.process p st (toWire p o)).pcs.filter (fun C => !st.pcs.contains C)

def handlesTest (st : State 8) (o u : Obj p) : Bool :=
  decide (o = u) || (match (toWire p o).decode with
  | some (.block s N) => namedParentHeld st N &&
      (match parentFG st N.erase with
      | some P => blockAccepted p st s N P &&
          (N.raw.map (ofHead p) ++ N.rows.map (ofRow p) ++ N.pcAcks.map (ofAck p)).contains u
      | none => false)
  | some (.pc C) => (C.acks.map (ofAck p)).contains u
  | _ => false) || (installedBy st o).any (fun C => decide (u = pcObj C) && carriesPC o C)

/-- A PC object is carried exactly when the carried PC test passes. -/
theorem carriesS_pcObj (o : Obj p) (C : PC 8) :
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
theorem handlesTest_exact (st : State 8) (o u : Obj p) :
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
def handledObjects (st : State 8) (o : Obj p) : List (Obj p) :=
  (o :: carriedObjects o ++ (installedBy st o).map pcObj).filter (fun u => handlesTest st o u)

def emitted (tr : Array (Array (Node p))) (i : Nat) : List (Obj p) :=
  match rho.events[i]? with
  | some (.tick x t) => (V2.D.tick E rho (atIndex tr i x) x t).2
  | _ => []

def deadline (t : Time) : Time := max t 15 + 1

/-- The same schedule with the old PC relayed before t_4. The honest
proposal and all current-slot HEADs and acks use the resulting parent. -/
def repairedN : NamedProposal 8 := namedProposal p B 4 0 raw3 raw3 [] (some C)
def repairedDeliveries (t : Nat) : List FixtureEvent :=
  if t = 15 then deliveries t ++ participants.map (fun x => .deliver x oldPC 15)
  else if t = 16 then honestNodes.map (fun x => .deliver x (prop 4 repairedN) 16)
  else if t = 17 then participants.flatMap (fun i =>
    honestNodes.map (fun x => .deliver x (head 4 i repairedN) 17))
  else if t = 18 then honestNodes.flatMap (fun i =>
    honestNodes.map (fun x => .deliver x (ack 4 i repairedN.root) 18))
  else deliveries t
def repairedRho : V2.D.Run (Fin 8) (pcsaWith .idle p unitCodec) :=
  { rho with events := (List.range 23).flatMap (fun (t : Nat) =>
    honestNodes.map (fun x => V2.Event.tick x (t : Int)) ++ repairedDeliveries t) }

def repairedStep (w : Array (Node p)) (e : FixtureEvent) : Array (Node p) :=
  Array.ofFn (V2.D.World.step E repairedRho (world w) e)

/-- The repaired cache uses the actual engine at every event and node. -/
theorem repairedStep_exact (w : Array (Node p)) (e : FixtureEvent) (x : Fin 8) :
    world (repairedStep w e) x = V2.D.World.step E repairedRho (world w) e x := by
  have h (f : Fin 8 → Node p) : (Array.ofFn f).getD x.val node0 = f x := by
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_ofFn]; exact x.isLt)]
    exact Array.getElem_ofFn _
  exact h (V2.D.World.step E repairedRho (world w) e)

def repairedTrace : Array (Array (Node p)) :=
  repairedRho.events.foldl (fun acc e =>
    acc.push (repairedStep (acc.getD (acc.size - 1) #[]) e)) #[Array.replicate 8 node0]
def repairedRead (x : Fin 8) (t : Time) : State 8 :=
  clock p (atIndex repairedTrace ((repairedRho.tickIdx? x t).getD 0) x).st t

def relayFor (r : V2.D.Run (Fin 8) (pcsaWith .idle p unitCodec))
    (tr : Array (Array (Node p))) : Bool :=
  let es := r.events.toArray
  let is := List.range es.size
  let handlesBy := fun x o t => is.any (fun j =>
    match es.getD j (.tick 0 0) with
    | .deliver y a u => x == y && decide (t ≤ u ∧ u < deadline t) &&
        handlesTest (atIndex tr j x).st a o
    | _ => false)
  let excluded := fun x o t =>
    let k := (es.toList.takeWhile (fun e => decide (e.time < deadline t))).length
    excludesS p (atIndex tr k x).st o
  is.all (fun i => match es.getD i (.tick 0 0) with
    | .deliver y o t => (handledObjects (atIndex tr i y).st o).all (fun a =>
        if !processedS p (atIndex tr i y).st a && processedS p (atIndex tr (i + 1) y).st a then
          honestNodes.all (fun x =>
            if !processedS p (atIndex tr (i + 1) x).st a && deadline t ≤ 22 && !excluded x a t then
              handlesBy x a t else true)
        else true)
    | _ => true)

def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"Formation relay regression: {label} failed")
  IO.println s!"Formation relay regression: {label}: PASS"

def audit : IO Unit := do
  let es : Array FixtureEvent := rho.events.toArray
  let tr := trace
  let hs := honestNodes
  let is := List.range es.size
  let states := List.range tr.size
  let emissions := is.flatMap (fun i =>
    let e := es.getD i (.tick 0 0)
    (emitted tr i).map (fun o => (e.node, o, e.time)))
  let hasEmission := fun u o t =>
    emissions.any (fun row => row.1 = u && row.2.1 == o && row.2.2 ≤ t)
  require "schedule" (decide ((rho.events : List FixtureEvent).Nodup) &&
    (es.toList.zip (es.toList.drop 1)).all (fun ef => decide (ef.1.key ≤ ef.2.key)) &&
    es.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ 22) && hs.contains e.node &&
      match e with | .restart .. => false | _ => true) &&
    (List.range 23).all (fun t => hs.all (fun x => es.contains (.tick x (t : Int)))) )
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
  let bodies := [.genesis, A, B, N]
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
  -- The fresh HEAD and ack maps and the linked FG map are the identity.
  require "fault cap/committee maps" (decide (4 * 1 ≤ p.n) &&
    (List.finRange 8).all (fun i => seats (.base .fg) i == i &&
      seats (.base (.head 4)) i == i && seats (.base (.ack 4)) i == i))
  let handlesBy := fun x o t => is.any (fun j =>
    match es.getD j (.tick 0 0) with
    | .deliver y a u => x == y && decide (t ≤ u ∧ u < deadline t) &&
        handlesTest (atIndex tr j x).st a o
    | _ => false)
  let excluded := fun x o t =>
    let k := (es.toList.takeWhile (fun e => decide (e.time < deadline t))).length
    excludesS p (atIndex tr k x).st o
  require "F1 broadcast" (emissions.all (fun row =>
    let (_, o, t) := row
    hs.all (fun x => if deadline t ≤ 22 && !excluded x o t then handlesBy x o t else true)))
  require "hidden whole PC violates F1 acceptance relay" (!(is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver y o t => (handledObjects (atIndex tr i y).st o).all (fun a =>
        if !processedS p (atIndex tr i y).st a && processedS p (atIndex tr (i + 1) y).st a then
          hs.all (fun x =>
            if !processedS p (atIndex tr (i + 1) x).st a && deadline t ≤ 22 && !excluded x a t then
              handlesBy x a t else true)
        else true)
    | _ => true)))
  require "honest proposal at slot 4" (seats (.prop 4) ⟨0, by change 0 < 1; decide⟩ == 0 &&
    E.awake 0 16 && (emitted tr ((rho.tickIdx? 0 16).getD 0)).contains (prop 4 N))
  require "F2 participation" (decide (nQuorum p.n ≤
    (hs.filter (fun x => E.awake x 17 && E.awake x 18)).length))
  require "F3 common view" (N.pc == none &&
    participants.all (fun x => voterPC p (readTick tr x 17) 4 == none))
  require "F4 proposerRootReachable" (
    let st := readTick tr 0 16
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    let raw := proposerVotes st 4
    let support := proposerSupport st 4
    Block.preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)))
  require "F4 voter upper bound" (participants.all (fun x =>
    let st := readTick tr x 17
    st.base.obligations.all (fun row =>
      if st.base.now < row.2.2 && Block.compatible row.1 .genesis && 0 < row.1.depth then
        Block.preceq row.1 N.erase.parent else true)))
  require "other Formation premises" (decide (0 < 4 ∧ SA.gateTime p.toParams 4 ≤ 22 ∧ E.Δ ≤ 1) &&
    E.Δ == p.Δ)
  require "six exact honest HEADs" (participants.all (fun x =>
    E.awake x 17 && E.awake x 18 && headVote p (readTick tr x 17) 4 == N.erase))
  require "N quorum at every honest early read" (hs.all (fun x =>
    holdsN p (actView (readTick tr x 18)) 4 N.erase))
  require "older PC split" (
    (readTick tr 6 16).pcs.any (fun C => C.slot == 1 && C.target == B.erase) &&
    participants.all (fun x => (readTick tr x 16).pcs.isEmpty))
  require "faulty ack cap differs" (
    participants.all (fun x => seatAcks (readTick tr x 16) 1 7 == [⟨99⟩, ⟨100⟩]) &&
    seatAcks (readTick tr 6 16) 1 7 == [B.root, ⟨99⟩])
  require "no PC wire trigger" (es.all (fun e => match e with
    | .deliver _ o _ => match o.payload with | .pc _ => false | _ => true
    | _ => true))
  let controlEvents := (es.toList.filter (fun e => decide (e.time < 16))) ++
    participants.map (fun x => V2.Event.deliver x oldPC 15)
  let controlWorld := controlEvents.foldl cachedStep (Array.replicate 8 node0)
  let controlRead := clock p (world controlWorld 0).st 16
  require "complete old PC delivery repairs the split" (C.wellFormed &&
    ((proposerPC p controlRead).map PC.target) == some B.erase &&
    getHead p controlRead (proposerPC p controlRead)
      (proposerVotes controlRead 4) (proposerSupport controlRead 4) == B.erase)
  require "six honest early acks" (participants.all (fun x =>
    ackFor p (readTick tr x 18) 4 == some N.erase))
  require "invalid hidden-PC run has an early ack split" (
    !E.awake 6 17 && E.awake 6 18 &&
    ((voterPC p (readTick tr 6 18) 4).map PC.target) == some B.erase &&
    !viewOK p (readTick tr 6 18) 4 N.erase && ackFor p (readTick tr 6 18) 4 == none)
  require "hAckAdmit at current slot" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver x o t => match o.auth, o.payload with
      | .seat (.base (.ack 4)) seat, .ack root =>
        if hs.contains seat && root == N.root && decide (18 ≤ t ∧ t < 19) then
          (atIndex tr (i + 1) x).st.ackPool.contains ⟨.seat (.ack 4) seat, N.root⟩
        else true
      | _, _ => true
    | _ => true))
  require "hAckPoolMono" (is.all (fun i => hs.all (fun x =>
    (atIndex tr i x).st.ackPool.all ((atIndex tr (i + 1) x).st.ackPool.contains))))
  require "hPCCollect at current slot" (hs.all (fun x =>
    (collectPCs (beforeTick tr x 19).st).pcs.any (fun C => C.slot == 4 && C.target == N.erase)))
  require "hFreezeKeep" (hs.all (fun x =>
    (collectPCs (beforeTick tr x 19).st).pcs.all ((readTick tr x 19).pcs.contains)))
  require "current PC stamped before freeze" (hs.all (fun x =>
    (readTick tr x 19).pcs.any (fun C => C.slot == 4 && C.target == N.erase &&
      (pcStamp? (readTick tr x 19) C).any (fun t => t < 19))))
  require "Formation source still present" (hs.all (fun x =>
    ((fgSource p (readTick tr x 22)).map eraseFG) == some N.erase))
  IO.println s!"Formation relay regression: events={es.size}; h_s=6; faults=1"
  IO.println "Formation relay regression: the negative control fails F1 and refuses node 6 ack"
  IO.println "Formation relay regression: current PC and source are present"

def auditRepair : IO Unit := do
  let r := repairedRho
  let es := r.events.toArray
  let tr := repairedTrace
  let is := List.range es.size
  require "repaired schedule" (decide ((r.events : List FixtureEvent).Nodup) &&
    (es.toList.zip (es.toList.drop 1)).all (fun ef => decide (ef.1.key ≤ ef.2.key)) &&
    es.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ 22) && honestNodes.contains e.node &&
      match e with | .restart .. => false | _ => true) &&
    (List.range 23).all (fun t => honestNodes.all (fun x => es.contains (.tick x (t : Int)))))
  let emissions := is.flatMap (fun i => match es.getD i (.tick 0 0) with
    | .tick x t => (V2.D.tick E r (atIndex tr i x) x t).2.map (fun o => (x, o, t))
    | _ => [])
  let hasEmission := fun x o t =>
    emissions.any (fun row => row.1 == x && row.2.1 == o && row.2.2 ≤ t)
  require "repaired direct and carried signatures" (es.all (fun e => match e with
    | .deliver _ o t => honestNodes.all (fun x =>
        if r.holder o.auth == some x then hasEmission x o t else true) &&
        (carriedObjects o).all (fun u => honestNodes.all (fun x =>
          if r.holder u.auth == some x then hasEmission x u t else true))
    | _ => true))
  let bodies := [.genesis, A, B, repairedN]
  require "repaired frame and root collision freedom" (
    (List.range tr.size).all (fun i => honestNodes.all (fun x =>
      let st := (atIndex tr i x).st
      st.fg.F == .genesis && (controls p st).Z == .genesis && (controls p st).lo == 0 &&
        st.namedBodies.all bodies.contains)) &&
    bodies.all (fun X => bodies.contains X.parent) &&
    bodies.all (fun X => bodies.all (fun Y => if X.root == Y.root then X == Y else true)))
  let handlesBy := fun x o t => is.any (fun j => match es.getD j (.tick 0 0) with
    | .deliver y a u => x == y && decide (t ≤ u ∧ u < deadline t) &&
        handlesTest (atIndex tr j x).st a o
    | _ => false)
  let excluded := fun x o t =>
    let k := (es.toList.takeWhile (fun e => decide (e.time < deadline t))).length
    excludesS p (atIndex tr k x).st o
  require "repaired F1 broadcast" (emissions.all (fun row =>
    let (_, o, t) := row
    honestNodes.all (fun x =>
      if deadline t ≤ 22 && !excluded x o t then handlesBy x o t else true)))
  require "repaired wire/dependencies/freshness" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver x o _ => (pcsaWith .idle p unitCodec).wellFormed o &&
        depsS p (atIndex tr i x).st o && !processedS p (atIndex tr i x).st o
    | _ => true))
  require "repaired F1 acceptance relay" (relayFor r tr)
  require "old PC reaches every honest node before proposal" (honestNodes.all (fun x =>
    (repairedRead x 16).pcs.any (fun D => D.slot == 1 && D.target == B.erase)))
  let ki := (r.tickIdx? 0 16).getD 0
  require "repaired honest proposal is emitted" (
    (V2.D.tick E r (atIndex tr ki 0) 0 16).2.contains (prop 4 repairedN))
  require "repaired F3 common view" (participants.all (fun x =>
    ((voterPC p (repairedRead x 17) 4).map PC.target) == some B.erase))
  require "repaired F4 root path" (
    let st := repairedRead 0 16
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    let raw := proposerVotes st 4
    let support := proposerSupport st 4
    Block.preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)))
  require "repaired F4 voter upper bound" (participants.all (fun x =>
    let st := repairedRead x 17
    st.base.obligations.all (fun row =>
      if st.base.now < row.2.2 && Block.compatible row.1 B.erase && B.erase.depth < row.1.depth then
        Block.preceq row.1 repairedN.erase.parent else true)))
  require "repaired honest HEADs" (participants.all (fun x =>
    headVote p (repairedRead x 17) 4 == repairedN.erase))
  require "repaired N quorum at every early read" (honestNodes.all (fun x =>
    holdsN p (actView (repairedRead x 18)) 4 repairedN.erase))
  require "relay repairs the ack-only node" (!E.awake 6 17 && E.awake 6 18 &&
    ((voterPC p (repairedRead 6 18) 4).map PC.target) == some B.erase &&
    ackFor p (repairedRead 6 18) 4 == some repairedN.erase)
  require "repaired all-awake-early acks" (honestNodes.all (fun x =>
    ackFor p (repairedRead x 18) 4 == some repairedN.erase))
  require "repaired PC before freeze" (honestNodes.all (fun x =>
    (repairedRead x 19).pcs.any (fun D => D.slot == 4 && D.target == repairedN.erase)))
  require "repaired source" (honestNodes.all (fun x =>
    ((fgSource p (repairedRead x 22)).map eraseFG) == some repairedN.erase))

#eval audit
#eval auditRepair
#print axioms carriesS_pcObj
#print axioms repairedStep_exact
#print axioms cachedStep_exact
#print axioms carriedObjects_signed
#print axioms handlesTest_exact
#print axioms cachedFold_exact
#print axioms fresh_committees
#print axioms linked_committee

end AvailableChain.PCSA.Run.Tests.FormationAckCounterexample
end
