module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming -- shake: keep
public meta import AvailableChainFGSAProofs.Proofs.Outage.Arming -- shake: keep (fixture evaluation)

@[expose] public section

/-! Executable check of outage-handoff.md at main 31fa4d7.
The V2 duty engine generates all honest emissions. No honest store is assigned.
The finite audits check the current outage premises and the loss of B after recovery.
The current finite outage contract covers [17,24). This test checks the draft's
stronger proposed continuation through the horizon. It does not refute that finite contract.
Kernel proofs cover execution validity and receipt root collision freedom.
The output loss remains an executable check. -/

open AvailableChain AvailableChain.FGSA AvailableChain.FGSA.Run AvailableChain.SimplexFG
namespace AvailableChain.FGSA.Run.Tests.OutageAfterWindowCounterexample

abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 7, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 100, δt := 200, RLarge := by decide,
    digest := fun d => ⟨d.slot + 1⟩ }
def B : NamedProposal 4 := namedProposal p .genesis 1 0 [] [] []
def C : NamedProposal 4 := namedProposal p .genesis 4 0 [] [] []
def prop (s : Nat) (N : NamedProposal 4) : Obj p :=
  ⟨.seat (.prop s) ⟨0, by change 0 < 1; decide⟩, .proposal N⟩
def head (s : Nat) (i : Fin 4) (N : NamedProposal 4) : Obj p :=
  ⟨.seat (.base (.head s)) i, .head N.root⟩
def E : Generic.Env (Fin 4) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 24, t_GST_nonneg := by decide,
    awake := fun _ t => decide (t < 17 ∨ 24 ≤ t) }
def seats : (l : RunLabel) → Fin (RunLabel.seats p l) → Fin 4
  | .prop _, _ => 3
  | .base _, i => i

def honestNodes : List (Fin 4) := [0, 1, 2]
abbrev FixtureEvent := V2.Event (Fin 4) (Obj p)
instance : DecidableEq (fgsa p unitCodec).Object :=
  inferInstanceAs (DecidableEq (Obj p))
instance : DecidableEq FixtureEvent := inferInstanceAs (DecidableEq (V2.Event (Fin 4) (Obj p)))
instance : BEq FixtureEvent := ⟨fun x y => decide (x = y)⟩

def runWith (es : List FixtureEvent) : V2.D.Run (Fin 4) (fgsa p unitCodec) :=
  { honest := {0, 1, 2}, horizon := 30, events := es, seatOf := seats, input := fun _ _ => () }
abbrev node0 : Node p := ⟨initial p.n, RecordOnce.initial⟩
abbrev world (w : Array (Node p)) : Fin 4 → Node p := fun x => w.getD x.val node0

def cachedStep (w : Array (Node p)) (e : FixtureEvent) : Array (Node p) :=
  Array.ofFn (V2.D.World.step E (runWith []) (world w) e)

/-- Materialization preserves the actual V2 step; events do not affect that step. -/
theorem outageCex_cachedStep_exact (es : List FixtureEvent) (w : Array (Node p))
    (e : FixtureEvent) (x : Fin 4) :
    world (cachedStep w e) x = V2.D.World.step E (runWith es) (world w) e x := by
  have h (f : Fin 4 → Node p) : (Array.ofFn f).getD x.val node0 = f x := by
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_ofFn]; exact x.isLt)]
    exact Array.getElem_ofFn _
  exact h (V2.D.World.step E (runWith []) (world w) e)

/-- Cached folds have exactly the event-fold semantics of the V2 engine. -/
theorem outageCex_cachedFold_exact (es : List FixtureEvent) (w : Array (Node p)) :
    world (es.foldl cachedStep w) = es.foldl (V2.D.World.step E (runWith es)) (world w) := by
  have stepEq (w : Array (Node p)) (e : FixtureEvent) :
      world (cachedStep w e) = V2.D.World.step E (runWith es) (world w) e :=
    funext (outageCex_cachedStep_exact es w e)
  have foldEq (xs : List FixtureEvent) (w : Array (Node p)) :
      world (xs.foldl cachedStep w) = xs.foldl (V2.D.World.step E (runWith es)) (world w) := by
    induction xs generalizing w with
    | nil => rfl
    | cons e xs ih => simp only [List.foldl_cons]; rw [ih, stepEq]; rfl
  exact foldEq es w

/-- Only four faulty objects supplement the actual honest emissions. -/
def faultyObjects (t : Nat) : List (Obj p) :=
  match t with
  | 4 => [prop 1 B]
  | 17 => [prop 4 C, head 4 3 C]
  | 21 => [head 5 3 C]
  | 25 => [head 6 3 C]
  | _ => []

/-- Restart at wake, tick awake nodes, then deliver pending objects to awake nodes. -/
def generateDay (acc : List FixtureEvent × Array (Node p)) (t : Nat) :
    List FixtureEvent × Array (Node p) := Id.run do
  let mut es := acc.1
  let mut w := acc.2
  let mut emitted : List (Obj p) := []
  if t == 24 then
    for x in honestNodes do
      let ev := V2.Event.restart x (t : Int)
      es := es ++ [ev]
      w := cachedStep w ev
  let awakeNodes := honestNodes.filter (fun x => E.awake x (t : Int))
  for x in awakeNodes do
    let released : List (Obj p) := (V2.D.tick E (runWith []) (world w x) x (t : Int)).2
    emitted := emitted ++ released
    let ev := V2.Event.tick x (t : Int)
    es := es ++ [ev]
    w := cachedStep w ev
  let pending := (List.range (t + 1)).flatMap faultyObjects
  for o in emitted ++ pending do
    for x in awakeNodes do
      if processedS p (world w x).st o then continue
      let ev := V2.Event.deliver x o (t : Int)
      es := es ++ [ev]
      w := cachedStep w ev
  return (es, w)

/-- A finite event plan. The audit compares it with the live emission generator. -/
def plannedObjects (t : Nat) : List (Obj p) :=
  match t with
  | 1 => honestNodes.map (fun x => head 0 x .genesis)
  | 4 => [prop 1 B]
  | 5 => honestNodes.map (fun x => head 1 x B)
  | 9 => honestNodes.map (fun x => head 2 x B)
  | 13 => honestNodes.map (fun x => head 3 x B)
  | 24 => [prop 4 C, head 4 3 C, head 5 3 C]
  | 25 => [head 4 3 C, head 6 3 C]
  | 26 | 27 | 28 | 30 => [head 4 3 C]
  | 29 => honestNodes.map (fun x => head 7 x C) ++ [head 4 3 C]
  | _ => []

def plannedDay (t : Nat) : List FixtureEvent :=
  let awakeNodes := honestNodes.filter (fun x => E.awake x (t : Int))
  (if t = 24 then honestNodes.map (fun x => .restart x (t : Int)) else []) ++
    awakeNodes.map (fun x => .tick x (t : Int)) ++
    (plannedObjects t).flatMap (fun o => awakeNodes.map (fun x => .deliver x o (t : Int)))

def generatedEvents : List FixtureEvent :=
  ((List.range 31).foldl generateDay ([], Array.replicate 4 node0)).1

def rho : V2.D.Run (Fin 4) (fgsa p unitCodec) :=
  runWith ((List.range 31).flatMap plannedDay)

theorem outageCex_fresh_committees : V2.D.CStar (fgsaFamilies p unitCodec).fresh rho := by
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l => cases l with
    | fg => exact hl.elim
    | head s => exact Function.bijective_id

theorem outageCex_linked_committee : V2.D.Linked (fgsaFamilies p unitCodec).linked rho := by
  refine ⟨4, Equiv.refl (Fin 4), ?_⟩
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l => cases l with
    | head s => exact hl.elim
    | fg => exact ⟨rfl, fun _ => rfl⟩

def trace : Array (Array (Node p)) :=
  rho.events.foldl (fun acc e =>
    acc.push (cachedStep (acc.getD (acc.size - 1) #[]) e)) #[Array.replicate 4 node0]
def atIndex (tr : Array (Array (Node p))) (i : Nat) (x : Fin 4) : Node p :=
  world (tr.getD i #[]) x
def atTime (tr : Array (Array (Node p))) (t : Time) (x : Fin 4) : State 4 :=
  (atIndex tr (rho.events.takeWhile (fun e => decide (e.time ≤ t))).length x).st
def beforeTick (tr : Array (Array (Node p))) (x : Fin 4) (t : Time) : State 4 :=
  (atIndex tr ((rho.tickIdx? x t).getD 0) x).st
def emitted (tr : Array (Array (Node p))) (i : Nat) : List (Obj p) :=
  match rho.events[i]? with
  | some (.tick x t) => (V2.D.tick E rho (atIndex tr i x) x t).2
  | _ => []

def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"Outage after window: {label} failed")
  IO.println s!"Outage after window: {label}: PASS"

/-- All carried-object checks enumerate the full model relation. -/
def carriedObjects (o : Obj p) : List (Obj p) :=
  match o.payload with
  | .proposal N => N.raw.map (ofHead p) ++ N.support.map (ofHead p) ++ N.rows.map (ofRow p)
  | _ => []

theorem carriedObjects_exact (o u : Obj p) :
    (fgsa p unitCodec).carries o u ↔ u ∈ carriedObjects o := by
  change carriesS p o u ↔ _
  delta carriesS carriedObjects
  cases o.payload <;> simp only [List.mem_append, List.not_mem_nil]
  all_goals tauto

def audit : IO Unit := do
  require "event plan equals the live emission generator"
    (decide ((show List FixtureEvent from rho.events) = generatedEvents))
  let es : Array FixtureEvent := rho.events.toArray
  let tr := trace
  let hs := honestNodes
  let is := List.range es.size
  let states := List.range tr.size
  let emissions := is.flatMap (fun i =>
    let e := es.getD i (.tick 0 0)
    (emitted tr i).map (fun o => (e.node, o, e.time)))
  let hasEmission := fun u o t =>
    emissions.any (fun row => row.1 == u && row.2.1 == o && row.2.2 ≤ t)
  let deliveredAt := fun x o t => es.contains (.deliver x o t)
  require "run parameters and honest set" (decide (
    p.n = 4 ∧ p.k = 2 ∧ p.Δ = 1 ∧ p.η = 7 ∧ L p = 7 ∧
    p.R = 100 ∧ p.δt = 200 ∧ p.K_W = 2 ∧ E.t_GST = 24 ∧ rho.horizon = 30) &&
    hs.length == 3 && ((List.finRange 4).filter (fun x => !hs.contains x)).length == 1)
  require "Base2 schedule, awake events, and wake restarts" (
    decide (rho.events.Nodup) && decide (rho.events.Pairwise (fun e f => e.key ≤ f.key)) &&
    es.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ rho.horizon) && hs.contains e.node &&
      E.awake e.node e.time &&
      match e with | .restart _ t => decide (t = 24) | _ => true) &&
    hs.all (fun x => es.contains (.restart x 24)) &&
    (List.range 31).all (fun t => hs.all (fun x =>
      if E.awake x (t : Int) then es.contains (.tick x (t : Int)) else true)))
  require "Base2 wires, exact dependencies, and freshness" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver x o _ => (fgsa p unitCodec).wellFormed o &&
        depsS p (atIndex tr i x).st o && !processedS p (atIndex tr i x).st o
    | _ => true))
  require "Base2 direct signatures" (es.all (fun e =>
    match e with
    | .deliver _ o t => hs.all (fun u =>
        if rho.holder o.auth == some u then hasEmission u o t else true)
    | _ => true))
  require "Base2 carried signatures and empty carriage" (es.all (fun e =>
    match e with
    | .deliver _ o t => (carriedObjects o).isEmpty &&
        (carriedObjects o).all (fun a => hs.all (fun u =>
          if rho.holder a.auth == some u then hasEmission u a t else true))
    | _ => true))
  let bodies := [.genesis, B, C]
  require "Base2 named root collision freedom" (
    es.all (fun e => match e with
      | .deliver _ o _ => match o.payload with
        | .proposal N => bodies.contains N
        | _ => true
      | _ => true) &&
    states.all (fun i => (List.finRange 4).all (fun x =>
      (atIndex tr i x).st.namedBodies.all bodies.contains)) &&
    bodies.all (fun N => bodies.contains N.parent) &&
    bodies.all (fun N => bodies.all (fun M => if N.root == M.root then N == M else true)))
  -- The family properties also have kernel proofs below. The maps are fixed for every label.
  require "Base2 committee maps and delta" (
    decide (hs.toFinset = rho.honest) && E.Δ == p.Δ &&
    (List.range 8).all (fun s =>
      seats (.prop s) ⟨0, by change 0 < 1; decide⟩ == 3 &&
      (List.finRange 4).all (fun i => seats (.base (.head s)) i == i &&
        seats (.base .fg) i == i)))
  -- With empty carriage, a handler call can only be for the delivered object itself.
  -- These unconditional same-time checks are stronger than both delivery regimes:
  -- they include all triggers, without an exclusion, cut, or horizon exception.
  require "HealthyPrefix2 and partial synchrony broadcast" (emissions.all (fun row =>
    let (_, o, t) := row
    hs.all (fun x => deliveredAt x o t) &&
    decide (t < t + 1 ∧ t < max t E.t_GST + 1)))
  require "HealthyPrefix2 and partial synchrony acceptance relay" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver y o t =>
        if !processedS p (atIndex tr i y).st o && processedS p (atIndex tr (i + 1) y).st o then
          hs.all (fun x => deliveredAt x o t) &&
            decide (t < t + 1 ∧ t < max t E.t_GST + 1)
        else true
    | _ => true))
  require "HealthyPrefix2 cut, deltaF, and participation" (
    decide (0 ≤ (17 : Time) ∧ 17 ≤ rho.horizon ∧ E.Δ ≤ (1 : Time)) &&
    (List.range 17).all (fun t =>
      decide (1 < (hs.filter (fun x => E.awake x (t : Int))).length)))
  require "Outage2 sleepy bound and fast participation" ((List.range 17).all (fun u =>
    let t : Time := u
    let awake := (hs.filter (fun x => E.awake x t)).length
    let recentOrFaulty := (List.finRange 4).filter (fun x =>
      !hs.contains x || (List.range 8).any (fun j => E.awake x (t - p.η + (j : Int))))
    decide (recentOrFaulty.length < 2 * awake ∧ (p.n + 1) / 2 ≤ awake)))
  require "Outage2 order, both lags, and budget" (decide (
    0 ≤ (10 : Time) ∧ 10 ≤ (17 : Time) ∧ 17 ≤ (24 : Time) ∧ 24 ≤ rho.horizon ∧
    10 + 4 * p.Δ ≤ 17 ∧ 10 + (L p - 3 * p.Δ) ≤ 17 ∧
    (24 : Time) - 17 ≤ min p.η (L p) ∧ (24 : Time) ≤ 17 + L p))
  require "GST and full honest participation after b1" (
    decide (E.t_GST ≤ (24 : Time)) &&
    (List.range 7).all (fun j => hs.all (fun x => E.awake x (24 + (j : Int)))))
  require "same-time delivery after b1" (emissions.all (fun row =>
    let (_, o, t) := row
    if 24 ≤ t then hs.all (fun x => deliveredAt x o t) else true) &&
    es.all (fun e => match e with
      | .deliver _ o t => if 24 ≤ t then hs.all (fun x => deliveredAt x o t) else true
      | _ => true))
  require "fixed FG frame throughout the run" (states.all (fun i => hs.all (fun x =>
    let st := (atIndex tr i x).st
    st.fg.F == .genesis && st.fg.J == .genesis &&
    (controls p st).Z == .genesis && (controls p st).lo == 0)))
  -- Check the paper trace in time order. Print actual values before each assertion.
  for t in ([4, 5, 9, 10, 13, 14, 17, 18, 21, 22, 24, 25, 26, 29, 30] : List Time) do
    for x in hs do
      let st := atTime tr t x
      let heads := (emitted tr ((rho.tickIdx? x t).getD 0)).filterMap (fun o =>
        match o.payload with | .head root => some root | _ => none)
      IO.println s!"time={t} node={x} S.root={repr st.base.stableRecord.root} \
        B.lease={leaseOf st B.erase} C.lease={leaseOf st C.erase} HEADs={repr heads}"
    if t == 4 then
      require "trace at 4: B received" (hs.all (fun x =>
        (atTime tr t x).namedBodies.contains B))
    if [5, 9, 13, 29].contains t then
      let s := p.slotOf t
      let N := if t < 17 then B else C
      require s!"trace at {t}: honest label-{s} HEADs" (hs.all (fun x =>
        (emitted tr ((rho.tickIdx? x t).getD 0)) == [head s x N]))
    if [10, 14].contains t then
      let target := if t < 26 then B else C
      let dl : Time := if t == 10 then 17 else if t == 14 then 21 else
        if t < 26 then 25 else if t == 26 then 33 else 37
      require s!"trace at {t}: S and lock deadline" (hs.all (fun x =>
        stable (atTime tr t x) == target.erase && leaseOf (atTime tr t x) target.erase == some dl))
    if t == 24 then
      require "trace at wake: pending C and faulty HEADs received" (hs.all (fun x =>
        (atTime tr t x).namedBodies.contains C &&
        processedS p (atTime tr t x) (head 5 3 C)))
    if t == 25 then
      require "trace after wake: expired B lock and joined duty guard" (hs.all (fun x =>
        leaseOf (atTime tr t x) B.erase == none &&
        emitted tr ((rho.tickIdx? x t).getD 0) == []))
  require "no honest outage emissions" (emissions.all (fun row =>
    decide (row.2.2 < 17 ∨ 24 ≤ row.2.2)))
  require "stable and confirmed lose B at 30" (hs.all (fun x =>
    stable (atTime tr 10 x) == B.erase && confirmed (atTime tr 10 x) == B.erase &&
    stable (atTime tr 24 x) == B.erase && stable (atTime tr 30 x) == C.erase &&
    !Block.preceq B.erase (stable (atTime tr 30 x)) &&
    !Block.preceq B.erase (confirmed (atTime tr 30 x))))
  IO.println s!"CEX: CONFIRMED; events={es.size}; honest=3; faulty=1"

private theorem event_certificate : rho.events.all (fun e =>
    decide (0 ≤ e.time ∧ e.time ≤ rho.horizon ∧ e.node ∈ rho.honest) &&
    E.awake e.node e.time) = true := by
  decide +kernel

private theorem sorted_certificate :
    rho.events.Pairwise (fun e f => e.key ≤ f.key) := by decide +kernel

private theorem nodup_certificate : (show List FixtureEvent from rho.events).Nodup := by
  decide +kernel

private theorem ticks_certificate : (List.finRange 4).all (fun v =>
    (List.range 31).all (fun t => if decide (v ∈ rho.honest) && E.awake v (t : Time) then
      decide ((V2.Event.tick v (t : Time) : FixtureEvent) ∈
        (show List FixtureEvent from rho.events)) else true)) = true := by
  decide +kernel

private def restart_check : Bool := rho.events.all (fun e =>
    match e with | .restart _ t => decide (t = 24) | _ => true)

private theorem restart_certificate : restart_check = true := by
  decide +kernel

private def delivery_check : Bool := (List.range rho.events.length).all (fun i =>
    match rho.events[i]? with
    | some (.deliver v o _) => (fgsa p unitCodec).wellFormed o &&
        (fgsa p unitCodec).depsPresent (V2.D.Run.stateBefore E rho i v) o &&
        !(fgsa p unitCodec).processed (V2.D.Run.stateBefore E rho i v) o
    | _ => true)

private theorem delivery_certificate : delivery_check = true := by
  decide +kernel

private theorem origin_certificate : (List.range rho.events.length).all (fun i =>
    match rho.events[i]? with
    | some (.deliver _ o t) => (List.finRange 4).all (fun u =>
        if decide (u ∈ rho.honest ∧ rho.holder o.auth = some u) then
          decide ((show Obj p from o) ∈
            (show List (Obj p) from V2.D.Run.emittedAt E rho u t)) else true)
    | _ => true) = true := by
  decide +kernel

private def carriage_check : Bool := rho.events.all (fun e =>
    match e with | .deliver _ o _ => decide (carriedObjects o = []) | _ => true)

private theorem carriage_certificate : carriage_check = true := by
  decide +kernel

private theorem wake_certificate : (List.finRange 4).all (fun v =>
    if decide (v ∈ rho.honest) then
      decide ((V2.Event.restart v 24 : FixtureEvent) ∈
        (show List FixtureEvent from rho.events)) else true) = true := by
  decide +kernel

/-- Full valid-run evidence for the finite plan, with the real FG-SA state fold. -/
theorem outageCex_execution : V2.D.ExecutionValid E rho := by
  have hevent (e : FixtureEvent) (he : e ∈ rho.events) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp event_certificate e he)
  have hs : V2.D.ScheduleWellFormed E rho :=
    { horizon_nonneg := by decide
      sorted := sorted_certificate
      nodup := nodup_certificate
      in_horizon := fun e he => ⟨(of_decide_eq_true (hevent e he).1).1,
        (of_decide_eq_true (hevent e he).1).2.1⟩
      honest_only := fun e he => (of_decide_eq_true (hevent e he).1).2.2
      tick_public := by
        intro v t he
        have ht : 0 ≤ t := (of_decide_eq_true (hevent _ he).1).1
        exact ⟨t.toNat, by simpa [E] using (Int.toNat_of_nonneg ht).symm⟩
      tick_total := by
        intro v hv t _ ht hh ha
        have hbound : t.toNat < 31 := by
          simp only [rho, runWith, Time] at *
          omega
        have hcast : (t.toNat : Time) = t := Int.toNat_of_nonneg ht
        have h := List.all_eq_true.mp
          (List.all_eq_true.mp ticks_certificate v (List.mem_finRange v))
          t.toNat (List.mem_range.mpr hbound)
        simp only [hcast, decide_eq_true hv, ha, Bool.true_and, ↓reduceIte] at h
        change decide ((V2.Event.tick v (t.toNat : Time) : FixtureEvent) ∈
          (show List FixtureEvent from rho.events)) = true at h
        rw [hcast] at h
        exact of_decide_eq_true h }
  have hdelivery (i : Nat) (v : Fin 4) (o : Obj p) (t : Time)
      (hi : rho.events[i]? = some (.deliver v o t)) :
      (fgsa p unitCodec).wellFormed o = true ∧
      (fgsa p unitCodec).depsPresent (V2.D.Run.stateBefore E rho i v) o = true ∧
      (fgsa p unitCodec).processed (V2.D.Run.stateBefore E rho i v) o = false := by
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    have hc := List.all_eq_true.mp delivery_certificate i (List.mem_range.mpr hlt)
    rw [hi] at hc
    simp only [Bool.and_eq_true_iff] at hc
    exact ⟨hc.1.1, hc.1.2, Bool.eq_false_of_not_eq_true' hc.2⟩
  refine
    { toScheduleWellFormed := hs
      wire := fun i v o t hi => (hdelivery i v o t hi).1
      deps := fun i v o t hi => (hdelivery i v o t hi).2.1
      fresh := fun i v o t hi => (hdelivery i v o t hi).2.2
      unforgeable := ?_
      carried := ?_
      tick_awake := fun v t he => (hevent _ he).2
      deliver_awake := fun v o t he => (hevent _ he).2
      restart_awake := fun v t he => (hevent _ he).2
      wake_restart := ?_ }
  · intro v o t hp u hu hh
    obtain ⟨i, hi⟩ := hp
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    have hc := List.all_eq_true.mp origin_certificate i (List.mem_range.mpr hlt)
    rw [hi] at hc
    have hu' := List.all_eq_true.mp hc u (List.mem_finRange u)
    simp only [decide_eq_true (And.intro hu hh), ↓reduceIte] at hu'
    exact ⟨t, le_rfl, hs.mem_emittedAt_iff_emits.mp (of_decide_eq_true hu')⟩
  · intro v o t hp o' ho u _ _
    obtain ⟨i, hi⟩ := hp
    have he := List.mem_of_getElem? hi
    have hc := List.all_eq_true.mp carriage_certificate _ he
    change decide (carriedObjects o = []) = true at hc
    have hc := of_decide_eq_true hc
    have hm := (carriedObjects_exact o o').mp ho
    rw [hc] at hm
    exact (List.not_mem_nil hm).elim
  · intro v hv t _ _ hw
    have ht : t = 24 := by
      have ha := hw.1
      have hf := hw.2
      simp only [V2.D.Wakes, E, decide_eq_true_eq, decide_eq_false_iff_not] at *
      simp only [Time] at *
      omega
    subst t
    have hr := List.all_eq_true.mp wake_certificate v (List.mem_finRange v)
    simp only [decide_eq_true hv, ↓reduceIte] at hr
    exact of_decide_eq_true hr

/-- Every fixture restart is the exact wake, before all ticks and deliveries. -/
theorem outageCex_restarts : V2.D.RestartsAtWakes E rho := by
  intro v t he
  have ht := List.all_eq_true.mp restart_certificate _ he
  change decide (t = 24) = true at ht
  have ht := of_decide_eq_true ht
  subst t
  exact ⟨by decide, by unfold V2.D.Wakes E; decide +revert⟩

def receiptBodies : List (NamedProposal 4) := [.genesis, B, C]

private def delivered_body_check : Bool := rho.events.all (fun e =>
    match e with
    | .deliver _ o _ => match o.payload with
      | .proposal N => decide (N ∈ receiptBodies)
      | _ => true
    | _ => true)

private theorem delivered_body_certificate : delivered_body_check = true := by decide +kernel

private theorem held_body_certificate : (List.range (rho.events.length + 1)).all (fun i =>
    (List.finRange 4).all (fun v =>
      (V2.D.Run.stateBefore E rho i v).st.namedBodies.all
        (fun N => decide (N ∈ receiptBodies)))) = true := by decide +kernel

private theorem emitted_body_certificate : (List.range rho.events.length).all (fun i =>
    (V2.D.Run.emitsAt E rho i).all (fun o => match o.payload with
      | .proposal N => decide (N ∈ receiptBodies)
      | _ => true)) = true := by decide +kernel

private theorem receipt_ancestor (N A : NamedProposal 4) (hN : N ∈ receiptBodies)
    (ha : NamedProposal.Preceq A N) : A ∈ receiptBodies := by
  simp only [receiptBodies, List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases hN with rfl | rfl | rfl
  · have he : A = .genesis := by
      simpa [NamedProposal.Preceq, NamedProposal.preceq] using ha
    rw [he]
    simp [receiptBodies]
  · have he : A = B ∨ A = .genesis := by
      simpa [B, namedProposal, NamedProposal.Preceq, NamedProposal.preceq] using ha
    rcases he with rfl | rfl <;> simp [receiptBodies]
  · have he : A = C ∨ A = .genesis := by
      simpa [C, namedProposal, NamedProposal.Preceq, NamedProposal.preceq] using ha
    rcases he with rfl | rfl <;> simp [receiptBodies]

/-- Honest emitted bodies are included in the finite receipt table. -/
theorem outageCex_emitted_in_table (v : Fin 4) (o : Obj p) (t : Time)
    (N : NamedProposal 4) (hem : V2.D.Run.emits E rho v o t)
    (hp : o.payload = .proposal N) : N ∈ receiptBodies := by
  obtain ⟨i, hi, ho⟩ := hem
  have hc := List.all_eq_true.mp emitted_body_certificate i
    (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1)
  have hm := List.all_eq_true.mp hc o ho
  rw [hp] at hm
  exact of_decide_eq_true hm

/-- P23-A: the fixture includes honest emissions in its root idealization. -/
theorem outageCex_receipt_roots : NamedReceiptRootCollisionFree p unitCodec E rho := by
  have hheld (i : Nat) (v : Fin 4) (N : NamedProposal 4)
      (hm : N ∈ (V2.D.Run.stateBefore E rho i v).st.namedBodies) : N ∈ receiptBodies := by
    have hcap : min i rho.events.length < rho.events.length + 1 := by omega
    have hc := List.all_eq_true.mp held_body_certificate _ (List.mem_range.mpr hcap)
    have hv := List.all_eq_true.mp hc v (List.mem_finRange v)
    have he : V2.D.Run.stateBefore E rho i v =
        V2.D.Run.stateBefore E rho (min i rho.events.length) v := by
      unfold V2.D.Run.stateBefore
      rw [List.take_eq_take_min (i := i)]
    rw [he] at hm
    exact of_decide_eq_true (List.all_eq_true.mp hv N hm)
  have hscope (A : NamedProposal 4)
      (hs : NamedProposalReceiptScope p unitCodec E rho A) : A ∈ receiptBodies := by
    rcases hs with ⟨N, hd, hAN⟩ | ⟨v, _, o, t, N, hem, hp, hAN⟩
    · apply receipt_ancestor N A _ hAN
      rcases hd with ⟨v, o, t, he, hp⟩ | ⟨v, _, i, hm⟩
      · have hc := List.all_eq_true.mp delivered_body_certificate _ he
        change (match o.payload with
          | .proposal N => decide (N ∈ receiptBodies) | _ => true) = true at hc
        rw [hp] at hc
        exact of_decide_eq_true hc
      · exact hheld i v N hm
    · exact receipt_ancestor N A (outageCex_emitted_in_table v o t N hem hp) hAN
  intro N M hN hM he
  have hN := hscope N hN
  have hM := hscope M hM
  simp only [receiptBodies, List.mem_cons, List.not_mem_nil, or_false] at hN hM
  rcases hN with rfl | rfl | rfl <;> rcases hM with rfl | rfl | rfl <;>
    first | rfl | simp [B, C, namedProposal, NamedProposal.root, genesisRoot] at he

#eval audit
#print axioms carriedObjects_exact
#print axioms outageCex_cachedStep_exact
#print axioms outageCex_cachedFold_exact
#print axioms outageCex_fresh_committees
#print axioms outageCex_linked_committee

#print axioms outageCex_execution
#print axioms outageCex_restarts
#print axioms outageCex_emitted_in_table
#print axioms outageCex_receipt_roots

end AvailableChain.FGSA.Run.Tests.OutageAfterWindowCounterexample
end
