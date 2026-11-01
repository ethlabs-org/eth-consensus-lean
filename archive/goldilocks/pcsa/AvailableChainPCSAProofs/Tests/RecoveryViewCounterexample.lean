module
public import Mathlib.Tactic
public import AvailableChainPCSAProofs.Proofs.Recovery.RunInputs
public meta import AvailableChainPCSAProofs.Proofs.Recovery.RunInputs -- shake: keep (closed run evaluation)

@[expose] public section

/-! Recovery relay regressions for whole-PC relay and PC target aliases.
Mode 0 omits whole-PC relay and is a negative control.
Mode 1 delivers whole PCs at GST and repairs F3 and the checked coverage.
Mode 2 changes event 92 at t=14 to a PC with the same root and a different
body, and delivers whole PCs at GST. Its acks install the real target's PC.
The PC tests of `carriesS` read the target root (861ca1f), so the alias call
handles the real PC, the relay obliges its delivery, and F3 and coverage hold.
Mode 3 is the alias without whole-PC relay: a negative control that violates
the RECOVERY relay premise. The exact-target carriage of 43733fe is kept only
as an explicit control (`carriesPCExact`): it does not carry the real PC.
These audits are not kernel proofs of C11 or C12.
The kernel proofs cover the cache and committee maps.
They also cover the fault cap, participation, recurrence, store facts, and
the alias acceptance. The handles checker follows PcRelayRegression. -/
open AvailableChain AvailableChain.PCSA AvailableChain.PCSA.Run AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run.Tests.RecoveryViewCounterexample

abbrev p : Params :=
  { Δ := 1, n := 4, k := 4, η := 20, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 1, RLarge := by decide,
    digest := fun d => ⟨d.slot⟩ }
def E : Generic.Env (Fin 4) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 19, t_GST_nonneg := by decide,
    awake := fun v t => decide (t ≤ 6 ∨ 19 ≤ t ∨
      (v = 0 ∧ t = 13) ∨ (v = 1 ∧ (t = 12 ∨ t = 13 ∨ t = 14))) }
def seats : (l : RunLabel) → Fin (RunLabel.seats p l) → Fin 4
  | .prop s, _ => if s = 3 then 1 else if s = 1 ∨ 5 ≤ s then 0 else 3
  | .base _, i => i
abbrev horizon : Nat := 64
def seed : V2.D.Run (Fin 4) (pcsaWith .idle p unitCodec) :=
  { honest := {0, 1, 2}, horizon := horizon, events := [], seatOf := seats, input := fun _ _ => () }
abbrev initNode : Node p := ⟨initial p.n, RecordOnce.initial⟩
def buildWorld (w : Array (Node p)) : Fin 4 → Node p := fun x => w.getD x.val initNode
abbrev BuildEvent := V2.Event (Fin 4) (Obj p)
structure Builder where
  nodes : Array (Node p) := Array.replicate 4 initNode
  events : List BuildEvent := []
  backlog : List (Obj p) := []
  outgoing : List (Obj p) := []
def pushEvent (b : Builder) (e : BuildEvent) : Builder :=
  { b with nodes := Array.ofFn (V2.D.World.step E seed (buildWorld b.nodes) e)
           events := b.events ++ [e] }
def pushTick (b : Builder) (x : Fin 4) (t : Time) : Builder :=
  let out : List (Obj p) := (V2.D.tick E seed (buildWorld b.nodes x) x t).2
  let b := pushEvent b (.tick x t)
  { b with backlog := b.backlog ++ out, outgoing := b.outgoing ++ out }
def send (b : Builder) (x : Fin 4) (o : Obj p) (t : Time) : Builder :=
  if processedS p (buildWorld b.nodes x).st o then b else pushEvent b (.deliver x o t)
def sendMany (b : Builder) (xs : List (Fin 4)) (os : List (Obj p)) (t : Time) : Builder :=
  os.foldl (fun b o => xs.foldl (fun b x => send b x o t) b) b
def faultAck (r : Nat) : Obj p := ⟨.seat (.base (.ack 3)) ⟨3, by change 3 < 4; decide⟩, .ack ⟨r⟩⟩
def faultHead : Obj p := ⟨.seat (.base (.head 3)) ⟨3, by change 3 < 4; decide⟩, .head ⟨3⟩⟩
def manual (b : Builder) (x : Fin 4) (o : Obj p) (t : Time) : Builder :=
  let b := send b x o t
  { b with backlog := b.backlog ++ [o] }
-- Run modes: 0 is the negative control, 1 is repaired, 2 uses the alias with
-- whole-PC relay, 3 uses the alias without it (negative control).
variable (mode : Nat)

def buildTime (b : Builder) (t : Nat) : Builder :=
  let b := ([0, 1, 2] : List (Fin 4)).foldl
    (fun b x => pushTick b x (t : Int)) { b with outgoing := [] }
  if t ≤ 6 then sendMany b [0, 1, 2] b.outgoing t else
  if t = 12 then
    let b := sendMany b [0, 1] b.outgoing t
    manual (manual b 0 (faultAck 100) t) 0 (faultAck 101) t
  else if t = 13 then manual (sendMany b [1] b.outgoing t) 1 faultHead t
  else if t = 14 then
    let b := sendMany b [1] b.outgoing t
    if mode == 2 || mode == 3 then
      let target := ((buildWorld b.nodes 1).st.base.blocks.find?
        (fun B => B.slot == 3)).getD .genesis
      let aliasTarget := Block.node target.parent target.slot target.root (target.body + 1)
      let C : PC 4 := ⟨3, aliasTarget,
        [⟨.seat (.ack 3) 1, target.root⟩, ⟨.seat (.ack 3) 3, target.root⟩]⟩
      let b := send b 1 (ofWire p ⟨.none, .pc C⟩) t
      { b with backlog := b.backlog ++ [faultAck 3] }
    else manual b 1 (faultAck 3) t
  else if t = 19 then
    let b := sendMany b [0, 1, 2] b.backlog.eraseDups t
    if mode == 1 || mode == 2 then sendMany b [0, 1, 2]
      (([0, 1, 2] : List (Fin 4)).flatMap (fun x =>
        (buildWorld b.nodes x).st.pcs.map (fun C => ofWire p ⟨.none, .pc C⟩))).eraseDups t
    else b
  else if 19 < t then sendMany b [0, 1, 2] b.outgoing t
  else b
def built : Builder := (List.range (horizon + 1)).foldl (buildTime mode) {}
def rho : V2.D.Run (Fin 4) (pcsaWith .idle p unitCodec) :=
  { seed with events := (built mode).events }

/-- The same identity committee map is used at every fresh label. -/
theorem recovery_view_fresh_committees :
    V2.D.CStar (pcsaFamilies p unitCodec).fresh (rho mode) := by
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | fg => exact hl.elim
    | head s => exact Function.bijective_id
    | ack s => exact Function.bijective_id

/-- The FG committee is fixed and linked. -/
theorem recovery_view_linked_committee :
    V2.D.Linked (pcsaFamilies p unitCodec).linked (rho mode) := by
  refine ⟨4, Equiv.refl (Fin 4), ?_⟩
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | head s => exact hl.elim
    | ack s => exact hl.elim
    | fg => exact ⟨rfl, fun _ => rfl⟩

/-- The fault cap holds for the actual finite participant set. -/
theorem recovery_view_quarter_cap : QuarterCap p unitCodec (rho mode) := by
  rw [QuarterCap_def, Gen.V2.Duty.faulty_def]
  change 4 * (Finset.univ \ ({0, 1, 2} : Finset (Fin 4))).card ≤ 4
  decide

/-- All honest nodes are awake from GST onward. -/
theorem recovery_view_full_participation : Gen.V2.Duty.FullParticipation E (rho mode) E.t_GST := by
  intro x _ t ht _
  change (19 : Int) ≤ t at ht
  change decide (t ≤ 6 ∨ 19 ≤ t ∨
    (x = 0 ∧ t = 13) ∨ (x = 1 ∧ (t = 12 ∨ t = 13 ∨ t = 14))) = true
  exact decide_eq_true (Or.inr (Or.inl ht))

/-- An honest proposer occurs in every recovery interval of length four. -/
theorem recovery_view_proposer_gap : ∀ t : Time, E.t_GST ≤ t → t + 4 ≤ (rho mode).horizon →
    ∃ s : Slot,
      t < V2.D.proposalTime (pcsaInterface p unitCodec (m := .idle)).toInterface s ∧
      V2.D.proposalTime (pcsaInterface p unitCodec (m := .idle)).toInterface s ≤ t + 4 ∧
      Gen.V2.Duty.HonestSlot (rho mode)
        (pcsaInterface p unitCodec (m := .idle)).toInterface s := by
  intro t ht _
  try delta Slot Time at *
  change (19 : Int) ≤ t at ht
  refine ⟨(t / 4).toNat + 1, ?_, ?_, ?_⟩
  · change t < 4 * (((t / 4).toNat + 1 : Nat) : Int)
    omega
  · change 4 * (((t / 4).toNat + 1 : Nat) : Int) ≤ t + 4
    omega
  · have hs : 5 ≤ (t / 4).toNat + 1 := by omega
    have hn : (t / 4).toNat + 1 ≠ 3 := by omega
    rw [Gen.V2.Duty.HonestSlot_def]
    refine ⟨Nat.zero_lt_succ _, ?_⟩
    change (if (t / 4).toNat + 1 = 3 then (1 : Fin 4)
      else if (t / 4).toNat + 1 = 1 ∨ 5 ≤ (t / 4).toNat + 1 then 0 else 3) ∈
        ({0, 1, 2} : Finset (Fin 4))
    rw [ite_eq_right hn, ite_eq_left (Or.inr hs)]
    decide

abbrev node0 : Node p := ⟨initial p.n, RecordOnce.initial⟩
abbrev world (w : Array (Node p)) : Fin 4 → Node p := fun x => w.getD x.val node0

section
variable (r : V2.D.Run (Fin 4) (pcsaWith .idle p unitCodec))

def cachedStep (w : Array (Node p)) (e : V2.Event (Fin 4) (Obj p)) : Array (Node p) :=
  Array.ofFn (V2.D.World.step E r (world w) e)

/-- Materializing a finite world preserves the actual engine step at each node. -/
theorem recovery_view_cached_step_exact (w : Array (Node p))
    (e : V2.Event (Fin 4) (Obj p)) (x : Fin 4) :
    world (cachedStep r w e) x = V2.D.World.step E r (world w) e x := by
  have h (f : Fin 4 → Node p) : (Array.ofFn f).getD x.val node0 = f x := by
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_ofFn]; exact x.isLt)]
    exact Array.getElem_ofFn _
  exact h (V2.D.World.step E r (world w) e)

/-- Cached folds have the same semantics as the engine's event fold. -/
theorem recovery_view_cached_fold_exact (es : List (V2.Event (Fin 4) (Obj p)))
    (w : Array (Node p)) :
    world (es.foldl (cachedStep r) w) = es.foldl (V2.D.World.step E r) (world w) := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih, funext (recovery_view_cached_step_exact r w e)]
    rfl

def trace : Array (Array (Node p)) :=
  r.events.foldl (fun acc e =>
    acc.push (cachedStep r (acc.getD (acc.size - 1) #[]) e)) #[Array.replicate 4 node0]

def atIndex (tr : Array (Array (Node p))) (i : Nat) (x : Fin 4) : Node p :=
  world (tr.getD i #[]) x

def beforeTick (tr : Array (Array (Node p))) (x : Fin 4) (t : Time) : Node p :=
  atIndex tr ((r.tickIdx? x t).getD 0) x

def readTick (tr : Array (Array (Node p))) (x : Fin 4) (t : Time) : State 4 :=
  clock p (beforeTick r tr x t).st t

end

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

abbrev FixtureEvent := V2.Event (Fin 4) (Obj p)
instance : DecidableEq (pcsaWith .idle p unitCodec).Object :=
  inferInstanceAs (DecidableEq (Obj p))
instance : DecidableEq FixtureEvent :=
  inferInstanceAs (DecidableEq (V2.Event (Fin 4) (Obj p)))
instance : BEq FixtureEvent := ⟨fun x y => decide (x = y)⟩

def pcObj (C : PC 4) : Obj p := ofWire p ⟨.none, .pc C⟩

/-- The carried PC test of `carriesS`. -/
def carriesPC (o : Obj p) (C : PC 4) : Bool :=
  match o.payload with
  | .ack _ => (C.acks.map (ofAck p)).contains o
  | .proposal N => (C.slot == N.erase.slot && C.target.root == N.erase.root) ||
      N.pc.any (fun d => d.slot == C.slot && d.target.root == C.target.root)
  | .pc c => c.slot == C.slot && c.target.root == C.target.root
  | _ => false

/-- The exact-target PC test (43733fe), for the control. -/
def carriesPCExact (o : Obj p) (C : PC 4) : Bool :=
  match o.payload with
  | .ack _ => (C.acks.map (ofAck p)).contains o
  | .proposal N => C.target == N.erase ||
      N.pc.any (fun d => d.slot == C.slot && d.target == C.target)
  | .pc c => c.slot == C.slot && c.target == C.target
  | _ => false

/-- The PCs that the call of `o` installs. -/
def installedBy (st : State 4) (o : Obj p) : List (PC 4) :=
  (PCSA.process p st (toWire p o)).pcs.filter (fun C => !st.pcs.contains C)

def handlesTest (st : State 4) (o u : Obj p) : Bool :=
  decide (o = u) || (match (toWire p o).decode with
  | some (.block s N) => namedParentHeld st N &&
      (match parentFG st N.erase with
      | some P => blockAccepted p st s N P &&
          (N.raw.map (ofHead p) ++ N.rows.map (ofRow p) ++ N.pcAcks.map (ofAck p)).contains u
      | none => false)
  | some (.pc C) => (C.acks.map (ofAck p)).contains u
  | _ => false) || (installedBy st o).any (fun C => decide (u = pcObj C) && carriesPC o C)

/-- A PC object is carried exactly when the carried PC test passes. -/
theorem carriesS_pcObj (o : Obj p) (C : PC 4) :
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
theorem recovery_view_handles_exact (st : State 4) (o u : Obj p) :
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
def handledObjects (st : State 4) (o : Obj p) : List (Obj p) :=
  (o :: carriedObjects o ++ (installedBy st o).map pcObj).filter (fun u => handlesTest st o u)

def emitted (r : V2.D.Run (Fin 4) (pcsaWith .idle p unitCodec))
    (tr : Array (Array (Node p))) (i : Nat) : List (Obj p) :=
  match r.events[i]? with
  | some (.tick x t) => (V2.D.tick E r (atIndex tr i x) x t).2
  | _ => []


def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"Recovery view counterexample: {label} failed")
  IO.println s!"Recovery view counterexample: {label}: PASS"

def capTarget : Block := .node .genesis 3 ⟨3⟩ 0
def oneAck : AckWire 4 := ⟨.seat (.ack 3) 1, ⟨3⟩⟩
def capSource : State 4 :=
  { base := { (GridCO.initial 4 .root) with now := 19, blocks := [.genesis, capTarget] }
    ackPool := [oneAck] }
def capReceiver : State 4 :=
  { capSource with ackPool :=
      [⟨.seat (.ack 3) 3, ⟨100⟩⟩, ⟨.seat (.ack 3) 3, ⟨101⟩⟩, oneAck] }

/-- A relayed third ack can be handled but refused, so the PC does not form. -/
theorem recovery_view_capped_ack_blocks_pc :
    (process p capSource (toWire p (faultAck 3))).pcs.length = 1 ∧
      (process p capReceiver (toWire p (faultAck 3))).pcs = [] ∧
      processedS p (process p capReceiver (toWire p (faultAck 3))) (faultAck 3) = false ∧
      excludesS p capReceiver (faultAck 3) = false := by
  decide

/-- A whole PC supplies its acks despite the receiver's existing cap. -/
theorem recovery_view_whole_pc_bypasses_cap :
    (process p capReceiver (toWire p
      (⟨.none, .pc ⟨3, capTarget, [oneAck, ⟨.seat (.ack 3) 3, ⟨3⟩⟩]⟩⟩ : Obj p))).pcs.length =
        1 := by
  decide

/-- The empty gossip hook is separate from the engine acceptance relay. -/
theorem recovery_view_no_local_pc_gossip (nd : Node p) (t : Time) :
    (pcsaWith .idle p unitCodec).gossip nd t = [] := rfl

#print axioms carriedObjects_signed
#print axioms carriesS_pcObj
#print axioms recovery_view_quarter_cap
#print axioms recovery_view_full_participation
#print axioms recovery_view_proposer_gap
#print axioms recovery_view_fresh_committees
#print axioms recovery_view_linked_committee
#print axioms recovery_view_cached_step_exact
#print axioms recovery_view_cached_fold_exact
#print axioms recovery_view_handles_exact
#print axioms recovery_view_capped_ack_blocks_pc
#print axioms recovery_view_whole_pc_bypasses_cap
#print axioms recovery_view_no_local_pc_gossip


def capPC : PC 4 := ⟨3, capTarget, [oneAck, ⟨.seat (.ack 3) 3, ⟨3⟩⟩]⟩
def aliasPC : PC 4 := { capPC with target := .node .genesis 3 ⟨3⟩ 1 }

/-- The alias passes the wire check and installs the held target's PC. -/
theorem recovery_view_alias_installs_real :
    wellFormed p (toWire p (pcObj aliasPC)) = true ∧
      (process p capSource (toWire p (pcObj aliasPC))).pcs = [capPC] ∧
      processedS p (process p capSource (toWire p (pcObj aliasPC))) (pcObj aliasPC) = false := by
  decide

/-- The alias carries the installed certificate: the PC tests read the root. -/
theorem recovery_view_alias_carries_real : carriesS p (pcObj aliasPC) (pcObj capPC) := by
  rw [carriesS_pcObj]
  decide

/-- Control: the exact-target test of 43733fe does not carry the real PC. -/
theorem recovery_view_alias_exact_control :
    carriesPCExact (pcObj aliasPC) capPC = false ∧ carriesPC (pcObj aliasPC) capPC = true := by
  decide

/-- The alias call at the source store handles the real certificate. -/
theorem recovery_view_alias_handles_real :
    handlesS p capSource (pcObj aliasPC) (pcObj capPC) := by
  apply (recovery_view_handles_exact capSource (pcObj aliasPC) (pcObj capPC)).mpr
  decide

/-- An alias delivery into the source store accepts the real PC, so the
acceptance relay obliges its delivery. -/
theorem recovery_view_alias_accepted
    (r : V2.D.Run (Fin 4) (pcsaWith .idle p unitCodec)) (i : Nat) (x : Fin 4) (t : Time)
    (he : r.events[i]? = some (.deliver x (pcObj aliasPC) t))
    (hs : (V2.D.Run.stateBefore E r i x).st = capSource) :
    V2.D.Run.acceptsAt E r i x (pcObj capPC) t := by
  refine ⟨⟨pcObj aliasPC, he, ?_⟩, ?_, ?_⟩
  · change handlesS p (V2.D.Run.stateBefore E r i x).st _ _
    rw [hs]
    exact recovery_view_alias_handles_real
  · change processedS p (V2.D.Run.stateBefore E r i x).st (pcObj capPC) = false
    rw [hs]
    decide
  · rw [V2.D.Run.stateBefore_succ E r he]
    change processedS p (Function.update (V2.D.Run.stateBefore E r i) x
      ((pcsaWith .idle p unitCodec).process (V2.D.Run.stateBefore E r i x) (pcObj aliasPC))
      x).st (pcObj capPC) = true
    rw [Function.update_self]
    change processedS p (process p (V2.D.Run.stateBefore E r i x).st
      (toWire p (pcObj aliasPC))) (pcObj capPC) = true
    rw [hs]
    decide

/-- The ordinary completing ack handles the same PC under the relay model. -/
theorem recovery_view_ack_handles_pc : handlesS p capSource (faultAck 3) (pcObj capPC) := by
  apply (recovery_view_handles_exact capSource (faultAck 3) (pcObj capPC)).mpr
  decide

#print axioms recovery_view_alias_installs_real
#print axioms recovery_view_alias_carries_real
#print axioms recovery_view_alias_exact_control
#print axioms recovery_view_alias_handles_real
#print axioms recovery_view_alias_accepted
#print axioms recovery_view_ack_handles_pc

def audit : IO Unit := do
  IO.println s!"Recovery test mode: {mode}"
  let r := rho mode
  let es : Array FixtureEvent := r.events.toArray
  let tr := (trace r)
  let hs := ([0, 1, 2] : List (Fin 4))
  let is := List.range es.size
  let states := List.range tr.size
  let emissions := is.flatMap (fun i =>
    let e := es.getD i (.tick 0 0)
    (emitted r tr i).map (fun o => (e.node, o, e.time)))
  let hasEmission := fun u o t =>
    emissions.any (fun row => row.1 = u && row.2.1 == o && row.2.2 ≤ t)
  require "schedule" (decide ((r.events : List FixtureEvent).Nodup) &&
    (es.toList.zip (es.toList.drop 1)).all (fun ef => decide (ef.1.key ≤ ef.2.key)) &&
    es.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ horizon) && hs.contains e.node &&
      match e with | .restart .. => false | _ => true) &&
    (List.range (horizon + 1)).all (fun t => hs.all (fun x => es.contains (.tick x (t : Int)))))
  require "wire/dependencies/freshness" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver x o _ => (pcsaWith .idle p unitCodec).wellFormed o &&
        depsS p (atIndex tr i x).st o && !processedS p (atIndex tr i x).st o
    | _ => true))
  require "direct signatures" (es.all (fun e =>
    match e with
    | .deliver _ o t => hs.all (fun u =>
        if r.holder o.auth == some u then hasEmission u o t else true)
    | _ => true))
  require "carried signatures" (es.all (fun e =>
    match e with
    | .deliver _ o t => (carriedObjects o).all (fun a => hs.all (fun u =>
        if r.holder a.auth == some u then hasEmission u a t else true))
    | _ => true))
  let bodies := (states.flatMap (fun i => hs.flatMap (fun x =>
    (atIndex tr i x).st.namedBodies))).eraseDups
  require "named root collision freedom" (
    es.all (fun e => match e with
      | .deliver _ o _ => match o.payload with | .proposal X => bodies.contains X | _ => true
      | _ => true) && bodies.all (fun X => bodies.contains X.parent) &&
    bodies.all (fun X => bodies.all (fun Y => if X.root == Y.root then X == Y else true)))
  require "stage-one frame" (states.all (fun i => hs.all (fun x =>
    let st := (atIndex tr i x).st
    st.fg.F == .genesis && (controls p st).Z == .genesis && (controls p st).lo == 0)))
  require "fault cap/committee maps" (decide (4 * 1 ≤ p.n) &&
    (List.finRange 4).all (fun i => seats (.base .fg) i == i &&
      seats (.base (.head 5)) i == i && seats (.base (.ack 5)) i == i))
  let auditDelivery := fun (dl : Time → Time) (cut : Time) =>
    let handlesBy := fun x o t => is.any (fun j =>
      match es.getD j (.tick 0 0) with
      | .deliver y a u => x == y && decide (t ≤ u ∧ u < dl t) &&
          handlesTest (atIndex tr j x).st a o
      | _ => false)
    let excluded := fun x o t =>
      let k := (es.toList.takeWhile (fun e => decide (e.time < dl t))).length
      excludesS p (atIndex tr k x).st o
    emissions.all (fun row => let (_, o, t) := row
      hs.all (fun x => if dl t ≤ cut && !excluded x o t then handlesBy x o t else true)) &&
    is.all (fun i => match es.getD i (.tick 0 0) with
      | .deliver y o t => (handledObjects (atIndex tr i y).st o).all (fun a =>
          if !processedS p (atIndex tr i y).st a && processedS p (atIndex tr (i + 1) y).st a then
            hs.all (fun x =>
              if !processedS p (atIndex tr (i + 1) x).st a && dl t ≤ cut && !excluded x a t then
                handlesBy x a t else true)
          else true)
      | _ => true)
  -- Modes 1 and 2 deliver whole PCs at GST; modes 0 and 3 are negative controls.
  let healed := mode == 1 || mode == 2
  let tag := if mode == 1 then "regression" else if mode == 2 then "alias regression"
    else if mode == 3 then "alias negative control" else "negative control"
  require (if healed then "RECOVERY strict delivery including whole-PC relay"
    else s!"{tag}: missing whole-PC relay violates RECOVERY")
    (auditDelivery (fun t => max t 19 + 1) horizon == healed)
  require "CLEAN through anchor freeze z_1=7" (auditDelivery (fun t => t + 1) 7 &&
    ([0, 1] : List Nat).all (fun j => decide (1 <
      (hs.filter (fun x => E.awake x (4*j+1) && E.awake x (4*j+2))).length)))
  require "RECOVERY full participation and G=4 recurrence" (
    (List.range (horizon + 1)).all (fun t =>
      if 19 ≤ t then hs.all (fun x => E.awake x t) else true) &&
    (List.range (horizon + 1)).all (fun t => if 19 ≤ t && t + 4 ≤ horizon then
      (List.range 17).any (fun s => decide (t < 4*s ∧ 4*s ≤ t+4) &&
        hs.contains (seats (.prop s) ⟨0, by change 0 < 1; decide⟩)) else true))
  require "parameter delays and recurrence bound" (decide (E.Δ = p.Δ ∧ E.Δ ≤ 1 ∧ 4*p.Δ ≤ 4))
  require "ShortBreak anchor/first slot/window" (E.awake 0 4 &&
    decide (nQuorum p.n ≤ (hs.filter (fun x => E.awake x 5 && E.awake x 6)).length) &&
    E.awake 0 20 && decide (19 + 1 ≤ 20 ∧ 1 < 5 ∧ 5 - 1 - 1 ≤ p.k - 1 ∧ 26 ≤ horizon))
  require "anchor PC is common before the break" (hs.all (fun x =>
    (readTick r tr x 7).pcs.any (fun pc => pc.slot == 1 && pc.target.root == ⟨1⟩)))
  require "first eligible positive proposer label" ((List.range 5).all (fun s =>
    decide (4 * (s : Int) < 20)))
  require "first gate meets the advertised bound" (decide
    (SA.gateTime p.toParams 5 ≤ E.t_GST + 4 + 7*p.Δ))
  require "F2 participation at the first slot" (decide (nQuorum p.n ≤
    (hs.filter (fun x => E.awake x 21 && E.awake x 22)).length))
  require "F4 no live locks at either read" (hs.all (fun x =>
    ([20, 21] : List Time).all (fun t =>
      (readTick r tr x t).base.obligations.all (fun row => decide (row.2.2 ≤ t)))))
  require "F5 proposer tree present at every HEAD read" (hs.all (fun x =>
    (readTick r tr 0 20).base.blocks.all (fun B => (readTick r tr x 21).base.blocks.contains B)))
  require "freeze readers equal inclusive output readers" (es.all (fun e => match e with
    | .deliver _ _ t => decide (t ≠ 23 ∧ t ≠ 63)
    | _ => true))
  let prop5 := (emitted r tr ((r.tickIdx? 0 20).getD 0)).find? (fun o =>
    match o.payload with | .proposal _ => true | _ => false)
  require "F5 proposal admitted at every HEAD read" (match prop5 with
    | some o => match o.payload with
      | .proposal N => hs.all (fun x =>
          (readTick r tr x 21).base.blocks.contains N.erase && processedS p (readTick r tr x 21) o)
      | _ => false
    | none => false)
  require "corrected F4 proposer-root reachability" (
    let st := (readTick r) tr 0 20
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    let raw := proposerVotes st 5
    let support := proposerSupport st 5
    Block.preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)))
  let viewRoot := fun x => ((voterPC p (readTick r tr x 21) 5).map PC.target).map Block.root
  IO.println s!"F3 voter roots: {reprStr (hs.map viewRoot)}"
  IO.println s!"PC slots before proposal: {hs.map (fun x => (readTick r tr x 20).pcs.map PC.slot)}"
  require (if healed then s!"{tag}: F3 common view" else s!"{tag}: F3 fails")
    ((match prop5 with
    | some o => match o.payload with
      | .proposal N => hs.any (fun x =>
          (voterPC p (readTick r tr x 21) 5).map PC.target != N.pc.map PC.target)
      | _ => false
    | none => false) == !healed)
  require (if healed then s!"{tag}: strong coverage at z_5"
    else s!"{tag}: strong coverage fails at z_5") ((match prop5 with
    | some o => match o.payload with
      | .proposal N => !Block.preceq N.erase (strong (readTick r tr 1 23))
      | _ => false
    | none => false) == !healed)
  if mode == 2 then
    let prop13 := (emitted r tr ((r.tickIdx? 0 52).getD 0)).find? (fun o =>
      match o.payload with | .proposal _ => true | _ => false)
    require "alias regression: F3 holds after mix time 49" (
      decide (SA.voteTime p.toParams (5 + 2 * p.k - 1) = 49) &&
      match prop13 with
      | some o => match o.payload with
        | .proposal N => hs.all (fun x =>
            (voterPC p (readTick r tr x 53) 13).map PC.target == N.pc.map PC.target)
        | _ => false
      | none => false)
  require "long-break horizon" (decide (19 + 2 * pcsaL p + 4 + 8 ≤ horizon))
  let boundedProposals := emissions.filterMap (fun row =>
    match row.2.1.payload with
    | .proposal N => if 4 * (N.slot : Int) + 6 ≤ 61 then some N else none
    | _ => none)
  require (if healed then s!"{tag}: a bounded proposal meets the checked healing outputs"
    else s!"{tag}: each bounded proposal fails a healed conclusion") ((
    boundedProposals.all (fun N =>
      !Block.preceq N.erase (strong (readTick r tr 1 63)) ||
      !Block.preceq N.erase (strong (readTick r tr 0 63)) ||
      !Block.compatible (confirmed (readTick r tr 0 63)) (strong (readTick r tr 1 63)))) ==
      !healed)
  IO.println s!"Recovery audit: {es.size} events, {bodies.length} named bodies"



/-- The first schedule change delivers PC(3) to node 0 at GST. -/
def auditRepairBoundary : IO Unit := do
  let old := (rho 0).events
  let repaired := (rho 1).events
  let i := ((old.zip repaired).takeWhile (fun pair => pair.1 == pair.2)).length
  require "regression: first changed event is whole PC(3) at GST" (
    match repaired[i]? with
    | some (.deliver x o t) => x == 0 && t == 19 &&
        match o.payload with | .pc C => C.slot == 3 | _ => false
    | _ => false)
  IO.println s!"First changed schedule index: {i}; deliver PC(3) to node 0 at t=19"
  let r := rho 0
  let tr := trace r
  let i := r.events.findIdx (fun e => e == .deliver 1 (faultAck 3) 14)
  require "regression: installing ack at t=14 handles PC(3)" (
    (installedBy (atIndex tr i 1).st (faultAck 3)).any (fun C =>
      C.slot == 3 && handlesTest (atIndex tr i 1).st (faultAck 3) (pcObj C) &&
      !processedS p (atIndex tr i 1).st (pcObj C) &&
      processedS p (atIndex tr (i + 1) 1).st (pcObj C)))
  IO.println s!"Missing whole-PC relay obligation: event {i}; PC(3) installed at node 1 at t=14"

#eval auditRepairBoundary

/-- The alias changes the installing call; the call accepts the real PC. -/
def auditAliasBoundary : IO Unit := do
  let old := (rho 0).events
  let r := rho 2
  let tr := trace r
  let i := ((old.zip r.events).takeWhile (fun pair => pair.1 == pair.2)).length
  require "alias regression: first changed call installs, handles and accepts the real PC" (
    match r.events[i]? with
    | some (.deliver x o t) => x == 1 && t == 14 &&
        match o.payload with
        | .pc declared => (installedBy (atIndex tr i x).st o).any (fun C =>
            C.slot == 3 && C.target.root == declared.target.root && C.target != declared.target &&
            handlesTest (atIndex tr i x).st o (pcObj C) &&
            !processedS p (atIndex tr i x).st (pcObj C) &&
            processedS p (atIndex tr (i + 1) x).st (pcObj C) &&
            !processedS p (atIndex tr (i + 1) x).st o &&
            !carriesPCExact o C)
        | _ => false
    | _ => false)
  IO.println s!"First alias difference: event {i}; declared PC at node 1 at t=14"

#eval auditAliasBoundary

#eval audit 0
#eval audit 1
#eval audit 2
#eval audit 3
end AvailableChain.PCSA.Run.Tests.RecoveryViewCounterexample
end
