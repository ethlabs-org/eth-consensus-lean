module
public import Mathlib.Logic.Equiv.Defs -- shake: keep (re-export)
public import Mathlib.Tactic.Ring -- shake: keep (re-export)
public import AvailableChainEngineV2.Engine.Duty.Spec
public import AvailableChainFGSA.Model.Handlers -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Clock -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Frame -- shake: keep (re-export)
public import AvailableChainFGSA.Model.FrameNext -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Restart

@[expose] public section

/-! The FG-SA protocol on engine v2 (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11, §3.1 and T7.2).

The v2 protocol `fgsa p c` runs the store model `AvailableChainFGSA` without a
change. The node state is the store and the client record Λ (`Node`). The v2
payload is the store payload `Msg p.n`. A v2 object reaches the store through
the adapter `toWire`, a bijection (`toWireEquiv`), so the store's decode
discipline (J1) does not change. Every hook reads only the store: the store
functions below (`depsS`, `processedS`, `excludesS`, `handlesS`) take the
store, and `fgsa` applies them to `nd.st`. The FG action (`attest`) is the
only duty that reads Λ, and `recordOwn` is the only step that writes it.

v1 `Auth` and `Signed` (namespace `AvailableChain`) and v2 `Auth` and `Signed`
(namespace `AvailableChain.V2`) clash, so this file writes the v2 names as
`V2.D.…` and does not open `AvailableChain.V2`. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan T7.2; 2c I1] The application codec: the run input `x : In` enters the
proposal body as the number `app x`, and `unapp` decodes it (`unapp_app`: a
left inverse of `app`). -/
structure AppCodec (In : Type) where
  app : In → Nat
  unapp : Nat → Option In
  unapp_app : ∀ x, unapp (app x) = some x

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan T7.2; I9] The codec of the unit input: application value `0`, so the
honest proposal is the I9 `propose` output (`withApp_zero`). -/
def unitCodec : AppCodec Unit where
  app _ := 0
  unapp _ := some ()
  unapp_app _ := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Signing labels: a HEAD label for each slot, one fixed FG label, and
one proposal label for each slot. Duties are separate scheduled actions. -/
inductive RunLabel where
  | base (ℓ : Label)
  | prop (s : Slot)
  deriving DecidableEq, Repr

namespace RunLabel

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 154–158; FRAMEWORK E1] The committee size of a label: `n` seats for a
store label, one seat for a proposal duty. -/
def seats (p : Params) : RunLabel → Nat
  | .base _ => p.n
  | .prop _ => 1

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 681; FRAMEWORK E5; plan T7.2] Only an FG label is self-visible: the
node records its own FG row in Λ at its tick. -/
def selfVisible : RunLabel → Bool
  | .base .fg => true
  | _ => false

end RunLabel

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Scheduled actions. FG actions share one signing label. -/
inductive RunDuty where
  | headAction (s : Slot)
  | fgAction (r : Nat)
  | propAction (s : Slot)
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The signing identity of an action. -/
def RunDuty.signLabel : RunDuty → RunLabel
  | .headAction s => .base (.head s)
  | .fgAction _ => .base .fg
  | .propAction s => .prop s

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The scheduled time of an action. -/
def RunDuty.actTime (p : Params) : RunDuty → Time
  | .headAction s => SA.voteTime p.toParams s
  | .fgAction r => p.actionTime r
  | .propAction s => SA.proposalTime p.toParams s

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1; DQ4] The node state: the store (Λ-free, the E5 base) and the
client record Λ. -/
structure Node (p : Params) where
  st : State p.n
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Λ. The plan calls this field `rec`; Lean reserves `Node.rec` for the
  recursor of the structure. -/
  record : RecordOnce

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1] The v2 wire objects of FG-SA. -/
abbrev Obj (p : Params) : Type := V2.Signed RunLabel (RunLabel.seats p) (Msg p.n)

/-! ### The adapter to the store wire (plan §3.1) -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1; FRAMEWORK :336] The store authentication of a v2
authentication: a store-label seat keeps its label and seat; the seat of a
proposal duty is the proposer key of its slot (`Fin 1` has one value); an
unsigned object stays unsigned. -/
def toAuth (p : Params) : V2.Auth RunLabel (RunLabel.seats p) → Auth Label p.n
  | .seat (.base ℓ) i => .seat ℓ i
  | .seat (.prop s) _ => .proposer s
  | .none => .none

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1] The inverse of `toAuth`. -/
def ofAuth (p : Params) : Auth Label p.n → V2.Auth RunLabel (RunLabel.seats p)
  | .seat ℓ i => .seat (.base ℓ) i
  | .proposer s => .seat (.prop s) ⟨0, Nat.one_pos⟩
  | .none => .none

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1; J1] The store wire of a v2 object: the authentication through
`toAuth`, the payload unchanged. Every store handler and the input check see
only `toWire o`. A malformed pair of authentication and payload gives a
malformed store wire, which `Wire.decode` refuses. -/
def toWire (p : Params) (o : Obj p) : Wire p.n := ⟨toAuth p o.auth, o.payload⟩

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1] The v2 object of a store wire (the inverse of `toWire`). -/
def ofWire (p : Params) (w : Wire p.n) : Obj p := ⟨ofAuth p w.auth, w.payload⟩

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1; Opus m15] The adapter is a bijection. -/
def toWireEquiv (p : Params) : Obj p ≃ Wire p.n where
  toFun := toWire p
  invFun := ofWire p
  left_inv := by
    rintro ⟨a, m⟩
    cases a with
    | seat ℓ i =>
        cases ℓ with
        | base ℓ => rfl
        | prop s =>
            have hi : i = ⟨0, Nat.one_pos⟩ := Subsingleton.elim (α := Fin 1) _ _
            subst hi
            rfl
    | none => rfl
  right_inv := by
    rintro ⟨a, m⟩
    cases a <;> rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1] A carried HEAD as a v2 object (through the inverse adapter). -/
def ofHead (p : Params) (h : HeadWire p.n) : Obj p := ofWire p ⟨h.auth, .head h.payload⟩

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan §3.1] A carried row as a v2 object (through the inverse adapter). -/
def ofRow (p : Params) (a : RowWire p.n) : Obj p := ofWire p ⟨a.auth, .row a.payload⟩

/-! ### Duties -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 197–220] The labels due at time `t`: the proposal of the slot whose
proposal time is `t`, the HEAD of the slot whose vote time is `t`, and the FG
action of the round whose action time is `t`. The three candidates come from
the slot of `t` (the action time of round `r` is in slot `rR + 1`), and each
one is due only if its act time is `t`. -/
def duties (p : Params) (t : Time) : List RunDuty :=
  let s := p.slotOf t
  let r := (s - 1) / p.R
  (if SA.proposalTime p.toParams s = t then [.propAction s] else []) ++
    (if SA.voteTime p.toParams s = t then [.headAction s] else []) ++
    (if p.actionTime r = t then [.fgAction r] else [])

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The slot of a time in slot `s` at offset `k`, `0 ≤ k < 4Δ`, is `s`. -/
theorem slotOf_offset (p : Params) (s : Slot) (k : Int) (hk0 : 0 ≤ k)
    (hk : k < 4 * p.Δ) : p.slotOf (4 * p.Δ * s + k) = s := by
  have hΔ : (4 * p.Δ : Int) ≠ 0 := by have : (0 : Int) < p.Δ := p.deltaPos; omega
  unfold Params.slotOf
  rw [add_comm, Int.add_mul_ediv_left _ _ hΔ, Int.ediv_eq_zero_of_lt hk0 hk, zero_add,
    Int.toNat_natCast]

theorem duties_spec (p : Params) (ℓ : RunDuty) (t : Time) :
    ℓ ∈ duties p t ↔ RunDuty.actTime p ℓ = t := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hR : 0 < p.R := by have := p.RLarge; omega
  simp only [duties, List.mem_append]
  constructor
  · intro h
    rcases h with (h | h) | h
    · split_ifs at h with ht
      · rw [List.mem_singleton] at h; subst h; exact ht
      · simp at h
    · split_ifs at h with ht
      · rw [List.mem_singleton] at h; subst h; exact ht
      · simp at h
    · split_ifs at h with ht
      · rw [List.mem_singleton] at h; subst h; exact ht
      · simp at h
  · intro h
    cases ℓ with
    | propAction s =>
        have h' : SA.proposalTime p.toParams s = t := h
        have ht : t = 4 * p.Δ * s + 0 := by
          rw [← h']; simp [SA.proposalTime, GridCO.proposalTime, SA.Params.engine]
        have hs : p.slotOf t = s := by rw [ht]; exact slotOf_offset p s 0 le_rfl (by omega)
        left; left
        rw [hs, ite_eq_left h']
        exact List.mem_singleton_self _
    | headAction s =>
        have h' : SA.voteTime p.toParams s = t := h
        have ht : t = 4 * p.Δ * s + p.Δ := by
          rw [← h']; simp [SA.voteTime, GridCO.voteTime, GridCO.proposalTime,
            SA.Params.engine]
        have hs : p.slotOf t = s := by
          rw [ht]; exact slotOf_offset p s p.Δ (by omega) (by omega)
        left; right
        rw [hs, ite_eq_left h']
        exact List.mem_singleton_self _
    | fgAction r =>
        have h' : p.actionTime r = t := h
        have ht : t = 4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + 2 * p.Δ := by
          rw [← h']
          simp only [Params.actionTime, SA.gateTime, GridCO.gateTime, GridCO.proposalTime,
            SA.Params.engine]
          push_cast
          ring
        have hs : p.slotOf t = r * p.R + 1 := by
          rw [ht]; exact slotOf_offset p _ (2 * p.Δ) (by omega) (by omega)
        have hr : (p.slotOf t - 1) / p.R = r := by
          rw [hs, Nat.add_sub_cancel, Nat.mul_div_cancel _ hR]
        right
        rw [hr, ite_eq_left h']
        exact List.mem_singleton_self _

theorem duties_nodup (p : Params) (t : Time) : (duties p t).Nodup := by
  simp only [duties]
  split_ifs <;> simp

/-! ### Duty payloads -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks] Replace the app and recompute the full digest.
The BODY codec, signed rows, raw list, and support list keep their roles. -/
def withApp (p : Params) (a : Nat) : Msg p.n → Msg p.n
  | .proposal (.node P s _ _ raw sup rows) =>
      .proposal (namedProposal p P s a raw sup rows)
  | m => m

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1236–1253, 1276–1302; plan T7.2] The payload of the base duties (the
AP labels): the HEAD vote at `v_s` and the proposal at `t_s`, with the input in
the body. It reads only the store. There is no base payload for an FG label. -/
def actS (p : Params) {In : Type} (c : AppCodec In) (st : State p.n) :
    RunDuty → In → Option (Msg p.n)
  | .headAction s, _ => if joinedNow p st then some (.head (headVote p st s).root) else none
  | .fgAction _, _ => none
  | .propAction s, x =>
      if joinedNow p st then (propose p st s).map (withApp p (c.app x)) else none

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1304–1313, 1391–1399; plan T7.2] The payload of a duty: `actS` on the
base labels, and the `attest` row body on an FG label. `attest` reads Λ; its
identity argument does not change the body (`attest_signer_irrel`), so seat
`0` is used. `act` returns `none` for `.prop 0` (`propose`). -/
def act (p : Params) {In : Type} (c : AppCodec In) (nd : Node p) :
    RunDuty → In → Option (Msg p.n)
  | .fgAction _, _ => (attest p nd.st nd.record ⟨0, p.nPos⟩).1.map Msg.row
  | ℓ, x => actS p c nd.st ℓ x

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 681, 1391–1399; Opus m11] The own-record step: an FG row signed with
seat `i` records the row `⟨i, height pair, finality pair⟩` in Λ
(`record_row_once`, which does not read the signer); any other object leaves Λ
unchanged. -/
def recordRow? (p : Params) (Λ : RecordOnce) (o : Obj p) : RecordOnce :=
  match o with
  | ⟨.seat (.base .fg) i, .row body⟩ =>
      record_row_once Λ (body.toRow i)
  | _ => Λ

/-! ### Hooks on the store

Each hook is a function of the store and reads the object through `toWire`. A
malformed wire decodes to `none`: `process` refuses it, and it is not
processed and not excluded. -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 519–522; I9 D2; plan T7.2] Dependencies: a proposal needs its stored
exact named parent and its FG projection (`parentFG`); other objects have none. -/
def depsS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.block _ N) => namedParentHeld st N && (parentFG st N.erase).isSome
  | _ => true

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 804–857; DQ9; plan T7.2] Processed: a proposal by root (a stored FG
block has the root of its block, the duplicate test of `blockAccepted`); a
HEAD if its base vote is in the vote pool; a row if it is in the row pool
(which only grows). -/
def processedS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.vote s i b) => decide (baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ st.base.votes)
  | some (.row i body) => decide ((⟨.seat .fg i, body⟩ : RowWire p.n) ∈ st.rowPool)
  | some (.block _ N) => decide (∃ Y ∈ st.fg.TF, Y.root = N.root)
  | none => false

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R6] Permanent invalidity once the immutable parent is held. An absent
parent is a missing dependency, not an invalidity result. -/
def invalidForParent (p : Params) (st : State p.n) (N : NamedProposal p.n) : Bool :=
  if !namedParentHeld st N then false else
  match parentFG st N.erase with
  | none => false
  | some P => !rowsValidForParent p P N.slot N.rows

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Permanent exclusions: a proposal conflicts with finality or fails R6
against a held parent; a HEAD is excluded by the base vote pool. Decoded rows
are never excluded. An absent parent remains a dependency condition. -/
def excludesS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.vote s i b) =>
      GridCO.excludes p.toParams.engine st.base (baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n))
  | some (.row _ _) => false
  | some (.block _ N) => blockExcluded st N.erase || invalidForParent p st N
  | none => false

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 804–829; plan T7.2] Handler calls: the delivered object itself; for a
proposal that the store accepts (`parentFG` and `blockAccepted`, the tests of
`admitBlock`), also its carried HEADs (the raw votes) and its carried rows, as
v2 objects (`ofHead`, `ofRow`). -/
def handlesS (p : Params) (st : State p.n) (o o' : Obj p) : Prop :=
  o = o' ∨ match (toWire p o).decode with
    | some (.block s N) =>
        (namedParentHeld st N = true ∧ ∃ P, parentFG st N.erase = some P ∧
          blockAccepted p st s N P = true) ∧
          (o' ∈ N.raw.map (ofHead p) ∨ o' ∈ N.rows.map (ofRow p))
    | _ => False

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 248–255; plan T7.2] Structural containment: a proposal payload
carries its raw HEADs, its support HEADs and its rows. -/
def carriesS (p : Params) (o o' : Obj p) : Prop :=
  match o.payload with
  | .proposal N =>
      o' ∈ N.raw.map (ofHead p) ∨ o' ∈ N.support.map (ofHead p) ∨ o' ∈ N.rows.map (ofRow p)
  | _ => False

/-! ### The protocol -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[plan T7.2; FRAMEWORK E1, E2, E5, E6] FG-SA on engine v2, with the
application codec `c`.

* State: the store and Λ (`Node`). A restart keeps the cumulative store,
  locks, stable record, F and Λ (`Durable := State p.n × RecordOnce`).
  `acRestart` clears the AC pools, replays retained HEADs and sets the wake time.
* `clock` and `process` run the store functions and keep Λ; `recordOwn`
  writes only Λ (`recordRow?`).
* `act`: HEAD and proposal from the store (`actS`), FG row from `attest`.
* The hooks are the store hooks (`depsS`, `processedS`, `excludesS`,
  `handlesS`) at `nd.st`. -/
def fgsa (p : Params) {In : Type} (c : AppCodec In) : V2.ProtocolSpecD In where
  State := Node p
  Label := RunLabel
  Duty := RunDuty
  signLabel := RunDuty.signLabel
  seats := RunLabel.seats p
  Payload := Msg p.n
  Durable := State p.n × RecordOnce
  init := ⟨initial p.n, RecordOnce.initial⟩
  clock nd t := { nd with st := FGSA.clock p nd.st t }
  actTime := RunDuty.actTime p
  duties := duties p
  duties_spec := duties_spec p
  duties_nodup := duties_nodup p
  act := act p c
  gossip _ _ := []
  process nd o := { nd with st := FGSA.process p nd.st (toWire p o) }
  selfVisible := RunLabel.selfVisible
  recordOwn nd o := { nd with record := recordRow? p nd.record o }
  durable nd := (nd.st, nd.record)
  restore d w := ⟨acRestart p d.1 w, d.2⟩
  wellFormed o := FGSA.wellFormed p (toWire p o)
  depsPresent nd o := depsS p nd.st o
  processed nd o := processedS p nd.st o
  excludes nd o := excludesS p nd.st o
  handles nd o o' := handlesS p nd.st o o'
  carries := carriesS p

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Labels of `fgsa` have decidable equality (the instance of `RunLabel`; the
projection does not unfold at instance transparency). -/
instance (p : Params) {In : Type} (c : AppCodec In) : DecidableEq (fgsa p c).Label :=
  inferInstanceAs (DecidableEq RunLabel)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Duties have decidable equality. -/
instance (p : Params) {In : Type} (c : AppCodec In) : DecidableEq (fgsa p c).Duty :=
  inferInstanceAs (DecidableEq RunDuty)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Payloads of `fgsa` have decidable equality (the instance of `Msg`). -/
instance (p : Params) {In : Type} (c : AppCodec In) : DecidableEq (fgsa p c).Payload :=
  inferInstanceAs (DecidableEq (Msg p.n))

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem ofAuth_eq_1_export :
    type_of% (@ofAuth.eq_1) := @ofAuth.eq_1
private theorem ofAuth_eq_2_export :
    type_of% (@ofAuth.eq_2) := @ofAuth.eq_2
private theorem ofAuth_eq_3_export :
    type_of% (@ofAuth.eq_3) := @ofAuth.eq_3
private theorem ofHead_eq_1_export :
    type_of% (@ofHead.eq_1) := @ofHead.eq_1
private theorem ofRow_eq_1_export :
    type_of% (@ofRow.eq_1) := @ofRow.eq_1
private theorem ofWire_eq_1_export :
    type_of% (@ofWire.eq_1) := @ofWire.eq_1
private theorem toAuth_eq_1_export :
    type_of% (@toAuth.eq_1) := @toAuth.eq_1
private theorem toAuth_eq_2_export :
    type_of% (@toAuth.eq_2) := @toAuth.eq_2
private theorem toAuth_eq_3_export :
    type_of% (@toAuth.eq_3) := @toAuth.eq_3
private theorem toWire_eq_1_export :
    type_of% (@toWire.eq_1) := @toWire.eq_1


/-! Raw payload and row reads for the provisional safety adapter. -/
def safetyProposalErase (p : Params) (o : Obj p) : Option Block :=
  match o.payload with
  | .proposal N => some N.erase
  | _ => none

theorem fgsa_safetyProposalErase_def (p : Params) (o : Obj p) :
    safetyProposalErase p o = (match o.payload with
      | .proposal N => some N.erase
      | _ => none) := rfl

def safetyProposalRows (p : Params) (o : Obj p) : List (RowWire p.n) :=
  match o.payload with
  | .proposal N => N.rows
  | _ => []

theorem fgsa_safetyProposalRows_def (p : Params) (o : Obj p) :
    safetyProposalRows p o = (match o.payload with
      | .proposal N => N.rows
      | _ => []) := rfl


end AvailableChain.FGSA.Run

end
