module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Confirmation

@[expose] public section

/-! # ½ pre-confirmations: acks, the PC store and the PC anchor

The pre-confirmation (PC) layer of a candidate that adds expiring ½ pre-confirmations to a lock
rule, at full committees (the committee of every slot is `V`, so `μ(K_s) = ⌊n/2⌋ + 1` for every
slot, `pcMu`). It adds no write mechanism to the core (the opt-in certified override is off): what
it changes is the block where a head walk starts, and through the heads it selects, the inputs of
the core's own update functions.

* **Ack** (`Ack`): validator `val` acks the key `(slot, target)` as a member of the committee of
  slot `slot + j`, `j ∈ {2, 3}`. An ack is its own message (`Msg := Vote ⊕ Ack`): the code sends
  it as a separate object at the tick of the slot-`(slot + j)` vote, not inside the vote.
* **The PC store** (`PCStore`): the ackers of each `(slot, target, j)` (`acks`), the keys with an
  ack quorum (`pcs`), the keys with pair evidence (`valid`, sticky), the annihilated keys (`dead`,
  sticky), the vote record (`votes`, the code's `rec`: for each slot and validator, the heads of
  its slot votes the node received, also from block payloads) and the node's own ack decisions
  (`myAcks`). All of it is volatile: a restart empties it.
* **Window** `e = max(k, 3)` (`pcWindow`): an ack of a key of slot `s` is admitted only while
  `slot(t) ≤ s + e`, and a key gives authority only through slot `s + e`. The vote record keeps
  the votes of slots `s ≥ slot(t) − e − 2`.
* **Admission** (`onAck`): an ack of `j ∈ {2, 3}` in the window, not yet held, joins its ackers;
  the key joins `pcs` when every ack committee holds `μ` ackers of it (`quorum`, the rule
  "each"). An acker that acks two keys counts for both.
* **Authority** (`refresh`, `authority`): at each evaluation the keys out of the window are
  dropped (with their `valid` and `dead` marks); the **held** keys are those whose target is in
  the frame's tree; two held keys with conflicting targets are both marked `dead`
  (annihilation, which reads the raw held targets and the quorum, not the pair evidence); a held
  key is marked `valid` once `μ` validators have a recorded slot-`s` vote whose head extends the
  target (`pairOk`; equivocators count). The authoritative keys are the held, valid, unannihilated
  ones.
* **D21 projection** (`pcProj`, `pcBase`): for a view of slot `b`, an authoritative key of slot
  `< b` moves its target down to its deepest ancestor in the tree with fewer than `μ`
  non-equivocating opponents (validators with a support vote of the view whose head conflicts
  with it; `d21Opponents`); a key of slot `≥ b` keeps its target. The **base** is the deepest
  projected target.
* **Anchor** (`pcAnchor`, `pcStart`): with a base `Y`, the walk starts at the deepest live lock
  block that extends `Y`, or at `Y`; without one it starts at the parent's anchor (`getAnchor`).
  `headFrom` is the parent's head walk from a given start.

The store is evaluated where the code evaluates it: the handlers (`Candidates/PreConfirmations/
Actions`) keep the refreshed store after the calls that compute a head or decide an ack. The reads
(`ac_head`, `ac_confirmed`) are pure: they evaluate the store without keeping it. The code's reads
keep it (its observation of the confirmed tip reaches the evaluation), and the one divergence this
can cause is a `dead` mark: a read can mark two held conflicting keys dead, the mark is sticky, and
when the older key leaves the window before the next kept evaluation, the code keeps the younger key
dead while here it is authoritative (for example, keys of slots `s₂ < s₁` with conflicting targets,
the slot-`s₂` key reaching its quorum late in slot `s₂ + e` after the node's last kept evaluation,
and a read in that slot). A `valid` mark read off the same store is the same at the next kept
evaluation. The reads are meant to be pure; the code's mutation at a read is the code's defect, not
modelled here. The code also caches the evaluation on (slot, tree size, number of keys, record
version); the definitions evaluate at every call. In the standalone code the tree only grows, so a
hit on that key means the same inputs (`RefreshIdem`); in the code's composite the tree is the
descendants of the finalized tip, which can change at the same size.

Only trivial frames are in scope for the base: outside them the code clamps the base into the
viable tree, which this layer does not model; here the projection falls back to `Φ.F` when no
ancestor in the tree has fewer than `μ` opponents (at a trivial frame genesis has none). -/

namespace Consensus.Goldilocks.PreConfirmations

open SA

variable (sp : SAParams) {FGP : Type}

/-- An ack: validator `val` acks the key `(slot, target)` (a target by root) as a member of the
committee of slot `slot + j`. -/
structure Ack (n : Nat) where
  /-- The acker. -/
  val : Fin n
  /-- The slot of the key. -/
  slot : Nat
  /-- The root of the key's target. -/
  target : Nat
  /-- The ack committee is that of slot `slot + j`. -/
  j : Nat
  deriving DecidableEq

/-- The PC store. -/
structure PCStore (n : Nat) where
  /-- The ackers of each `(slot, target, j)`. -/
  acks : Nat → Nat → Nat → Set (Fin n)
  /-- The keys `(slot, target)` with an ack quorum. -/
  pcs : Set (Nat × Nat)
  /-- The keys whose pair evidence was seen (sticky). -/
  valid : Set (Nat × Nat)
  /-- The annihilated keys (sticky). -/
  dead : Set (Nat × Nat)
  /-- The vote record: for each slot and validator, the heads (by root) of its recorded votes. -/
  votes : Nat → Fin n → Set Nat
  /-- The node's own ack decision of each slot (a target by root). -/
  myAcks : Nat → Option Nat

/-- The empty store (initial, and after every restart). -/
def PCStore.empty {n : Nat} : PCStore n where
  acks _ _ _ := ∅
  pcs := ∅
  valid := ∅
  dead := ∅
  votes _ _ := ∅
  myAcks _ := none

/-- The PC threshold `μ = ⌊n/2⌋ + 1` (full committees): the ack quorum of each ack committee, the
ack's fast test, the pair evidence and the D21 projection. -/
def pcMu : Nat := sp.n / 2 + 1

/-- The PC window `e = max(k, 3)`. -/
def pcWindow : Nat := max sp.k 3

/-- The ack committees: `j ∈ {2, 3}`. -/
def AckSlot (j : Nat) : Prop := j = 2 ∨ j = 3

/-! ## The vote record and the acks -/

/-- `_record`: a vote of slot `s ≥ slot(t) − e − 2` adds its head to its validator's record of
its slot; an older vote changes nothing. -/
def recordVote (P : PCStore sp.n) (t : Time) (v : Vote sp.n) : PCStore sp.n :=
  if sp.slot t ≤ v.slot + pcWindow sp + 2 then
    { P with votes := fun s i => if s = v.slot ∧ i = v.val then insert v.head (P.votes s i)
                                 else P.votes s i }
  else P

/-- The votes of a list recorded in order. -/
def recordVotes (P : PCStore sp.n) (t : Time) (l : List (Vote sp.n)) : PCStore sp.n :=
  l.foldl (fun Q v => recordVote sp Q t v) P

/-- The ack quorum of the key `(s, X)`: `μ` ackers in each ack committee. -/
def quorum (P : PCStore sp.n) (s X : Nat) : Prop :=
  ∀ j, AckSlot j → pcMu sp ≤ (P.acks s X j).ncard

open Classical in
/-- `on_ack`: an ack of an ack committee, in the window and not yet held, joins its ackers, and
its key joins `pcs` when it reaches the quorum; otherwise nothing changes. -/
noncomputable def onAck (P : PCStore sp.n) (t : Time) (a : Ack sp.n) : PCStore sp.n :=
  if ¬ AckSlot a.j ∨ a.slot + pcWindow sp < sp.slot t ∨ a.val ∈ P.acks a.slot a.target a.j then P
  else
    let P₁ := { P with acks := fun s X j =>
      if s = a.slot ∧ X = a.target ∧ j = a.j then insert a.val (P.acks s X j) else P.acks s X j }
    if quorum sp P₁ a.slot a.target then { P₁ with pcs := insert (a.slot, a.target) P₁.pcs }
    else P₁

/-! ## Authority -/

/-- The targets of roots `r` and `r'` are in the tree and conflict. -/
def ConflictsR (Φ : Frm sp.n FGP) (r r' : Nat) : Prop :=
  ∃ A ∈ Φ.tree, ∃ B ∈ Φ.tree, A.root = r ∧ B.root = r' ∧ ¬ Compatible Φ.tree A B

/-- The pair evidence of the key `(s, X)`: `μ` validators with a recorded slot-`s` vote whose head
(in the tree) extends the target (equivocators count). -/
def pairOk (Φ : Frm sp.n FGP) (P : PCStore sp.n) (k : Nat × Nat) : Prop :=
  pcMu sp ≤ {i | ∃ h ∈ P.votes k.1 i, ∃ X ∈ Φ.tree, X.root = k.2 ∧ AncR Φ X h}.ncard

/-- The key is in the window at `t`: `slot(t) ≤ s + e`. -/
def InWindow (t : Time) (k : Nat × Nat) : Prop := sp.slot t ≤ k.1 + pcWindow sp

/-- The evaluation of the store at `(Φ, t)` (`_authority`): the keys out of the window are
dropped with their marks; the held keys with a conflicting held key are marked `dead`; the held
keys with pair evidence are marked `valid`. -/
def refresh (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) : PCStore sp.n :=
  let pcs := {k | k ∈ P.pcs ∧ InWindow sp t k}
  let held := {k | k ∈ pcs ∧ InTree Φ k.2}
  { P with
    pcs := pcs
    dead := {k | k ∈ P.dead ∧ k ∈ pcs} ∪ {k | k ∈ held ∧ ∃ k' ∈ held, ConflictsR sp Φ k.2 k'.2}
    valid := {k | k ∈ P.valid ∧ k ∈ pcs} ∪ {k | k ∈ held ∧ pairOk sp Φ P k} }

/-- The authoritative keys at `(Φ, t)`: of the evaluated store, the held, valid, unannihilated
keys. -/
def authority (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) : Set (Nat × Nat) :=
  {k | k ∈ (refresh sp P Φ t).pcs ∧ InTree Φ k.2 ∧ k ∈ (refresh sp P Φ t).valid ∧
    k ∉ (refresh sp P Φ t).dead}

/-! ## The base and the anchor -/

/-- The D21 opponents of `Y` in a view: the validators that do not equivocate in its votes and
have a support vote whose head (in the tree) conflicts with `Y`. The views the handlers pass have
every support vote's head in the frame's tree (a vote is resolved only with its head in the tree,
and a proposal's support entries are taken only with their head in the tree), so "in the tree"
drops no support vote. -/
def d21Opponents (Φ : Frm sp.n FGP) (V : View sp.n) (Y : Blk sp.n FGP) : Set (Fin sp.n) :=
  {i | i ∉ equivocators V.votes ∧ ∃ x ∈ V.support, x.val = i ∧
    ∃ H ∈ Φ.tree, H.root = x.head ∧ ¬ Compatible Φ.tree H Y}

/-- The D21 projection, for a view of slot `b`, of a key of slot `s` with target `X`: for
`s < b`, the deepest ancestor of `X` in the tree with fewer than `μ` D21 opponents (`Φ.F` when
there is none); for `s ≥ b`, `X`. -/
noncomputable def pcProj (Φ : Frm sp.n FGP) (V : View sp.n) (b : Int) (s : Nat)
    (X : Blk sp.n FGP) : Blk sp.n FGP :=
  if (s : Int) < b then
    (deepest Φ {Y | Y ∈ Φ.tree ∧ Φ.Anc Y X ∧ (d21Opponents sp Φ V Y).ncard < pcMu sp}).getD Φ.F
  else X

/-- `pc_base`: the deepest D21 projection of an authoritative key's target, for a view `V` of
slot `b`; `none` when no key is authoritative. -/
noncomputable def pcBase (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) (V : View sp.n)
    (b : Int) : Option (Blk sp.n FGP) :=
  deepest Φ {Y | ∃ k ∈ authority sp P Φ t, ∃ X ∈ Φ.tree, X.root = k.2 ∧ Y = pcProj sp Φ V b k.1 X}

/-- `get_anchor` with a base `Y`: the deepest live lock block that extends `Y`, or `Y`. -/
noncomputable def pcAnchor (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (Y : Blk sp.n FGP) :
    Blk sp.n FGP :=
  (deepest Φ ({B | B ∈ liveLockBlocks sp A.locks Φ t ∧ Φ.Anc Y B} ∪ {Y})).getD Y

/-- Where the head walk of a view `V` of slot `b` starts at state `A` with the store `P`: the PC
anchor of the base, or the parent's anchor when there is no base. -/
noncomputable def pcStart (P : PCStore sp.n) (Φ : Frm sp.n FGP) (t : Time) (A : SAState sp.n)
    (V : View sp.n) (b : Int) : Blk sp.n FGP :=
  match pcBase sp P Φ t V b with
  | none => getAnchor sp A Φ t
  | some Y => pcAnchor sp A Φ t Y

/-- The parent's head walk (`get_head`) of `tree` with the view `V` of slot `s`, from `a`. -/
noncomputable def headFrom (a : Blk sp.n FGP) (Φ : Frm sp.n FGP) (t : Time)
    (tree : Set (Blk sp.n FGP)) (V : View sp.n) (s : Int) : Blk sp.n FGP :=
  ghost sp tree (goldfishScore sp Φ V s) (goldfishEligible sp Φ t V s) Φ.tree.ncard a

/-! ## The ack decision -/

/-- The view of the update of slot `u`: the slot's pool, with the votes resolved before
`t_u + 2Δ` as support (the votes `confirmationScore` reads). -/
noncomputable def updateView (A : SAState sp.n) (Φ : Frm sp.n FGP) (u : Nat) : View sp.n :=
  ⟨{v | v ∈ A.pool u}, {v | v ∈ A.pool u ∧ resolutionTime A Φ v < ETime.of (sp.ts u + 2 * sp.Δ)}⟩

open Classical in
/-- The ack decision after the update of slot `u` at state `A` (after the update's writes): with
a result `C`, no decision of slot `u` yet (A3) and no live lock conflicting with `C` (A1), the
target is the deepest block of `C`'s path with `μ` clean early supporters (FT,
`confirmationScore`); it is decided unless it conflicts with the base of the update's view
(A2/W). The store is evaluated when the target exists (the base reads it). -/
noncomputable def decideAck (P : PCStore sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (u : Nat) : PCStore sp.n :=
  match (A.saved u).bind (lookup Φ) with
  | none => P
  | some C =>
    if (P.myAcks u).isSome ∨ conflictsWithLock sp A.locks Φ t C then P
    else
      match deepest Φ
          {B | B ∈ confirmationPath sp Φ C ∧ pcMu sp ≤ confirmationScore sp A Φ u B} with
      | none => P
      | some X =>
        let Q := refresh sp P Φ t
        if ∃ Y, pcBase sp Q Φ t (updateView sp A Φ u) u = some Y ∧ ¬ Compatible Φ.tree X Y then Q
        else { Q with myAcks := Function.update Q.myAcks u (some X.root) }

/-- The acks the node sends with its slot-`s` vote: for `j ∈ {2, 3}` with `j ≤ s`, its decision
of slot `s − j`, if any. -/
def ackSends (P : PCStore sp.n) (self : Fin sp.n) (s : Nat) : List (Ack sp.n) :=
  [2, 3].filterMap fun j =>
    if j ≤ s then (P.myAcks (s - j)).map fun X => ⟨self, s - j, X, j⟩ else none

end Consensus.Goldilocks.PreConfirmations

end
