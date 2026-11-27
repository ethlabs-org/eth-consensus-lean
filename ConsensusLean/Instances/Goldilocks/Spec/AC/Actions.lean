module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Interface
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Confirmation

@[expose] public section

/-! # Goldilocks AC: node actions

goldilocks-spec.tex §"Node actions" (Figures "Goldilocks: the vote and the vote receipt" and
"Goldilocks: block, tick, proposal and FG update").

* `try_vote` runs after each receipt and in the tick at `t_s + Δ`: a joined node that has not
  voted in slot `s` votes at the first time in `[t_s, t_s + Δ]` at which it holds a ready
  proposal of slot `s > 0` and every declared head vote of the slot-`s` proposals should be
  counted (`voteReady`), else at `t_s + Δ`. The vote is one sequence: the unlocking against
  the slot-`(s−1)` votes of the merged view (for `s > 0`); the walk of the viable tree of the
  vote domain (`voteDomain`: the voter block tree, or the whole tree when the voter block tree
  has no viable block in the current frame) with the merged view; `voted_slot ← s`; the own
  vote, broadcast and processed
  as a receipt by `ac_on_message`. That re-entrant `ac_on_message` admits the own vote and runs
  the optimistic check; its own `try_vote` returns at once, since `voted_slot = s` was written
  before (so it is not unfolded here). The emission records the vote, the state at its read
  point (after the unlocking and `voted_slot ← s`, before the own admission), and its duty head
  (the walk from the anchor over the viable tree of the vote domain).
* `ac_on_message`: admission, the optimistic check, `try_vote`.
* `ac_on_block`: the stamp of the block (its declared head votes are not admitted), the
  optimistic check, `try_vote`.
* `ac_on_tick`: nothing when not joined; at `t_s + Δ` `try_vote`; at `t_s + 2Δ`, for `s > 0`,
  the confirmation update of slot `s − 1`.
* `ac_proposal`: `⊥` when not joined; else the unlocking against the whole slot-`(s−1)` pool
  view, and the head of the full viable tree from the unlocked anchor, with the slot-`(s−1)`
  votes held (pool order) as the declared head votes and the resolved ones as the support list
  (the Lean form of the support bits).
* `ac_to_fg`: for a joined node the deepest candidate (a block of the full
  viable tree under a live fast lock of slot `slot(t) − 2` or later); when there is none, deep
  sources are on (`deepDepth = some D`) and there is a deep anchor `a` (`deepAnchor`), the deepest
  deep candidate (a block of the full viable tree at or below `a`, not genesis, that the node
  accepted by `t_{slot(t) − D}`). The block is returned when it is not at or below `fg_reported`
  (in the tree), which it then records. -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} (sp : ACParams)

/-- An emission of the AC. -/
abbrev Em (sp : ACParams) (FGP : Type) :=
  Emission sp.n FGP (Payload sp.n) (ACState sp.n) (Vote sp.n)

/-- `vote_ready(𝒜, Φ, s)`: a slot-`s` proposal of the tree whose slot-`(s−1)` support entries
`(v, s−1, H)` all have `H ∈ Φ.tree` and `H.slot ≤ s − 1`, and every declared head vote of every
slot-`s` proposal of the tree should be counted (`AllDeclaredVotesCounted`). -/
def voteReady (A : ACState sp.n) (Φ : Frm sp.n FGP) (s : Nat) : Prop :=
  (∃ P ∈ Φ.tree, P.slot = s ∧ ∀ x ∈ declaredSupportVotes P, x.slot + 1 = s →
    ∃ H ∈ Φ.tree, H.root = x.head ∧ H.slot + 1 ≤ s) ∧
    AllDeclaredVotesCounted sp A Φ s

open Classical in
/-- `try_vote(𝒜, Φ, t)` at validator `self`, with the own vote's receipt unfolded. -/
noncomputable def tryVote (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp A Φ s) then (A, [])
  else
    let V := mergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := unlock sp A.locks Φ t ((s : Int) - 1) V } else A
    let dom := voteDomain sp A₁ Φ s
    let H := getHead sp A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let A₃ := if A.mayVote s then optimisticConfirmation sp (admitVote sp A₂ t vote) Φ t else A₂
    (A₃, if A.mayVote s then
      [{ msg := vote, readPoint := A₂,
         head := some { head := H, start := getAnchor sp A₁ Φ t, dom := dom } }] else [])

/-- `ac_on_message(𝒜, Φ, t, vote)` at validator `self`. -/
noncomputable def acOnMessage (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) : ACState sp.n × List (Em sp FGP) :=
  tryVote sp self (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ t

/-- The receipt part of `ac_on_block(𝒜, Φ, t, B)`: the stamp of `B`. Its declared head votes are
not admitted (only the merged view reads them). -/
def blockReceipt (A : ACState sp.n) (t : Time) (B : Blk sp.n FGP) : ACState sp.n :=
  { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }

/-- `ac_on_block(𝒜, Φ, t, B)` at validator `self`. -/
noncomputable def acOnBlock (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : ACState sp.n × List (Em sp FGP) :=
  tryVote sp self (optimisticConfirmation sp (blockReceipt sp A t B) Φ t) Φ t

open Classical in
/-- `ac_on_tick(𝒜, Φ, t)` at validator `self`. -/
noncomputable def acOnTick (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVote sp self A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmation sp r.1 Φ t (s - 1) else r.1
    (A₂, r.2)

open Classical in
/-- `ac_proposal(𝒜, Φ, t)`, at `t_s`: the parent (with its walk) and the payload, or `⊥`. -/
noncomputable def acProposal (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp A t then (A, none)
  else
    let s : Int := sp.slot t
    let p := voteViewList A Φ (s - 1) ⊤
    let V := View.ofLists p
    let A₁ := { A with locks := unlock sp A.locks Φ t (s - 1) V }
    let H := getHead sp A₁ Φ t (Φ.viableTree Φ.tree) V (s - 1)
    (A₁, some (⟨H, getAnchor sp A₁ Φ t, Φ.tree⟩, p))

/-- The candidates of `ac_to_fg`: the blocks of the full viable tree under a live fast lock of
slot `slot(t) − 2` or later. -/
def toFGCandidates (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Set (Blk sp.n FGP) :=
  {B | B ∈ Φ.viableTree Φ.tree ∧
    ∃ l ∈ liveLocks sp A.locks Φ t, l.block = B.root ∧ l.fast = true ∧ sp.slot t ≤ l.slot + 2}

open Classical in
/-- `deep_anchor(𝒜, Φ, t)`: the deepest block of the live locks, fast or slow, or `none` when
there is no live lock (no `fc_root` fallback; `get_anchor` is unchanged). -/
noncomputable def deepAnchor (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Option (Blk sp.n FGP) :=
  deepest Φ (liveLockBlocks sp A.locks Φ t)

/-- The deep candidates of `ac_to_fg` at depth `D` under the anchor `a`: the blocks of the full
viable tree at or below `a` (`a` itself included), other than genesis, whose stamp (the time the
node accepted them, or its last restart) is at most `t_{slot(t) − D}`. So a lock that is not fast
is never a fast candidate, but its block (or one below it) can be a deep candidate. A restart
re-stamps every held block other than genesis at the restart time, so a node has no deep
candidate for at least `D` slots after each restart; one that restarts more often than every `D`
slots never has one. Genesis is excluded by its own conjunct, whatever its stamp (`−∞` in the
initial state, kept by a restart whose replay order skips it); the `fg_reported` test excludes it
only when the reported block is in the frame's tree. -/
def toFGDeepCandidates (D : Nat) (a : Blk sp.n FGP) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : Set (Blk sp.n FGP) :=
  {B | B ∈ Φ.viableTree Φ.tree ∧ Φ.Anc B a ∧ B.root ≠ sp.genesisRoot ∧
    A.blockStamp B.root ≤ ETime.of (sp.ts ((sp.slot t : Int) - D))}

open Classical in
/-- The block `ac_to_fg` considers: the deepest fast-lock candidate; with deep sources on
(`deepDepth = some D`), no fast-lock candidate and a deep anchor `a`, the deepest deep candidate
at or below `a`, which can be `a` itself, the block of a lock that is not fast (none for at least
`D` slots after a restart, see `toFGDeepCandidates`). With `deepDepth = none` it is the deepest
fast-lock candidate. -/
noncomputable def fgSource (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Option (Blk sp.n FGP) :=
  match sp.deepDepth with
  | none => deepest Φ (toFGCandidates sp A Φ t)
  | some D => (deepest Φ (toFGCandidates sp A Φ t)).orElse fun _ =>
      (deepAnchor sp A Φ t).bind fun a => deepest Φ (toFGDeepCandidates sp D a A Φ t)

open Classical in
/-- `ac_to_fg(𝒜, Φ, t)`: `fg_confirmed` (or `⊥`). -/
noncomputable def acToFG (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n × Option (Blk sp.n FGP) :=
  if ¬ joined sp A t then (A, none)
  else
    match fgSource sp A Φ t with
    | none => (A, none)
    | some C =>
      if AncR Φ C A.fgReported then (A, none)
      else ({ A with fgReported := C.root }, some C)

end Consensus.Goldilocks.AC

end
