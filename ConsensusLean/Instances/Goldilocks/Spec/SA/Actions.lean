module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Interface
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Confirmation

@[expose] public section

/-! # Goldilocks SA: node actions

fgsa-spec.tex §"Node actions" (Figures "Goldilocks: the vote and the vote receipt" and
"Goldilocks: block, tick, proposal and FG update").

* `try_vote` runs after each receipt and in the tick at `t_s + Δ`: a joined node that has not
  voted in slot `s` votes at the first time in `[t_s, t_s + Δ]` at which it holds a ready
  proposal of slot `s > 0`, else at `t_s + Δ`. The vote is one sequence: the unlocking against
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
* `ac_on_block`: the stamp of the block, admission of its votes in order, the optimistic check,
  `try_vote`.
* `ac_on_tick`: nothing when not joined; at `t_s + Δ` `try_vote`; at `t_s + 2Δ`, for `s > 0`,
  the confirmation update of slot `s − 1`.
* `ac_proposal`: `⊥` when not joined; else the unlocking against the whole slot-`(s−1)` pool
  view, and the head of the full viable tree from the unlocked anchor, with the slot-`(s−1)`
  votes held (pool order) and the resolved ones as the payload.
* `ac_to_fg`: for a joined node the deepest candidate (a block of the full
  viable tree under a live fast lock of slot `slot(t) − 2` or later) when it is not at or below
  `fg_reported` (in the tree), which it then records. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} (sp : SAParams)

/-- An emission of the SA. -/
abbrev Em (sp : SAParams) (FGP : Type) :=
  Emission sp.n FGP (Payload sp.n) (SAState sp.n) (Vote sp.n)

/-- `vote_ready(Φ, s)`: a slot-`s` proposal of the tree whose slot-`(s−1)` support entries
`(v, s−1, H)` all have `H ∈ Φ.tree` and `H.slot ≤ s − 1`. -/
def voteReady (Φ : Frm sp.n FGP) (s : Nat) : Prop :=
  ∃ P ∈ Φ.tree, P.slot = s ∧ ∀ x ∈ blockSupport P, x.slot + 1 = s →
    ∃ H ∈ Φ.tree, H.root = x.head ∧ H.slot + 1 ≤ s

open Classical in
/-- `try_vote(𝒜, Φ, t)` at validator `self`, with the own vote's receipt unfolded. -/
noncomputable def tryVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (A, [])
  else
    let V := mergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := unlock sp A.locks Φ t ((s : Int) - 1) V } else A
    let dom := voteDomain sp A₁ Φ s
    let H := getHead sp A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := ⟨self, s, H.root⟩
    let A₃ := optimisticConfirmation sp (admitVote sp A₂ t vote) Φ t
    (A₃, [⟨vote, A₂, some ⟨H, getAnchor sp A₁ Φ t, dom⟩⟩])

/-- `ac_on_message(𝒜, Φ, t, vote)` at validator `self`. -/
noncomputable def acOnMessage (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) : SAState sp.n × List (Em sp FGP) :=
  tryVote sp self (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ t

/-- The receipt part of `ac_on_block(𝒜, Φ, t, B)`: the stamp of `B`, then the admission of its
votes in order. -/
def blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) : SAState sp.n :=
  (blockVotes B).foldl (fun A v => admitVote sp A t v)
    { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }

/-- `ac_on_block(𝒜, Φ, t, B)` at validator `self`. -/
noncomputable def acOnBlock (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : SAState sp.n × List (Em sp FGP) :=
  tryVote sp self (optimisticConfirmation sp (blockReceipt sp A t B) Φ t) Φ t

open Classical in
/-- `ac_on_tick(𝒜, Φ, t)` at validator `self`. -/
noncomputable def acOnTick (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVote sp self A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmation sp r.1 Φ t (s - 1) else r.1
    (A₂, r.2)

open Classical in
/-- `ac_proposal(𝒜, Φ, t)`, at `t_s`: the parent (with its walk) and the payload, or `⊥`. -/
noncomputable def acProposal (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
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
def toFGCandidates (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Set (Blk sp.n FGP) :=
  {B | B ∈ Φ.viableTree Φ.tree ∧
    ∃ l ∈ liveLocks sp A.locks Φ t, l.block = B.root ∧ l.fast = true ∧ sp.slot t ≤ l.slot + 2}

open Classical in
/-- `ac_to_fg(𝒜, Φ, t)`: `fg_confirmed` (or `⊥`). -/
noncomputable def acToFG (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × Option (Blk sp.n FGP) :=
  if ¬ joined sp A t then (A, none)
  else
    match deepest Φ (toFGCandidates sp A Φ t) with
    | none => (A, none)
    | some C =>
      if AncR Φ C A.fgReported then (A, none)
      else ({ A with fgReported := C.root }, some C)

end Consensus.Goldilocks.SA

end
