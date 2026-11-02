module
public import Mathlib.Data.Set.Card
public import ConsensusLean.Instances.Goldilocks.Spec.Frame
public import ConsensusLean.Instances.Goldilocks.Spec.SA.State

@[expose] public section

/-! # Goldilocks SA: blocks by name, votes and views

fgsa-spec.tex §"Votes and views" (Figure "Goldilocks: votes and views"), over a frame `Φ` whose
blocks carry the FG payload `FGP` (never read) and the SA payload.

Blocks by name: the AC holds blocks by root, and "`H ∈ Φ.tree`" means that the tree holds a
block with that root (`InTree`); `lookup` returns it. "Deepest" is maximum depth, ties by a
fixed root order (composition.tex §"Blocks"); here the depth of a block of the tree is the
number of its ancestors in the tree (the tree is rooted at `Φ.F`, so this orders blocks as the
depth from genesis does), the smaller root wins a tie, and `deepest Φ S` is `none` when `S`
has no deepest block (empty; at a well-formed frame a nonempty `S ⊆ Φ.tree` has one).

Views are pairs of vote sets (a count reads distinct votes); `voteViewList` keeps the pool
order, which the proposal payload needs. -/

namespace Consensus.Goldilocks.SA

variable {n : Nat} {FGP : Type}

/-- The blocks the SA sees. -/
abbrev Blk (n : Nat) (FGP : Type) := Block n FGP (Payload n)

/-- The frames the SA reads. -/
abbrev Frm (n : Nat) (FGP : Type) := Frame n FGP (Payload n)

/-- A block's votes. -/
abbrev blockVotes (B : Blk n FGP) : List (Vote n) := B.acPayload.1

/-- A block's support votes. -/
abbrev blockSupport (B : Blk n FGP) : List (Vote n) := B.acPayload.2

section Blocks

variable (Φ : Frm n FGP)

/-- `r ∈ Φ.tree`: the tree holds a block with root `r`. -/
def InTree (r : Nat) : Prop := ∃ B ∈ Φ.tree, B.root = r

open Classical in
/-- The block of the tree with root `r`, if any. -/
noncomputable def lookup (r : Nat) : Option (Blk n FGP) :=
  if h : InTree Φ r then some h.choose else none

/-- `B ⪯ r`: the tree holds a block with root `r` that extends `B`. -/
def AncR (B : Blk n FGP) (r : Nat) : Prop := ∃ R ∈ Φ.tree, R.root = r ∧ Φ.Anc B R

/-- The depth of a block in the tree: the number of its ancestors in the tree. -/
noncomputable def depth (B : Blk n FGP) : Nat := {A | Φ.Anc A B}.ncard

/-- `B` is a deepest block of `S`: deeper than every other block of `S`, ties by root (the
smaller root wins). -/
def IsDeepest (S : Set (Blk n FGP)) (B : Blk n FGP) : Prop :=
  B ∈ S ∧ ∀ C ∈ S, C ≠ B → depth Φ C < depth Φ B ∨ (depth Φ C = depth Φ B ∧ B.root < C.root)

open Classical in
/-- The deepest block of `S`, ties by root order, or `none`. -/
noncomputable def deepest (S : Set (Blk n FGP)) : Option (Blk n FGP) :=
  if h : ∃ B, IsDeepest Φ S B then some h.choose else none

end Blocks

/-- A view: a vote set and its support subset. -/
structure View (n : Nat) where
  /-- The votes. -/
  votes : Set (Vote n)
  /-- The support votes. -/
  support : Set (Vote n)

/-- The view of two vote lists. -/
def View.ofLists (l : List (Vote n) × List (Vote n)) : View n := ⟨{v | v ∈ l.1}, {v | v ∈ l.2}⟩

variable (sp : SAParams)

/-- `ac_valid_payload(B)`: every vote of `B.votes` has slot `B.slot − 1 ≥ 0` (form, committee
and signature are not modelled, see `Vote`), and every support entry is in `B.votes`. -/
def validPayload (B : Blk n FGP) : Prop :=
  (∀ v ∈ blockVotes B, v.slot + 1 = B.slot) ∧ ∀ v ∈ blockSupport B, v ∈ blockVotes B

/-- `on_goldfish_vote(𝒜, t, vote)`: admission. The vote enters the pool of its slot with the
stamp `t` when its slot is `slot(t) − 1` or `slot(t)`, the pool does not hold it, and the pool
holds fewer than two distinct votes of its validator for that slot; otherwise nothing happens. -/
def admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) : SAState sp.n :=
  if (v.slot : Int) < (sp.slot t : Int) - 1 ∨ sp.slot t < v.slot ∨ v ∈ A.pool v.slot then A
  else if 2 ≤ ((A.pool v.slot).filter (fun x => x.val = v.val)).dedup.length then A
  else { A with
    pool := Function.update A.pool v.slot (A.pool v.slot ++ [v])
    voteStamp := Function.update A.voteStamp v (ETime.of t) }

open Classical in
/-- `resolution_time(𝒜, Φ, vote)`: `+∞` when the head is not in the tree or is of a later slot
than the vote; otherwise the later of the vote's stamp and the head's stamp. -/
noncomputable def resolutionTime (A : SAState n) (Φ : Frm n FGP) (v : Vote n) : ETime :=
  match lookup Φ v.head with
  | none => ⊤
  | some H => if v.slot < H.slot then ⊤ else max (A.voteStamp v) (A.blockStamp v.head)

open Classical in
/-- `vote_view(𝒜, Φ, s, cutoff)` as lists in pool order: the slot-`s` votes held before the
cutoff, and the members resolved before it. -/
noncomputable def voteViewList (A : SAState n) (Φ : Frm n FGP) (s : Int) (cutoff : ETime) :
    List (Vote n) × List (Vote n) :=
  let votes := (A.poolAt s).filter (fun v => A.voteStamp v < cutoff)
  (votes, votes.filter (fun v => resolutionTime A Φ v < cutoff))

/-- `vote_view(𝒜, Φ, s, cutoff)` as a view. -/
noncomputable def voteView (A : SAState n) (Φ : Frm n FGP) (s : Int) (cutoff : ETime) : View n :=
  View.ofLists (voteViewList A Φ s cutoff)

/-- `latest_view(𝒜, Φ, t)`: every held vote of the latest slot whose votes are due (slot
`s − 1` before `t_s + 2Δ`, slot `s` from then on), the resolved ones as support, and that slot. -/
noncomputable def latestView (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : View sp.n × Int :=
  let s : Int := sp.slot t
  let s' : Int := if sp.ts s + 2 * sp.Δ ≤ t then s else s - 1
  (voteView A Φ s' ⊤, s')

/-- The vote freeze of the slot-`(s − 1)` votes, `t_{s−1} + 3Δ`. -/
def freeze (s : Nat) : Time := sp.ts ((s : Int) - 1) + 3 * sp.Δ

/-- `merged_vote_view(𝒜, Φ, s)`: the slot-`(s−1)` votes held before the vote freeze
`t_{s−1} + 3Δ`, with those resolved before it as support, plus the votes of the slot-`s`
proposals of `Φ.tree` and, as support, their support entries `(v, s−1, H)` with `H ∈ Φ.tree`
and `H.slot ≤ s − 1`. -/
noncomputable def mergedVoteView (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) : View sp.n :=
  let base := voteView A Φ ((s : Int) - 1) (ETime.of (freeze sp s))
  { votes := base.votes ∪ {v | ∃ B ∈ Φ.tree, B.slot = s ∧ v ∈ blockVotes B}
    support := base.support ∪ {v | ∃ B ∈ Φ.tree, B.slot = s ∧ v ∈ blockSupport B ∧
      v.slot + 1 = s ∧ ∃ H ∈ Φ.tree, H.root = v.head ∧ H.slot + 1 ≤ s} }

/-- `equivocators(votes)`: the validators with two distinct votes. -/
def equivocators (votes : Set (Vote n)) : Set (Fin n) :=
  {i | ∃ x ∈ votes, ∃ y ∈ votes, x ≠ y ∧ x.val = i ∧ y.val = i}

/-- The voters of a vote set: the validators with a vote in it. -/
def voters (votes : Set (Vote n)) : Set (Fin n) := {i | ∃ x ∈ votes, x.val = i}

/-- `supporters(votes, support_votes, s, B)`: the validators that are not equivocators and have
a slot-`s` vote in the support set whose head (in the tree) extends `B`. -/
def supporters (Φ : Frm n FGP) (V : View n) (s : Int) (B : Blk n FGP) : Set (Fin n) :=
  {i | i ∉ equivocators V.votes ∧ ∃ x ∈ V.support, x.val = i ∧ (x.slot : Int) = s ∧ AncR Φ B x.head}

/-- `voter_block_tree(𝒜, Φ, s)`: the blocks of the tree received before the vote freeze
`t_{s−1} + 3Δ`, and every ancestor of a slot-`s` proposal of the tree. -/
def voterBlockTree (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) : Set (Blk sp.n FGP) :=
  {B | B ∈ Φ.tree ∧ (A.blockStamp B.root < ETime.of (freeze sp s) ∨
    ∃ P ∈ Φ.tree, P.slot = s ∧ Φ.Anc B P)}

/-- The head domain of an honest slot-`s` vote: the voter block tree, or the whole tree when the
voter block tree has no viable block in the current frame `Φ` (`fc_root` and viable heads as of
now). -/
def voteDomain (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) : Set (Blk sp.n FGP) :=
  {B | (B ∈ voterBlockTree sp A Φ s ∧ (Φ.viableTree (voterBlockTree sp A Φ s)).Nonempty) ∨
    (B ∈ Φ.tree ∧ ¬ (Φ.viableTree (voterBlockTree sp A Φ s)).Nonempty)}

end Consensus.Goldilocks.SA

end
