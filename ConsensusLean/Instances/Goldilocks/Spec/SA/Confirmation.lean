module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.ForkChoice

@[expose] public section

/-! # Goldilocks SA: confirmation

goldilocks-spec.tex §"Confirmation" (Figure "Goldilocks: confirmation"): the record
`latest_confirmed`; the confirmation update of slot `s` at `t_s + 6Δ` (the result: the deepest
block of the tree at or above `Φ.F` with a strict majority of the slot's participants among the
votes resolved before `t_s + 2Δ` of validators with no second vote; saved also when vetoed; a
fast lock on the deepest block of the result's chain with half of the committee or more, a slow
lock when the saved results of the previous `k − 1` slots are in the tree and extend a deeper
block); the optimistic confirmation of the current slot before `t_s + 2Δ` (three quarters of
the committee with a slot-`s` vote whose head extends the block, equivocators included, and no
conflicting live lock); and the confirmed tip. A slow lock of slot `s` expires after `s + k`; a
fast lock gets `fastExpiry`, except that the update's fast lock keeps the slow expiry `s + k` when
a block of the update's path passes the slow test (a fast lock never shortens what the slow rule
gives). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} (sp : SAParams)

open Classical in
/-- `update_latest_confirmed(𝒜, Φ, C)`: the record moves to `C` unless it is in the tree and
`C` is an ancestor of it (`C ⪯ E` with `E` in the tree). -/
noncomputable def updateLatestConfirmed (A : SAState sp.n) (Φ : Frm sp.n FGP) (C : Blk sp.n FGP) :
    SAState sp.n :=
  if AncR Φ C A.latestConfirmed then A
  else { A with latestConfirmed := C.root }

open Classical in
/-- `confirmation_score(𝒜, Φ, s, B)`: the supporters of `B` in the whole slot-`s` pool (which
decides who equivocates) with the votes resolved before `t_s + 2Δ` as support. -/
noncomputable def confirmationScore (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat)
    (B : Blk sp.n FGP) : Nat :=
  let votes := {v | v ∈ A.pool s}
  let early := {v | v ∈ A.pool s ∧ resolutionTime A Φ v < ETime.of (sp.ts s + 2 * sp.Δ)}
  (supporters Φ ⟨votes, early⟩ s B).ncard

/-- `get_confirmation(𝒜, Φ, s)`: the deepest block of the tree at or above `Φ.F` whose
confirmation score is a strict majority of the slot's voters, or `⊥`. -/
noncomputable def getConfirmation (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) :
    Option (Blk sp.n FGP) :=
  deepest Φ {B | B ∈ Φ.tree ∧ Φ.Anc Φ.F B ∧
    (voters {v | v ∈ A.pool s}).ncard < 2 * confirmationScore sp A Φ s B}

/-- The non-genesis blocks of the tree at or above the result `C` (the path of the update). -/
def confirmationPath (Φ : Frm sp.n FGP) (C : Blk sp.n FGP) : Set (Blk sp.n FGP) :=
  {B | B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot ∧ Φ.Anc B C}

/-- The fast test of the update of slot `s`: half of the committee or more supports `B`. -/
def FastTest (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (B : Blk sp.n FGP) : Prop :=
  sp.n ≤ 2 * confirmationScore sp A Φ s B

/-- The block `D` that the fast test of the update of slot `s` selects on the path of the result
`C`: the deepest block of the path that passes it (whether or not a lock vetoes the result). -/
noncomputable def fastSelect (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (C : Blk sp.n FGP) :
    Option (Blk sp.n FGP) :=
  deepest Φ {B | B ∈ confirmationPath sp Φ C ∧ FastTest sp A Φ s B}

/-- The validators the fast test counts for `B` in slot `s`, with their counted votes: the
votes of the slot-`s` pool resolved before `t_s + 2Δ`, of validators with no second vote, whose
head extends `B`. -/
noncomputable def fastCounted (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (B : Blk sp.n FGP) :
    Set (Vote sp.n) :=
  {v | v ∈ A.pool s ∧ v.val ∉ equivocators {x | x ∈ A.pool s} ∧
    resolutionTime A Φ v < ETime.of (sp.ts s + 2 * sp.Δ) ∧ AncR Φ B v.head}

open Classical in
/-- `update_confirmation(𝒜, Φ, t, s)`, at `t_s + 6Δ`. -/
noncomputable def updateConfirmation (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    SAState sp.n :=
  let C := getConfirmation sp A Φ s
  let A₁ := { A with saved := Function.update A.saved s (C.map Block.root) }
  match C with
  | none => A₁
  | some C =>
    if conflictsWithLock sp A₁.locks Φ t C then A₁
    else
      let A₂ := updateLatestConfirmed sp A₁ Φ C
      let path := confirmationPath sp Φ C
      let fast := FastTest sp A Φ s
      let slow := fun B : Blk sp.n FGP => ∀ j : Int, (s : Int) - sp.k < j → j < s →
        ∃ S ∈ Φ.tree, A₁.saved j = some S.root ∧ Φ.Anc B S
      let D := fastSelect sp A Φ s C
      let lockBlock := deepest Φ {B | B ∈ path ∧ (fast B ∨ slow B)}
      -- never shorten: a slow-qualified update's fast lock keeps the slow expiry
      let eD := if (∃ B, B ∈ path ∧ slow B) then s + sp.k else fastExpiry sp A₂.locks Φ t s
      let N : Set (Nat × Bool × Nat) :=
        {p | (∃ B, D = some B ∧ p = (B.root, true, eD)) ∨
          (lockBlock ≠ D ∧ ∃ B, lockBlock = some B ∧ p = (B.root, false, s + sp.k))}
      { A₂ with locks := addLocks sp A₂.locks Φ t s N }

/-- The voters of `B` in the optimistic test of slot `s`: the validators with a vote in the
slot-`s` pool whose head (in the tree) extends `B`, equivocators included. -/
def optimisticVoters (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (B : Blk sp.n FGP) :
    Set (Fin sp.n) :=
  {i | ∃ x ∈ A.pool s, x.val = i ∧ AncR Φ B x.head}

open Classical in
/-- The block the optimistic check at `(𝒜, Φ, t)` locks, if any: for a joined node in a slot
`s > 0` before `t_s + 2Δ`, the deepest block of the tree with three quarters of the committee as
`optimisticVoters` and no conflicting live lock. -/
noncomputable def optimisticSelect (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Option (Blk sp.n FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ s = 0 ∨ sp.ts s + 2 * sp.Δ ≤ t then none
  else deepest Φ {B | B ∈ Φ.tree ∧ 3 * sp.n ≤ 4 * (optimisticVoters sp A Φ s B).ncard ∧
    ¬ conflictsWithLock sp A.locks Φ t B}

/-- `optimistic_confirmation(𝒜, Φ, t)`, after each receipt: a fast lock of slot `slot(t)` on the
block of `optimisticSelect`, and the record. -/
noncomputable def optimisticConfirmation (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n :=
  match optimisticSelect sp A Φ t with
  | none => A
  | some B =>
    updateLatestConfirmed sp
      { A with locks := addLocks sp A.locks Φ t (sp.slot t)
                  {(B.root, true, fastExpiry sp A.locks Φ t (sp.slot t))} } Φ B

open Classical in
/-- `ac_confirmed(𝒜, Φ, t)`: the deepest common ancestor of the effective record
(`latest_confirmed` if in the tree, else `Φ.F`) and the head. -/
noncomputable def acConfirmed (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  let C := (lookup Φ A.latestConfirmed).getD Φ.F
  let H := acHead sp A Φ t
  (deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X C ∧ Φ.Anc X H}).getD Φ.F

end Consensus.Goldilocks.SA

end
