module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Confirmation
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-! # Support counting in one row (statements)

Three counting facts about the confirmation tests of the Goldilocks SA, transcribed from the
FT-H paper (dc-autoresearch `docs/notes/ft-h-paper.md`), each pinned to the revision whose
argument it states. They are standalone: none is a settling statement, none bounds a healing
coefficient, and none is a step of a proof of short-asynchrony healing.

* **(a) Split capacity** (paper `cfb2d338`, §1). In a two-group split of the honest validators,
  groups of sizes `a ≥ b`, with `m = n − a − b` other seats and at most `h` counted identities
  outside the groups, a block on the smaller side that the larger side does not support has at
  most `b + h` counted identities. An absolute test of threshold `q` then needs
  `2h ≥ (2q − 1)·n + m + (a − b)`; the half test, in its integer form `n ≤ 2·count`, needs
  `2h ≥ m + (a − b)`, so `2h < m` excludes it, and equality does not (`a = b`, `2h = m`). The
  three-quarter test is impossible when `h ≤ f ≤ m` and `2f < n`. Arithmetic only: the support
  bound `b + h` is the premise.
* **(b) Same-row support** (paper `ae83bd82`, §7). At every cut of an honest node, the honest
  identities that the fast counter (`fastCounted`) or the optimistic counter (`optimisticVoters`)
  counts for a block `X` in row `j` are among the honest validators whose actual row-`j` vote head
  descends from `X` in `U` (`rowSupport`); for conflicting blocks these sets are disjoint; and the
  identities outside `H` they count have a row-`j` vote that an honest node admitted before the cut
  (`CountedFaultyAdmitted`). So two conflicting blocks cannot both reach half of the committee in
  one row, at any honest cuts and with any mixture of the two counters, when each count has at most
  `h` faulty identities and `2h < |Hᶜ|`. One such origin can still exist.
* **(c) The same-row selector** (paper `e439ef2`, §10). Under a common full denominator `D`
  (the voters of the row's pool) at two update inputs, and with every counted supporter of a
  block in `D` and its unique vote head descending from that block, the two selected results
  are comparable, and an eligible block (strict majority over `|D|`) at a reader is an ancestor
  of that reader's selected result. The hypotheses are the lemma's: nothing here supplies them.

Trace premises are mode-generic (`ACLocalRunU m u`), so the candidate runs reach them through
their projections; (a) and (c) read no trace. Statements only (Prop definitions): the proofs are
in `Lemmas/Healing/AC/SupportCounting/`. -/

namespace Consensus.Goldilocks.SA

/-! ### (a) Split capacity -/

/-- **(a), the half test** (paper `cfb2d338`, §1): with `a + b + m = n` and `b ≤ a`, a count
of at most `b + h` that passes the half test in its integer form (`n ≤ 2·count`) needs
`m + (a − b) ≤ 2h`. -/
def SplitCapacityHalf : Prop :=
  ∀ n m a b h : ℕ, a + b + m = n → b ≤ a → n ≤ 2 * (b + h) → m + (a - b) ≤ 2 * h

/-- **(a), every rational threshold** (paper `cfb2d338`, §1): with `a + b + m = n` and `b ≤ a`, a
count of at most `b + h` that reaches `q·n` needs `(2q − 1)·n + m + (a − b) ≤ 2h`. -/
def SplitCapacity : Prop :=
  ∀ (n m a b h : ℕ) (q : ℚ), a + b + m = n → b ≤ a → q * n ≤ (b + h : ℚ) →
    (2 * q - 1) * n + m + (a - b : ℚ) ≤ 2 * h

/-- **(a), the half test is excluded below `m/2`** (paper `cfb2d338`, §1): with `a + b + m = n`
and `b ≤ a`, if `2h < m` no count of at most `b + h` passes the half test. -/
def SplitHalfExcluded : Prop :=
  ∀ n m a b h : ℕ, a + b + m = n → b ≤ a → 2 * h < m → ¬ n ≤ 2 * (b + h)

/-- **(a), the three-quarter test is excluded** (paper `cfb2d338`, §1): with `a + b + m = n`,
`b ≤ a`, `h ≤ f ≤ m` and `2f < n`, no count of at most `b + h` reaches three quarters
(`3n ≤ 4·count`). -/
def SplitThreeQuarterExcluded : Prop :=
  ∀ n m a b h f : ℕ, a + b + m = n → b ≤ a → h ≤ f → f ≤ m → 2 * f < n →
    ¬ 3 * n ≤ 4 * (b + h)

/-! ### (b) Same-row support -/

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- `Q_j(X)`: the honest validators whose actual row-`j` vote (an emission of their own node)
has a head that is a block of `U` descending from `X`. -/
def rowSupport (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (j : Nat)
    (X : Blk sp.n FGP) : Set (Fin sp.n) :=
  {x | x ∈ H ∧ ∃ i e, VoteAt tr x i e ∧ e.msg.slot = j ∧
    ∃ Hd ∈ U, Hd.root = e.msg.head ∧ Anc U X Hd}

/-- The two counters of a row's early support: the fast test's counted votes, and the
optimistic test's voters (equivocators included). -/
inductive Counter where
  | fast
  | optimistic

variable (sp) in
/-- The identities a counter counts for `X` in row `j` at state `A` and frame `Φ`. -/
def counted (A : SAState sp.n) (Φ : Frm sp.n FGP) (j : Nat) (X : Blk sp.n FGP) :
    Counter → Set (Fin sp.n)
  | .fast => (fun v : Vote sp.n => v.val) '' fastCounted sp A Φ j X
  | .optimistic => optimisticVoters sp A Φ j X

/-- **(b), per cut** (paper `ae83bd82`, §7): over an AC trace of the SA at any write mode `m`
with the unlock given by any oracle `u` (`ACLocalRunU m u`), with honest objects, at
every call of an honest node, the honest identities that either counter counts for a block `X`
of the call's frame in row `j` are in `rowSupport`. -/
def CountedHonestInRowSupport : Prop :=
  ∀ (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n)
    (m : WriteMode) (u : Nat → Set Lock),
    ACLocalRunU m u H U tr → HonestObjects proposer tr H →
    ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ∀ (κ : Counter) (j : Nat) (X : Blk sp.n FGP),
      X ∈ ℓ.frame.tree →
        counted sp (tr.state y i) ℓ.frame j X κ ∩ H ⊆ rowSupport tr H U j X

/-- A vote admitted by an honest node before cut `i`: at an earlier cut some node of `H` sent or
admitted it (`SendOrAdmit`: an emission, or a call other than a restart after which its AC holds the
vote and before which it did not, as a message or from the payload of an accepted block), or
replayed it from a block of its frame at a restart. -/
def HonestAdmittedBefore (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (i : Nat)
    (v : Vote sp.n) : Prop :=
  ∃ z ∈ H, ∃ k < i, tr.SendOrAdmit z k v ∨
    ∃ ℓ, tr.CallAt z k ℓ ∧ ℓ.call = .restart ∧ ∃ B ∈ ℓ.frame.tree, v ∈ blockVotes B

/-- **(b), the faulty part has honest pool provenance** (paper `ae83bd82`, §7, the provenance half
of `E \ H ⊆ A_i`): over an AC trace of the SA at any write mode and unlock oracle, at every call of
an honest node (cut `i`), every identity outside `H` that either counter counts for a block `X` of
the call's frame in row `j` has a row-`j` vote that an honest node sent or admitted before cut `i`,
or replayed from a block of a restart frame.

This is a pool-origin statement, not the activity measure. `HonestAdmittedBefore` is not the
first-receipt activity set of the design (raw receipts by any honest node in a window): the restart
disjunct only witnesses the vote inside a frame block at a restart, which on an arbitrary
`ACLocalRunU` frame gives no earlier network receipt event or time, and a restart replay is not a
fresh charge; and an admission before cut `i` does not place the first receipt in any particular
activity window (it may precede it). Discharging the per-count premise of
`NoConflictingHalfOrigins` from an activity bound needs a separate transport obligation: the
content origin of frame blocks and payloads, the first receipt of every counted faulty content
(nested, rejected and orphan contents included), the duty floor, and membership in the window. -/
def CountedFaultyAdmitted : Prop :=
  ∀ (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) (m : WriteMode) (u : Nat → Set Lock),
    ACLocalRunU m u H U tr →
    ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ∀ (κ : Counter) (j : Nat) (X : Blk sp.n FGP),
      X ∈ ℓ.frame.tree → ∀ x ∈ counted sp (tr.state y i) ℓ.frame j X κ \ H,
        ∃ v : Vote sp.n, v.val = x ∧ v.slot = j ∧ HonestAdmittedBefore tr H i v

/-- **(b), disjointness** (paper `ae83bd82`, §7): over an AC trace of the SA at any write mode and
unlock oracle, the row-`j` supports of two conflicting blocks of `U` are disjoint. -/
def RowSupportDisjoint : Prop :=
  ∀ (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) (m : WriteMode) (u : Nat → Set Lock),
    ACLocalRunU m u H U tr → ∀ (j : Nat) (X Y : Blk sp.n FGP), X ∈ U → Y ∈ U → ¬ Anc U X Y →
      ¬ Anc U Y X → Disjoint (rowSupport tr H U j X) (rowSupport tr H U j Y)

/-- **(b), no two conflicting half origins in one row** (paper `ae83bd82`, §7): over an AC trace of
the SA at any write mode and unlock oracle with honest objects, at calls of honest nodes `y` (cut
`i`) and `y'` (cut `i'`), for counters `κ` and `κ'` and conflicting blocks `X` and `Y` of `U` in the
respective frames, if each count has at most `h` identities outside `H` and `2h < |Hᶜ|`, the two
counts do not both reach half of the committee (`n ≤ 2·count`). -/
def NoConflictingHalfOrigins : Prop :=
  ∀ (sp : SAParams) (FGP : Type) (ro : ReplayOrder sp FGP) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) (proposer : Nat → Fin sp.n)
    (m : WriteMode) (u : Nat → Set Lock) (h : ℕ),
    ACLocalRunU m u H U tr → HonestObjects proposer tr H → 2 * h < Hᶜ.ncard →
    ∀ y ∈ H, ∀ y' ∈ H, ∀ i i' ℓ ℓ', tr.CallAt y i ℓ → tr.CallAt y' i' ℓ' →
    ∀ (κ κ' : Counter) (j : Nat) (X Y : Blk sp.n FGP), X ∈ ℓ.frame.tree → Y ∈ ℓ'.frame.tree →
      ¬ Anc U X Y → ¬ Anc U Y X →
      (counted sp (tr.state y i) ℓ.frame j X κ \ H).ncard ≤ h →
      (counted sp (tr.state y' i') ℓ'.frame j Y κ' \ H).ncard ≤ h →
      ¬ (sp.n ≤ 2 * (counted sp (tr.state y i) ℓ.frame j X κ).ncard ∧
        sp.n ≤ 2 * (counted sp (tr.state y' i') ℓ'.frame j Y κ').ncard)

/-! ### (c) The same-row selector -/

/-- The supporters the update of row `j` counts for `B` at state `A` and frame `Φ` (those of
`confirmationScore`). -/
def scoreSupporters (A : SAState sp.n) (Φ : Frm sp.n FGP) (j : Nat) (B : Blk sp.n FGP) :
    Set (Fin sp.n) :=
  supporters Φ ⟨{v | v ∈ A.pool j},
    {v | v ∈ A.pool j ∧ resolutionTime A Φ v < ETime.of (sp.ts j + 2 * sp.Δ)}⟩ j B

/-- **The selector hypotheses** at an update input `(A, Φ)` of row `j`, for a denominator `D`, a
head map `head` and a coherent block universe `U`: the frame's tree is in `U`; the voters of the
row-`j` pool are exactly `D`; and every counted supporter of a block `B` is in `D` with its head
`head x`, a block of `U`, descending from `B`. -/
structure SelectorHyp (U : Set (Blk sp.n FGP)) (D : Set (Fin sp.n))
    (head : Fin sp.n → Blk sp.n FGP) (A : SAState sp.n) (Φ : Frm sp.n FGP) (j : Nat) : Prop where
  tree_sub : Φ.tree ⊆ U
  denominator : voters {v | v ∈ A.pool j} = D
  supporters_sub : ∀ B, scoreSupporters A Φ j B ⊆ {x | x ∈ D ∧ head x ∈ U ∧ Anc U B (head x)}

/-- **(c), selected results are comparable** (paper `e439ef2`, §10): in a coherent `U`, at two
update inputs of row `j` with the selector hypotheses for one denominator `D` and one head map,
the two selected results (`getConfirmation`) are comparable. -/
def SelectedResultsComparable : Prop :=
  ∀ (sp : SAParams) (FGP : Type) (U : Set (Blk sp.n FGP)) (D : Set (Fin sp.n))
    (head : Fin sp.n → Blk sp.n FGP) (A A' : SAState sp.n) (Φ Φ' : Frm sp.n FGP) (j : Nat)
    (C C' : Blk sp.n FGP), Coherent U → SelectorHyp U D head A Φ j →
    SelectorHyp U D head A' Φ' j → getConfirmation sp A Φ j = some C →
    getConfirmation sp A' Φ' j = some C' → Anc U C C' ∨ Anc U C' C

/-- **(c), an eligible block is below the selected result** (paper `e439ef2`, §10): in a
coherent `U`, at an update input of row `j` with the selector hypotheses, a block `R` of the
frame's tree at or above `Φ.F` with a strict majority (`|D| < 2·score`) is an ancestor of the
selected result. -/
def EligibleBelowSelected : Prop :=
  ∀ (sp : SAParams) (FGP : Type) (U : Set (Blk sp.n FGP)) (D : Set (Fin sp.n))
    (head : Fin sp.n → Blk sp.n FGP) (A : SAState sp.n) (Φ : Frm sp.n FGP) (j : Nat)
    (R C : Blk sp.n FGP), Coherent U → SelectorHyp U D head A Φ j → R ∈ Φ.tree →
    Φ.Anc Φ.F R → D.ncard < 2 * confirmationScore sp A Φ j R →
    getConfirmation sp A Φ j = some C → Anc U R C

end Consensus.Goldilocks.SA

end
