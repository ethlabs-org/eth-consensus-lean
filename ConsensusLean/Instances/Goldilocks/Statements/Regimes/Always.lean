module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run

@[expose] public section

/-! # Goldilocks milestone Regimes: the rows that hold in every run (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"L2: regime theorems
(skeleton)" (main `c6653258`), rows R.7 and R.8, over the Goldilocks run (`Spec/Run`,
`GoldilocksRun`) with no regime premise: R.8 and non-framing hold in every run, also with digest
collisions (the target rows are `HoldsAlways`), so they read ancestry in the node's own tree and
take no `NoColl`; final accountability and finalized safety take `NoColl` (their target rows
allow the collision escape), and finalized safety the fault bound `f < 2q − n`:

* **R.8** (`nested`, `finalMonotone`, `outputValid`; uses C0.1, C0.2, F.2, F.3): at every honest
  node and cut, the finalized tip is an ancestor of the confirmed tip, which is an ancestor of the
  head (`OutputsNested`); the finalized tip moves only to descendants, across restarts
  (`FinalizedMonotone`); and the finalized and confirmed outputs are blocks of the node's accepted
  tree whose chains are linked to genesis with increasing slots and their slots' proposers
  (`OutputsValid`).
* **R.7** (`finalAccountable`, `nonFraming`, `finalized_safe_below_third`; uses G1.3–G1.5): two
  conflicting honest finalized tips convict at least `2q − n` validators from the attestations on
  chains the two readers hold (`FinalAccountable`, G1.3 with G1.5's binding); an honest validator
  signs no slashable pair (`NonFraming`, G0.5 with durable records; unforgeability puts every
  attestation of an honest validator among its signings); and with `f < 2q − n` no two honest
  finalized tips conflict (`FinalizedSafe`, G1.4 over the run).

These are run-level statements over the Goldilocks run; the Refinement milestone carries them to
the model system. "Conflict" is incompatibility inside the honest blocks of the run.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- The attestations included on the chain of `X` in the tree of `y` before cut `i`: the FG
payloads of the blocks of `y`'s tree at or below `X`. -/
def ChainAtts (y : Fin sp.n) (i : Nat) (X : SA.Blk sp.n (List (FG.Att sp.n))) :
    Set (FG.Att sp.n) :=
  {a | ∃ Y ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc Y X ∧ a ∈ Y.fgPayload}

/-- The block `X` of `y`'s tree before cut `i` is a valid output: its chain in that tree is linked
to genesis (`X` is in the tree, which is rooted), and every block of it other than genesis has its
digest as its root (`RootOk`), was accepted by `y` at an earlier cut (seen by the reader), has its
slot's proposer, and has a parent of a smaller slot in the tree. -/
def ValidOutput (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (y : Fin sp.n) (i : Nat)
    (X : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  X ∈ (tr.state y i).fg.tree ∧
    ∀ Z, (tr.state y i).fg.Anc Z X → Z.root ≠ sp.genesisRoot →
      Z.RootOk dg ∧ (∃ k < i, tr.AcceptAt y k Z) ∧
      Z.proposer = proposer Z.slot ∧
      ∃ Pz ∈ (tr.state y i).fg.tree, Z.parent = some Pz.root ∧ Pz.slot < Z.slot

end Defs

/-- **R.8, `nested`.** At every honest node and cut, the finalized tip is an ancestor of the
confirmed tip, and the confirmed tip of the head, in the node's tree (C0.1; no `NoColl`). -/
def OutputsNested : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr →
    ∀ y ∈ H, ∀ i,
      (tr.state y i).fg.Anc (tr.finalizedAt y i) (tr.confirmedAt y i) ∧
      (tr.state y i).fg.Anc (tr.confirmedAt y i) (tr.headAt y i)

/-- **R.8, `finalMonotone`.** The finalized tip of an honest node moves only to descendants,
across restarts, in the node's later tree (C0.2; no `NoColl`). -/
def FinalizedMonotone : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr →
    ∀ y ∈ H, ∀ i j, i ≤ j → (tr.state y j).fg.Anc (tr.finalizedAt y i) (tr.finalizedAt y j)

/-- **R.8, `outputValid`.** The finalized and confirmed outputs of an honest node are valid
outputs of its tree (F.2; no `NoColl`). -/
def OutputsValid : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr →
    ∀ y ∈ H, ∀ i,
      ValidOutput tr proposer dg y i (tr.finalizedAt y i) ∧
      ValidOutput tr proposer dg y i (tr.confirmedAt y i)

/-- **R.7, `finalAccountable`** (G1.3 with G1.5's evidence binding). If the finalized tips of two
honest nodes (at any cuts) conflict, at least `2q − n` validators each have a slashable pair among
the attestations included on two chains that the two readers hold: a block `X₁` of the first
reader's tree and a block `X₂` of the second's, taken together. -/
def FinalAccountable : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y ∈ H, ∀ z ∈ H, ∀ i j,
      ¬ Compatible (tr.HonestBlocks H) (tr.finalizedAt y i) (tr.finalizedAt z j) →
      ∃ X₁ ∈ (tr.state y i).fg.tree, ∃ X₂ ∈ (tr.state z j).fg.tree,
        ∃ S : Finset (Fin sp.n), 2 * sp.toParams.q - sp.n ≤ S.card ∧
          ∀ v ∈ S, ∃ a ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂,
            ∃ b ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂, a.val = v ∧ FG.slashable a b

/-- **R.7, `nonFraming`.** An honest validator signs no slashable pair (G0.5 over the run's
durable, serialized clients; no `NoColl`). -/
def NonFraming : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr →
    ∀ v ∈ H, ∀ k k' a b, tr.SignAt v k a → tr.SignAt v k' b → ¬ FG.slashable a b

/-- **R.7, `finalized_safe_below_third`** (G1.4 over the run). With `f < 2q − n`, the finalized
tips of two honest nodes (at any cuts) never conflict. -/
def FinalizedSafe : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    Hᶜ.ncard < 2 * sp.toParams.q - sp.n →
    ∀ y ∈ H, ∀ z ∈ H, ∀ i j,
      Compatible (tr.HonestBlocks H) (tr.finalizedAt y i) (tr.finalizedAt z j)

end Consensus.Goldilocks.Regimes

end
