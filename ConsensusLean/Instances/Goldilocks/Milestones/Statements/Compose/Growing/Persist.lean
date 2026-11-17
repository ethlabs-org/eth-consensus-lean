module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Growing

@[expose] public section

/-! # Goldilocks Persist vocabulary under growing faults (statements)

The vocabulary of C1.1's premises (`Statements/Compose/Persist`) for a time-indexed honest set `H`
(antitone), over `Growing.GoldilocksRun`; C1.1 itself is retired as a milestone statement. Its
premises read faults as follows:

* the writer is honest at its write; votes are those of nodes honest at their votes; every node
  named at a cut is honest at that cut; caches at `t_s` are those of nodes honest at `t_s`;
* the counts are charged where they are consumed: `f < h_t` at each vote time; the
  half-committee of slot `s'` among the validators honest at `t_{s'+1} + Δ`, by when the votes of
  slot `s' + 1` that read it are cast, that voted in slot `s'` while honest; and `2 f < n` at
  `t_m + Δ`, the last `ac_to_fg` call the attestations read;
* **(K1)**, the attestation cut of G1.10 at the scope of C1.1, is charged at the consumption
  horizon of the whole induction, `d = t_m + 2Δ` (every block the cuts cover is accepted before
  `t_{s'} + 2Δ ≤ t_m + 2Δ`): the namers of an excluded entry are the validators compromised by
  `d` or naming it by `T₀ = t_{s+1} + Δ`. A consumer discharges it from a fault bound at `d`, not
  from a fixed honest set.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- The votes of slot `σ` of the validators honest at their votes. -/
def honestVotes (σ : Nat) : Set (Vote sp.n) :=
  {v | ∃ x j e', x ∈ H (tr.time j) ∧ SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = σ}

/-- **The excluded entries of C1.1's scope of G1.10** under growing faults: the blocks that
conflict with `B` and strictly extend the `Σ.F` at `t_s` of some node honest at `t_s`. -/
def excludedEntries (s : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) :
    Set (SA.Blk sp.n (List (FG.Att sp.n))) :=
  {E' | ¬ Compatible (tr.HonestBlocksAt H) E' B ∧
    ∃ y j, y ∈ H (sp.ts s) ∧ tr.FirstCutFrom j (sp.ts s) ∧
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F E' ∧ E' ≠ (tr.state y j).fg.F}

/-- **`Clean(s, m, B)`** under growing faults. -/
structure Clean (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  /-- (K0) The caches at `t_s` of the nodes honest at `t_s` are compatible with `B`. -/
  caches : ∀ y j, y ∈ H (sp.ts s) → tr.FirstCutFrom j (sp.ts s) →
    Compatible (tr.HonestBlocksAt H) (tr.state y j).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y j).fg.J B
  /-- (K1) The attestation cut, charged at `d = t_m + 2Δ`. -/
  fgAttCut : ∀ E' ∈ excludedEntries tr H s B,
    (Store.Growing.namers sp.toParams (Payload sp.n) H tr.projFG (sp.ts (s + 1 : Nat) + sp.Δ)
      (sp.ts m + 2 * sp.Δ) E').ncard < sp.toParams.fg.q
  /-- (K2) Height lead at each vote of a slot in `(s, m]` by a node honest at its vote. -/
  heightLead : ∀ y i ℓ e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ℓ e → s < e.msg.slot →
    e.msg.slot ≤ m →
    (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y i).fg.IsViable D) ∨
    Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot

end Consensus.Goldilocks.Compose.Growing

end
