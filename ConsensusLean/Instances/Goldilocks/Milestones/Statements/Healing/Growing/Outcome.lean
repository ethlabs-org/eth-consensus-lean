module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Outcome
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

@[expose] public section

/-! # Goldilocks milestone Healing under growing faults: AC outcome service (statements)

C1.2 (`Statements/Healing/Outcome`) for a time-indexed honest set `H` (antitone), over
`Growing.GoldilocksRun` under the growing-fault HS shared premises:

* an entry is accepted by a node honest at its acceptance; the entry block is a ready proposal of
  a proposer honest through `t_u + hold`;
* the good window is `Store.Growing.GoodWindow` on the FG projection (its proposer honest at the
  proposal cut, `emitted` read at the window's deadline);
* "every honest node accepts the carrier within a further `Δ`" is every node honest at
  `T₁ + Δ`, and the early justification is accepted by a node honest at its acceptance.

At `H := fun _ => H₀` the statement implies its static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- An entry of the run: the block `T` accepted at cut `i` by `y` honest at the cut, whose own
state names it as the entry of its height. -/
def RunEntry (y : Fin sp.n) (i : Nat) (T : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  y ∈ H (tr.time i) ∧ tr.AcceptAt y i T ∧ ((tr.post i).fg.σ T.root).Th = T.root

/-- An accepted block `X`, accepted before `T₁` by a node honest at its acceptance, on whose chain
the entry `T` (height `h`) is justified, and accepted before `T₁ + Δ` by every node honest at
`T₁ + Δ`. -/
def EarlyOutcome (T : SA.Blk sp.n (List (FG.Att sp.n))) (h : Nat) (bound : Bool) (Jr : Nat)
    (T₁ : Time) : Prop :=
  ∃ y k X, y ∈ H (tr.time k) ∧ tr.AcceptAt y k X ∧ tr.time k < T₁ ∧
    Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T h X ∧
    (bound = true → ((tr.post k).fg.σ X.root).hF + 1 = h ∧
      ((tr.post k).fg.σ X.root).F = Jr) ∧
    ∀ z, z ∈ H (T₁ + sp.Δ) → ∃ k', tr.AcceptAt z k' X ∧ tr.time k' < T₁ + sp.Δ

/-- **C1.2 under growing faults, AC outcome service for honest entries.** -/
def OutcomeService : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF a : Time) (cF kF : Nat),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    Healing.Growing.HSShared tr H dg g ΔF →
    Healing.Growing.CatchRun tr H g (2 * sp.Δ) → 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time) →
    cF + kF ≤ sp.toParams.δt →
    Healing.Growing.IsReset tr H g a →
    ∀ (p : Fin sp.n) (k i : Nat) (T : SA.Blk sp.n (List (FG.Att sp.n))) (u : Nat),
      Healing.Growing.ReadyProposal tr H proposer p k u T →
      RunEntry tr H p i T →
      sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) ≤ sp.ts u →
      Healing.Growing.HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).h →
      (0 < ((tr.post i).fg.σ T.root).hj →
        ((tr.post i).fg.σ T.root).hj + 1 = ((tr.post i).fg.σ T.root).h →
        Healing.Growing.HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).hj) →
      (∃ (w : Fin sp.n) (kw : Nat) (W : SA.Blk sp.n (List (FG.Att sp.n))),
        Healing.Growing.ReadyProposal tr H proposer w kw W.slot W ∧
        u + cF ≤ W.slot ∧ W.slot ≤ u + cF + kF ∧
        ∃ Pr, W.parent = some Pr.root ∧ Anc (tr.HonestBlocksAt H) T Pr) →
      let h := ((tr.post i).fg.σ T.root).h
      let bound := decide ((tr.post i).fg.σ T.root).previousHeightJustified
      let T₁ := sp.ts (u + cF + kF + 1 : Nat)
      ((∃ (q : Fin sp.n) (j : Nat) (Bs Pr : SA.Blk sp.n (List (FG.Att sp.n)))
          (R : Finset (FG.Att sp.n)),
          tr.projFG.time j < T₁ ∧
          Store.Growing.GoodWindow sp.toParams (Payload sp.n) H tr.projFG cF T 0 kF q j Bs Pr R ∧
          ∀ z, z ∈ H (T₁ + sp.Δ) → ∃ k', tr.AcceptAt z k' Bs ∧ tr.time k' < T₁ + sp.Δ) ∨
        EarlyOutcome tr H T h bound ((tr.post i).fg.σ T.root).J T₁) ∧
      (bound = false → ∃ y k' X, y ∈ H (tr.time k') ∧ tr.AcceptAt y k' X ∧ tr.time k' < T₁ ∧
        Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k').fg T h X)

end Consensus.Goldilocks.Compose.Growing

end
