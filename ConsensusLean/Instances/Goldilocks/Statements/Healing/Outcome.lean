module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run

@[expose] public section

/-! # Goldilocks milestone Healing: AC outcome service for honest entries (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"Available chain, after
C1.1", over the Goldilocks run (`Spec/Run`, `GoldilocksRun`). Its premises are the healing regime,
so it lives with the healing statements, next to its proof (`Lemmas/Healing/Outcome`); its names
stay in `Compose`.

* **C1.2, AC outcome service for honest entries** (claims at goldilocks `6703bf05`, #37: its
  run premises are the healing regime after the reset `a_z`): under `Healthy(g)`, `Catch(2Δ)`,
  `Prop⁺(G_p)` and the HS shared premises, an entry whose entry block `P` is an actual honest
  ready proposal of slot `u` with `t_u ≥ R_z = t_{slot(a_z)+2k+5}`, at a height `≥ H_z + 1`
  (with its predecessor that high when it is bound), and with retained ready inclusion in its
  window, gets outcome service by the end of the window: a literal good window
  (`Store.GoodWindow`, on the FG projection) or an accepted early justification, which at a
  bound entry has finalized the predecessor (the gate), and at an unbound entry gives its
  actual bound successor.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- An entry of the run: the block `T` that some honest node has accepted at cut `i`, whose own
state names it as the entry of its height (`σ[T].T_h = T`). -/
def RunEntry (y : Fin sp.n) (i : Nat) (T : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  y ∈ H ∧ tr.AcceptAt y i T ∧ ((tr.post i).fg.σ T.root).Th = T.root

/-- An accepted block `X` of an honest node at cut `k` on whose chain the entry `T` (height `h`)
is justified, accepted before `T₁`, and its carrier relayed: every honest node accepts `X`
before `T₁ + Δ`. At a bound entry it has also finalized the predecessor `(h − 1, J)`. -/
def EarlyOutcome (T : SA.Blk sp.n (List (FG.Att sp.n))) (h : Nat) (bound : Bool) (Jr : Nat)
    (T₁ : Time) : Prop :=
  ∃ y ∈ H, ∃ k X, tr.AcceptAt y k X ∧ tr.time k < T₁ ∧
    Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T h X ∧
    (bound = true → ((tr.post k).fg.σ X.root).hF + 1 = h ∧
      ((tr.post k).fg.σ X.root).F = Jr) ∧
    ∀ z ∈ H, ∃ k', tr.AcceptAt z k' X ∧ tr.time k' < T₁ + sp.Δ

/-- **C1.2, AC outcome service for honest entries** (claims C1.2 at goldilocks `6703bf05`). Under
`Healthy(g)` (in `HSShared`), `Catch(2Δ)`, `Prop⁺(G_p)` and the HS shared premises, with the reset
`a_z` (HR.1): let `T` be an entry of height `h ≥ H_z + 1` whose entry block is an actual honest
ready proposal of slot `u` (made by the honest joined proposer at `t_u`) with
`t_u ≥ R_z = t_{slot(a_z)+2k+5}`; when the entry is bound (`h_j = h − 1 > 0` in its state), let
its predecessor `(h − 1, J)` have `h − 1 ≥ H_z + 1`; and assume retained ready inclusion: some
honest ready proposal `W` of a slot of the window `I(E, 0, k_F)` has a parent that extends `T`.
Here `𝓕 = cF = ⌈(6Δ + Δ_F)/(4Δ)⌉` and `δ_t ≥ 𝓕 + k_F` (the parameters, with `x = 0`). Then by
the end of the window (`t_{u+𝓕+k_F+1}`) either (i) the literal good window `GW(E, 0, k_F)` holds
on the FG projection (`Store.GoodWindow`, at some honest proposer's acceptance of its own
proposal), or (ii) an accepted block justifies `E`, which at a bound entry has finalized `J`; in
both branches the carrier (the window's proposal, or the justifying block) is accepted by every
honest node within a further `Δ`; at an unbound entry, in both cases `E`
is justified by then (its actual bound successor exists). -/
def OutcomeService : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a : Time) (cF kF : Nat),
    GoldilocksRun proposer dg H tr → Healing.HSShared tr H dg g ΔF →
    Healing.CatchRun tr H g (2 * sp.Δ) → Healing.PropPlus tr H proposer g Gp →
    4 * sp.Δ * ((cF : Time) - 1) < 6 * sp.Δ + ΔF → 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time) →
    cF + kF ≤ sp.toParams.δt →
    Healing.IsReset tr H g a →
    ∀ (p : Fin sp.n) (k i : Nat) (T : SA.Blk sp.n (List (FG.Att sp.n))) (u : Nat),
      Healing.ReadyProposal tr H proposer p k u T →
      RunEntry tr H p i T →
      sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) ≤ sp.ts u →
      Healing.HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).h →
      (0 < ((tr.post i).fg.σ T.root).hj →
        ((tr.post i).fg.σ T.root).hj + 1 = ((tr.post i).fg.σ T.root).h →
        Healing.HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).hj) →
      (∃ (w : Fin sp.n) (kw : Nat) (W : SA.Blk sp.n (List (FG.Att sp.n))),
        Healing.ReadyProposal tr H proposer w kw W.slot W ∧
        u + cF ≤ W.slot ∧ W.slot ≤ u + cF + kF ∧
        ∃ Pr, W.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) T Pr) →
      let h := ((tr.post i).fg.σ T.root).h
      let bound := decide ((tr.post i).fg.σ T.root).bound
      let T₁ := sp.ts (u + cF + kF + 1 : Nat)
      ((∃ (q : Fin sp.n) (j : Nat) (Bs Pr : SA.Blk sp.n (List (FG.Att sp.n)))
          (R : Finset (FG.Att sp.n)),
          tr.projFG.time j < T₁ ∧
          Store.GoodWindow sp.toParams (Payload sp.n) H tr.projFG cF T 0 kF q j Bs Pr R ∧
          ∀ z ∈ H, ∃ k', tr.AcceptAt z k' Bs ∧ tr.time k' < T₁ + sp.Δ) ∨
        EarlyOutcome tr H T h bound ((tr.post i).fg.σ T.root).J T₁) ∧
      (bound = false → ∃ y ∈ H, ∃ k' X, tr.AcceptAt y k' X ∧ tr.time k' < T₁ ∧
        Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k').fg T h X)

end Consensus.Goldilocks.Compose

end
