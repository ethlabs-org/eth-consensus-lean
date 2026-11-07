module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Recovery
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Outcome

@[expose] public section

/-! # Goldilocks milestone Healing under growing faults: recovery under a pattern (statements)

O.1, C1.3 and HR.5 (`Statements/Healing/Recovery`) for a time-indexed honest set `H` (antitone),
over `Growing.GoldilocksRun`:

* `Rec(t₀)` reads every writer, source and record at a cut of a node honest at that cut, with
  `Clean` as `Compose.Growing.Clean` (its (K1) namers charged at the consumption horizon of C1.1);
* `UPat(W, M)` asks for ready proposals of proposers honest through `t_s + hold`;
* the covering proposal of C1.3 is by a proposer honest at its proposal cut, the finalizing
  block is accepted by a node honest at its acceptance, and every later reader is honest at its
  cut;
* HR.5 is at the acceptance of a node honest at it, under `HealthyRunAt`;
* O.1 and C1.3 are **indexed by the lag** `L` of a counting cohort, as H.3 and H.4: their constants
  `T_rec` and `R_*` embed HR.3 (c)'s reset bound `ḡ + 24Δ + 12C_HS`, which under growing faults
  holds at lag `L` with `LΔ` added (`resetWindow`, `LagWithin`); so both are shifted by `LΔ`.

The constants are the static ones; at a constant honest set `L = 0`. At `H := fun _ => H₀` each
statement implies its static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- **The recovery predicate `Rec(t₀)`** under growing faults. -/
structure Rec (t₀ : Time) : Prop where
  /-- (a), (c) `Clean(s, m, B)` for the fast confirmations written after `t₀` by nodes honest at
  their writes. -/
  clean : ∀ x i s B CV, x ∈ H (tr.time i) → Compose.StoredFastLockAt tr x i s B CV →
    t₀ < tr.time i → SA.joined sp (tr.state x i).ac (tr.time i) → ∀ m, s < m →
    Compose.Growing.Clean tr H s m B
  /-- (b) The sources after `t₀` of nodes honest at their calls are pairwise compatible. -/
  sources : ∀ y z k ℓ C k' ℓ' C', y ∈ H (tr.time k) → z ∈ H (tr.time k') →
    SA.ToFGAt tr.projAC y k ℓ C → SA.ToFGAt tr.projAC z k' ℓ' C' → t₀ < tr.time k →
    t₀ < tr.time k' → Compatible (tr.HonestBlocksAt H) C C'
  /-- (b) Clean records at the first source of an entry entered after `t₀`. -/
  records : ∀ y k ℓ C E h, y ∈ H (tr.time k) → SA.ToFGAt tr.projAC y k ℓ C → t₀ < tr.time k →
    EntryOf (tr.state y k).fg C E h → t₀ < sp.ts E.slot →
    (∀ k' < k, ∀ ℓ' C', SA.ToFGAt tr.projAC y k' ℓ' C' → ¬ EntryOf (tr.state y k').fg C' E h) →
    ((tr.state y k).record.target h = none ∨ (tr.state y k).record.target h = some E.root) ∧
    (∀ r ∈ (tr.state y k).record.timeout h, r = E.root) ∧
    ((tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root)

/-- **The pattern regime `UPat(W, M)`** under growing faults. -/
def UPat (proposer : Nat → Fin sp.n) (g : Time) (W M cF kF : Nat) : Prop :=
  ∀ τ, gbar g ≤ τ → ∃ v : Nat, τ ≤ sp.ts v ∧ sp.ts v ≤ τ + 4 * sp.Δ * ((W : Time) + 1) ∧
    ∀ s, v ≤ s → s < v + M →
      ∃ (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
        ReadyProposal tr H proposer (proposer s) k s B ∧
        ∀ y i, Compose.Growing.RunEntry tr H y i B →
          ∃ (w : Fin sp.n) (kw : Nat) (W' : SA.Blk sp.n (List (FG.Att sp.n))),
            ReadyProposal tr H proposer w kw W'.slot W' ∧
            s + cF ≤ W'.slot ∧ W'.slot ≤ s + cF + kF ∧
            ∃ Pr, W'.parent = some Pr.root ∧ Anc (tr.HonestBlocksAt H) B Pr

/-- The premises of C1.2 and `UPat(W, M)` with `M ≥ M*`, under growing faults. -/
structure PatternPremises (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF Gp : Time)
    (W M cF kF : Nat) : Prop where
  /-- The HS shared premises, with `Healthy(g)`. -/
  shared : HSShared tr H dg g ΔF
  /-- `Catch(2Δ)`. -/
  catchPremise : CatchRun tr H g (2 * sp.Δ)
  /-- `Prop⁺(G_p)`. -/
  prop : PropPlus tr H proposer g Gp
  /-- `c_F > ⌈(6Δ + Δ_F)/(4Δ)⌉ − 1`. -/
  cF_lower : 4 * sp.Δ * ((cF : Time) - 1) < 6 * sp.Δ + ΔF
  /-- `c_F ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`. -/
  cF_upper : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time)
  /-- `δ_t ≥ c_F + k_F`. -/
  timeout : cF + kF ≤ sp.toParams.δt
  /-- `W ≥ 1`. -/
  one_le_W : 1 ≤ W
  /-- The uniform pattern. -/
  pattern : UPat tr H proposer g W M cF kF
  /-- `M ≥ M*`. -/
  long : Mstar sp ΔF Gp cF kF ≤ M

end Defs

/-- **Node O.1 under growing faults, recovery under a bounded uniform pattern**, at the lag `L` of
a counting cohort: `Rec` and the height bound hold from `ḡ + T_rec + LΔ`. -/
def PatternRecovery : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time) (W M cF kF : Nat),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    PatternPremises tr H proposer dg g ΔF Gp W M cF kF →
    ∀ L D, resetWindow sp g ΔF Gp L ≤ D → LagWithin tr H g D L →
    Rec tr H (gbar g + T_rec sp ΔF Gp W M + (L : Time) * sp.Δ) ∧
    ∀ y k, y ∈ H (tr.time k) → tr.IsCall y k →
      gbar g + T_rec sp ΔF Gp W M + (L : Time) * sp.Δ - 12 * sp.Δ ≤ tr.time k →
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ (tr.state y k).fg.F.root).h

/-- **C1.3 under growing faults, recurring finalizing coverage**, at the lag `L` of a counting
cohort: for every `t ≥ R_* + LΔ`. -/
def FinalizingCoverage : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time) (W M cF kF : Nat),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr →
    PatternPremises tr H proposer dg g ΔF Gp W M cF kF →
    ∀ L D, resetWindow sp g ΔF Gp L ≤ D → LagWithin tr H g D L →
    ∀ t, Rstar sp g ΔF Gp + (L : Time) * sp.Δ ≤ t →
      ∃ (q : Fin sp.n) (kP : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
        q ∈ H (tr.time kP) ∧ tr.ProposesAt q kP P ∧ t ≤ sp.ts P.slot ∧
        sp.ts P.slot ≤ t + 4 * sp.Δ * ((W : Time) + 1 + M) ∧
        (∃ x kX X, x ∈ H (tr.time kX) ∧ tr.AcceptAt x kX X ∧ ∃ Fx ∈ (tr.post kX).fg.tree,
          Fx.root = ((tr.post kX).fg.σ X.root).F ∧ Anc (tr.HonestBlocksAt H) P Fx) ∧
        ∀ y k, y ∈ H (tr.time k) → tr.IsCall y k →
          t + 4 * sp.Δ * ((W : Time) + 1 + M) + sp.Δ ≤ tr.time k →
          Anc (tr.HonestBlocksAt H) P (tr.state y k).fg.F

/-- **HR.5 under growing faults, cache acceptance** (G1.9 (b)), at the acceptance of a node
honest at it. -/
def CacheAcceptanceAfterReset : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → tr.HealthyRunAt H ΔF g →
    Compose.NoCollRun dg tr →
      ∀ y k B, y ∈ H (tr.time k) → tr.AcceptAt y k B →
        ∀ Fs ∈ (tr.post k).fg.tree, Fs.root = ((tr.post k).fg.σ B.root).F →
          (tr.post k).fg.Anc Fs (tr.post k).fg.F

end Consensus.Goldilocks.Healing.Growing

end
