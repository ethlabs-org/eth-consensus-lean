module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Outcome

@[expose] public section

/-! # Goldilocks milestone Healing: recovery under a bounded uniform pattern (statements)

Transcribed from `specs/goldilocks/tex/goldilocks-claims.tex`:
§"O.1" (the recovery predicate `Rec(t₀)`, the pattern regime `UPat(W, M)` and
its constants, node O.1), node C1.3 (recurring finalizing coverage) and node HR.5 (cache
acceptance after the reset, G1.9 (b) at high heights), over the Goldilocks run.

**The pattern regime is the regime node O.1 is proved under, not O.1's target**: O.1's target
for the contract's own proposer premise (bounded single-proposer gaps, or an eventual pattern
without a uniform wait) has no statement here and stays open (claims §"O.1", Status).

Node O.1 and C1.3 are conditional paper results (claims: a reviewed conditional assembly):
on C1.2 (with its open high-or-seed-ancestor split), the old-entry crossing by
`t_s + L_old` (not a node), HR.5 and the uniform pattern.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

section Constants

variable (sp : SAParams)

/-- `⌈x / (4Δ)⌉` in slots (for `x ≥ 0`). -/
def slotsCeil (x : Time) : Nat := ((x + 4 * sp.Δ - 1) / (4 * sp.Δ)).toNat

/-- `b₀ = ⌈((8k + 26)Δ + G_p)/(4Δ)⌉ + 1` (the fresh high-proposal acquisition). -/
def acqSlots (Gp : Time) : Nat := slotsCeil sp ((8 * (sp.k : Time) + 26) * sp.Δ + Gp) + 1

/-- `L_old = (7 + 4δ_t)Δ + Δ_F + G_p` (the old-entry crossing delay). -/
def L_old (ΔF Gp : Time) : Time := (7 + 4 * (sp.toParams.δt : Time)) * sp.Δ + ΔF + Gp

/-- `r_old = ⌈L_old/(4Δ)⌉ + 1`. -/
def oldSlots (ΔF Gp : Time) : Nat := slotsCeil sp (L_old sp ΔF Gp) + 1

/-- `M* = b₀ + r_old + 2(c_F + k_F) + 1`. -/
def Mstar (ΔF Gp : Time) (cF kF : Nat) : Nat :=
  acqSlots sp Gp + oldSlots sp ΔF Gp + 2 * (cF + kF) + 1

/-- `Z = 24Δ + 12C_HS` (HR.3's reset bound after `ḡ`). -/
def Zreset (ΔF Gp : Time) : Time := 24 * sp.Δ + 12 * C_HS sp ΔF Gp

/-- `T_rec = Z + (8k + 20)Δ + 4Δ(W + 1 + M) + 13Δ`. -/
def T_rec (ΔF Gp : Time) (W M : Nat) : Time :=
  Zreset sp ΔF Gp + (8 * (sp.k : Time) + 20) * sp.Δ + 4 * sp.Δ * ((W : Time) + 1 + M) +
    13 * sp.Δ

/-- `R_* = ḡ + Z + (8k + 20)Δ`. -/
def Rstar (g ΔF Gp : Time) : Time :=
  gbar g + Zreset sp ΔF Gp + (8 * (sp.k : Time) + 20) * sp.Δ

end Constants

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **The recovery predicate `Rec(t₀)`** (O.1's (a)–(c) at `t₀`): (a), (c) every honest fast
confirmation written after `t₀` by an honest joined node (of any label `s`, stored block `B`)
satisfies C1.1's `Clean(s, m, B)` ((K0), (K1), (K2)) for every `m > s`; (b) the honest sources
returned after `t₀` are pairwise compatible, and at each honest validator's first source of an
entry entered after `t₀` (an entry block of slot start `> t₀`, the entry at its height `h` of the
source's chain: the served entry, the sources after `t₀` being compatible), its durable record
holds no target, timeout or lock at `h` for another block. (This covers every entry entered after
`t₀` at the height of a post-`t₀` honest source, which is the claims' served entry when the earliest
honest source reaching `h` is after `t₀`; an earlier source of a different entry at `h` would be
pre-`c_z` and so at height `≤ H_z` (by `H_z`'s and the store's `h_max` monotonicity), or a high
origin comparable with the later ones (HR.4). Checked against node O.1's proof:
the conditional assembly covers this quantifier without asking that the earliest honest
source reaching `h` be after `t₀`.) -/
structure Rec (t₀ : Time) : Prop where
  /-- (a), (c) `Clean(s, m, B)` for the honest fast confirmations written after `t₀`. -/
  clean : ∀ x ∈ H, ∀ i s B CV, Compose.StoredFastLockAt tr x i s B CV → t₀ < tr.time i →
    SA.joined sp (tr.state x i).ac (tr.time i) → ∀ m, s < m → Compose.Clean tr H s m B
  /-- (b) The honest sources after `t₀` are pairwise compatible. -/
  sources : ∀ y ∈ H, ∀ z ∈ H, ∀ k ℓ C k' ℓ' C', SA.ToFGAt tr.projAC y k ℓ C →
    SA.ToFGAt tr.projAC z k' ℓ' C' → t₀ < tr.time k → t₀ < tr.time k' →
    Compatible (tr.HonestBlocks H) C C'
  /-- (b) Clean records at the first source of an entry entered after `t₀`. -/
  records : ∀ y ∈ H, ∀ k ℓ C E h, SA.ToFGAt tr.projAC y k ℓ C → t₀ < tr.time k →
    EntryOf (tr.state y k).fg C E h → t₀ < sp.ts E.slot →
    (∀ k' < k, ∀ ℓ' C', SA.ToFGAt tr.projAC y k' ℓ' C' → ¬ EntryOf (tr.state y k').fg C' E h) →
    ((tr.state y k).record.target h = none ∨ (tr.state y k).record.target h = some E.root) ∧
    (∀ r ∈ (tr.state y k).record.timeout h, r = E.root) ∧
    ((tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root)

/-- **The pattern regime `UPat(W, M)`** (with C1.2's window parameters `c_F`, `k_F`): for every
`τ ≥ ḡ` there is a slot `v` with `τ ≤ t_v ≤ τ + 4Δ(W + 1)` such that each of the `M` slots
`v, …, v + M − 1` has an honest joined ready proposal (`ReadyProposal`), and C1.2's retained ready
inclusion holds, in its window `I(E, 0, k_F)`, for every entry whose entry block is one of those
proposals (not merely for entries that happen to be served). -/
def UPat (proposer : Nat → Fin sp.n) (g : Time) (W M cF kF : Nat) : Prop :=
  ∀ τ, gbar g ≤ τ → ∃ v : Nat, τ ≤ sp.ts v ∧ sp.ts v ≤ τ + 4 * sp.Δ * ((W : Time) + 1) ∧
    ∀ s, v ≤ s → s < v + M →
      ∃ (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
        ReadyProposal tr H proposer (proposer s) k s B ∧
        ∀ y i, Compose.RunEntry tr H y i B →
          ∃ (w : Fin sp.n) (kw : Nat) (W' : SA.Blk sp.n (List (FG.Att sp.n))),
            ReadyProposal tr H proposer w kw W'.slot W' ∧
            s + cF ≤ W'.slot ∧ W'.slot ≤ s + cF + kF ∧
            ∃ Pr, W'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) B Pr

/-- The premises of C1.2 (the HS shared premises, `Catch(2Δ)`, `Prop⁺(G_p)`, the window
parameters `c_F = ⌈(6Δ + Δ_F)/(4Δ)⌉` and `c_F + k_F ≤ δ_t`) and `UPat(W, M)` with `M ≥ M*`. -/
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

/-- **Node O.1, recovery under a bounded uniform pattern.** Under C1.2's premises and
`UPat(W, M)` with `M ≥ M*`: `Rec(ḡ + T_rec)` holds, and at every call of an honest node at a time
`≥ T_F = ḡ + T_rec − 12Δ`, `Σ.F` has state height `≥ H_z + 1`. (Not O.1's target: see the module
docstring.) -/
def PatternRecovery : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time) (W M cF kF : Nat),
    GoldilocksRun proposer dg H tr → PatternPremises tr H proposer dg g ΔF Gp W M cF kF →
    Rec tr H (gbar g + T_rec sp ΔF Gp W M) ∧
    ∀ y ∈ H, ∀ k, tr.IsCall y k → gbar g + T_rec sp ΔF Gp W M - 12 * sp.Δ ≤ tr.time k →
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ (tr.state y k).fg.F.root).h

/-- **C1.3, recurring finalizing coverage.** Under C1.2's premises and `UPat(W, M)` with
`M ≥ M*`: for every `t ≥ R_* = ḡ + Z + (8k + 20)Δ` there is an honest proposal `P` of a slot `p`
with `t ≤ t_p ≤ t + 4Δ(W + 1 + M)` and an honestly accepted block whose state finalizes a block
extending `P`, such that at every call of an honest node at a time
`≥ t + 4Δ(W + 1 + M) + Δ`, `P ⪯ Σ.F` (so `P` is in that node's finalized output). (The
coverage goes through the current entry of `P`, crossed on `P`'s retained chain, the new honest
entry `U ⪰ P` and its actual successor `V`.) -/
def FinalizingCoverage : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time) (W M cF kF : Nat),
    GoldilocksRun proposer dg H tr → PatternPremises tr H proposer dg g ΔF Gp W M cF kF →
    ∀ t, Rstar sp g ΔF Gp ≤ t →
      ∃ (q : Fin sp.n) (kP : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
        q ∈ H ∧ tr.ProposesAt q kP P ∧ t ≤ sp.ts P.slot ∧
        sp.ts P.slot ≤ t + 4 * sp.Δ * ((W : Time) + 1 + M) ∧
        (∃ x ∈ H, ∃ kX X, tr.AcceptAt x kX X ∧ ∃ Fx ∈ (tr.post kX).fg.tree,
          Fx.root = ((tr.post kX).fg.σ X.root).F ∧ Anc (tr.HonestBlocks H) P Fx) ∧
        ∀ y ∈ H, ∀ k, tr.IsCall y k →
          t + 4 * sp.Δ * ((W : Time) + 1 + M) + sp.Δ ≤ tr.time k →
          Anc (tr.HonestBlocks H) P (tr.state y k).fg.F

/-- **HR.5, cache acceptance** (G1.9 (b)). In a Goldilocks run under `Healthy(g)` and `NoColl`:
at every honest node's acceptance of a block `B`, `F* = σ[B].F` satisfies `F* ⪯ Σ.F` after that
`fg_on_block` call. (The claims state it after the reset `a_z` and at state heights `≥ H_z + 1`;
neither is needed: of `Healthy(g)` only its fault bound `3|Hᶜ| ≤ n − 1` is used, at every height
and time. The name keeps the claims node's.) -/
def CacheAcceptanceAfterReset : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    GoldilocksRun proposer dg H tr → tr.HealthyRun H ΔF g → Compose.NoCollRun dg tr →
      ∀ y ∈ H, ∀ k B, tr.AcceptAt y k B →
        ∀ Fs ∈ (tr.post k).fg.tree, Fs.root = ((tr.post k).fg.σ B.root).F →
          (tr.post k).fg.Anc Fs (tr.post k).fg.F

end Consensus.Goldilocks.Healing

end
