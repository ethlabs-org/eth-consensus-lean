module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run

@[expose] public section

/-! # Goldilocks milestone Service: the available chain after C1.1 (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks main
`4ea71d05`) §"Available chain, after C1.1", over the Goldilocks run (`Spec/Run`,
`GoldilocksRun`) under `Sleepy` (`SleepyRun`) and `NoColl` (`NoCollRun`; the claims' standing
assumption on the digest, taken explicitly here as every run-level statement does, since the
SA's chain reasoning identifies blocks by root):

* **A1.6, head extends the record under synchrony**: at an honest node awake and joined at `t`
  that has run the update of slot `slot(t) − 2` with no restart since, the head extends
  `𝒜.latest_confirmed` when that block is in the frame's tree, so `ac_confirmed` is that block;
  and while both conditions hold, the record only moves to a descendant.
* **A1.7, inclusion**: an honest proposal `P` of slot `s` by a joined proposer is in the
  confirmed tip of every honest node awake and joined at `t ≥ t_s + 6Δ` that was awake and
  joined at `t_s + 6Δ` with no restart since.

* **C1.2, AC outcome service for honest entries** (claims at goldilocks `6703bf05`, #37: its
  run premises are the healing regime after the reset `a_z`): under `Healthy(g)`, `Catch(2Δ)`,
  `Prop⁺(G_p)` and the HS shared premises, an entry whose entry block `P` is an actual honest
  ready proposal of slot `u` with `t_u ≥ R_z = t_{slot(a_z)+2k+5}`, at a height `≥ H_z + 1`
  (with its predecessor that high when it is bound), and with retained ready inclusion in its
  window, gets outcome service by the end of the window: a literal good window
  (`Store.GoodWindow`, on the FG projection) or an accepted early justification, which at a
  bound entry has finalized the predecessor (the gate), and at an unbound entry gives its
  actual bound successor.

C1.3 (finalizing coverage recurs) is in `Statements/Healing/Recovery` (`FinalizingCoverage`).
"At `t`" is read at a cut of the node at time `t` (`tr.IsCall y i`, `tr.time i = t`),
with the state before the cut.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- `y` has run the update of slot `s` before cut `i` with no restart since: the update ran at a
cut `k < i` and no cut in `(k, i)` is a restart of `y`. -/
def UpdatedNoRestart (y : Fin sp.n) (i s : Nat) : Prop :=
  ∃ k < i, ∃ ℓ, SA.UpdateAt tr.projAC y k s ℓ ∧ ∀ k', k < k' → k' < i → ¬ tr.RestartAt y k'

/-- The condition of A1.6 at cut `i` of `y`: awake and joined at its time, and the update of
slot `slot(t) − 2` has run with no restart since (`slot(t) ≥ 2`). -/
def ServedAt (y : Fin sp.n) (i : Nat) : Prop :=
  tr.IsCall y i ∧ tr.awake y (tr.time i) ∧ tr.JoinedAt y (tr.time i) ∧
    ∃ s : Nat, s + 2 = sp.slot (tr.time i) ∧ UpdatedNoRestart tr y i s

/-- The block of `y`'s record `𝒜.latest_confirmed` before cut `i`, if it is in the frame's
tree. -/
def RecordAt (y : Fin sp.n) (i : Nat) (R : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  R ∈ (Node.frame (tr.state y i)).tree ∧ R.root = (tr.state y i).ac.latestConfirmed

/-- **A1.6, head extends the record under synchrony.** Under `Sleepy`, at every cut of an honest
node awake and joined at its time that has run the update of slot `slot(t) − 2` with no restart
since: when the record `𝒜.latest_confirmed` is a block of the frame's tree, the head extends it
(inside the frame) and `ac_confirmed` is that block; and while the condition keeps holding (at
every cut of the node from now to a later cut), the record then extends the record now (inside
the honest blocks). -/
def HeadExtendsRecord : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time),
    GoldilocksRun dg H tr → NoCollRun dg tr → tr.SleepyRun H ΔF →
    ∀ y ∈ H, ∀ i, ServedAt tr y i → ∀ R, RecordAt tr y i R →
      ((Node.frame (tr.state y i)).Anc R (tr.headAt y i) ∧ tr.confirmedAt y i = R) ∧
      ∀ i', i ≤ i' → (∀ k, i ≤ k → k ≤ i' → tr.IsCall y k → ServedAt tr y k) →
        ∀ R', RecordAt tr y i' R' → Anc (tr.HonestBlocks H) R R'

/-- **A1.7, inclusion.** Under `Sleepy`, with a genesis whose root is its digest, an honest
proposal `P` of slot `s` by a proposer joined at its proposal is in the confirmed tip (inside
the honest blocks) of every honest node at every cut at a time `t ≥ t_s + 6Δ` where it is awake
and joined, if it was awake and joined at `t_s + 6Δ`, has not restarted at a cut in
`(t_s + 6Δ, t]`, and has run the update of slot `s` at a cut before this one with no restart
since (`UpdatedNoRestart`, as A1.6). The update clause is needed at the boundary `t = t_s + 6Δ`:
"at `t`" is the state before a cut at `t`, and the node's first cut there is the AC tick that
runs the update of slot `s` (at `t_{s+1} + 2Δ`), so before it the record can still be older
than `P` (consensus-lean#77). With the node awake and joined at `t_s + 6Δ` the update is that
tick, so the clause excludes only the cuts of that tick up to the update. The genesis root is
needed as in C0.3: an honest proposal whose root is `P.genesisRoot` is refused by every FG, so
it is in no honest tree (consensus-lean#73). -/
def Inclusion : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time),
    GoldilocksRun dg H tr → NoCollRun dg tr → tr.SleepyRun H ΔF →
    (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg →
    ∀ p ∈ H, ∀ k (P : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat),
      tr.ProposesAt p k P → P.slot = s → SA.joined sp (tr.state p k).ac (tr.time k) →
      ∀ y ∈ H, ∀ i, tr.IsCall y i → sp.ts s + 6 * sp.Δ ≤ tr.time i →
        tr.awake y (tr.time i) → tr.JoinedAt y (tr.time i) →
        tr.awake y (sp.ts s + 6 * sp.Δ) → tr.JoinedAt y (sp.ts s + 6 * sp.Δ) →
        (∀ k', tr.RestartAt y k' → sp.ts s + 6 * sp.Δ < tr.time k' → tr.time k' ≤ tr.time i →
          False) →
        UpdatedNoRestart tr y i s →
        Anc (tr.HonestBlocks H) P (tr.confirmedAt y i)

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
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a : Time) (cF kF : Nat),
    GoldilocksRun dg H tr → Healing.HSShared tr H dg g ΔF →
    Healing.CatchRun tr H g (2 * sp.Δ) → Healing.PropPlus tr H g Gp →
    4 * sp.Δ * ((cF : Time) - 1) < 6 * sp.Δ + ΔF → 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time) →
    cF + kF ≤ sp.toParams.δt →
    Healing.IsReset tr H g a →
    ∀ (p : Fin sp.n) (k i : Nat) (T : SA.Blk sp.n (List (FG.Att sp.n))) (u : Nat),
      Healing.ReadyProposal tr H p k u T →
      RunEntry tr H p i T →
      sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) ≤ sp.ts u →
      Healing.HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).h →
      (0 < ((tr.post i).fg.σ T.root).hj →
        ((tr.post i).fg.σ T.root).hj + 1 = ((tr.post i).fg.σ T.root).h →
        Healing.HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).hj) →
      (∃ (w : Fin sp.n) (kw : Nat) (W : SA.Blk sp.n (List (FG.Att sp.n))),
        Healing.ReadyProposal tr H w kw W.slot W ∧ u + cF ≤ W.slot ∧ W.slot ≤ u + cF + kF ∧
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

/-- The statements of milestone Service (so far). -/
structure ServiceStatements : Prop where
  headExtendsRecord : HeadExtendsRecord
  inclusion : Inclusion
  outcomeService : OutcomeService

end Consensus.Goldilocks.Compose

end
