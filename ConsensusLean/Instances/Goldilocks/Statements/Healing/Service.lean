module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service

@[expose] public section

/-! # Goldilocks milestone Healing: the phase-service statements HS.1–HS.4 (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"Healing: phase service"
(goldilocks main `c6653258`; workbench `notes/goldilocks/healing-simple/phase-service.md` §§1–8),
over the Goldilocks run (`GoldilocksRun`) under the HS shared premises (`HSShared`, `Catch(2Δ)`,
and, for HS.2–HS.4, `Prop⁺(G_p)` and a settled time `w`). HS.0 (`Settle(Δ)`) and HS.5's
`Producer(A)` are stated as HR.3 (a), (b) (`Statements/Healing/Run`, `ResetExistence`).

**Vocabulary.**

* The **effective phase geometry** of a phase `(m, c)`: its floor `ℓ` is `m` in a contest and
  `m − 1` otherwise (the head height floor of a node that sees the phase); a block `W` is
  **allowed** in it when its state height is `≥ ℓ` and, in the top-`J` case, it extends `J`
  (`EffAllowed`). This is the phase's geometry, not one node's lagging local allowedness.
* **Before the phase end `e`**: the effective phase is `(m, c)` at every cut from a cut `i` through
  a cut `k` (`PhaseOn`). "Until `e`" for an event at cut `k` is `PhaseOn i k m c` from the cut `i`
  that fixes the phase.
* `slotA w` is `a`, the least slot with `t_a ≥ w + 4Δ`; `rTime w` is `r = t_{a + 2k + 2}`.
  "Label `j ≥ a`" is `t_j ≥ w + 4Δ`.
* A **source** is a block `C` that `ac_to_fg` returns at an honest node (`SA.ToFGAt`) and so passes
  to `fg_attest`; its **entry at `h`** is the entry block `E ⪯ C` of state height `h` (`EntryOf`).
  A **matching row** for `E` at `h` is an honestly signed attestation whose height pair is
  `(h, E)`, target or timeout.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

section Geometry

variable {P : Params} {ACP : Type}

/-- The floor `ℓ` of the effective phase `(m, c)`: `m` in a contest, `m − 1` otherwise. -/
def phaseFloor {β : Type} (m : Nat) : PhaseCase β → Nat
  | .contest _ => m
  | _ => m - 1

/-- `W` is allowed in the effective phase geometry of `(m, c)`, read at a store that holds it: its
state height is at least the floor and, in the top-`J` case, it extends `J`. -/
def EffAllowed (st : Store P ACP) (m : Nat) (c : PhaseCase (NodeBlock P ACP))
    (W : NodeBlock P ACP) : Prop :=
  W ∈ st.tree ∧ phaseFloor m c ≤ (st.σ W.root).h ∧ ∀ J, c = .top J → st.Anc J W

/-- The effective phase is `(m, c)` at every cut from `i` through `k` (no phase end in between). -/
def PhaseOn (tr : FGTrace P ACP) (H : Set (Fin P.n)) (i k m : Nat)
    (c : PhaseCase (NodeBlock P ACP)) : Prop :=
  ∀ k', i ≤ k' → k' ≤ k → PhaseAt tr H k' m c

/-- `E` is the entry at height `h` of the chain of `C` in the store `st`: an entry block (its own
state names it as the entry of its height) of state height `h` that `C` extends. -/
def EntryOf (st : Store P ACP) (C E : NodeBlock P ACP) (h : Nat) : Prop :=
  Store.IsEntry P ACP st E ∧ (st.σ E.root).h = h ∧ st.Anc E C

end Geometry

section Times

variable (sp : SAParams)

/-- `a`, the least slot with `t_a ≥ w + 4Δ`. -/
noncomputable def slotA (w : Time) : Nat := sInf {s : Nat | w + 4 * sp.Δ ≤ sp.ts s}

/-- `r = t_{a + 2k + 2}`. -/
noncomputable def rTime (w : Time) : Time := sp.ts (slotA sp w + 2 * sp.k + 2 : Nat)

end Times

section Run

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- The run is settled at `w` (with `κ = 2Δ`) in the effective phase `(m, c)`: `SettledAt` at `w`
and the phase at the state at `w` (cut `i₀`, the first cut at a time `≥ w`) is `(m, c)`. -/
def SettledIn (g w : Time) (i₀ m : Nat) (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) :
    Prop :=
  SettledAt tr H g (2 * sp.Δ) w ∧ tr.FirstCutFrom i₀ w ∧ PhaseAt tr.projFG H i₀ m c

/-- The vote of emission `e` (a call with label `ℓ`) extends `B`, and at that vote `B` is in the
viable voter block tree or at or below `fc_root` (block order). -/
def VoteKeeps (ℓ : ACLabel (goldilocksNode sp ro))
    (e : SA.Em sp (List (FG.Att sp.n))) (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
    (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)

/-- `x` writes, at cut `i`, a slow lock of label `j` whose stored block (the selected block `D`
after the move back of `add_locks`) is `B`. -/
def StoredSlowLockAt (x : Fin sp.n) (i j : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ ℓ D, tr.projAC.CallAt x i ℓ ∧ SA.SlowLockAt tr.projAC x i j D ∧
    B = ℓ.frame.viableAncestor D

end Run

/-- **HS.1, effective-phase viable-witness retention.** Under the HS shared premises (`HSShared`,
`Catch(2Δ)`): let the effective phase be `(m, c)` from cut `i` through cut `k`, and let `W`, held by
an honest `y` at cut `i`, be allowed in the effective phase geometry. Then (a) at every cut up to
`k`, every honest finalized root `Σ.F` extends to `W` (`F ⪯ W`); (b) so a lower advance of an honest
`Σ.F` removes `W` neither from the frame tree nor from the allowed heads: when an honest `z` holds
`W` at a cut `k' ∈ [i, k]`, `W` is in its frame tree and is a viable head of its frame unless
`W ⪯ fc_root`; (c) the viable-ancestor closure of the allowed heads grows during the phase, except
for the redundant prefix below the current fork-choice root: every ancestor `X` of such a `W` is
at or below `z`'s `fc_root` or in the viable tree of its frame; and (d) at an honest vote at a cut
in `[i, k]` whose voter block tree holds `W`, every such `X` is in the viable voter block tree or
at or below `fc_root` (a frozen viability witness; not every later disclosed witness is claimed to
be in that domain). -/
def ViableWitnessRetention : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF : Time),
    GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
    ∀ (i k m : Nat) (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
      PhaseOn tr.projFG H i k m c →
      ∀ y ∈ H, ∀ W, EffAllowed (tr.state y i).fg m c W →
        ∀ z ∈ H, ∀ k', i ≤ k' → k' ≤ k →
          Anc (tr.HonestBlocks H) (tr.state z k').fg.F W ∧
          (W ∈ (tr.state z k').fg.tree →
            W ∈ (Node.frame (tr.state z k')).tree ∧
            (W ∈ (Node.frame (tr.state z k')).viableHeads ∨
              Anc (tr.HonestBlocks H) W (Node.frame (tr.state z k')).fcRoot) ∧
            ∀ X, Anc (tr.HonestBlocks H) X W →
              Anc (tr.HonestBlocks H) X (Node.frame (tr.state z k')).fcRoot ∨
              X ∈ (Node.frame (tr.state z k')).viableTree (Node.frame (tr.state z k')).tree) ∧
          ∀ ℓ e, SA.CastAt tr.projAC z k' ℓ e →
            W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot →
            ∀ X, Anc (tr.HonestBlocks H) X W →
              X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
              Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot

/-- **HS.2, clean-lock transfer and two-window drain.** Under the HS shared premises with
`Catch(2Δ)` and `Prop⁺(G_p)`, settled at `w` in the effective phase `(m, c)` (cut `i₀`), with `a`
and `r` from `w`, for events until the phase end:
(1) a fast lock of label `j ≥ a` written by an honest node before the phase end with stored block
`B` and counted votes `CV`: every honest vote of slot `j + 1` extends `B`, with `B` in the viable
voter block tree or at or below `fc_root`, and `Carry` holds at it for the retained counted heads
(`CV`, when `B` is not at or below the voter's `fc_root`); every honest vote of a later slot extends
`B` unless `B` is already at or below the voter's `fc_root`, with the same viability;
(2) a slow lock of label `j` with `j − k + 1 ≥ a` and stored block `B`: the same conclusion from
slot `j + 1`, with `Carry` for the counted votes of the update's result;
(3) every live lock of an honest node at a time `≥ r` is clean (a fast lock of label `≥ a`, or a
slow lock with `j − k + 1 ≥ a`): the possibly unclean locks have expired before `r`; and at each
honest proposal `P` of a slot `s` with `t_s ≥ r`, the proposal walk follows every effective live
lock of an earlier label that can affect the slot-`s` voters: at each honest slot-`s` vote, every
live lock of a label `< s` of the voter has its block below `P` or at or below the voter's
`fc_root` (the voter lock premise of the first part of claims HS.3; HS.3 is proved from HS.2).
All conclusions hold through lower advances of `Σ.F`, with the original `a` and `r` (the phase
does not read `Σ.F`). -/
def CleanLockDrain : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp w : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
    GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
    PropPlus tr H proposer g Gp → SettledIn tr H g w i₀ m c →
    (∀ x ∈ H, ∀ i j B CV, Compose.StoredFastLockAt tr x i j B CV → w + 4 * sp.Δ ≤ sp.ts j →
      PhaseOn tr.projFG H i₀ i m c →
      ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
        PhaseOn tr.projFG H i₀ k m c →
        (e.msg.slot = j + 1 → VoteKeeps tr H ℓ e B ∧
          (¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
            SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV)) ∧
        (¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot → VoteKeeps tr H ℓ e B)) ∧
    (∀ x ∈ H, ∀ i j B, StoredSlowLockAt tr x i j B →
      w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1) → PhaseOn tr.projFG H i₀ i m c →
      ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
        PhaseOn tr.projFG H i₀ k m c →
        (e.msg.slot = j + 1 → VoteKeeps tr H ℓ e B ∧
          ∀ C CV, SA.ResultAt tr.projAC x i j C CV →
            ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
            SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV) ∧
        (¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot → VoteKeeps tr H ℓ e B)) ∧
    (∀ y ∈ H, ∀ k ℓ, tr.projAC.CallAt y k ℓ → rTime sp w ≤ tr.time k →
      PhaseOn tr.projFG H i₀ k m c →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k),
        (l.fast = true → w + 4 * sp.Δ ≤ sp.ts l.slot) ∧
        (l.fast = false → w + 4 * sp.Δ ≤ sp.ts ((l.slot : Int) - sp.k + 1))) ∧
    ∀ (s : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), HonestProposalRun tr H proposer s P →
      rTime sp w ≤ sp.ts s →
      ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
        PhaseOn tr.projFG H i₀ k m c →
        ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
          ∀ L ∈ ℓ.frame.tree, L.root = l.block →
            Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot

/-- **HS.3, honest-proposal frozen-tree agreement after `r`.** Under the HS shared premises with
`Catch(2Δ)` and `Prop⁺(G_p)`, settled at `w` in the effective phase `(m, c)` (cut `i₀`; claims:
"HS.2–HS.5 assume that the run is settled at w"): let `P` be the honest joined ready proposal of
slot `s` (`ReadyProposal`, made at cut `kP`) with `t_s ≥ r`, in the effective phase `(m, c)` from a
cut `i` with `i₀ ≤ i ≤ kP` at or before the previous freeze `t_{s−1} + 3Δ` through every honest
slot-`s` vote (a stable effective phase geometry on the compared events, which include the
voters' pre-freeze trees), with acceptance relay from the previous freeze `t_{s−1} + 3Δ`
(`t_{s−1} + 3Δ ≥ ḡ`). Then every honest slot-`s` vote is exactly `P`; at it `P` is a viable head of
the voter's frame and in its viable voter block tree, or at or below its `fc_root`; every ancestor
of `P` is in that viable voter block tree or at or below `fc_root` (the unlocked parent path is
retained); every honest vote of a slot `> s` until the phase end extends `P`; and every honest
proposal of a slot `> s` until the phase end has a parent that extends `P` (if `P`'s entry is
crossed its ancestry is still retained; no claim that the entry stays current). HS.2 supplies both
lock premises of the claims' first part (the voter lock premise and the proposer-anchor premise)
for every such proposal, so neither is a premise here.

This is the claims' after-`r` part only. The first part (every slot-`s` vote is `P`, viable at it
with its parent path retained, under the explicit lock premise and the proposer-anchor premise of
consensus-lean#100, without `Prop⁺` or `t_s ≥ r`) is not stated: its proof is open, and nothing
consumes it (`docs/decisions.md`, HS.3). -/
def FrozenTreeAgreement : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF w : Time) (i₀ i m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
    GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
    SettledIn tr H g w i₀ m c → i₀ ≤ i →
    ∀ (p : Fin sp.n) (kP s : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H proposer p kP s P → i ≤ kP →
      tr.time i ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ →
      gbar g ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ →
      (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
        PhaseOn tr.projFG H i k m c) →
      ∀ Gp : Time, PropPlus tr H proposer g Gp →
        rTime sp w ≤ sp.ts s →
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          e.msg.head = P.root ∧
          ((P ∈ ℓ.frame.viableHeads ∧
              P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
            Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot) ∧
          ∀ X, Anc (tr.HonestBlocks H) X P →
            X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
            Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot) ∧
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
          PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg P) ∧
        ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
          tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H →
          PhaseOn tr.projFG H i₀ k' m c →
          ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) P Pr

/-- **HS.4, bounded common path and actual-report acquisition.** Under the HS shared premises with
`Catch(2Δ)` and `Prop⁺(G_p)`, settled at `w` in the effective phase `(m, c)` (cut `i₀`), with `D =
D_HS(G_p)`: (a) either the phase has changed by `w + D` (after all events there), or there are a
slot `s` with `t_s ≥ r` (the first honest proposal after `r`, or the second one after a suppressing
descendant source), a height `h ∈ {ℓ, m}` with `h ≥ 1`, an entry `E` at `h` and an honest proposal
`W` of slot `s` extending `E` with state height `h`, such that `w ≤ t_s`, `v = t_s + 6Δ ≤ w + D`,
the phase is still `(m, c)` after all events at `v` (`v < e`), every honest slot-`s` vote is exactly
`W` with `W` in its viable voter block tree or at or below its `fc_root`, by `v` every honest
validator has actually received a current source of state height `h` with entry `E` (an `ac_to_fg`
return in `[t_s, v]` of a block extending `W` and allowed in the phase geometry, so (b) applies to
it; not a historical source, nor a higher descendant that suppresses the report at `h`) or has
signed a matching row for `E` (so the report and row set has weight `n − f ≥ q`), and until the
phase end every later honest vote and every honest proposal parent of a later slot extends `W`; (b)
the client subclaim (P1/P2 of workbench#6): in the settled phase, at an honest `fg_attest` whose
source `C` has state height `h ≥ ℓ` and entry `E` and is allowed in the phase geometry, the client
signs a matching row for `E` (target or timeout), or has signed one at an earlier cut (its durable
record holds it). -/
def CommonPathAcquisition : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp w : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
    GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
    PropPlus tr H proposer g Gp → SettledIn tr H g w i₀ m c →
    ((∀ j', FirstCutAfter tr j' (w + D_HS sp Gp) → PhaseChanged tr.projFG H i₀ j') ∨
      ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
        (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
        tr.ProposesAt (proposer s) kW W ∧ W.slot = s ∧ proposer s ∈ H ∧
        EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
        w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
        (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) ∧
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          e.msg.head = W.root ∧
          (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
            Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot)) ∧
        (∀ y ∈ H, (∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
            tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ (tr.state y k).fg.Anc W C ∧
            EntryOf (tr.state y k).fg C E h ∧ ((tr.state y k).fg.σ C.root).h = h ∧
            EffAllowed (tr.state y k).fg m c C) ∨
          ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = h ∧
            att.T = E.root) ∧
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
          PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W) ∧
        ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
          tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H →
          PhaseOn tr.projFG H i₀ k' m c →
          ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr) ∧
    ∀ y ∈ H, ∀ k (C : SA.Blk sp.n (List (FG.Att sp.n))) (signed : Option (FG.Att sp.n)),
      tr.CallAt y k (.fg (.attest C signed)) → i₀ ≤ k → PhaseOn tr.projFG H i₀ k m c →
      ∀ E h, EntryOf (tr.state y k).fg C E h → ((tr.state y k).fg.σ C.root).h = h →
        phaseFloor m c ≤ h →
        EffAllowed (tr.state y k).fg m c C →
        (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
        ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root

/-- The phase-service statements of milestone Healing (HS.1–HS.4). -/
structure PhaseServiceStatements : Prop where
  viableWitnessRetention : ViableWitnessRetention
  cleanLockDrain : CleanLockDrain
  frozenTreeAgreement : FrozenTreeAgreement
  commonPathAcquisition : CommonPathAcquisition

end Consensus.Goldilocks.Healing

end
