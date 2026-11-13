module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

@[expose] public section

/-! # Goldilocks milestone Healing under growing faults: the phase service HS.1–HS.4 (statements)

HS.1–HS.4 (`Statements/Healing/Service`) for a time-indexed honest set `H` (antitone), over
`Growing.GoldilocksRun` under the growing-fault HS shared premises (`Healing.Growing.HSShared`):

* each statement holds for every **cohort horizon `d`**: every honesty read at time `t` (a holder,
  voter, caller, writer or proposer at its cut, the phase at a cut, settledness at `w`, a phase
  change by `w + D`, HS.4's acquisition at the report deadline `v = t_s + 6Δ`) is at `max d t`;
  so up to `d` the statements are about the fixed cohort `H d`, and `d = 0` gives the reading at
  each cut's own time; HS.4's phase change is read at both cuts over one fixed `H d` with
  `d ≥ w + D` (no horizon moves with an endpoint);
* the premises `HSShared`, `Catch(2Δ)`, `Prop⁺(G_p)` and the ready proposal of HS.3 (proposer
  honest through `t_s + hold`) are read at their own times.

The geometry and times that bind no honest set (`phaseFloor`, `EffAllowed`, `EntryOf`, `slotA`,
`rTime`, `StoredSlowLockAt`) are the static ones. At `H := fun _ => H₀` each statement implies its
static counterpart.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

/-- The effective phase is `(m, c)` at every cut from `i` through `k`, read at each cut `k'` over
the validators honest at `max d (time k')`: the cohort `H d` up to the horizon `d`. -/
def PhaseOn {P : Params} {ACP : Type} (tr : FGTrace P ACP) (H : Time → Set (Fin P.n))
    (d : Time) (i k m : Nat) (c : PhaseCase (NodeBlock P ACP)) : Prop :=
  ∀ k', i ≤ k' → k' ≤ k → PhaseAt tr (H (max d (tr.time k'))) k' m c

section Run

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))

/-- Settled at `w`, for the cohort of horizon `d`, in the effective phase `(m, c)` read over the
validators honest at `max d w`. -/
def SettledIn (d g w : Time) (i₀ m : Nat) (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) :
    Prop :=
  SettledAt tr H d g (2 * sp.Δ) w ∧ tr.FirstCutFrom i₀ w ∧
    PhaseAt tr.projFG (H (max d w)) i₀ m c

/-- The vote of emission `e` extends `B`, with `B` in the viable voter block tree or at or below
`fc_root`, inside the blocks held while honest. -/
def VoteKeeps (ℓ : ACLabel (goldilocksNode sp ro))
    (e : SA.Em sp (List (FG.Att sp.n))) (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  SA.VoteExtends (tr.HonestBlocksAt H) e.msg B ∧
    (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot)

end Run

/-- **HS.1 under growing faults, effective-phase viable-witness retention.** `W` is held by `y`
honest at cut `i`; the conclusions are at cuts `k'` of nodes `z` honest at `k'`. -/
def ViableWitnessRetention : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF d : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF →
    CatchRun tr H g (2 * sp.Δ) →
    ∀ (i k m : Nat) (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
      PhaseOn tr.projFG H d i k m c →
      ∀ y W, y ∈ H (max d (tr.time i)) → EffAllowed (tr.state y i).fg m c W →
        ∀ z k', z ∈ H (max d (tr.time k')) → i ≤ k' → k' ≤ k →
          Anc (tr.HonestBlocksAt H) (tr.state z k').fg.F W ∧
          (W ∈ (tr.state z k').fg.tree →
            W ∈ (Node.frame (tr.state z k')).tree ∧
            (W ∈ (Node.frame (tr.state z k')).viableHeads ∨
              Anc (tr.HonestBlocksAt H) W (Node.frame (tr.state z k')).fcRoot) ∧
            ∀ X, Anc (tr.HonestBlocksAt H) X W →
              Anc (tr.HonestBlocksAt H) X (Node.frame (tr.state z k')).fcRoot ∨
              X ∈ (Node.frame (tr.state z k')).viableTree (Node.frame (tr.state z k')).tree) ∧
          ∀ ℓ e, SA.CastAt tr.projAC z k' ℓ e →
            W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot →
            ∀ X, Anc (tr.HonestBlocksAt H) X W →
              X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
              Anc (tr.HonestBlocksAt H) X ℓ.frame.fcRoot

/-- **HS.2 under growing faults, clean-lock transfer and two-window drain.** Writers are honest at
their writes, voters at their votes, callers at their calls; the honest proposal of (3) is by a
proposer honest through `t_s + hold`. -/
def CleanLockDrain : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF w d : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF →
    CatchRun tr H g (2 * sp.Δ) → SettledIn tr H d g w i₀ m c →
    (∀ x i j B CV, x ∈ H (max d (tr.time i)) → Compose.StoredFastLockAt tr x i j B CV →
      w + 4 * sp.Δ ≤ sp.ts j →
      ∀ y k ℓ e, y ∈ H (max d (tr.time k)) → SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
        PhaseOn tr.projFG H d i₀ k m c →
        VoteKeeps tr H ℓ e B ∧
          (e.msg.slot = j + 1 → ¬ Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot →
            SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e j CV)) ∧
    (∀ x i j B, x ∈ H (max d (tr.time i)) → StoredSlowLockAt tr x i j B →
      w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1) →
      ∀ y k ℓ e, y ∈ H (max d (tr.time k)) → SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
        PhaseOn tr.projFG H d i₀ k m c →
        VoteKeeps tr H ℓ e B ∧
          (e.msg.slot = j + 1 → ∀ C CV, SA.ResultAt tr.projAC x i j C CV →
            ¬ Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot →
            SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e j CV)) ∧
    (∀ y k ℓ, y ∈ H (max d (tr.time k)) → tr.projAC.CallAt y k ℓ → rTime sp w ≤ tr.time k →
      ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k),
        (l.fast = true → w + 4 * sp.Δ ≤ sp.ts l.slot) ∧
        (l.fast = false → w + 4 * sp.Δ ≤ sp.ts ((l.slot : Int) - sp.k + 1))) ∧
    ∀ (s : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), HonestProposalRun tr H proposer s P →
      rTime sp w ≤ sp.ts s →
      ∀ y k ℓ e, y ∈ H (max d (tr.time k)) → SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
        PhaseOn tr.projFG H d i₀ k m c →
        ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
          ∀ L ∈ ℓ.frame.tree, L.root = l.block →
            Anc (tr.HonestBlocksAt H) L P ∨ Anc (tr.HonestBlocksAt H) L ℓ.frame.fcRoot

/-- **HS.3 under growing faults, honest-proposal frozen-tree agreement after `r`.** The ready
proposer is honest through `t_s + hold`; voters are honest at their votes; a later proposal is by a
proposer honest at its proposal cut. -/
def FrozenTreeAgreement : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF w d : Time) (i₀ i m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF →
    CatchRun tr H g (2 * sp.Δ) → SettledIn tr H d g w i₀ m c → i₀ ≤ i →
    ∀ (p : Fin sp.n) (kP s : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H proposer p kP s P → i ≤ kP →
      tr.time i ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ →
      gbar g ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ →
      (∀ y k ℓ e, y ∈ H (max d (tr.time k)) → SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
        PhaseOn tr.projFG H d i k m c) →
      rTime sp w ≤ sp.ts s →
      (∀ y k ℓ e, y ∈ H (max d (tr.time k)) → SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
        e.msg.head = P.root ∧
        ((P ∈ ℓ.frame.viableHeads ∧
            P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
          Anc (tr.HonestBlocksAt H) P ℓ.frame.fcRoot) ∧
        ∀ X, Anc (tr.HonestBlocksAt H) X P →
          X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
          Anc (tr.HonestBlocksAt H) X ℓ.frame.fcRoot) ∧
      (∀ y k ℓ e, y ∈ H (max d (tr.time k)) → SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
        PhaseOn tr.projFG H d i₀ k m c → SA.VoteExtends (tr.HonestBlocksAt H) e.msg P) ∧
      ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
        tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H (max d (tr.time k')) →
        PhaseOn tr.projFG H d i₀ k' m c →
        ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocksAt H) P Pr

/-- **HS.4 under growing faults, bounded common path and actual-report acquisition**, for a
fixed cohort horizon `d ≥ w + D`: the phase change by `w + D` is read at both cuts over the cohort
`H d`, settledness at `w` and the acquisition by `v = t_s + 6Δ ≤ w + D` are by the cohort (a
validator compromised by `d` is charged as faulty in the count `n − f_d ≥ q` that reads it); the
proposal `W`, the votes, the later proposals and the client subclaim are at cuts of nodes honest
at `max d` of their cut times. -/
def CommonPathAcquisition : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp w d : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF →
    CatchRun tr H g (2 * sp.Δ) → PropPlus tr H proposer g Gp → w + D_HS sp Gp ≤ d →
    SettledIn tr H d g w i₀ m c →
    ((∀ j', FirstCutAfter tr j' (w + D_HS sp Gp) → PhaseChanged tr.projFG (H d) i₀ j') ∨
      ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
        (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
        tr.ProposesAt (proposer s) kW W ∧ W.slot = s ∧ proposer s ∈ H (max d (tr.time kW)) ∧
        EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
        w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
        (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H d i₀ jv m c) ∧
        (∀ y k ℓ e, y ∈ H (max d (tr.time k)) → SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          e.msg.head = W.root ∧
          (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
            Anc (tr.HonestBlocksAt H) W ℓ.frame.fcRoot)) ∧
        (∀ y, y ∈ H (max d (sp.ts s + 6 * sp.Δ)) →
          (∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
            tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ (tr.state y k).fg.Anc W C ∧
            EntryOf (tr.state y k).fg C E h ∧ ((tr.state y k).fg.σ C.root).h = h ∧
            EffAllowed (tr.state y k).fg m c C) ∨
          ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = h ∧
            att.T = E.root) ∧
        (∀ y k ℓ e, y ∈ H (max d (tr.time k)) → SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
          PhaseOn tr.projFG H d i₀ k m c → SA.VoteExtends (tr.HonestBlocksAt H) e.msg W) ∧
        ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
          tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H (max d (tr.time k')) →
          PhaseOn tr.projFG H d i₀ k' m c →
          ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocksAt H) W Pr) ∧
    ∀ y k (C : SA.Blk sp.n (List (FG.Att sp.n))) (signed : Option (FG.Att sp.n)),
      y ∈ H (max d (tr.time k)) → tr.CallAt y k (.fg (.attest C signed)) → i₀ ≤ k →
      PhaseOn tr.projFG H d i₀ k m c →
      ∀ E h, EntryOf (tr.state y k).fg C E h → ((tr.state y k).fg.σ C.root).h = h →
        phaseFloor m c ≤ h →
        EffAllowed (tr.state y k).fg m c C →
        (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
        ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root

end Consensus.Goldilocks.Healing.Growing

end
