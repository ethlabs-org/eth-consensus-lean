module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

@[expose] public section

/-! # Goldilocks Healing under growing faults: the phase-service vocabulary (statements)

The vocabulary of HS.1–HS.4 (`Statements/Healing/Service`) for a time-indexed honest set `H`
(antitone), over `Growing.GoldilocksRun` under the growing-fault HS shared premises
(`Healing.Growing.HSShared`); HS.1–HS.4 under growing faults are retired with the phase-service
bundle. The reading:

* every **cohort horizon `d`**: every honesty read at time `t` (a holder, voter, caller, writer
  or proposer at its cut, the phase at a cut, settledness at `w`, a phase change by `w + D`, HS.4's
  acquisition at the report deadline `v = t_s + 6Δ`) is at `max d t`;
  so up to `d` the statements are about the fixed cohort `H d`, and `d = 0` gives the reading at
  each cut's own time; HS.4's phase change is read at both cuts over one fixed `H d` with
  `d ≥ w + D` (no horizon moves with an endpoint);
* the premises `HSShared`, `Catch(2Δ)`, `Prop⁺(G_p)` and the ready proposal of HS.3 (proposer
  honest through `t_s + hold`) are read at their own times.

The geometry and times that bind no honest set (`phaseFloor`, `EffAllowed`, `EntryOf`, `slotA`,
`rTime`, `StoredSlowLockAt`) are the static ones.

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

end Consensus.Goldilocks.Healing.Growing

end
