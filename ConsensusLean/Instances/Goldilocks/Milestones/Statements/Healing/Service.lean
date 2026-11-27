module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Service

@[expose] public section

/-! # Goldilocks Healing: the shared phase-service vocabulary (statements)

The phase-service statements HS.0–HS.5 and their bundle are retired (owner decision, with HR.3);
what stays is the vocabulary that live code reads, transcribed from
`specs/goldilocks/tex/goldilocks-claims.tex` §"Healing: phase service":

* **Before the phase end `e`**: the effective phase is `(m, c)` at every cut from a cut `i` through
  a cut `k` (`PhaseOn`).
* A **source** is a block `C` that `ac_to_fg` returns at an honest node (`AC.ToFGAt`); its **entry
  at `h`** is the entry block `E ⪯ C` of state height `h` (`EntryOf`).
* **Settled at `w`** in the effective phase `(m, c)` from the cut `i₀` (`SettledIn`).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

section Geometry

variable {P : Params} {ACP : Type}

/-- The effective phase is `(m, c)` at every cut from `i` through `k` (no phase end in between). -/
def PhaseOn (tr : FGTrace P ACP) (H : Set (Fin P.n)) (i k m : Nat)
    (c : PhaseCase (NodeBlock P ACP)) : Prop :=
  ∀ k', i ≤ k' → k' ≤ k → PhaseAt tr H k' m c

/-- `E` is the entry at height `h` of the chain of `C` in the store `st`: an entry block (its own
state names it as the entry of its height) of state height `h` that `C` extends. -/
def EntryOf (st : Store P ACP) (C E : NodeBlock P ACP) (h : Nat) : Prop :=
  Store.IsEntry P ACP st E ∧ (st.σ E.root).h = h ∧ st.Anc E C

end Geometry

section Run

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Set (Fin sp.n))

/-- The run is settled at `w` (with `κ = 2Δ`) in the effective phase `(m, c)`: `SettledAt` at `w`
and the phase at the state at `w` (cut `i₀`, the first cut at a time `≥ w`) is `(m, c)`. -/
def SettledIn (g w : Time) (i₀ m : Nat) (c : PhaseCase (AC.Blk sp.n (List (FG.Att sp.n)))) :
    Prop :=
  SettledAt tr H g (2 * sp.Δ) w ∧ tr.FirstCutFrom i₀ w ∧ PhaseAt tr.projFG H i₀ m c

end Run

end Consensus.Goldilocks.Healing

end
