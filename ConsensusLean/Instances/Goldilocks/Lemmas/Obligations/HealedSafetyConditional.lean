module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.WeakBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.CoefficientAdapters
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Conditional read safety: the latest view and the live-lock anchor

`result_label_lt_latest_of_time`: a completed result is strictly older than the current latest
view. `record_below_anchor_of_stored_live_lock`: a stored time-live lock gives the anchor arm when
its normalized block still covers the record and the current live lock blocks form a chain. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

/-- A completed result is strictly older than the current latest view, including
the equality boundary at its update time. -/
theorem result_label_lt_latest_of_time
    {sp : AC.ACParams} {FGP : Type} {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    {s : Nat} {t : Time} (ht0 : 0 ≤ t) (ht : sp.ts s + 6 * sp.Δ ≤ t) :
    (s : Int) < (AC.latestView sp A Φ t).2 := by
  have hnext : sp.ts (s + 1 : Nat) + 2 * sp.Δ ≤ t := by
    simp only [AC.ACParams.ts] at ht ⊢
    push_cast
    linarith
  have hd := sp.toParams.hΔ
  simp only [AC.latestView]
  split_ifs with hphase
  · have hh := (AC.ts_le_iff_le_slot sp ht0 (s + 1 : Nat)).mp
      (show sp.ts (s + 1 : Nat) ≤ t by linarith)
    push_cast at hh
    omega
  · have hh := (AC.ts_lt_iff sp).mp
      (show sp.ts (s + 1 : Nat) < sp.ts (sp.slot t) by linarith)
    push_cast at hh
    omega

/-- An actual stored time-live lock gives the anchor arm only when its normalized
block still covers the record and the current live blocks form a chain. -/
theorem record_below_anchor_of_stored_live_lock
    {sp : AC.ACParams} {FGP : Type} {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {A : AC.ACState sp.n} {t : Time} {R B : AC.Blk sp.n FGP} {l : AC.Lock}
    (hl : l ∈ A.locks) (hB : B ∈ Φ.tree) (hroot : B.root = l.block)
    (ht : l.LiveAt sp t) (hcover : Φ.Anc R (Φ.viableAncestor B))
    (hchain : ∀ X ∈ AC.liveLockBlocks sp A.locks Φ t,
      ∀ Y ∈ AC.liveLockBlocks sp A.locks Φ t, Goldilocks.Compatible Φ.tree X Y) :
    Φ.Anc R (AC.getAnchor sp A Φ t) := by
  have hmem : Φ.viableAncestor B ∈ AC.liveLockBlocks sp A.locks Φ t :=
    ⟨(AC.viableAncestor_anc hΦ hB).1,
      ⟨⟨(Φ.viableAncestor B).root, l.slot, l.fast, l.expiry⟩, ⟨l, hl, B, hB, hroot, ht, rfl⟩,
        rfl⟩⟩
  exact hcover.trans ((AC.anc_getAnchor hΦ hchain).2 _ (Or.inl hmem))

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

end Consensus.Goldilocks.Obligations
end
