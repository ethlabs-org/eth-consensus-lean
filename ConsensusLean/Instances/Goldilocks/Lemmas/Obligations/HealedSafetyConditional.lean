module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
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
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
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
    {sp : SA.SAParams} {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {s : Nat} {t : Time} (ht0 : 0 ≤ t) (ht : sp.ts s + 6 * sp.Δ ≤ t) :
    (s : Int) < (SA.latestView sp A Φ t).2 := by
  have hnext : sp.ts (s + 1 : Nat) + 2 * sp.Δ ≤ t := by
    simp only [SA.SAParams.ts] at ht ⊢
    push_cast
    linarith
  have hd := sp.toParams.hΔ
  simp only [SA.latestView]
  split_ifs with hphase
  · have hh := (SA.ts_le_iff_le_slot sp ht0 (s + 1 : Nat)).mp
      (show sp.ts (s + 1 : Nat) ≤ t by linarith)
    push_cast at hh
    omega
  · have hh := (SA.ts_lt_iff sp).mp
      (show sp.ts (s + 1 : Nat) < sp.ts (sp.slot t) by linarith)
    push_cast at hh
    omega

/-- An actual stored time-live lock gives the anchor arm only when its normalized
block still covers the record and the current live blocks form a chain. -/
theorem record_below_anchor_of_stored_live_lock
    {sp : SA.SAParams} {FGP : Type} {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {A : SA.SAState sp.n} {t : Time} {R B : SA.Blk sp.n FGP} {l : SA.Lock}
    (hl : l ∈ A.locks) (hB : B ∈ Φ.tree) (hroot : B.root = l.block)
    (ht : l.LiveAt sp t) (hcover : Φ.Anc R (Φ.viableAncestor B))
    (hchain : ∀ X ∈ SA.liveLockBlocks sp A.locks Φ t,
      ∀ Y ∈ SA.liveLockBlocks sp A.locks Φ t, Goldilocks.Compatible Φ.tree X Y) :
    Φ.Anc R (SA.getAnchor sp A Φ t) := by
  have hmem : Φ.viableAncestor B ∈ SA.liveLockBlocks sp A.locks Φ t :=
    ⟨(SA.viableAncestor_anc hΦ hB).1,
      ⟨⟨(Φ.viableAncestor B).root, l.slot, l.fast, l.expiry⟩, ⟨l, hl, B, hB, hroot, ht, rfl⟩,
        rfl⟩⟩
  exact hcover.trans ((SA.anc_getAnchor hΦ hchain).2 _ (Or.inl hmem))

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

end Consensus.Goldilocks.Obligations
end
