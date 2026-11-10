module
public import Mathlib.Data.Set.Card
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View

@[expose] public section

/-! # Local observed-row provenance and high roots

Conditional contracts only: the observation and source laws are instance inputs, while
strictly earlier root comparisons remain explicit. No reset or origin induction is asserted.
The historical universe includes stores at their own honest events, not a terminal cohort.
-/

namespace Consensus.Goldilocks.LocalSources

variable {P : Params} {ACP : Type}

/-- A row surviving in an honest observer's tree was signed strictly earlier by a signer
still honest at observation, with the same entry height in the signing store. -/
def Observations (st : Fin P.n → Nat → Store P ACP) (time : Nat → Time)
    (H : Time → Set (Fin P.n)) (Sign : Fin P.n → Nat → FG.Att P.n → Prop)
    (Hz : Nat) (b : Time) : Prop :=
  ∀ y k, y ∈ H (time k) → time k ≤ b →
    ∀ E ∈ (st y k).tree, Hz + 1 ≤ ((st y k).σ E.root).h →
    ((st y k).σ E.root).Th = E.root →
    ∀ W ∈ (st y k).tree, ∀ att ∈ W.fgPayload,
    att.T = E.root → att.val ∈ H (time k) →
    ∃ d < k, Sign att.val d att ∧ att.val ∈ H (time d) ∧
      ∃ Es ∈ (st att.val d).tree, Es.root = att.T ∧
        ((st att.val d).σ Es.root).h = att.h ∧
        ((st att.val d).σ Es.root).h = ((st y k).σ E.root).h

/-- A high signed entry comes from an actual strictly prior source event of the signer.
The event relation is supplied by the instance; no root comparison is part of this law. -/
def Sources (st : Fin P.n → Nat → Store P ACP) (time : Nat → Time)
    (H : Time → Set (Fin P.n)) (Sign : Fin P.n → Nat → FG.Att P.n → Prop)
    (Origin : Fin P.n → Nat → Nat → NodeBlock P ACP → Prop)
    (Joined : Fin P.n → Time → Prop) (U : Set (NodeBlock P ACP))
    (Hz : Nat) (b : Time) : Prop :=
  ∀ v d att, v ∈ H (time d) → time d ≤ b → Sign v d att → Hz + 1 ≤ att.h →
    ∃ r < d, ∃ l O, Origin v r l O ∧
      v ∈ H (time r) ∧ Joined v (time r) ∧ time r ≤ b ∧
      O ∈ (st v r).tree ∧ Hz + 1 ≤ ((st v r).σ O.root).h ∧
      ∃ E0 ∈ (st v r).tree, Anc U E0 O ∧ E0.root = att.T ∧
        ((st v r).σ E0.root).h = att.h ∧ ((st v r).σ E0.root).Th = E0.root

/-- Composition to be proved: observation and source laws retain the actual sign event,
the earlier source event, and its entry identities in the own-event historical universe. -/
def ObservedHighRowSourceBefore (st : Fin P.n → Nat → Store P ACP) (time : Nat → Time)
    (H : Time → Set (Fin P.n)) (Sign : Fin P.n → Nat → FG.Att P.n → Prop)
    (Origin : Fin P.n → Nat → Nat → NodeBlock P ACP → Prop)
    (Joined : Fin P.n → Time → Prop) (U : Set (NodeBlock P ACP))
    (Hz : Nat) (b : Time) : Prop :=
  Monotone time →
  (∀ v i, v ∈ H (time i) → time i ≤ b → (st v i).tree ⊆ U) →
  Observations st time H Sign Hz b → Sources st time H Sign Origin Joined U Hz b →
  ∀ y k E W att, y ∈ H (time k) → time k ≤ b →
    E ∈ (st y k).tree → Hz + 1 ≤ ((st y k).σ E.root).h →
    ((st y k).σ E.root).Th = E.root → W ∈ (st y k).tree →
    att ∈ W.fgPayload → att.T = E.root → att.val ∈ H (time k) →
    ∃ d < k, Sign att.val d att ∧ att.val ∈ H (time d) ∧
      ∃ r < d, ∃ l O, Origin att.val r l O ∧ r < k ∧
        att.val ∈ H (time r) ∧ Joined att.val (time r) ∧ time r ≤ b ∧
        O ∈ (st att.val r).tree ∧ Hz + 1 ≤ ((st att.val r).σ O.root).h ∧
        ∃ E0 ∈ (st att.val r).tree, Anc U E0 O ∧ E0.root = E.root ∧
          ((st att.val r).σ E0.root).h = att.h ∧
          ((st att.val r).σ E0.root).Th = E0.root

/-- High-root contract to be proved using the existing `Healing.Store.J_compatible_of_rows`.
Reachability, genesis ancestry, the current quorum bound and every strictly prior comparison
are explicit inputs. The numerical threshold is not a reset theorem. -/
def HighRootsBefore (acp₀ : ACP) (st : Fin P.n → Nat → Store P ACP) (time : Nat → Time)
    (H : Time → Set (Fin P.n)) (Sign : Fin P.n → Nat → FG.Att P.n → Prop)
    (Origin : Fin P.n → Nat → Nat → NodeBlock P ACP → Prop)
    (Joined : Fin P.n → Time → Prop) (U : Set (NodeBlock P ACP))
    (Hz : Nat) (b : Time) : Prop :=
  Coherent U → Monotone time →
  (∀ v i, v ∈ H (time i) → time i ≤ b → (st v i).tree ⊆ U) →
  Observations st time H Sign Hz b → Sources st time H Sign Origin Joined U Hz b →
  ∀ y k B, y ∈ H (time k) → time k ≤ b → (st y k).Reachable acp₀ →
    Anc U (P.genesisBlock acp₀) B → (H (time k))ᶜ.ncard < P.fg.q →
    Hz + 1 ≤ (st y k).hj →
    (∀ v r l O, r < k → time r ≤ b → Origin v r l O → Compatible U B O) →
    Compatible U (st y k).J B ∧ Compatible U (st y k).F B ∧
      Compatible U (st y k).fcRoot B

/-- Call-facing contract: the instance must supply the actual frame equality, not merely
an arbitrary frame with a compatible root. No call or engine semantics is assumed here. -/
def HighFrameRootBefore (acp₀ : ACP) (st : Fin P.n → Nat → Store P ACP) (time : Nat → Time)
    (H : Time → Set (Fin P.n)) (Sign : Fin P.n → Nat → FG.Att P.n → Prop)
    (Origin : Fin P.n → Nat → Nat → NodeBlock P ACP → Prop)
    (Joined : Fin P.n → Time → Prop) (U : Set (NodeBlock P ACP))
    (Hz : Nat) (b : Time) : Prop :=
  Coherent U → Monotone time →
  (∀ v i, v ∈ H (time i) → time i ≤ b → (st v i).tree ⊆ U) →
  Observations st time H Sign Hz b → Sources st time H Sign Origin Joined U Hz b →
  ∀ y k B (frame : Frame P.n (List (FG.Att P.n)) ACP),
    y ∈ H (time k) → time k ≤ b → (st y k).Reachable acp₀ →
    Anc U (P.genesisBlock acp₀) B → (H (time k))ᶜ.ncard < P.fg.q →
    Hz + 1 ≤ (st y k).hj →
    (∀ v r l O, r < k → time r ≤ b → Origin v r l O → Compatible U B O) →
    frame = (st y k).toFrame → Compatible U frame.fcRoot B

end Consensus.Goldilocks.LocalSources

end
