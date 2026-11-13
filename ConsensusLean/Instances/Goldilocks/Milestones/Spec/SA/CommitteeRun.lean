module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Committee

@[expose] public section

/-! # Goldilocks SA: a slot committee over an SA trace

The committee facts the committee-native AC step statements take, for a slot dictionary
`K : CommitteeDict sp.n` of an AC trace with honest set `H`:

* **P** (`CommitteeP`): the votes in the pools of honest nodes, and in the states at which an honest
  node runs the optimistic check, are signed by members of their slot's committee.
* **T** (`CommitteeT`): the votes in the merged vote view of an honest vote are signed by members
  of their slot's committee.
* **CS** (`FaultBoundK`): among the members of the slot-`s` committee, fewer are faulty than are
  honest, awake and joined at `t`.

Under growing faults (a time-indexed honest set `H`), `CommitteePAt` and `CommitteeTAt` read P and
T for the nodes honest at each time `t`, at the cuts through `t`: on the prefix of the run through
`t`, with honest set `H t`, they are P and T.

Thresholds stay in `sp.committeeSize`; a caller binds `K` to it by `(K.committee s).ncard =
sp.committeeSize`. At `K = CommitteeDict.full sp.n` with `sp.committeeSize = sp.n`, P and T hold
for every signer and CS is `FaultBound tr H t`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- **P**: honest pools and optimistic-check states hold only signatures of the slot's
committee. -/
def CommitteeP (K : CommitteeDict sp.n) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop :=
  (∀ y ∈ H, ∀ (i s : Nat), ∀ v ∈ (tr.state y i).pool s, v.val ∈ K.committee s) ∧
  (∀ y ∈ H, ∀ i ℓ A, OptimisticPoint tr y i ℓ A → ∀ s : Nat, ∀ v ∈ A.pool s,
    v.val ∈ K.committee s)

/-- **T**: the merged-view votes of an honest vote, block payload votes included, are signed by
members of their slot's committee. -/
def CommitteeT (K : CommitteeDict sp.n) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ i ℓ e, CastAt tr y i ℓ e → ∀ m : Nat,
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes, v.val ∈ K.committee v.slot

/-- **CS** at the slot-`s` committee, with the faults charged at `t`. -/
def FaultBoundK (K : CommitteeDict sp.n) (s : Nat) (tr : SATrace sp FGP ro)
    (H : Set (Fin sp.n)) (t : Time) : Prop :=
  (K.committee s ∩ Hᶜ).ncard <
    (K.committee s ∩ {y | y ∈ H ∧ tr.awake y t ∧ JoinedAt tr y t}).ncard

/-- **P under growing faults**: a node honest at `t` holds only committee signatures in its pools
before every cut whose earlier cuts are at times `≤ t`, and at every optimistic check of a cut at
which it is honest. -/
def CommitteePAt (K : CommitteeDict sp.n) (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) :
    Prop :=
  (∀ t, ∀ y ∈ H t, ∀ i, (∀ k < i, tr.time k ≤ t) → ∀ s : Nat, ∀ v ∈ (tr.state y i).pool s,
    v.val ∈ K.committee s) ∧
  (∀ y i ℓ A, y ∈ H (tr.time i) → OptimisticPoint tr y i ℓ A → ∀ s : Nat, ∀ v ∈ A.pool s,
    v.val ∈ K.committee s)

/-- **T under growing faults**: the merged-view votes of a vote of a node honest at its cut are
signed by members of their slot's committee. -/
def CommitteeTAt (K : CommitteeDict sp.n) (tr : SATrace sp FGP ro) (H : Time → Set (Fin sp.n)) :
    Prop :=
  ∀ y i ℓ e, y ∈ H (tr.time i) → CastAt tr y i ℓ e → ∀ m : Nat,
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes, v.val ∈ K.committee v.slot

end Consensus.Goldilocks.SA

end
