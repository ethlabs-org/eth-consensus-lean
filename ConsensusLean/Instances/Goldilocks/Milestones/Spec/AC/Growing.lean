module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace

@[expose] public section

/-! # AC traces under growing faults

`ACLocalRun` and `SyncAC` (`Spec/AC/Trace`) for a time-indexed honest set `H` (antitone:
compromise is permanent). Each law constrains the nodes honest at the time of the cut it reads; a
message stays owed after its sender is compromised, and a recipient is served while honest. At
`H := fun _ => H₀` they are `ACLocalRun A H₀ U tr` and `SyncAC A H₀ U a b tr`
(`Lemmas/Growing/Run/Const`). -/

namespace Consensus.Goldilocks

variable {P : Params} {FGP : Type}

namespace Growing

/-- **The AC trace contract under growing faults** (claims C0.5 (a), (b)): the laws of
`ACLocalRun`, each for the nodes honest at the time of the cut (or the time) it constrains. -/
structure ACLocalRun (A : ACInterface P FGP) (H : Time → Set (Fin P.n)) (U : Set A.Blk)
    (tr : ACTrace A) (ini : Fin P.n → A.State := fun _ => A.initial) : Prop where
  /-- Compromise is permanent. -/
  antitone : Antitone H
  /-- `U` is coherent: roots injective, slots increasing along parent edges. -/
  coherent : Coherent U
  /-- Each node `y` honest at time `0` starts from its given AC state `ini y` (by default
  `A.initial`). -/
  init : ∀ y ∈ H 0, tr.init y = ini y
  /-- Each call of a node honest at its time executes the AC on the pre-state, the label's frame
  and the cut's time. -/
  exec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H (tr.time i) →
    A.step (tr.node i) (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call = (tr.post i, ℓ.emits)
  /-- The frame law and the input contract, for a node honest at the call. -/
  frameLaw : ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ →
    (tr.NoCallBetween y 0 i ∧ ∃ Φ₀, A.InitialFrame Φ₀ ∧ A.FrameIn U Φ₀ ∧
      A.CallOK U Φ₀ (tr.time i) ℓ.call ℓ.frame) ∨
    (∃ j ℓ', j < i ∧ tr.CallAt y j ℓ' ∧ tr.NoCallBetween y (j + 1) i ∧
      A.CallOK U ℓ'.frame (tr.time i) ℓ.call ℓ.frame)
  /-- Cuts are at times from `0` on. -/
  time_nonneg : ∀ i, 0 ≤ tr.time i
  /-- The cut order is by time. -/
  time_mono : Monotone tr.time
  /-- A node honest at its call is called only while awake. -/
  awake_of_call : ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ → tr.awake y (tr.time i)
  /-- The first call of a node after it was asleep is a restart (honest at the call). -/
  restart_of_sleep : ∀ y i ℓ (u : Time), y ∈ H (tr.time i) → tr.CallAt y i ℓ → 0 ≤ u →
    u < tr.time i → ¬ tr.awake y u → (∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u) →
    ℓ.call = .restart
  /-- A wake is a restart, for a node honest at the wake. -/
  restart_at_wake : ∀ y (u v : Time), y ∈ H v → 0 ≤ u → u < v → ¬ tr.awake y u →
    tr.awake y v → ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  /-- A restart is a wake (honest at the restart). -/
  sleep_of_restart : ∀ y i ℓ, y ∈ H (tr.time i) → tr.CallAt y i ℓ → ℓ.call = .restart →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧
      ∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u

end Growing

/-- **`Sync[a, b]` over an AC trace under growing faults**: a message that a node honest at the
time sends or admits at `τ ∈ [a, b]` is processed by every node honest at the reading call, within
its deadline; a block that a node honest at the time accepts at `τ ∈ [a, b]` is accepted within
its deadline by every node honest at the reading call whose finalized tip it extends inside
`U`. -/
def SyncACAt (A : ACInterface P FGP) (H : Time → Set (Fin P.n)) (U : Set A.Blk) (a b : Time)
    (tr : ACTrace A) : Prop :=
  (∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmit x i m → a ≤ tr.time i → tr.time i ≤ b →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (tr.time i)) ∧
  (∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → a ≤ tr.time i → tr.time i ≤ b →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      Anc U ℓ.frame.F B →
      ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i))

end Consensus.Goldilocks

end
