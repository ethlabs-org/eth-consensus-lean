module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Premises
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model

@[expose] public section

/-! # Goldilocks runs under growing faults: the premises

The premises of `Spec/Run/Premises` for a time-indexed honest set `H`:

* **`SyncOnAt`**: `SyncOn` with the sender honest at its send or admission and the recipient
  honest at the call that reads the deadline. A release stays owed after its sender is
  compromised; a recipient is served while honest. The acceptance relay reads extension inside
  `HonestBlocksAt`. `SyncRunAt` and `GSTRunAt` are `Sync[a, b]` and `GST(g)`.
* **`FaultBoundAt t d`**: `f_d < h_t` charged at the consumption horizon `d`: the validators
  compromised by `d` are fewer than those honest at `d`, awake and joined at `t`. A later `d` is a
  stronger premise. At `d = t` it is the count at its own time.
* **`SleepyRunAt W`**: `Sync[0, ∞)` and, at every slot point `t ∈ {t_s, t_s + Δ, t_s + 2Δ}`,
  `FaultBoundAt t (t + W)`: the look-ahead form of the L0 sleepy budget (`EnvPoint.SleepyOn` on the
  view retained through `t + W`). The Goldilocks contract's look-ahead is `ahead = 5`, `W = 5Δ` at
  `Δp = Δe`. `SleepyPrefixAt W b` is the prefix form through `b`, the look-ahead clamped at `b`.
* **`HealthyRunAt`**: `GST(g)`, every validator honest at a time from `max g 0` on is awake then,
  and `3 f_t ≤ n − 1` at every `t` (by monotonicity, the bound at the latest time).

At `H := fun _ => H₀` each is the premise of `Spec/Run/Premises` with `H₀`, for every look-ahead
(`Lemmas/Growing/Run/Const`). -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- `f_d < h_t`: the validators compromised by `d` are fewer than the validators honest at `d`,
awake and joined at `t`. -/
def FaultBoundAt (H : Time → Set (Fin P.n)) (t d : Time) : Prop :=
  (H d)ᶜ.ncard < {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard

/-- **`Sync` over a run under growing faults**, for the sends in the window `W` with effective
send time `eff`: senders honest at the send, recipients honest at the reading call. -/
structure SyncOnAt (H : Time → Set (Fin P.n)) (ΔF : Time) (W Wr : Time → Prop)
    (eff : Time → Time) : Prop where
  /-- The attestation delay `Δ_F` is positive. -/
  deltaF : 0 < ΔF
  /-- The attestation delay is at least the delay of blocks and messages. -/
  delta_le : P.Δ ≤ ΔF
  /-- Every AC message that a node honest at the time sends or admits in the window is processed
  before its deadline by every node honest at the reading call. -/
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m → W (tr.time i) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (eff (tr.time i)) m
  /-- Every block that a node honest at the time sends (its own proposal) or accepts in the window
  is processed before its deadline by every node honest at the reading call. -/
  block : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    W (tr.time i) → ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (eff (tr.time i)) B
  /-- Acceptance relay inside the blocks held while honest. -/
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → Wr (tr.time i) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (eff (tr.time i)) B
  /-- Every attestation that a node honest at the time signs or admits in the window is processed
  before its deadline with `Δ_F` by every node honest at the reading call. -/
  attestation : ∀ x i a, x ∈ H (tr.time i) → tr.SendOrAdmitAttAt x i a → W (tr.time i) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (eff (tr.time i)) ΔF ≤ tr.time j →
      tr.AttDeliveredBy y j (eff (tr.time i)) ΔF a

/-- **`Sync[a, b]`** under growing faults. -/
def SyncRunAt (H : Time → Set (Fin P.n)) (ΔF a b : Time) : Prop :=
  tr.SyncOnAt H ΔF (fun τ => a ≤ τ ∧ τ ≤ b) (fun τ => a ≤ τ ∧ τ ≤ b) id

/-- **`GST(g)`** under growing faults. -/
def GSTRunAt (H : Time → Set (Fin P.n)) (ΔF g : Time) : Prop :=
  tr.SyncOnAt H ΔF (fun _ => True) (fun τ => g ≤ τ) (fun τ => max τ g)

/-- **`Sleepy` with look-ahead `W`**: `Sync[0, ∞)` and the count at every slot point charged with
the faults of `W` later. -/
def SleepyRunAt (H : Time → Set (Fin P.n)) (ΔF W : Time) : Prop :=
  tr.SyncOnAt H ΔF (fun τ => 0 ≤ τ) (fun τ => 0 ≤ τ) id ∧
    ∀ s : Nat, ∀ d ∈ ({0, P.Δ, 2 * P.Δ} : Set Time),
      tr.FaultBoundAt H (P.slotTime s + d) (P.slotTime s + d + W)

/-- **The sleepy premises up to `b`** with look-ahead `W` clamped at `b`: `Sync[0, b − Δ]` and the
count at every slot point `≤ b` charged with the faults of `min (t + W) b`. -/
def SleepyPrefixAt (H : Time → Set (Fin P.n)) (ΔF W b : Time) : Prop :=
  0 ≤ b ∧ tr.SyncRunAt H ΔF 0 (b - P.Δ) ∧
    ∀ s : Nat, ∀ d ∈ ({0, P.Δ, 2 * P.Δ} : Set Time), P.slotTime s + d ≤ b →
      tr.FaultBoundAt H (P.slotTime s + d) (min (P.slotTime s + d + W) b)

/-- **`Healthy(g)`** under growing faults: `GST(g)`, every validator honest at a time from
`max g 0` on is awake then, and `3 f_t ≤ n − 1` at every time. -/
def HealthyRunAt (H : Time → Set (Fin P.n)) (ΔF g : Time) : Prop :=
  tr.GSTRunAt H ΔF g ∧ (∀ y t, max g 0 ≤ t → y ∈ H t → tr.awake y t) ∧
    ∀ t, 3 * (H t)ᶜ.ncard ≤ P.n - 1

end Consensus.Goldilocks.RunTrace

end
