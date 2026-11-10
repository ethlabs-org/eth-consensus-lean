module
public import Mathlib.Data.Set.Card
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model

@[expose] public section

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- `y` is joined at `t`: every restart of `y` at or before `t` is at or before
`t_{slot(t) − 1}` (none when `t` is in slot `0`). -/
def JoinedAt (y : Fin P.n) (t : Time) : Prop :=
  ∀ k, tr.RestartAt y k → tr.time k ≤ t →
    0 < P.slotOf t ∧ tr.time k ≤ P.slotTime (P.slotOf t - 1)

/-- `h_t`: the number of honest validators awake and joined at `t`. -/
noncomputable def honestAwakeJoined (H : Set (Fin P.n)) (t : Time) : Nat :=
  {y | y ∈ H ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard

/-- `f < h_t`, with `f` the number of faulty (non-honest) validators. -/
def FaultBound (H : Set (Fin P.n)) (t : Time) : Prop := Hᶜ.ncard < tr.honestAwakeJoined H t

/-- `y` has processed the AC message `m` by cut `j` within the deadline of an object of
effective time `τ`: at a cut `k ≤ j`, not before the object's time `τ₀`, before `y`'s deadline
as of `k`. -/
def MsgDeliveredBy (y : Fin P.n) (j : Nat) (τ₀ τ : Time) (m : A.Msg) : Prop :=
  ∃ k ≤ j, τ₀ ≤ tr.time k ∧ tr.ProcessMsgAt y k m ∧ tr.time k < tr.deadline y k τ P.Δ

/-- `y` has processed the block `B` by cut `j` within the deadline (as `MsgDeliveredBy`). -/
def BlockDeliveredBy (y : Fin P.n) (j : Nat) (τ₀ τ : Time) (B : A.Blk) : Prop :=
  ∃ k ≤ j, τ₀ ≤ tr.time k ∧ tr.BlockCallAt y k B ∧ tr.time k < tr.deadline y k τ P.Δ

/-- `y` has accepted the block `B` by cut `j` within the deadline. -/
def BlockAcceptedBy (y : Fin P.n) (j : Nat) (τ : Time) (B : A.Blk) : Prop :=
  ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k τ P.Δ

/-- `y` has processed the attestation `a` by cut `j` within the deadline with `Δ_F`, at a cut
before its own deadline; an earlier processing counts (no lower bound, unlike blocks and
messages). -/
def AttDeliveredBy (y : Fin P.n) (j : Nat) (τ ΔF : Time) (a : FG.Att P.n) : Prop :=
  ∃ k ≤ j, tr.ProcessAttAt y k a ∧ tr.time k < tr.deadline y k τ ΔF

/-- **`Sync` over a run**, for the sends in the window `W` with effective send time `eff`
(claims §"Premises", `Sync[a, b]` and `GST(g)`). -/
structure SyncOn (H : Set (Fin P.n)) (ΔF : Time) (W Wr : Time → Prop) (eff : Time → Time) :
    Prop where
  /-- The attestation delay `Δ_F` is positive. -/
  deltaF : 0 < ΔF
  /-- The attestation delay is at least the delay of blocks and messages (claims
  §"Parameters"): an attestation admitted from a block is forwarded with the block. -/
  delta_le : P.Δ ≤ ΔF
  /-- Every AC message an honest node sends or admits in the window is processed by every honest
  node before its deadline. -/
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmitAt x i m → W (tr.time i) →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (eff (tr.time i)) m
  /-- Every block an honest node sends (its own proposal) or accepts in the window is processed
  by every honest node before its deadline. -/
  block : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B → W (tr.time i) →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (eff (tr.time i)) B
  /-- Acceptance relay: every block an honest node accepts in the relay window `Wr` is accepted
  before its deadline by every honest node whose `Σ.F` it extends (inside the honest blocks of the
  run, as `SyncAC` inside `U`). -/
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → Wr (tr.time i) →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (eff (tr.time i)) B
  /-- Every attestation an honest node signs or admits in the window is processed by every honest
  node before its deadline with `Δ_F`, possibly before the signing or admission. -/
  attestation : ∀ x ∈ H, ∀ i a, tr.SendOrAdmitAttAt x i a → W (tr.time i) →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (eff (tr.time i)) ΔF ≤ tr.time j →
      tr.AttDeliveredBy y j (eff (tr.time i)) ΔF a

/-- **`Sync[a, b]`**: the sends at `τ ∈ [a, b]`, at their own time. -/
def SyncRun (H : Set (Fin P.n)) (ΔF a b : Time) : Prop :=
  tr.SyncOn H ΔF (fun τ => a ≤ τ ∧ τ ≤ b) (fun τ => a ≤ τ ∧ τ ≤ b) id

/-- **`GST(g)`**: `Sync[g, ∞)`, and an object sent before `g` is processed as if sent at `g`:
its deadline is `max(g, w_y) + Δ'`; it may still be delivered before `g`. The acceptance relay
covers only acceptances at `τ ≥ g` (pre-`g` acceptance catch-up is `Catch(κ)`). -/
def GSTRun (H : Set (Fin P.n)) (ΔF g : Time) : Prop :=
  tr.SyncOn H ΔF (fun _ => True) (fun τ => g ≤ τ) (fun τ => max τ g)

/-- **`Sleepy`**: `Sync[0, ∞)` and `f < h_t` at every `t ∈ {t_s, t_s + Δ, t_s + 2Δ}`. -/
def SleepyRun (H : Set (Fin P.n)) (ΔF : Time) : Prop :=
  tr.SyncOn H ΔF (fun τ => 0 ≤ τ) (fun τ => 0 ≤ τ) id ∧
    ∀ s : Nat, tr.FaultBound H (P.slotTime s) ∧ tr.FaultBound H (P.slotTime s + P.Δ) ∧
      tr.FaultBound H (P.slotTime s + 2 * P.Δ)

/-- **`Healthy(g)`**: `GST(g)`, every honest validator awake on `[max(g, 0), ∞)`, and
`f ≤ ⌊(n − 1)/3⌋`. With `awake_in_horizon`, a `Healthy` run is infinite (intended). -/
def HealthyRun (H : Set (Fin P.n)) (ΔF g : Time) : Prop :=
  tr.GSTRun H ΔF g ∧ (∀ y ∈ H, ∀ t, max g 0 ≤ t → tr.awake y t) ∧ 3 * Hᶜ.ncard ≤ P.n - 1

end Consensus.Goldilocks.RunTrace

end
