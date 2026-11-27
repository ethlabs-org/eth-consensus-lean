module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

@[expose] public section

/-! # Generic available-chain healing obligations

Growing, event-honest contracts for an available chain plugged into the population FG.
The fields are obligations, not supplied evidence. No amended field has an inherited proof.
-/

namespace Consensus.Goldilocks.Generic

open AC (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ IsReset CatchRun NoRestartAfter)

variable {P : Params} {A : NodeAC P}

/-- A report returned by the available chain at its actual node call. -/
def ReportAt (tr : RunTrace A) (y : Fin P.n) (i : Nat) (R : A.Blk) : Prop :=
  ∃ ℓ : ACLabel A, tr.CallAt y i (.ac ℓ) ∧ ℓ.call = .toFG ∧
    (A.toFG (tr.state y i).ac ℓ.frame (tr.time i)).2 = some R

/-- The actual proposal call returning a duty head and payload. -/
def ProposalHeadAt (tr : RunTrace A) (y : Fin P.n) (i : Nat)
    (d : DutyHead P.n (List (FG.Att P.n)) A.Payload) : Prop :=
  ∃ (ℓ : ACLabel A) (pay : A.Payload), tr.CallAt y i (.ac ℓ) ∧ ℓ.call = .proposal ∧
    (A.proposal (tr.state y i).ac ℓ.frame (tr.time i)).2 = some (d, pay)

/-- Constant maximum height, top status and conditional J on a real-time window. -/
structure FrameWindow (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (lo hi : Time) (M : Nat) (isTop : Prop) (J : A.Blk) : Prop where
  M_eq : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
    (tr.state y i).fg.hmax = M
  top_iff : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
    ((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ↔ isTop)
  root_eq : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi → isTop →
    (tr.state y i).fg.J = J

/-- A slot window includes the last slot's report deadline. -/
abbrev SlotWindow (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (s₀ N M : Nat) (isTop : Prop) (J : A.Blk) : Prop :=
  FrameWindow tr H (P.slotTime s₀) (P.slotTime N + 2 * P.Δ) M isTop J

/-- No signing strictly before T by a signer honest at it and at `c_z` exceeds the snapshot
height. -/
def NoAdvance (tr : RunTrace A) (H : Time → Set (Fin P.n)) (g T : Time) : Prop :=
  ∀ v k att, v ∈ H (max (cutZ P g) (tr.time k)) → tr.SignAt v k att → tr.time k < T →
    att.h ≤ HZ tr H g

/-- Every G-slot interval contains an actual designated honest proposal. -/
def ProposalGap (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (proposer : Nat → Fin P.n) (G s₀ N : Nat) : Prop :=
  ∀ a, s₀ ≤ a → a + G ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + G ∧
    proposer x ∈ H (P.slotTime x + P.Δ) ∧ ∃ k Q, tr.ProposesAt (proposer x) k Q ∧ Q.slot = x

/-- Population message, block, relay and signed-row service. With a release hold `hold > 0`
(own signed attestations published up to `hold` after the effective signing time), a signing is
served only when its signer is still honest at `max (time i) g + hold`, in the form of
`SyncOnAt.attestation`, and the hold is within `ΔF`; at `hold = 0` both are implied. -/
structure Service (tr : RunTrace A) (H : Time → Set (Fin P.n)) (g ΔF b : Time)
    (hold : Time := 0) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) P.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j →
      tr.deadline y j (max (tr.time i) g) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B
  signedRow : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
    (∀ k ≤ i, tr.SignAt x k att → tr.time k = tr.time i → hold ≠ 0 →
      x ∈ H (max (tr.time i) g + hold)) →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
      ∃ k ≤ j, tr.ProcessAttAt y k att ∧ tr.time k < tr.deadline y k (max (tr.time i) g) ΔF
  /-- The release hold is within the attestation delay (at `hold = 0`, `deltaF`). -/
  hold_le : hold ≤ ΔF

/-- Nonempty committees selected from GST onward obey the contract fraction at
every charge time up to the horizon. No pre-GST selection count is assumed. -/
def CommitteeFaultsUpTo (βK : ℚ) (cm : Time → Finset (Fin P.n))
    (H : Time → Set (Fin P.n)) (g b : Time) : Prop :=
  ∀ t d, max g 0 ≤ t → t ≤ b → 0 ≤ d → d ≤ b →
    (cm t).Nonempty →
      (((↑(cm t) : Set (Fin P.n)) ∩ (H d)ᶜ).ncard : ℚ) < βK * (cm t).card

/-- Strong bundled premises for corollary forms, never a replacement for old-premise leaves; the
service at release hold `hold` (default `0`). -/
structure Premises (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (cm : Time → Finset (Fin P.n)) (βK : ℚ)
    (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (sg : A.Msg → Fin P.n) (g ΔF b : Time) (hold : Time := 0) : Prop where
  committee : CommitteeFaultsUpTo βK cm H g b
  noColl : Compose.NoCollRun dg tr
  sync : Service tr H g ΔF b hold
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1
  catchUp : CatchRun tr H g (2 * P.Δ)
  noRestart : NoRestartAfter tr H (gbar g)
  timeoutDelay : ∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)
  slotLen : ∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)
  snapshot : ∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b
  nonempty : (H b).Nonempty

/-- A designated proposal honest through its vote deadline. -/
structure HonestProposal (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (proposer : Nat → Fin P.n) (u : Nat) (z : Fin P.n) (k : Nat) (X : A.Blk) : Prop where
  honest : z ∈ H (P.slotTime u + P.Δ)
  designated : z = proposer u
  proposes : tr.ProposesAt z k X
  slot : X.slot = u

/-- Proposal chaining only; no confirmed-tip or finality guarantee is included. -/
def HealedFrom (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (proposer : Nat → Fin P.n) (s₁ : Nat) (b : Time) : Prop :=
  ∀ s s' z z' k k' X X', s₁ ≤ s → s < s' → P.slotTime s' + 6 * P.Δ ≤ b →
    HonestProposal tr H proposer s z k X → HonestProposal tr H proposer s' z' k' X' →
    Anc (tr.HonestBlocksAt H) X X'

/-- Honesty truncated after a finite horizon. -/
def truncH (H : Time → Set (Fin P.n)) (b : Time) : Time → Set (Fin P.n) :=
  fun t => {y | y ∈ H t ∧ t ≤ b}

/-- The AC's run predicate and committee start, shared by the assembly obligations. -/
structure ACRun (A : NodeAC P) (sg : A.Msg → Fin P.n) where
  Run : (Time → Finset (Fin P.n)) → (Nat → Fin P.n) →
    Digest (List (FG.Att P.n)) A.Payload → (Time → Set (Fin P.n)) → RunTrace A → Prop
  start : (Time → Finset (Fin P.n)) → Fin P.n → A.State
  run_local : ∀ {cm proposer dg H tr}, Run cm proposer dg H tr →
    Growing.LocalRun proposer dg H sg tr (start cm)
  /-- Requirements hold at every node's actual committee start. -/
  run_requirements : ∀ {cm proposer dg H tr}, Run cm proposer dg H tr →
    ∀ y, ({ A with initial := start cm y } : NodeAC P).Requirements
  /-- The run supplies the genesis digest equation independently of a finite horizon. -/
  run_root : ∀ {cm proposer dg H tr}, Run cm proposer dg H tr →
    (P.genesisBlock A.genesisPayload).RootOk dg
  /-- Removing honesty strictly after a horizon preserves the same run and committee start. -/
  run_truncH : ∀ {cm proposer dg H tr}, Run cm proposer dg H tr →
    ∀ b, Run cm proposer dg (truncH H b) tr

/-- Canonical high entries, with historical honesty read at independently bounded cuts. -/
structure HighCanonical
    (Origin : RunTrace A → Fin P.n → Nat → Nat → A.Blk → Prop)
    (tr : RunTrace A) (H : Time → Set (Fin P.n)) (g b : Time) : Prop where
  no_high_contest : ∀ p i, p ∈ H (tr.time i) → tr.time i ≤ b →
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)
  row_origin : ∀ y k att, y ∈ H (max (cutZ P g) (tr.time k)) →
    tr.SignAt y k att → tr.time k ≤ b →
    HZ tr H g + 1 ≤ att.h →
    ∃ r < k, ∃ j B, Origin tr y r j B ∧ y ∈ H (max (cutZ P g) (tr.time r)) ∧
      HZ tr H g + 1 ≤ ((tr.state y r).fg.σ B.root).h ∧
      ∃ E ∈ (tr.state y r).fg.tree, (tr.state y r).fg.Anc E B ∧ E.root = att.T ∧
        ((tr.state y r).fg.σ E.root).h = att.h ∧ ((tr.state y r).fg.σ E.root).Th = E.root
  entry_eq : ∀ x x' i j i' j' B B' y₁ y₂ m₁ m₂ Z₁ Z₂ t₁ t₂,
    x ∈ H (max (cutZ P g) (tr.time i)) → Origin tr x i j B → tr.time i ≤ b →
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h →
    x' ∈ H (max (cutZ P g) (tr.time i')) → Origin tr x' i' j' B' → tr.time i' ≤ b →
    HZ tr H g + 1 ≤ ((tr.state x' i').fg.σ B'.root).h →
    Anc (tr.HonestBlocksAt H) Z₁ B → Anc (tr.HonestBlocksAt H) Z₂ B' →
    0 ≤ t₁ → (∀ q < m₁, tr.time q ≤ t₁) → y₁ ∈ H t₁ →
    0 ≤ t₂ → (∀ q < m₂, tr.time q ≤ t₂) → y₂ ∈ H t₂ →
    Z₁ ∈ (tr.state y₁ m₁).fg.tree → Z₂ ∈ (tr.state y₂ m₂).fg.tree →
    ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h →
    ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root →
    ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root → Z₁.root = Z₂.root

/-- Shift a time by `d` delays; definitionally `t` at `d = 0`. -/
def shiftDelay (P : Params) (d : Nat) (t : Time) : Time :=
  match d with
  | 0 => t
  | d' + 1 => t + ((d' + 1 : Nat) : Time) * P.Δ

/-- A constant frame through the delayed report deadline. -/
abbrev SlotWindowWithin (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (d s₀ N M : Nat) (isTop : Prop) (J : A.Blk) : Prop :=
  FrameWindow tr H (P.slotTime s₀) (shiftDelay P d (P.slotTime N + 2 * P.Δ)) M isTop J

/-- A reset within a deep budget: with budget `m`, the slot after the reset's drain is at most
`m` slots after `c_z`. Vacuous without a budget. -/
def ResetInBudget (P : Params) (budget : Option Nat) (drain : Nat) (g a : Time) : Prop :=
  ∀ m, budget = some m → P.slotOf a + drain + 1 ≤ P.slotOf (cutZ P g) + m

/-- A time within the origin cap: with budget `m`, at or before `m` slots after `c_z` (for
Goldilocks, the end `c_z + 4DΔ` of the deep quarantine). Vacuous without a budget. -/
def OriginInCap (P : Params) (budget : Option Nat) (g t : Time) : Prop :=
  ∀ m, budget = some m → t ≤ P.slotTime (P.slotOf (cutZ P g) + m)

/-- The horizon `b` capped at the origin cap; `b` itself without a budget. -/
def originCapTime (P : Params) (budget : Option Nat) (g b : Time) : Time :=
  match budget with
  | none => b
  | some m => min b (P.slotTime (P.slotOf (cutZ P g) + m))

/-- Protocol obligations for growing runs. New source and warmth laws require genuine suppliers.
The premises are read at release hold `hold` (default `0`). -/
structure ACHealing (A : NodeAC P) (sg : A.Msg → Fin P.n) (runs : ACRun A sg)
    (hold : Time := 0) where
  warmup : Nat
  follow : Nat
  reportDelay : Nat
  drain : Nat
  /-- Deep budget in slots after `c_z`: bounds admissible resets (`ResetInBudget`) and the times
  the origin fields speak about (`OriginInCap`); `none` bounds nothing. -/
  deepBudget : Option Nat := none
  Origin : RunTrace A → Fin P.n → Nat → Nat → A.Blk → Prop
  follow_le : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b : Time},
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold → follow ≤ P.δt
  report_in_frame : ∀ {cm proposer dg H tr} {y : Fin P.n} {i : Nat} {R : A.Blk},
    runs.Run cm proposer dg H tr → y ∈ H (tr.time i) → ReportAt tr y i R →
    R ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R
  /-- The proposal reaches the predecessor of the maximum height and exceeds justification. -/
  proposal_floor : ∀ {cm proposer dg H tr} {lo hi : Time} {M u : Nat} {isTop : Prop}
    {J B : A.Blk} {z : Fin P.n} {kB : Nat},
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr → FrameWindow tr H lo hi M isTop J →
    z ∈ H (P.slotTime u) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    lo ≤ P.slotTime u → P.slotTime u ≤ hi →
    (H (P.slotTime u))ᶜ.ncard < 2 * P.fg.q - P.n →
    (tr.state z kB).fg.hmax - 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h ∧
      (tr.state z kB).fg.hj < ((tr.state z (kB + 1)).fg.σ B.root).h
  /-- After warmup, an honest proposal is reported within one slot plus `2 + reportDelay` delays,
  and later honest proposal heads extend the report. Certificate: cert obligation open:
  honest committee members support an honest proposal after healing. -/
  report_follow : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b : Time}
    {s₀ N u M : Nat} {isTop : Prop} {J B : A.Blk} {z : Fin P.n} {kB : Nat},
    βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold →
    FrameWindow tr H (P.slotTime s₀)
      (shiftDelay P reportDelay (P.slotTime N + 2 * P.Δ)) M isTop J →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ + warmup ≤ u →
    u + 1 ≤ N → shiftDelay P reportDelay (P.slotTime N + 2 * P.Δ) ≤ b →
    HonestProposal tr H proposer u z kB B →
    ∀ y, y ∈ H (shiftDelay P reportDelay (P.slotTime (u + 1) + 2 * P.Δ)) →
      ∃ i R, y ∈ H (tr.time i) ∧ ReportAt tr y i R ∧ P.slotTime u ≤ tr.time i ∧
        tr.time i ≤ shiftDelay P reportDelay (P.slotTime (u + 1) + 2 * P.Δ) ∧
        Anc (tr.HonestBlocksAt H) B R ∧
        ∀ x, u + follow ≤ x → x ≤ N → ∀ w c d, w ∈ H (tr.time c) →
          ProposalHeadAt tr w c d → tr.time c = P.slotTime x → Anc (tr.HonestBlocksAt H) R d.head
  /-- A high honest report after a reset has an earlier origin extending it.
  Certificate: no open obligation recorded. -/
  report_origin : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time}
    {y : Fin P.n} {i : Nat} {R : A.Blk},
    βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold →
    IsReset tr H g a → a ≤ b → y ∈ H (tr.time i) → tr.time i ≤ b →
    OriginInCap P deepBudget g (tr.time i) → ReportAt tr y i R →
    HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h →
    ∃ r ≤ i, ∃ j B, y ∈ H (tr.time r) ∧ Origin tr y r j B ∧
      B ∈ (tr.state y r).fg.tree ∧ Anc (tr.HonestBlocksAt H) R B
  /-- High honest FG sources after a reset are compatible across all slots.
  Certificate: cert obligation open: same-slot FG-source safety plus C1.1 across slots,
  including the analogue excluding high sources before cutZ. -/
  origins_comparable : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time} {x x' : Fin P.n}
    {i j i' j' : Nat} {B B' : A.Blk},
    βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold →
    IsReset tr H g a → a ≤ b → OriginInCap P deepBudget g a →
    x ∈ H (max (cutZ P g) (tr.time i)) → Origin tr x i j B → tr.time i ≤ b →
    OriginInCap P deepBudget g (tr.time i) →
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h →
    x' ∈ H (max (cutZ P g) (tr.time i')) → Origin tr x' i' j' B' → tr.time i' ≤ b →
    OriginInCap P deepBudget g (tr.time i') →
    HZ tr H g + 1 ≤ ((tr.state x' i').fg.σ B'.root).h →
    Compatible (tr.HonestBlocksAt H) B B'
  /-- Canonical high sources yield chained honest proposals after the AC's drain bound.
  Certificate: cert obligation open: the certificate healing bound. -/
  heal_after_reset : ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time},
    βK ≤ 1 / 2 →
    runs.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b hold →
    IsReset tr H g a → a ≤ b → ResetInBudget P deepBudget drain g a →
    HighCanonical Origin tr H g (originCapTime P deepBudget g b) →
    HealedFrom tr H proposer (P.slotOf a + drain) b

end Consensus.Goldilocks.Generic

end
