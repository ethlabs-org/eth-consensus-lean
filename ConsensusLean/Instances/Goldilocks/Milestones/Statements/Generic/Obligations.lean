module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

@[expose] public section

/-! # Generic available-chain healing obligations

Growing, event-honest contracts for an available chain plugged into the population FG.
The fields are obligations, not supplied evidence. No amended field has an inherited proof.
-/

namespace Consensus.Goldilocks.Generic

open SA (gbar)
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

/-- Constant floor, root kind and conditional J on a real-time window. -/
structure FrameWindow (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (lo hi : Time) (floor : Nat) (kindJ : Prop) (J : A.Blk) : Prop where
  floor_eq : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
    (tr.state y i).fg.headHeightFloor = floor
  kind_iff : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi →
    (((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧ ¬ (tr.state y i).fg.Contest) ↔ kindJ)
  root_eq : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i ≤ hi → kindJ →
    (tr.state y i).fg.J = J

/-- A slot window includes the last slot's report deadline. -/
abbrev SlotWindow (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (s₀ N floor : Nat) (kindJ : Prop) (J : A.Blk) : Prop :=
  FrameWindow tr H (P.slotTime s₀) (P.slotTime N + 2 * P.Δ) floor kindJ J

/-- No honest signing strictly before T exceeds the snapshot height. -/
def NoAdvance (tr : RunTrace A) (H : Time → Set (Fin P.n)) (g T : Time) : Prop :=
  ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g

/-- Every G-slot interval contains an actual designated honest proposal. -/
def ProposalGap (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (proposer : Nat → Fin P.n) (G s₀ N : Nat) : Prop :=
  ∀ a, s₀ ≤ a → a + G ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + G ∧
    proposer x ∈ H (P.slotTime x + P.Δ) ∧ ∃ k Q, tr.ProposesAt (proposer x) k Q ∧ Q.slot = x

/-- Population message, block, relay and signed-row service. -/
structure Service (tr : RunTrace A) (H : Time → Set (Fin P.n)) (g ΔF b : Time) : Prop where
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
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
      ∃ k ≤ j, tr.ProcessAttAt y k att ∧ tr.time k < tr.deadline y k (max (tr.time i) g) ΔF

/-- Strong bundled premises for corollary forms, never a replacement for old-premise leaves. -/
structure Premises (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (sg : A.Msg → Fin P.n) (g ΔF b : Time) : Prop where
  run : Growing.LocalRun proposer dg H sg tr
  noColl : Compose.NoCollRun dg tr
  genesisRoot : (P.genesisBlock A.genesisPayload).RootOk dg
  sync : Service tr H g ΔF b
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1
  catchUp : CatchRun tr H g (2 * P.Δ)
  noRestart : NoRestartAfter tr H (gbar g)
  timeoutDelay : 3 ≤ P.δt ∧ ∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)
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

/-- Canonical high entries, with historical honesty read at independently bounded cuts. -/
structure HighCanonical
    (Origin : RunTrace A → Fin P.n → Nat → Nat → A.Blk → Prop)
    (tr : RunTrace A) (H : Time → Set (Fin P.n)) (g b : Time) : Prop where
  no_high_contest : ∀ p i, p ∈ H (tr.time i) → tr.time i ≤ b →
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)
  row_origin : ∀ y k att, y ∈ H (tr.time k) → tr.SignAt y k att → tr.time k ≤ b →
    HZ tr H g + 1 ≤ att.h →
    ∃ r < k, ∃ j B, Origin tr y r j B ∧ y ∈ H (tr.time r) ∧
      HZ tr H g + 1 ≤ ((tr.state y r).fg.σ B.root).h ∧
      ∃ E ∈ (tr.state y r).fg.tree, (tr.state y r).fg.Anc E B ∧ E.root = att.T ∧
        ((tr.state y r).fg.σ E.root).h = att.h ∧ ((tr.state y r).fg.σ E.root).Th = E.root
  entry_eq : ∀ x x' i j i' j' B B' y₁ y₂ m₁ m₂ Z₁ Z₂ t₁ t₂,
    x ∈ H (tr.time i) → Origin tr x i j B → tr.time i ≤ b →
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h →
    x' ∈ H (tr.time i') → Origin tr x' i' j' B' → tr.time i' ≤ b →
    HZ tr H g + 1 ≤ ((tr.state x' i').fg.σ B'.root).h →
    Anc (tr.HonestBlocksAt H) Z₁ B → Anc (tr.HonestBlocksAt H) Z₂ B' →
    0 ≤ t₁ → (∀ q < m₁, tr.time q ≤ t₁) → y₁ ∈ H t₁ →
    0 ≤ t₂ → (∀ q < m₂, tr.time q ≤ t₂) → y₂ ∈ H t₂ →
    Z₁ ∈ (tr.state y₁ m₁).fg.tree → Z₂ ∈ (tr.state y₂ m₂).fg.tree →
    ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h →
    ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root →
    ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root → Z₁.root = Z₂.root

/-- Protocol obligations for growing runs. New source and warmth laws require genuine suppliers. -/
structure ACHealing (A : NodeAC P) (sg : A.Msg → Fin P.n) where
  Run : (Nat → Fin P.n) → Digest (List (FG.Att P.n)) A.Payload →
    (Time → Set (Fin P.n)) → RunTrace A → Prop
  warmup : Nat
  follow : Nat
  drain : Nat
  Warm : RunTrace A → (Time → Set (Fin P.n)) → Nat → Nat → Prop
  Origin : RunTrace A → Fin P.n → Nat → Nat → A.Blk → Prop
  run_local : ∀ {proposer dg H tr}, Run proposer dg H tr → Growing.LocalRun proposer dg H sg tr
  run_truncate : ∀ {proposer dg H tr} (b : Time),
    Run proposer dg H tr → Run proposer dg (truncH H b) tr
  /-- Only forward transport is needed by the drain-output transfer. The bound is in time units. -/
  warm_truncate : ∀ {proposer dg H tr} {s₀ u : Nat} {b : Time},
    Run proposer dg H tr → P.slotTime u + P.Δ ≤ b →
    Warm tr H s₀ u → Warm tr (truncH H b) s₀ u
  follow_le : ∀ {proposer dg H tr} {g ΔF b : Time},
    Run proposer dg H tr → Premises tr H proposer dg sg g ΔF b → follow ≤ P.δt
  report_in_frame : ∀ {proposer dg H tr} {y : Fin P.n} {i : Nat} {R : A.Blk},
    Run proposer dg H tr → y ∈ H (tr.time i) → ReportAt tr y i R →
    R ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc (tr.state y i).fg.fcRoot R
  proposal_floor : ∀ {proposer dg H tr} {lo hi : Time} {floor u : Nat} {kindJ : Prop}
    {J B : A.Blk} {z : Fin P.n} {kB : Nat},
    Run proposer dg H tr → Compose.NoCollRun dg tr → FrameWindow tr H lo hi floor kindJ J →
    z ∈ H (P.slotTime u) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    lo ≤ P.slotTime u → P.slotTime u ≤ hi →
    (H (P.slotTime u))ᶜ.ncard < 2 * P.fg.q - P.n →
    floor ≤ ((tr.state z (kB + 1)).fg.σ B.root).h
  warm_exists : ∀ {proposer dg H tr} {g ΔF b : Time} {s₀ N G floor : Nat} {kindJ : Prop}
    {J : A.Blk}, Run proposer dg H tr → Premises tr H proposer dg sg g ΔF b →
    SlotWindow tr H s₀ N floor kindJ J → gbar g + 4 * P.Δ ≤ P.slotTime s₀ →
    1 ≤ G → s₀ + warmup + G ≤ N + 1 → P.slotTime N + 2 * P.Δ ≤ b →
    (∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k ≤ P.slotTime N + 2 * P.Δ → att.h ≤ HZ tr H g) →
    ProposalGap tr H proposer G s₀ N →
    ∃ u, s₀ ≤ u ∧ u + 1 ≤ s₀ + warmup + G ∧ Warm tr H s₀ u ∧
      ∃ z k X, HonestProposal tr H proposer u z k X
  /-- New persistence law at the old round premises, not an arithmetic theorem for arbitrary ACs. -/
  warm_mono : ∀ {proposer dg H tr} {g ΔF b : Time} {s₀ N u u' floor : Nat}
    {kindJ : Prop} {J : A.Blk},
    Run proposer dg H tr → Compose.NoCollRun dg tr → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    SlotWindow tr H s₀ N floor kindJ J → gbar g + 4 * P.Δ ≤ P.slotTime s₀ →
    P.slotTime N + 2 * P.Δ ≤ b → s₀ ≤ u → Warm tr H s₀ u → u ≤ u' → u' ≤ N →
    Warm tr H s₀ u'
  report_follow : ∀ {proposer dg H tr} {g ΔF b : Time} {s₀ N u floor : Nat} {kindJ : Prop}
    {J B : A.Blk} {z : Fin P.n} {kB : Nat},
    FrameWindow tr H (P.slotTime s₀) (P.slotTime N + 2 * P.Δ) floor kindJ J →
    Run proposer dg H tr → Compose.NoCollRun dg tr → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ ≤ u → Warm tr H s₀ u →
    u + 1 ≤ N → P.slotTime N + 2 * P.Δ ≤ b →
    z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    ∀ y, y ∈ H (P.slotTime (u + 1) + 2 * P.Δ) →
      ∃ i R, y ∈ H (tr.time i) ∧ ReportAt tr y i R ∧ P.slotTime u ≤ tr.time i ∧
        tr.time i ≤ P.slotTime (u + 1) + 2 * P.Δ ∧ Anc (tr.HonestBlocksAt H) B R ∧
        ∀ x, u + follow ≤ x → x ≤ N → ∀ w c d, w ∈ H (tr.time c) →
          ProposalHeadAt tr w c d → tr.time c = P.slotTime x → Anc (tr.HonestBlocksAt H) R d.head
  /-- New source law, without a horizon bundle or a high-root compatibility conclusion. -/
  report_origin : ∀ {proposer dg H tr} {y : Fin P.n} {i : Nat} {R : A.Blk},
    Run proposer dg H tr → Compose.NoCollRun dg tr →
    y ∈ H (tr.time i) → ReportAt tr y i R →
    ∃ r ≤ i, ∃ j B, y ∈ H (tr.time r) ∧ Origin tr y r j B ∧
      B ∈ (tr.state y r).fg.tree ∧ Anc (tr.HonestBlocksAt H) R B
  origins_comparable : ∀ {proposer dg H tr} {g ΔF a b : Time} {x x' : Fin P.n}
    {i j i' j' : Nat} {B B' : A.Blk},
    Run proposer dg H tr → Compose.NoCollRun dg tr → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    IsReset tr H g a → a ≤ b → (∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    x ∈ H (tr.time i) → Origin tr x i j B → tr.time i ≤ b →
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h →
    x' ∈ H (tr.time i') → Origin tr x' i' j' B' → tr.time i' ≤ b →
    HZ tr H g + 1 ≤ ((tr.state x' i').fg.σ B'.root).h →
    Compatible (tr.HonestBlocksAt H) B B'
  heal_after_reset : ∀ {proposer dg H tr} {g ΔF a b : Time},
    Run proposer dg H tr → Premises tr H proposer dg sg g ΔF b → IsReset tr H g a → a ≤ b →
    HighCanonical Origin tr H g b → HealedFrom tr H proposer (P.slotOf a + drain) b

end Consensus.Goldilocks.Generic

end
