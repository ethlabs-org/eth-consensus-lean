module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations

@[expose] public section

/-! # Generic healing leaf contracts

Every contract is an intended theorem type. Old-premise leaves are primary; no definition here
supplies theorem evidence or replaces an existing theorem. Each contract's docstring names the
theorem that proves it.
-/

namespace Consensus.Goldilocks.Generic

open AC (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ IsReset CatchRun NoRestartAfter)

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
variable {runs : ACRun A sg} {hold : Time}

open Classical in
/-- The merged frame key, restated without importing its proof module. -/
noncomputable def frameKey'' (st : Store P A.Payload) : Nat :=
  2 * st.hmax + if st.hmax = st.hj + 1 then 1 else 0

/-- Remaining rise rounds at merged key v. -/
def riseRounds (hz v : Nat) : Nat := 2 - (v - 2 * hz) / 2

/-- Attempt length in slots, including the final report slot. -/
def windowSlots (W Gp δt j : Nat) (d : Nat := 0) : Nat :=
  W + Gp + riseRounds 0 j * (δt + Gp - 1) + 1 + (d + 3) / 4

/-- Slot-based assembly budget for five merged keys. -/
def resetSlots (W Gp δt : Nat) (d : Nat := 0) : Nat :=
  ∑ j ∈ Finset.range 5, (windowSlots W Gp δt j d + 2)

/-- Grid alignment contract, not a chosen alignment witness. Proved by `exists_slot_align_of_grid`
(Lemmas/Generic/HealingLeaves). -/
def exists_slot_align : Prop :=
  (∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) →
    ∀ af : Time, 0 ≤ af → ∃ s₀ : Nat,
      af ≤ P.slotTime s₀ ∧ 4 * P.Δ * (s₀ : ℤ) < af + 4 * P.Δ

/-- Leaf 4: explicit report-tree membership avoids an AC-specific inference. Proved for any run
predicate by `row_or_high_of_report_at_from` (Lemmas/Generic/HealingLeaves), through
`ACRun.run_local`. -/
def row_or_high_of_report_at (runs : ACRun A sg) : Prop :=
  ∀ {cm proposer dg H tr} {g T : Time} {y : Fin P.n} {i : Nat} {R B : A.Blk},
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    (∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ P.n - 1) → NoAdvance tr H g T →
    y ∈ H (max (cutZ P g) (tr.time i)) → ReportAt tr y i R → tr.time i < T →
    R ∈ (tr.state y i).fg.tree → Anc (tr.HonestBlocksAt H) B R →
    (((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ B.root).h →
      ((tr.state y i).fg.σ B.root).h = HZ tr H g ∨
      (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ B.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)) →
    B ∈ (tr.state y i).fg.tree ∧ R ∈ (tr.state y i).fg.tree ∧
      ((∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
        att.h = ((tr.state y i).fg.σ B.root).h ∧
        att.T = ((tr.state y i).fg.σ B.root).Th) ∨
        ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ R.root).h)

/-- Leaf 6: a high report by a reporter honest at it and at `c_z` implies a reset. Proved for any
run predicate by `reset_of_high_report_at_from` (Lemmas/Generic/HealingLeaves), through
`ACRun.run_local`. -/
def reset_of_high_report_at (runs : ACRun A sg) : Prop :=
  ∀ {cm proposer dg H tr} {g : Time} {y : Fin P.n} {i : Nat} {R : A.Blk},
    runs.Run cm proposer dg H tr → y ∈ H (max (cutZ P g) (tr.time i)) →
    (H (max (cutZ P g) (tr.time i)))ᶜ.ncard < P.fg.q → ReportAt tr y i R →
    HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h →
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i

/-- Leaf 8: deficit at a fixed key. The Prop is parameterized by a healing supplier whose value does
not occur in its body; its proof uses the supplier's `proposal_floor`. Proved over any supplier by
`rounds_le_warm_proposal_at_of_healing` (Lemmas/Generic/HealingRounds). -/
def rounds_le_warm_proposal_at (_O : ACHealing A sg runs hold) : Prop :=
  ∀ {cm proposer dg H tr} {g af len : Time} {u M v : Nat} {isTop : Prop} {J B : A.Blk}
    {z : Fin P.n} {kB : Nat},
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    FrameWindow tr H af (af + len) M isTop J →
    (∀ y i, y ∈ H (tr.time i) → af ≤ tr.time i → tr.time i ≤ af + len →
      frameKey'' A (tr.state y i).fg = v) →
    2 * HZ tr H g ≤ v → af ≤ P.slotTime u → P.slotTime u ≤ af + len →
    z ∈ H (P.slotTime u) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    (H (P.slotTime u))ᶜ.ncard < 2 * P.fg.q - P.n →
    HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + riseRounds (HZ tr H g) v

/-- Leaf 9: report kind. The Prop is parameterized by a healing supplier whose value does not occur
in its body; its proof uses the supplier's `proposal_floor` and `report_in_frame`. Proved over any
supplier by `report_kind_of_warm_at_of_healing` (Lemmas/Generic/HealingRounds). -/
def report_kind_of_warm_at (_O : ACHealing A sg runs hold) : Prop :=
  ∀ {cm proposer dg H tr} {lo hi : Time} {M u : Nat} {isTop : Prop} {J B R : A.Blk}
    {z : Fin P.n} {kB : Nat} {y : Fin P.n} {i : Nat},
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr → FrameWindow tr H lo hi M isTop J →
    z ∈ H (P.slotTime u) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    lo ≤ P.slotTime u → P.slotTime u ≤ hi → (H (P.slotTime u))ᶜ.ncard < 2 * P.fg.q - P.n →
    y ∈ H (tr.time i) → ReportAt tr y i R → Anc (tr.HonestBlocksAt H) B R →
    lo ≤ tr.time i → tr.time i ≤ hi →
    ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ B.root).h →
    (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ B.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)

/-- Leaf 10: a warm high proposal forces the next reset. Proved over any supplier by
`reset_of_high_proposal_at_of_healing` (Lemmas/Generic/HealingRounds). -/
def reset_of_high_proposal_at (O : ACHealing A sg runs hold) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b : Time} {s₀ u N M : Nat}
    {isTop : Prop} {J B : A.Blk}
    {z : Fin P.n} {kB : Nat},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindowWithin tr H O.reportDelay s₀ N M isTop J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    Service tr H g ΔF b hold → (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    (∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    (∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ ≤ u → s₀ + O.warmup ≤ u →
    u + 1 ≤ N → shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b → (H b).Nonempty →
    z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h →
    ∃ a, IsReset tr H g a ∧ a ≤ shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ)

/-- Leaf 11: both compared heights are read in the later proposer's store. Proved over any
supplier by `round_of_warm_at_of_healing` (Lemmas/Generic/HealingRounds). -/
def round_of_warm_at (O : ACHealing A sg runs hold) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b T : Time} {s₀ u x N M : Nat} {isTop : Prop}
    {J B X : A.Blk} {z : Fin P.n} {kB : Nat} {p : Fin P.n} {kX : Nat},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindowWithin tr H O.reportDelay s₀ N M isTop J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    Service tr H g ΔF b hold → (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    (∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) →
    (∀ s, shiftDelay P O.reportDelay (P.slotTime (s + 1) + 2 * P.Δ) + ΔF ≤
      P.slotTime (s + P.δt)) →
    (∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ ≤ u → s₀ + O.warmup ≤ u → O.follow ≤ P.δt →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    u + P.δt ≤ x → x ≤ N → shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b →
    (H b).Nonempty → T ≤ b →
    NoAdvance tr H g T → shiftDelay P O.reportDelay (P.slotTime (u + 1) + 2 * P.Δ) < T →
    z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    p ∈ H (tr.time kX) → p = proposer x → tr.ProposesAt p kX X → X.slot = x →
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤ ((tr.state p (kX + 1)).fg.σ X.root).h

/-- A high origin combines own-write honesty, protocol origin, and the exact height bound. -/
def HighOrigin (O : ACHealing A sg runs hold) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (g : Time) (x : Fin P.n) (i j : Nat) (B : A.Blk) : Prop :=
  x ∈ H (max (cutZ P g) (tr.time i)) ∧ O.Origin tr x i j B ∧
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h

/-- Leaf 12: strict source cut, original entry identities and ancestry.
The reset premises are required by the abstract origin producer `report_origin`. Proved over any
supplier by `high_row_source_at_of_healing` (Lemmas/Generic/HealingRounds). -/
def high_row_source_at (O : ACHealing A sg runs hold) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time}
    {v : Fin P.n} {d : Nat} {att : FG.Att P.n},
    βK ≤ 1 / 2 → runs.Run cm proposer dg H tr →
    Premises tr H cm βK proposer dg sg g ΔF b hold → IsReset tr H g a → a ≤ b →
    v ∈ H (max (cutZ P g) (tr.time d)) → tr.time d ≤ b →
    OriginInCap P O.deepBudget g (tr.time d) →
    tr.SignAt v d att → HZ tr H g + 1 ≤ att.h →
    ∃ r < d, ∃ l Og, HighOrigin A sg O tr H g v r l Og ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E Og ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root

/-- Leaf 13: no high contest, for a reset and an observation within the supplier's origin cap.
Its proof uses the supplier's `report_origin`, `report_in_frame` and
`origins_comparable`. Proved over any supplier by `no_high_contest_at_of_healing`
(Lemmas/Generic/HealingRounds). -/
def no_high_contest_at (O : ACHealing A sg runs hold) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time} {p : Fin P.n} {i : Nat},
    βK ≤ 1 / 2 → runs.Run cm proposer dg H tr →
    Premises tr H cm βK proposer dg sg g ΔF b hold → IsReset tr H g a → a ≤ b →
    OriginInCap P O.deepBudget g a →
    p ∈ H (tr.time i) → tr.time i ≤ b → OriginInCap P O.deepBudget g (tr.time i) →
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)

/-- Leaf 14: independently bounded historical readers, not event-only readers. Proved over any
supplier by `high_entry_eq_at_of_healing` (Lemmas/Generic/HealingRounds). -/
def high_entry_eq_at (O : ACHealing A sg runs hold) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF a b : Time} {x x' : Fin P.n} {i j i' j' : Nat}
    {B B' Z₁ Z₂ : A.Blk} {y₁ y₂ : Fin P.n} {m₁ m₂ : Nat} {t₁ t₂ : Time},
    βK ≤ 1 / 2 → runs.Run cm proposer dg H tr →
    Premises tr H cm βK proposer dg sg g ΔF b hold → IsReset tr H g a → a ≤ b →
    OriginInCap P O.deepBudget g a →
    HighOrigin A sg O tr H g x i j B → tr.time i ≤ b → OriginInCap P O.deepBudget g (tr.time i) →
    HighOrigin A sg O tr H g x' i' j' B' → tr.time i' ≤ b →
    OriginInCap P O.deepBudget g (tr.time i') →
    Anc (tr.HonestBlocksAt H) Z₁ B → Anc (tr.HonestBlocksAt H) Z₂ B' →
    0 ≤ t₁ → (∀ q < m₁, tr.time q ≤ t₁) → y₁ ∈ H t₁ →
    0 ≤ t₂ → (∀ q < m₂, tr.time q ≤ t₂) → y₂ ∈ H t₂ →
    Z₁ ∈ (tr.state y₁ m₁).fg.tree → Z₂ ∈ (tr.state y₂ m₂).fg.tree →
    ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h →
    ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root →
    ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root → Z₁.root = Z₂.root

end Consensus.Goldilocks.Generic

end
