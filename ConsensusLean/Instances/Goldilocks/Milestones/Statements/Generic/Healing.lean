module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Obligations

@[expose] public section

/-! # Generic healing leaf contracts

Every declaration is an UNPROVED intended theorem type. Old-premise leaves are primary;
no definition here supplies theorem evidence or replaces an existing theorem.
-/

namespace Consensus.Goldilocks.Generic

open SA (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ IsReset CatchRun NoRestartAfter)

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)

open Classical in
/-- The merged frame key, restated without importing its proof module. -/
noncomputable def frameKey' (st : Store P A.Payload) : Nat :=
  let key := 3 * st.hmax + (if st.Contest then 2 else if st.hmax = st.hj + 1 then 1 else 0)
  2 * (key / 3) + key % 3

/-- Remaining rise rounds at merged key v. -/
def riseRounds (hz v : Nat) : Nat := 2 - (v - 2 * hz) / 2

/-- Attempt length in slots, including the final report slot. -/
def windowSlots (W G δt j : Nat) : Nat := W + G + riseRounds 0 j * (δt + G - 1) + 1

/-- Slot-based assembly budget for five merged keys. -/
def resetSlots (W G δt : Nat) : Nat := ∑ j ∈ Finset.range 5, (windowSlots W G δt j + 2)

/-- Real-time bound of the grid-instantiated endpoint. -/
def resetBoundRounds (r D lam δt X Ld : ℤ) : ℤ :=
  r + (20 * Ld + 24 * (δt + X - 1) + 54) * D + 5 * lam

/-- UNPROVED grid alignment contract, not a chosen alignment witness. -/
def exists_slot_align : Prop :=
  (∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) →
    ∀ af : Time, 0 ≤ af → ∃ s₀ : Nat,
      af ≤ P.slotTime s₀ ∧ 4 * P.Δ * (s₀ : ℤ) < af + 4 * P.Δ

/-- UNPROVED leaf 1: an honest high signing gives a reset no later. -/
def reset_of_height_advance_at : Prop :=
  ∀ {proposer dg H tr} {g : Time} {y : Fin P.n} {k : Nat} {att : FG.Att P.n},
    Growing.LocalRun proposer dg H sg tr →
    (H (tr.time k))ᶜ.ncard < P.fg.q → y ∈ H (tr.time k) →
    tr.SignAt y k att → HZ tr H g + 1 ≤ att.h →
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k

/-- UNPROVED leaf 2 upper bound, under strictly no advance. -/
def hmax_le_of_noAdvance_at : Prop :=
  ∀ {proposer dg H tr} {g T : Time} {y : Fin P.n} {i : Nat},
    Growing.LocalRun proposer dg H sg tr → NoAdvance tr H g T →
    y ∈ H (tr.time i) → (H (tr.time i))ᶜ.ncard < P.fg.q → tr.time i < T →
    (tr.state y i).fg.hmax ≤ HZ tr H g + 1

/-- UNPROVED leaf 2 lower bound, with its original snapshot and call premises. -/
def HZ_le_hmax_at : Prop :=
  ∀ {proposer dg H tr} {g ΔF b κ : Time} {z : Fin P.n} {m : Nat},
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    Service tr H g ΔF b → CatchRun tr H g κ →
    (H (cutZ P g)).Nonempty → (∃ j, FirstCutAfter tr j (cutZ P g)) →
    z ∈ H (tr.time m) →
    (H (max (cutZ P g) (tr.time m)))ᶜ.ncard < 2 * P.fg.q - P.n →
    (∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (cutZ P g) g) P.Δ ≤ tr.time j) →
    gbar g + κ ≤ tr.time m → HZ tr H g ≤ (tr.state z m).fg.hmax

/-- UNPROVED snapshot and call supply for the lower-bound leaf. -/
def snapshotCall_of_awake_at : Prop :=
  ∀ {proposer dg H tr} {g b : Time} {z : Fin P.n} {m : Nat},
    Growing.LocalRun proposer dg H sg tr →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    z ∈ H (tr.time m) → cutZ P g + P.Δ + 1 ≤ tr.time m → tr.time m ≤ b →
    (∃ j, FirstCutAfter tr j (cutZ P g)) ∧
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (cutZ P g) g) P.Δ ≤ tr.time j

/-- UNPROVED relay-call supply at the two-delay lag. -/
def callLag_of_awake_at : Prop :=
  ∀ {proposer dg H tr} {g b lo : Time} {z : Fin P.n} {i m : Nat},
    Growing.LocalRun proposer dg H sg tr →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    cutZ P g ≤ lo → z ∈ H (tr.time m) → lo ≤ tr.time i →
    tr.time i + 2 * P.Δ ≤ tr.time m → tr.time m ≤ b →
    ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j

/-- UNPROVED leaf 3: real-time constant-frame window, with key-dependent lengths. -/
def exists_frameWindow_seq_of_service_at : Prop :=
  ∀ {proposer dg H tr} {g ΔF b κ lo lam T : Time} {hz : Nat} (len : Nat → Time),
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    (∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * P.fg.q - P.n) →
    Service tr H g ΔF b → CatchRun tr H g κ →
    (∀ v, 0 ≤ len v) → 0 ≤ lam → gbar g + κ ≤ lo → T ≤ b →
    (∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1) →
    (∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) P.Δ ≤ tr.time j) →
    lo + ∑ j ∈ Finset.range 5, (len (2 * hz + j) + lam) < T →
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' A (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow tr H a (a + len v) floor kindJ J

/-- UNPROVED leaf 4: explicit report-tree membership avoids an AC-specific inference. -/
def row_or_high_of_report_at : Prop :=
  ∀ {proposer dg H tr} {g T : Time} {y : Fin P.n} {i : Nat} {R B : A.Blk},
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    (∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ P.n - 1) → NoAdvance tr H g T →
    y ∈ H (tr.time i) → ReportAt tr y i R → tr.time i < T →
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

/-- UNPROVED leaf 5: rows or higher reports force a round crossing. -/
def round_cross_at : Prop :=
  ∀ {proposer dg H tr} {g ΔF b v : Time} {B D X : A.Blk} {p : Fin P.n} {kX : Nat},
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    Service tr H g ΔF b → NoRestartAfter tr H (gbar g) →
    B ∈ tr.HonestBlocksAt H → Anc (tr.HonestBlocksAt H) B D → X.parent = some D.root →
    p ∈ H (tr.time kX) → tr.ProposesAt p kX X →
    3 * (H (tr.time kX))ᶜ.ncard ≤ P.n - 1 →
    gbar g ≤ v → v + ΔF ≤ tr.time kX → tr.time kX ≤ b → B.slot + P.δt ≤ X.slot →
    (∀ y ∈ H (tr.time kX),
      (∃ w c, w ∈ H (tr.time c) ∧ B ∈ (tr.state w c).fg.tree ∧
        ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ v ∧
          att.h = ((tr.state w c).fg.σ B.root).h ∧ att.T = ((tr.state w c).fg.σ B.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocksAt H) R D ∧ ∃ w c, w ∈ H (tr.time c) ∧
        B ∈ (tr.state w c).fg.tree ∧ R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ B.root).h < ((tr.state w c).fg.σ R.root).h) →
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤ ((tr.state p (kX + 1)).fg.σ X.root).h

/-- UNPROVED leaf 6: high report implies a reset. -/
def reset_of_high_report_at : Prop :=
  ∀ {proposer dg H tr} {g : Time} {y : Fin P.n} {i : Nat} {R : A.Blk},
    Growing.LocalRun proposer dg H sg tr → y ∈ H (tr.time i) →
    (H (tr.time i))ᶜ.ncard < P.fg.q → ReportAt tr y i R →
    HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h →
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i

/-- UNPROVED FG-call companion of leaf 6. -/
def reset_of_high_source_at : Prop :=
  ∀ {proposer dg H tr} {g : Time} {y : Fin P.n} {k : Nat} {C : A.Blk}
    {s : Option (FG.Att P.n)},
    Growing.LocalRun proposer dg H sg tr → y ∈ H (tr.time k) →
    (H (tr.time k))ᶜ.ncard < P.fg.q → tr.CallAt y k (.fg (.attest C s)) →
    HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h →
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k

/-- UNPROVED new leaf 7: signing provenance, without a stronger horizon bundle. -/
def sign_from_report : Prop :=
  ∀ {proposer dg H tr} {y : Fin P.n} {k : Nat} {att : FG.Att P.n},
    Growing.LocalRun proposer dg H sg tr → y ∈ H (tr.time k) → tr.SignAt y k att →
    ∃ i < k, ∃ R, ReportAt tr y i R ∧ tr.time i = tr.time k ∧
      att.h ≤ ((tr.state y i).fg.σ R.root).h ∧
      ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E R ∧ E.root = att.T ∧
        ((tr.state y i).fg.σ E.root).h = att.h ∧ ((tr.state y i).fg.σ E.root).Th = E.root

/-- UNPROVED leaf 8: deficit at a fixed key, with slot-start proposer honesty. -/
def rounds_le_warm_proposal_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g af len : Time} {u floor v : Nat} {kindJ : Prop} {J B : A.Blk}
    {z : Fin P.n} {kB : Nat},
    O.Run proposer dg H tr → Compose.NoCollRun dg tr →
    FrameWindow tr H af (af + len) floor kindJ J →
    (∀ y i, y ∈ H (tr.time i) → af ≤ tr.time i → tr.time i ≤ af + len →
      frameKey' A (tr.state y i).fg = v) →
    2 * HZ tr H g ≤ v → af ≤ P.slotTime u → P.slotTime u ≤ af + len →
    z ∈ H (P.slotTime u) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    (H (P.slotTime u))ᶜ.ncard < 2 * P.fg.q - P.n →
    HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + riseRounds (HZ tr H g) v

/-- UNPROVED leaf 9: report kind under old window/proposer premises. -/
def report_kind_of_warm_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {lo hi : Time} {floor u : Nat} {kindJ : Prop} {J B R : A.Blk}
    {z : Fin P.n} {kB : Nat} {y : Fin P.n} {i : Nat},
    O.Run proposer dg H tr → Compose.NoCollRun dg tr → FrameWindow tr H lo hi floor kindJ J →
    z ∈ H (P.slotTime u) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    lo ≤ P.slotTime u → P.slotTime u ≤ hi → (H (P.slotTime u))ᶜ.ncard < 2 * P.fg.q - P.n →
    y ∈ H (tr.time i) → ReportAt tr y i R → Anc (tr.HonestBlocksAt H) B R →
    lo ≤ tr.time i → tr.time i ≤ hi →
    ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ B.root).h →
    (tr.state y i).fg.hj < ((tr.state y i).fg.σ B.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ B.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)

/-- UNPROVED leaf 10: a warm high proposal forces the next reset. -/
def reset_of_high_proposal_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop} {J B : A.Blk}
    {z : Fin P.n} {kB : Nat},
    SlotWindow tr H s₀ N floor kindJ J → O.Run proposer dg H tr → Compose.NoCollRun dg tr →
    Service tr H g ΔF b → (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ ≤ u → O.Warm tr H s₀ u →
    u + 1 ≤ N → P.slotTime N + 2 * P.Δ ≤ b → (H b).Nonempty →
    z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h →
    ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (u + 1) + 2 * P.Δ

/-- UNPROVED leaf 11: both compared heights are read in the later proposer's store. -/
def round_of_warm_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g ΔF b T : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J B X : A.Blk} {z : Fin P.n} {kB : Nat} {p : Fin P.n} {kX : Nat},
    SlotWindow tr H s₀ N floor kindJ J → O.Run proposer dg H tr → Compose.NoCollRun dg tr →
    Service tr H g ΔF b → (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ ≤ u → O.Warm tr H s₀ u → 3 ≤ P.δt →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    u + P.δt ≤ x → x ≤ N → P.slotTime N + 2 * P.Δ ≤ b → T ≤ b →
    NoAdvance tr H g T → P.slotTime (u + 1) + 2 * P.Δ < T →
    z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
    p ∈ H (tr.time kX) → p = proposer x → tr.ProposesAt p kX X → X.slot = x →
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤ ((tr.state p (kX + 1)).fg.σ X.root).h

/-- A high origin combines own-write honesty, protocol origin, and the exact height bound. -/
def HighOrigin (O : ACHealing A sg) (tr : RunTrace A) (H : Time → Set (Fin P.n)) (g : Time)
    (x : Fin P.n) (i j : Nat) (B : A.Blk) : Prop :=
  x ∈ H (tr.time i) ∧ O.Origin tr x i j B ∧
    HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h

/-- UNPROVED leaf 12: strict source cut, original entry identities and ancestry. -/
def high_row_source_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g : Time} {v : Fin P.n} {d : Nat} {att : FG.Att P.n},
    O.Run proposer dg H tr → Compose.NoCollRun dg tr →
    v ∈ H (tr.time d) → tr.SignAt v d att → HZ tr H g + 1 ≤ att.h →
    ∃ r < d, ∃ l Og, HighOrigin A sg O tr H g v r l Og ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E Og ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root

/-- The eight old reset-premise fields, without catch-up or timeout assumptions. -/
structure ResetPremisesUpTo (O : ACHealing A sg) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (g ΔF a b : Time) : Prop where
  run : O.Run proposer dg H tr
  noColl : Compose.NoCollRun dg tr
  sync : Service tr H g ΔF b
  awake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t
  faults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1
  reset : IsReset tr H g a
  reset_le : a ≤ b
  snapshot : ∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b

/-- UNPROVED leaf 13: no high contest under only the old reset premises. -/
def no_high_contest_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g ΔF a b : Time} {p : Fin P.n} {i : Nat},
    ResetPremisesUpTo A sg O tr H proposer dg g ΔF a b →
    p ∈ H (tr.time i) → tr.time i ≤ b →
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)

/-- UNPROVED leaf 14: independently bounded historical readers, not event-only readers. -/
def high_entry_eq_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g ΔF a b : Time} {x x' : Fin P.n} {i j i' j' : Nat}
    {B B' Z₁ Z₂ : A.Blk} {y₁ y₂ : Fin P.n} {m₁ m₂ : Nat} {t₁ t₂ : Time},
    ResetPremisesUpTo A sg O tr H proposer dg g ΔF a b →
    HighOrigin A sg O tr H g x i j B → tr.time i ≤ b →
    HighOrigin A sg O tr H g x' i' j' B' → tr.time i' ≤ b →
    Anc (tr.HonestBlocksAt H) Z₁ B → Anc (tr.HonestBlocksAt H) Z₂ B' →
    0 ≤ t₁ → (∀ q < m₁, tr.time q ≤ t₁) → y₁ ∈ H t₁ →
    0 ≤ t₂ → (∀ q < m₂, tr.time q ≤ t₂) → y₂ ∈ H t₂ →
    Z₁ ∈ (tr.state y₁ m₁).fg.tree → Z₂ ∈ (tr.state y₂ m₂).fg.tree →
    ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h →
    ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root →
    ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root → Z₁.root = Z₂.root

end Consensus.Goldilocks.Generic

end
