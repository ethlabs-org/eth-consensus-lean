module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService

public section

/-! # Goldilocks old-premise bridge statements

These unproved Prop contracts reserve the original Goldilocks statement sides of the generic
bridges. Generic antecedents are added when their statement contracts are available. Nothing
here supplies proved evidence. Each original premise and conclusion is retained verbatim.

This leaf has an isolated concrete bridge proof closure, not a vocabulary-only closure.
`Kernel.Boundaries` supplies `FrameWindow`, `ProposalGap`, `DrainOutputs`, `NoRestartUpTo`,
`frameKey'`, `riseRounds`, and `Obligations.resetBoundRounds` in the exact original types below.
`Report.Row` supplies the concrete report-row declaration whose complete type is restated below.
`RowService` supplies `ResetPremisesUpTo.high_entry_eq_at` and the retained-origin vocabulary
`ResetPremisesUpTo` and `HighOrigin`, again used in the exact original types below.
No generic statement or sibling edge may import this leaf, and it has no descendants.

No old name: `exists_reset`, `generic_healing`, `highCanonical`, the slot-form
`exists_frameWindow`, and `sign_from_report`.
-/

-- Quantified proof binders deliberately keep the original statement's names.
set_option linter.unusedVariables false

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder Payload gbar)
open Healing Healing.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Original side: `Growing/Healing/Kernel/NoAdvance.lean:24`. -/
def reset_of_height_advance_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g : Time} {y : Fin sp.n} {k : Nat}
    (hq : (H (tr.time k))ᶜ.ncard < sp.toParams.fg.q) (hy : y ∈ H (tr.time k))
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hh : HZ tr H g + 1 ≤ att.h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k

/-- Original side: `Growing/Healing/Kernel/NoAdvance.lean:60`, upper range bound. -/
def hmax_le_of_noAdvance_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g T : Time}
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q) (hiT : tr.time i < T),
    (tr.state y i).fg.hmax ≤ HZ tr H g + 1

/-- Original side: `Growing/Healing/M1/FrameLag.lean:93`, lower range bound. -/
def HZ_le_hmax_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : (H (cutZ sp.toParams g)).Nonempty)
    (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hf : (H (max (cutZ sp.toParams g) (tr.time m)))ᶜ.ncard <
      2 * sp.toParams.fg.q - sp.n)
    (hcall : ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m), HZ tr H g ≤ (tr.state z m).fg.hmax

/-- Original side: `Growing/Healing/Kernel/DrainWarm.lean:70`. -/
def snapshotCall_of_awake_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hfit : cutZ sp.toParams g + sp.Δ + 1 ≤ tr.time m) (hmb : tr.time m ≤ b),
    (∃ j, FirstCutAfter tr j (cutZ sp.toParams g)) ∧
      ∃ j < m, tr.IsCall z j ∧
        tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:52`. -/
def callLag_of_awake_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g b lo : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hlo : cutZ sp.toParams g ≤ lo) {z : Fin sp.n} {i m : Nat}
    (hz : z ∈ H (tr.time m)) (hi : lo ≤ tr.time i)
    (him : tr.time i + 2 * sp.Δ ≤ tr.time m) (hmb : tr.time m ≤ b),
    ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:141`. -/
def reset_of_high_source_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g : Time}
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (hq : (H (tr.time k))ᶜ.ncard < sp.toParams.fg.q)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest C s)))
    (hh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:219`. -/
def reset_of_high_report_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g : Time}
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q)
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:251`. -/
def proposal_mem_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    (hp : p ∈ H (tr.time k)) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P), P ∈ (tr.state p (k + 1)).fg.tree

/-- Original side: `Growing/Healing/Kernel/Boundaries.lean:29`, real-time window. -/
def exists_frameWindow_seq_of_service_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (hlen : ∀ v, 0 ≤ len v) (hlam : 0 ≤ lam) (hlo : gbar g + κ ≤ lo) (hTb : T ≤ b)
    (hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + ∑ j ∈ Finset.range 5, (len (2 * hz + j) + lam) < T),
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, FrameWindow tr H a (a + len v) floor kindJ J

/-- Original side: `Growing/Healing/Report/Row.lean:24`; no added tree premise. -/
def row_or_high_of_report_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g T : Time}
    (hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {R P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R) (hiT : tr.time i < T)
    (hPR : Anc (tr.HonestBlocksAt H) P R)
    (hkind : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h →
      ((tr.state y i).fg.σ P.root).h = HZ tr H g ∨
      (tr.state y i).fg.hj < ((tr.state y i).fg.σ P.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ P.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)),
    P ∈ (tr.state y i).fg.tree ∧ R ∈ (tr.state y i).fg.tree ∧
      ((∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
        att.h = ((tr.state y i).fg.σ P.root).h ∧
        att.T = ((tr.state y i).fg.σ P.root).Th) ∨
        ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ R.root).h)

/-- Original side: `Growing/Healing/Kernel/Crossing.lean:22`. -/
def round_cross_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b v : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    {P D X : SA.Blk sp.n (List (FG.Att sp.n))} (hPH : P ∈ tr.HonestBlocksAt H)
    (hPD : Anc (tr.HonestBlocksAt H) P D) (hpar : X.parent = some D.root)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    (hX : tr.ProposesAt p kX X) (hf : 3 * (H (tr.time kX))ᶜ.ncard ≤ sp.n - 1)
    (hv : gbar g ≤ v) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hage : P.slot + sp.toParams.fg.δt ≤ X.slot)
    (hrow : ∀ y ∈ H (tr.time kX),
      (∃ w c, w ∈ H (tr.time c) ∧ P ∈ (tr.state w c).fg.tree ∧
        ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧
          tr.time k ≤ v ∧ att.h = ((tr.state w c).fg.σ P.root).h ∧
          att.T = ((tr.state w c).fg.σ P.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocksAt H) R D ∧ ∃ w c, w ∈ H (tr.time c) ∧
        P ∈ (tr.state w c).fg.tree ∧ R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ P.root).h < ((tr.state w c).fg.σ R.root).h),
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:530`. -/
def rounds_le_warm_proposal_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g af len : Time} {u floor v : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hwin : FrameWindow tr H af (af + len) floor kindJ J)
    (hK : ∀ y i, y ∈ H (tr.time i) → af ≤ tr.time i → tr.time i ≤ af + len →
      frameKey' (tr.state y i).fg = v)
    (hv : 2 * HZ tr H g ≤ v) (hlo : af ≤ sp.ts u) (hhi : sp.ts u ≤ af + len)
    {z : Fin sp.n} {kP : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n),
    HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + riseRounds (HZ tr H g) v

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:285`. -/
def report_kind_of_warm_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {lo hi : Time} {floor u : Nat} {kindJ : Prop}
    {J P R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    {z : Fin sp.n} {kP : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hlo : lo ≤ sp.ts u) (hhi : sp.ts u ≤ hi)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hR : SA.ToFGAt tr.projAC y i ell R)
    (hPR : Anc (tr.HonestBlocksAt H) P R) (hil : lo ≤ tr.time i) (hih : tr.time i ≤ hi)
    (heq : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h),
    (tr.state y i).fg.hj < ((tr.state y i).fg.σ P.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ P.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:415`. -/
def reset_of_high_proposal_at_goldilocks : Prop := ∀
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b) (hH : (H b).Nonempty)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:320`; both heights at `p`. -/
def round_of_warm_at_goldilocks : Prop := ∀
    {g ΔF b T : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hux : u + sp.toParams.fg.δt ≤ x) (hxN : x ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ < T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX)) (hdx : p = proposer x)
    (hX : tr.ProposesAt p kX X) (hXs : X.slot = x),
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:457`. -/
def rise_reset_rounds_at_goldilocks : Prop := ∀
    {g ΔF b T : Time} {s₀ N G floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hδ : 3 ≤ sp.toParams.fg.δt) (hG : 1 ≤ G)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hgp : ProposalGap tr H proposer G s₀ N)
    (hmb : sp.ts N + 2 * sp.Δ ≤ b) (hH : (H b).Nonempty) (hTb : T ≤ b)
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (r : Nat) {u : Nat} (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + r * (sp.toParams.fg.δt + G - 1) + 1 ≤ N)
    (hT : sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ ≤ T)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hrise : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + r),
    ∃ a, IsReset tr H g a ∧
      a ≤ sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ

/-- Original side: `Growing/Healing/Kernel/Boundaries.lean:75`; free `Ld`, bounded restarts. -/
def exists_reset_of_drain_rounds_awake_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r : Time} {G Ld : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : DrainOutputs tr proposer H g G Ld b),
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld

/-- Public restatement of the private supplier at `Kernel/ResetRounds.lean:708`. -/
def goldilocksRun_truncH : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (b : Time),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg (fun t => {y | y ∈ H t ∧ t ≤ b}) tr

/-- Original side: `Growing/Healing/Outcome/RowSource.lean:107`. -/
def high_row_source_at_goldilocks : Prop := ∀
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g : Time}
    {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h),
    ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root

/-- Original side: `Growing/Healing/Outcome/Contest.lean:41`. -/
def no_high_contest_at_goldilocks : Prop := ∀ {g ΔF a b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i : Nat} (hpH : p ∈ H (tr.time i)) (hib : tr.time i ≤ b),
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)

/-- Original side: `Growing/Healing/RowService.lean:235`; arbitrary honesty bounds retained. -/
def high_entry_eq_at_goldilocks : Prop := ∀ {g ΔF a b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (ho' : HighOrigin tr H g x' i' j' B') (hi'b : tr.time i' ≤ b)
    (h₁ : Anc (tr.HonestBlocksAt H) Z₁ B) (h₂ : Anc (tr.HonestBlocksAt H) Z₂ B')
    {y₁ y₂ : Fin sp.n} {m₁ m₂ : Nat} {t₁ t₂ : Time}
    (ht₁ : 0 ≤ t₁) (hle₁ : ∀ q < m₁, tr.time q ≤ t₁) (hy₁ : y₁ ∈ H t₁)
    (ht₂ : 0 ≤ t₂) (hle₂ : ∀ q < m₂, tr.time q ≤ t₂) (hy₂ : y₂ ∈ H t₂)
    (hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root), Z₁.root = Z₂.root

end Consensus.Goldilocks.Generic
