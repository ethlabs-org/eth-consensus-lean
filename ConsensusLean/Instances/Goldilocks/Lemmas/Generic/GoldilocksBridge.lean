module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.GoldilocksBridge

public section

/-! # Goldilocks old-premise bridge statements

These unproved Prop contracts retain the original Goldilocks statement sides and connect them
to the generic contracts by conditional implications. Nothing here supplies proved evidence.
Every original premise and conclusion is retained, up to unused proof-binder alpha-renaming.

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

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder Payload gbar)
open Healing Healing.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Original side: `Growing/Healing/Kernel/NoAdvance.lean:24`. -/
def reset_of_height_advance_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {g : Time} {y : Fin sp.n} {k : Nat}
    (_hq : (H (tr.time k))ᶜ.ncard < sp.toParams.fg.q) (_hy : y ∈ H (tr.time k))
    {att : FG.Att sp.n} (_hs : tr.SignAt y k att) (_hh : HZ tr H g + 1 ≤ att.h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k

/-- Original side: `Growing/Healing/Kernel/NoAdvance.lean:60`, upper range bound. -/
def hmax_le_of_noAdvance_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g T : Time}
    (_hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (_hy : y ∈ H (tr.time i))
    (_hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q) (_hiT : tr.time i < T),
    (tr.state y i).fg.hmax ≤ HZ tr H g + 1

/-- Original side: `Growing/Healing/M1/FrameLag.lean:93`, lower range bound. -/
def HZ_le_hmax_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (_hsvc : ResetService tr H g ΔF b) (_hcatch : CatchRun tr H g κ)
    (_hH : (H (cutZ sp.toParams g)).Nonempty)
    (_hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    {z : Fin sp.n} {m : Nat} (_hz : z ∈ H (tr.time m))
    (_hf : (H (max (cutZ sp.toParams g) (tr.time m)))ᶜ.ncard <
      2 * sp.toParams.fg.q - sp.n)
    (_hcall : ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (_hcm : gbar g + κ ≤ tr.time m), HZ tr H g ≤ (tr.state z m).fg.hmax

/-- Original side: `Growing/Healing/Kernel/DrainWarm.lean:70`. -/
def snapshotCall_of_awake_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g b : Time}
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin sp.n} {m : Nat} (_hz : z ∈ H (tr.time m))
    (_hfit : cutZ sp.toParams g + sp.Δ + 1 ≤ tr.time m) (_hmb : tr.time m ≤ b),
    (∃ j, FirstCutAfter tr j (cutZ sp.toParams g)) ∧
      ∃ j < m, tr.IsCall z j ∧
        tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:52`. -/
def callLag_of_awake_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g b lo : Time}
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hlo : cutZ sp.toParams g ≤ lo) {z : Fin sp.n} {i m : Nat}
    (_hz : z ∈ H (tr.time m)) (_hi : lo ≤ tr.time i)
    (_him : tr.time i + 2 * sp.Δ ≤ tr.time m) (_hmb : tr.time m ≤ b),
    ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:141`. -/
def reset_of_high_source_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g : Time}
    {y : Fin sp.n} {k : Nat} (_hy : y ∈ H (tr.time k))
    (_hq : (H (tr.time k))ᶜ.ncard < sp.toParams.fg.q)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Option (FG.Att sp.n)}
    (_hc : tr.CallAt y k (.fg (.attest C s)))
    (_hh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:219`. -/
def reset_of_high_report_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g : Time}
    {y : Fin sp.n} {i : Nat} (_hy : y ∈ H (tr.time i))
    (_hq : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q)
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hR : SA.ToFGAt tr.projAC y i ell R)
    (_hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:251`. -/
def proposal_mem_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    (_hp : p ∈ H (tr.time k)) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hP : tr.ProposesAt p k P), P ∈ (tr.state p (k + 1)).fg.tree

/-- Original side: `Growing/Healing/Kernel/Boundaries.lean:29`, real-time window. -/
def exists_frameWindow_seq_of_service_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (_hf : ∀ t, 0 ≤ t → t ≤ b → (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (_hsvc : ResetService tr H g ΔF b) (_hcatch : CatchRun tr H g κ)
    {lo lam T : Time} {hz : Nat} (len : Nat → Time)
    (_hlen : ∀ v, 0 ≤ len v) (_hlam : 0 ≤ lam) (_hlo : gbar g + κ ≤ lo) (_hTb : T ≤ b)
    (_hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < T →
      hz ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ hz + 1)
    (_hcall : ∀ z i m, z ∈ H (tr.time m) → lo ≤ tr.time i →
      tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (_hT : lo + ∑ j ∈ Finset.range 5, (len (2 * hz + j) + lam) < T),
    ∃ v, 2 * hz ≤ v ∧ v ≤ 2 * hz + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + len v ≤ lo + ∑ j ∈ Finset.range (v - 2 * hz + 1), (len (2 * hz + j) + lam) ∧
      (∀ y i, y ∈ H (tr.time i) → a ≤ tr.time i → tr.time i ≤ a + len v →
        Healing.frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J, Healing.Growing.FrameWindow tr H a (a + len v) floor kindJ J

/-- Original side: `Growing/Healing/Report/Row.lean:24`; no added tree premise. -/
def row_or_high_of_report_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g T : Time}
    (_hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (_hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {R P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hR : SA.ToFGAt tr.projAC y i ell R) (_hiT : tr.time i < T)
    (_hPR : Anc (tr.HonestBlocksAt H) P R)
    (_hkind : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h →
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
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g ΔF b v : Time}
    (_hsvc : ResetService tr H g ΔF b) (_hnr : NoRestartAfter tr H (gbar g))
    {P D X : SA.Blk sp.n (List (FG.Att sp.n))} (_hPH : P ∈ tr.HonestBlocksAt H)
    (_hPD : Anc (tr.HonestBlocksAt H) P D) (_hpar : X.parent = some D.root)
    {p : Fin sp.n} {kX : Nat} (_hp : p ∈ H (tr.time kX))
    (_hX : tr.ProposesAt p kX X) (_hf : 3 * (H (tr.time kX))ᶜ.ncard ≤ sp.n - 1)
    (_hv : gbar g ≤ v) (_hvx : v + ΔF ≤ tr.time kX) (_hkb : tr.time kX ≤ b)
    (_hage : P.slot + sp.toParams.fg.δt ≤ X.slot)
    (_hrow : ∀ y ∈ H (tr.time kX),
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
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g af len : Time} {u floor v : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hwin : Healing.Growing.FrameWindow tr H af (af + len) floor kindJ J)
    (_hK : ∀ y i, y ∈ H (tr.time i) → af ≤ tr.time i → tr.time i ≤ af + len →
      Healing.frameKey' (tr.state y i).fg = v)
    (_hv : 2 * HZ tr H g ≤ v) (_hlo : af ≤ sp.ts u) (_hhi : sp.ts u ≤ af + len)
    {z : Fin sp.n} {kP : Nat} (_hz : z ∈ H (sp.ts u)) (_hdes : z = proposer u)
    (_hP : tr.ProposesAt z kP P) (_hPs : P.slot = u)
    (_hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n),
    HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h +
      Healing.riseRounds (HZ tr H g) v

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:285`. -/
def report_kind_of_warm_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {lo hi : Time} {floor u : Nat} {kindJ : Prop}
    {J P R : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hframe : Healing.Growing.FrameWindow tr H lo hi floor kindJ J)
    {z : Fin sp.n} {kP : Nat} (_hz : z ∈ H (sp.ts u)) (_hdes : z = proposer u)
    (_hP : tr.ProposesAt z kP P) (_hPs : P.slot = u)
    (_hlo : lo ≤ sp.ts u) (_hhi : sp.ts u ≤ hi)
    (_hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} {i : Nat} (_hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (_hR : SA.ToFGAt tr.projAC y i ell R)
    (_hPR : Anc (tr.HonestBlocksAt H) P R) (_hil : lo ≤ tr.time i) (_hih : tr.time i ≤ hi)
    (_heq : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h),
    (tr.state y i).fg.hj < ((tr.state y i).fg.σ P.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ P.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:415`. -/
def reset_of_high_proposal_at_goldilocks : Prop := ∀
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hframe : Healing.Growing.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) (_hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hcatch : CatchRun tr H g (2 * sp.Δ)) (_hnr : NoRestartAfter tr H (gbar g))
    (_hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (_hwarm : s₀ + 2 * sp.k ≤ u)
    (_hN : u + 1 ≤ N) (_hmb : sp.ts N + 2 * sp.Δ ≤ b) (_hH : (H b).Nonempty)
    {z : Fin sp.n} (_hz : z ∈ H (sp.ts u + sp.Δ)) (_hdes : z = proposer u)
    {kP : Nat} (_hP : tr.ProposesAt z kP P) (_hPs : P.slot = u)
    (_hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:320`; both heights at `p`. -/
def round_of_warm_at_goldilocks : Prop := ∀
    {g ΔF b T : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hframe : Healing.Growing.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) (_hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hcatch : CatchRun tr H g (2 * sp.Δ)) (_hnr : NoRestartAfter tr H (gbar g))
    (_hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (_hwarm : s₀ + 2 * sp.k ≤ u)
    (_hδ : 3 ≤ sp.toParams.fg.δt)
    (_hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (_hux : u + sp.toParams.fg.δt ≤ x) (_hxN : x ≤ N) (_hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (_hTb : T ≤ b)
    (_hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (_hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ < T)
    {z : Fin sp.n} (_hz : z ∈ H (sp.ts u + sp.Δ)) (_hdes : z = proposer u)
    {kP : Nat} (_hP : tr.ProposesAt z kP P) (_hPs : P.slot = u)
    {p : Fin sp.n} {kX : Nat} (_hp : p ∈ H (tr.time kX)) (_hdx : p = proposer x)
    (_hX : tr.ProposesAt p kX X) (_hXs : X.slot = x),
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h

/-- Original side: `Growing/Healing/Kernel/ResetRounds.lean:457`. -/
def rise_reset_rounds_at_goldilocks : Prop := ∀
    {g ΔF b T : Time} {s₀ N G floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hframe : Healing.Growing.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) (_hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hcatch : CatchRun tr H g (2 * sp.Δ)) (_hnr : NoRestartAfter tr H (gbar g))
    (_hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (_hδ : 3 ≤ sp.toParams.fg.δt) (_hG : 1 ≤ G)
    (_hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (_hgp : Healing.Growing.ProposalGap tr H proposer G s₀ N)
    (_hmb : sp.ts N + 2 * sp.Δ ≤ b) (_hH : (H b).Nonempty) (_hTb : T ≤ b)
    (_hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (r : Nat) {u : Nat} (_hwarm : s₀ + 2 * sp.k ≤ u)
    (_hN : u + r * (sp.toParams.fg.δt + G - 1) + 1 ≤ N)
    (_hT : sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ ≤ T)
    {z : Fin sp.n} (_hz : z ∈ H (sp.ts u + sp.Δ)) (_hdes : z = proposer u)
    {kP : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hP : tr.ProposesAt z kP P) (_hPs : P.slot = u)
    (_hrise : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + r),
    ∃ a, IsReset tr H g a ∧
      a ≤ sp.ts (u + r * (sp.toParams.fg.δt + G - 1) + 1 : Nat) + 2 * sp.Δ

/-- Original side: `Growing/Healing/Kernel/Boundaries.lean:75`; free `Ld`, bounded restarts. -/
def exists_reset_of_drain_rounds_awake_at_goldilocks : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g ΔF b r : Time} {G Ld : Nat}
    (_hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hcatch : CatchRun tr H g (2 * sp.Δ))
    (_hnr : Healing.Growing.NoRestartUpTo tr H (gbar g) b)
    (_hH : (H b).Nonempty) (_hδ : 3 ≤ sp.toParams.fg.δt)
    (_hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (_hr : 0 ≤ r) (_hgr : gbar g ≤ r) (_hG : 1 ≤ G)
    (_hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (_hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld ≤ b)
    (_hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld →
      Healing.Growing.ProposalGap tr H proposer G s₀ N)
    (_hdrain : Healing.Growing.DrainOutputs tr proposer H g G Ld b),
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld

/-- Public restatement of the private supplier at `Kernel/ResetRounds.lean:708`. -/
def goldilocksRun_truncH : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (b : Time),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg (fun t => {y | y ∈ H t ∧ t ≤ b}) tr

/-- Original side: `Growing/Healing/Outcome/RowSource.lean:107`. -/
def high_row_source_at_goldilocks {tr : GoldilocksTrace sp ro}
    {H : Time → Set (Fin sp.n)} : Prop := ∀
    (_hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g : Time}
    {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (_hv : v ∈ H (tr.time d)) (_hs : tr.SignAt v d att)
    (_hh : HZ tr H g + 1 ≤ att.h),
    ∃ r < d, ∃ l O, Healing.Growing.HighOrigin tr H g v r l O ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root

/-- Original side: `Growing/Healing/Outcome/Contest.lean:41`. -/
def no_high_contest_at_goldilocks : Prop := ∀ {g ΔF a b : Time}
    (_hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {i : Nat} (_hpH : p ∈ H (tr.time i)) (_hib : tr.time i ≤ b),
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)

/-- Original side: `Growing/Healing/RowService.lean:235`; arbitrary honesty bounds retained. -/
def high_entry_eq_at_goldilocks
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} : Prop := ∀ {g ΔF a b : Time}
    (_hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (_ho : Healing.Growing.HighOrigin tr H g x i j B) (_hib : tr.time i ≤ b)
    (_ho' : Healing.Growing.HighOrigin tr H g x' i' j' B') (_hi'b : tr.time i' ≤ b)
    (_h₁ : Anc (tr.HonestBlocksAt H) Z₁ B) (_h₂ : Anc (tr.HonestBlocksAt H) Z₂ B')
    {y₁ y₂ : Fin sp.n} {m₁ m₂ : Nat} {t₁ t₂ : Time}
    (_ht₁ : 0 ≤ t₁) (_hle₁ : ∀ q < m₁, tr.time q ≤ t₁) (_hy₁ : y₁ ∈ H t₁)
    (_ht₂ : 0 ≤ t₂) (_hle₂ : ∀ q < m₂, tr.time q ≤ t₂) (_hy₂ : y₂ ∈ H t₂)
    (_hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (_hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (_hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (_hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (_hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root), Z₁.root = Z₂.root

/-- UNPROVED grid equation used by the rise and finite-horizon endpoint bridges.
The numerical side is exactly `ResetRounds.lean:331` and `Boundaries.lean:83`.
The grid is the explicit premise of `Generic/Truncation.lean:110,126`; its cell length
is instantiated to `4 * P.Δ`, not an arbitrary slot duration. -/
def timeout_grid_equation {P : Params} : Prop :=
  ∀ (ΔF : Time),
    (∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) →
      ((∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) ↔
        6 * P.Δ + ΔF ≤ 4 * P.Δ * (P.δt : Time))

/-! Each consequent below universally closes the original target without changing its premises.
The full validator set is used: no committee or ready-majority restriction is added. -/

/-- UNPROVED full-set old-name implication; original source NoAdvance.lean:24. -/
def reset_of_height_advance_at_bridge : Prop :=
  reset_of_height_advance_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, reset_of_height_advance_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED upper half of the original range, NoAdvance.lean:60. -/
def hmax_le_of_noAdvance_at_bridge : Prop :=
  hmax_le_of_noAdvance_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, hmax_le_of_noAdvance_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED lower half of the original range, M1/FrameLag.lean:93. -/
def HZ_le_hmax_at_bridge : Prop :=
  HZ_le_hmax_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, HZ_le_hmax_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED full-set snapshot-call implication, DrainWarm.lean:70. -/
def snapshotCall_of_awake_at_bridge : Prop :=
  snapshotCall_of_awake_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, snapshotCall_of_awake_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED full-set call-lag implication, ResetRounds.lean:52. -/
def callLag_of_awake_at_bridge : Prop :=
  callLag_of_awake_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, callLag_of_awake_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED full-set high-source implication, ResetRounds.lean:141. -/
def reset_of_high_source_at_bridge : Prop :=
  reset_of_high_source_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, reset_of_high_source_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED full-set high-report implication, ResetRounds.lean:219. -/
def reset_of_high_report_at_bridge : Prop :=
  reset_of_high_report_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, reset_of_high_report_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED full-set proposal membership implication, ResetRounds.lean:251. -/
def proposal_mem_at_bridge : Prop :=
  proposal_mem_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, proposal_mem_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED real-time window implication, Boundaries.lean:29; not the slot-window endpoint. -/
def exists_frameWindow_seq_of_service_at_bridge : Prop :=
  exists_frameWindow_seq_of_service_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, exists_frameWindow_seq_of_service_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED report-row implication, Report/Row.lean:24.
The old consequent has no added report-tree membership premise. -/
def row_or_high_of_report_at_bridge : Prop :=
  row_or_high_of_report_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, row_or_high_of_report_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED crossing implication, Crossing.lean:22; both heights remain at the later proposer. -/
def round_cross_at_bridge : Prop :=
  round_cross_at (goldilocksNode sp ro) (fun v => v.val) →
    ∀ {proposer dg H tr}, round_cross_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED deficit implication, ResetRounds.lean:530. -/
def rounds_le_warm_proposal_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    rounds_le_warm_proposal_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, rounds_le_warm_proposal_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED report-kind implication, ResetRounds.lean:285. -/
def report_kind_of_warm_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    report_kind_of_warm_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, report_kind_of_warm_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED high-proposal implication, ResetRounds.lean:415; original arithmetic Warm retained. -/
def reset_of_high_proposal_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    reset_of_high_proposal_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, reset_of_high_proposal_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED round implication, ResetRounds.lean:320; no stronger timeout premise. -/
def round_of_warm_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    round_of_warm_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, round_of_warm_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED rise implication, ResetRounds.lean:457; original numerical timeout retained. -/
def rise_reset_rounds_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    rise_reset_rounds_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, rise_reset_rounds_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED finite-horizon endpoint implication, Boundaries.lean:75.
Free Ld, bounded NoRestartUpTo and the original resetBoundRounds remain in the consequent. -/
def exists_reset_of_drain_rounds_awake_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    exists_reset_of_drain_rounds_awake_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, exists_reset_of_drain_rounds_awake_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED high-row implication, Outcome/RowSource.lean:107. -/
def high_row_source_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    high_row_source_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg tr H}, high_row_source_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (tr := tr) (H := H)

/-- UNPROVED no-contest implication, Outcome/Contest.lean:41; old reset record unchanged. -/
def no_high_contest_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    no_high_contest_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, no_high_contest_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED historical-entry implication, RowService.lean:235.
Arbitrary observation times are retained. -/
def high_entry_eq_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksHealingData sp ro O →
    high_entry_eq_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {dg H tr proposer}, high_entry_eq_at_goldilocks (sp := sp) (ro := ro)
        (dg := dg) (H := H) (tr := tr) (proposer := proposer)

end Consensus.Goldilocks.Generic
