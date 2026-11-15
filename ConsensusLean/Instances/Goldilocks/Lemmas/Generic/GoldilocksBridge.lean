module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.CorrectnessEdges
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # Goldilocks old-premise bridge statements

The shared run interface supplies the canonical committee start and its run laws. The remaining
unproved Prop contracts give Goldilocks-side targets and connect them
to the generic contracts by conditional implications; they supply no healing evidence.
These targets use committee-indexed starts, positive matching committee sizes, and membership
facts under collision freedom. Population FG fault bounds remain population bounds; committee
fault bounds are separate. The concrete stock proofs need in-place committee generalisation.

This leaf has an isolated concrete bridge proof closure, not a vocabulary-only closure.
`Kernel.Boundaries` supplies `FrameWindow`, `ProposalGap`, `DrainOutputs`, `NoRestartUpTo`,
`frameKey'`, `riseRounds`, and `Obligations.resetBoundRounds` used below.
`Report.Row` supplies the concrete report-row vocabulary.
`RowService` supplies `ResetPremisesUpTo.high_entry_eq_at` and the retained-origin vocabulary
`ResetPremisesUpTo` and `HighOrigin`, with committee-aware reset premises below.
Generic statements do not import this concrete proof closure. The run transport and
concrete sleepy adapters read `goldilocksRunInterface` from it.

No old name: `exists_reset`, `generic_healing`, `highCanonical`, the slot-form
`exists_frameWindow`, and `sign_from_report`.
-/

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder Payload gbar)
open Healing Healing.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The shared Goldilocks run interface, starting each node with its committee permission. -/
noncomputable def goldilocksRunInterface (sp : SAParams)
    (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    ACRun (goldilocksNode sp ro) (fun v => v.val) where
  Run cm proposer dg H tr := Growing.GoldilocksRun proposer dg H tr
    (SA.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
    0 < sp.committeeSize ∧
    (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
    (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm))
  start cm := SA.committeeStart sp.genesisRoot (dictOfTime sp cm)
  start_univ := by
    have h : dictOfTime sp (fun _ => Finset.univ) = SA.CommitteeDict.full sp.n := by
      simp [dictOfTime, SA.CommitteeDict.full]
    rw [h]
    exact SA.committeeStart_full _
  run_local h := h.1.toLocalRun
  run_requirements h y := Compose.requirements_from sp ro (h.1.vstart y)
  run_root h := h.1.genesis_root_ok

/-- The run projection uses the committee-indexed initial AC states. -/
theorem goldilocksRunInterface_run_iff (cm : Time → Finset (Fin sp.n)) :
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr ↔
      Growing.GoldilocksRun proposer dg H tr
        (SA.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
      0 < sp.committeeSize ∧
      (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
      (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm)) := by rfl

/-- Source: `Healing.Growing.reset_of_height_advance_at` in Kernel/NoAdvance. -/
def reset_of_height_advance_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    {g : Time} {y : Fin sp.n} {k : Nat}
    (_hq : (H (max (cutZ sp.toParams g) (tr.time k)))ᶜ.ncard < sp.toParams.fg.q)
    (_hy : y ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    {att : FG.Att sp.n} (_hs : tr.SignAt y k att) (_hh : HZ tr H g + 1 ≤ att.h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k

/-- Source: `Healing.Growing.hmax_le_of_noAdvance_at`, upper range bound. -/
def hmax_le_of_noAdvance_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr) {g T : Time}
    (_hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (_hy : y ∈ H (tr.time i))
    (_hq : (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard < sp.toParams.fg.q)
    (_hiT : tr.time i < T),
    (tr.state y i).fg.hmax ≤ HZ tr H g + 1

/-- Original side: `Growing/Healing/Kernel/DrainWarm.lean:70`. -/
def snapshotCall_of_awake_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr) {g b : Time}
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    {z : Fin sp.n} {m : Nat} (_hz : z ∈ H (tr.time m))
    (_hfit : cutZ sp.toParams g + sp.Δ + 1 ≤ tr.time m) (_hmb : tr.time m ≤ b),
    (∃ j, FirstCutAfter tr j (cutZ sp.toParams g)) ∧
      ∃ j < m, tr.IsCall z j ∧
        tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j

/-- Source: `Healing.Growing.callLag_of_awake_at` in Kernel/ResetRounds. -/
def callLag_of_awake_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr) {g b lo : Time}
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hlo : cutZ sp.toParams g ≤ lo) {z : Fin sp.n} {i m : Nat}
    (_hz : z ∈ H (tr.time m)) (_hi : lo ≤ tr.time i)
    (_him : tr.time i + 2 * sp.Δ ≤ tr.time m) (_hmb : tr.time m ≤ b),
    ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j

/-- Specialization of the generic high-source reset leaf to Goldilocks. -/
def reset_of_high_source_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr) {g : Time}
    {y : Fin sp.n} {k : Nat} (_hy : y ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    (_hq : (H (max (cutZ sp.toParams g) (tr.time k)))ᶜ.ncard < sp.toParams.fg.q)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Option (FG.Att sp.n)}
    (_hc : tr.CallAt y k (.fg (.attest C s)))
    (_hh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k

/-- Source: `Healing.Growing.reset_of_high_report_at` in Kernel/ResetRounds. -/
def reset_of_high_report_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr) {g : Time}
    {y : Fin sp.n} {i : Nat} (_hy : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (_hq : (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard < sp.toParams.fg.q)
    {ell : ACLabel (goldilocksNode sp ro)} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hR : SA.ToFGAt tr.projAC y i ell R)
    (_hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time i

/-- Original side: `Growing/Healing/Report/Row.lean:24`; no added tree premise. -/
def row_or_high_of_report_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g T : Time}
    (_hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (_hy : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
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

/-- Source: `Healing.Growing.rounds_le_warm_proposal_at` in Kernel/ResetRounds. -/
def rounds_le_warm_proposal_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
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

/-- Source: `Healing.Growing.report_kind_of_warm_at` in Kernel/ResetRounds. -/
def report_kind_of_warm_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
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

/-- Source: `Healing.Growing.reset_of_high_proposal_at` in Kernel/ResetRounds. -/
def reset_of_high_proposal_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hβ : βK ≤ 1 / 2) (_hcommittee : CommitteeFaultsUpTo βK cm H g b)
    (_hframe : Healing.Growing.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) (_hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hcatch : CatchRun tr H g (2 * sp.Δ)) (_hnr : NoRestartAfter tr H (gbar g))
    (_htimeout : ∀ s, sp.ts s + 6 * sp.Δ + ΔF ≤ sp.ts (s + sp.toParams.δt))
    (_hsnapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b)
    (_hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (_hsu : s₀ ≤ u) (_hwarm : s₀ + 2 * sp.k ≤ u)
    (_hN : u + 1 ≤ N) (_hmb : sp.ts N + 2 * sp.Δ ≤ b) (_hH : (H b).Nonempty)
    {z : Fin sp.n} (_hz : z ∈ H (sp.ts u + sp.Δ)) (_hdes : z = proposer u)
    {kP : Nat} (_hP : tr.ProposesAt z kP P) (_hPs : P.slot = u)
    (_hh : HZ tr H g + 1 ≤ ((tr.state z (kP + 1)).fg.σ P.root).h),
    ∃ a, IsReset tr H g a ∧ a ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ

/-- Source: `Healing.Growing.round_of_warm_at`; both heights at `p`. -/
def round_of_warm_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF b T : Time} {s₀ u x N floor : Nat} {kindJ : Prop}
    {J P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hβ : βK ≤ 1 / 2) (_hcommittee : CommitteeFaultsUpTo βK cm H g b)
    (_hframe : Healing.Growing.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) (_hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hcatch : CatchRun tr H g (2 * sp.Δ)) (_hnr : NoRestartAfter tr H (gbar g))
    (_hsnapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b)
    (_hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (_hsu : s₀ ≤ u) (_hwarm : s₀ + 2 * sp.k ≤ u)
    (_hδ : 3 ≤ sp.toParams.fg.δt)
    (_hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (_hux : u + sp.toParams.fg.δt ≤ x) (_hxN : x ≤ N) (_hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (_hH : (H b).Nonempty) (_hTb : T ≤ b)
    (_hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (_hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ < T)
    {z : Fin sp.n} (_hz : z ∈ H (sp.ts u + sp.Δ)) (_hdes : z = proposer u)
    {kP : Nat} (_hP : tr.ProposesAt z kP P) (_hPs : P.slot = u)
    {p : Fin sp.n} {kX : Nat} (_hp : p ∈ H (tr.time kX)) (_hdx : p = proposer x)
    (_hX : tr.ProposesAt p kX X) (_hXs : X.slot = x),
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h

/-- Source: `Healing.Growing.rise_reset_rounds_at` in Kernel/ResetRounds. -/
def rise_reset_rounds_at_goldilocks : Prop := ∀
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {g ΔF b T : Time} {s₀ N G floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hβ : βK ≤ 1 / 2) (_hcommittee : CommitteeFaultsUpTo βK cm H g b)
    (_hframe : Healing.Growing.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) (_hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (_hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (_hcatch : CatchRun tr H g (2 * sp.Δ)) (_hnr : NoRestartAfter tr H (gbar g))
    (_hsnapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b)
    (_hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (_hδ : 3 ≤ sp.toParams.fg.δt) (_hG : 1 ≤ G)
    (_hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (_hgp : Healing.Growing.ProposalGap tr H proposer G s₀ N)
    (_hmb : sp.ts N + 2 * sp.Δ ≤ b) (_hH : (H b).Nonempty) (_hTb : T ≤ b)
    (_hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    (r : Nat) {u : Nat} (_hsu : s₀ ≤ u) (_hwarm : s₀ + 2 * sp.k ≤ u)
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
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    (_hnc : Compose.NoCollRun dg tr) {g ΔF b r : Time} {G Ld : Nat}
    (_hβ : βK ≤ 1 / 2) (_hcommittee : CommitteeFaultsUpTo βK cm H g b)
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

/-- Conditional high-row bridge corresponding to
`Growing/Healing/Outcome/RowSource.high_row_source_at`. The earlier-origin conclusion and historical
honesty charge are retained, but this target uses the committee-valid run interface and additionally
assumes `βK ≤ 1/2`, `Premises`, `IsReset` at `a ≤ b`, and the signing cutoff `tr.time d ≤ b`. It
proves the conclusion under these added premises, not under the original concrete theorem's
premises. -/
def high_row_source_at_goldilocks {tr : GoldilocksTrace sp ro}
    {H : Time → Set (Fin sp.n)} : Prop := ∀
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {g ΔF a b : Time}
    (_hβ : βK ≤ 1 / 2)
    (_hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    (_hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b)
    (_hr : IsReset tr H g a) (_hab : a ≤ b)
    {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (_hv : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (_hdb : tr.time d ≤ b)
    (_hs : tr.SignAt v d att)
    (_hh : HZ tr H g + 1 ≤ att.h),
    ∃ r < d, ∃ l O, Healing.Growing.HighOrigin tr H g v r l O ∧
      ∃ E ∈ (tr.state v r).fg.tree, (tr.state v r).fg.Anc E O ∧
        E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
        ((tr.state v r).fg.σ E.root).Th = E.root

/-- Original side: `Outcome.no_high_contest_at`. -/
def no_high_contest_at_goldilocks : Prop := ∀ {g ΔF a b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (_hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {p : Fin sp.n} {i : Nat} (_hpH : p ∈ H (tr.time i)) (_hib : tr.time i ≤ b),
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax)

/-- Original side: `ResetPremisesUpTo.high_entry_eq_at`; arbitrary honesty bounds retained. -/
def high_entry_eq_at_goldilocks
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} : Prop := ∀ {g ΔF a b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (_hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) {x x' : Fin sp.n}
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

/-! Each consequent below universally closes its committee-indexed target. Historical signing
is charged at the maximum of the snapshot and event time. No ready-majority premise is added. -/

/-- UNPROVED implication for `Healing.Growing.reset_of_height_advance_at`. -/
def reset_of_height_advance_at_bridge : Prop :=
  reset_of_height_advance_at (goldilocksNode sp ro) (fun v => v.val)
    (goldilocksRunInterface sp ro) →
    ∀ {proposer dg H tr}, reset_of_height_advance_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED upper bound for `Healing.Growing.hmax_le_of_noAdvance_at`. -/
def hmax_le_of_noAdvance_at_bridge : Prop :=
  hmax_le_of_noAdvance_at (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro) →
    ∀ {proposer dg H tr}, hmax_le_of_noAdvance_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED snapshot-call implication at `goldilocksRunInterface`, DrainWarm.lean:70. -/
def snapshotCall_of_awake_at_bridge : Prop :=
  snapshotCall_of_awake_at (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro) →
    ∀ {proposer dg H tr}, snapshotCall_of_awake_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED implication for `Healing.Growing.callLag_of_awake_at`. -/
def callLag_of_awake_at_bridge : Prop :=
  callLag_of_awake_at (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro) →
    ∀ {proposer dg H tr}, callLag_of_awake_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED specialization of the generic high-source reset leaf. -/
def reset_of_high_source_at_bridge : Prop :=
  reset_of_high_source_at (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro) →
    ∀ {proposer dg H tr}, reset_of_high_source_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED implication for `Healing.Growing.reset_of_high_report_at`. -/
def reset_of_high_report_at_bridge : Prop :=
  reset_of_high_report_at (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro) →
    ∀ {proposer dg H tr}, reset_of_high_report_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED report-row implication, Report/Row.lean:24.
The old consequent has no added report-tree membership premise. -/
def row_or_high_of_report_at_bridge : Prop :=
  row_or_high_of_report_at (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro) →
    ∀ {proposer dg H tr}, row_or_high_of_report_at_goldilocks (sp := sp) (ro := ro)
      (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED implication for `Healing.Growing.rounds_le_warm_proposal_at`. -/
def rounds_le_warm_proposal_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    rounds_le_warm_proposal_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, rounds_le_warm_proposal_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED implication for `Healing.Growing.report_kind_of_warm_at`. -/
def report_kind_of_warm_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    report_kind_of_warm_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, report_kind_of_warm_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED high-proposal implication; the original arithmetic Warm premise is retained. -/
def reset_of_high_proposal_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    GoldilocksHealingData sp ro O →
    reset_of_high_proposal_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, reset_of_high_proposal_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED round implication; the numerical timeout premise is retained. -/
def round_of_warm_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    GoldilocksHealingData sp ro O →
    round_of_warm_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, round_of_warm_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED rise implication; the original numerical timeout premise is retained. -/
def rise_reset_rounds_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    GoldilocksHealingData sp ro O →
    rise_reset_rounds_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, rise_reset_rounds_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED finite-horizon endpoint implication, Boundaries.lean:75.
Free Ld, bounded NoRestartUpTo and the original resetBoundRounds remain in the consequent. -/
def exists_reset_of_drain_rounds_awake_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    GoldilocksHealingData sp ro O →
    exists_reset_of_drain_rounds_awake_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, exists_reset_of_drain_rounds_awake_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED high-row implication, Outcome/RowSource.lean:107. -/
def high_row_source_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    GoldilocksHealingData sp ro O →
    high_row_source_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg tr H}, high_row_source_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (tr := tr) (H := H)

/-- UNPROVED no-contest implication, Outcome/Contest.lean:41; committee-aware reset record. -/
def no_high_contest_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    no_high_contest_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {proposer dg H tr}, no_high_contest_at_goldilocks (sp := sp) (ro := ro)
        (proposer := proposer) (dg := dg) (H := H) (tr := tr)

/-- UNPROVED historical-entry implication, RowService.lean:235.
Arbitrary observation times are retained. -/
def high_entry_eq_at_bridge : Prop :=
  ∀ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) (goldilocksRunInterface sp ro),
    GoldilocksHealingData sp ro O →
    high_entry_eq_at (goldilocksNode sp ro) (fun v => v.val) O →
      ∀ {dg H tr proposer}, high_entry_eq_at_goldilocks (sp := sp) (ro := ro)
        (dg := dg) (H := H) (tr := tr) (proposer := proposer)

end Consensus.Goldilocks.Generic
