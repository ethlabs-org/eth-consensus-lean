module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HealedMembers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock

public section

/-! # Deep FG sources: the high-source cover accessor

A high report `C` of a node honest at its report and at `c_z` is either below a stored fast-lock
origin written before it (`high_report_origin_of_quarantine_at`, when the report is inside the
deep quarantine `t_r ≤ c_z + 4DΔ`), or the bundle's `deepCover` is the high-source cover and the
report is on the healed chain of the reset: after the quarantine the drain is over
(`HighSourceCover.drain_le`), so the source, fast or deep, is below a lock write past the drain
(`deep_source_on_healed_chain_at`). In the second case the cover's S1 and S2 are at hand. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {g ΔF a b : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time}

/-- **`E` is below a stored high origin, or covered.** Either `E` is below a high origin `B` (a
stored fast-lock write of a node honest at its write and at `c_z`) written by the horizon `b`, or
the high-source cover through `b` holds and `E` is on the healed chain of the reset `a` at its
floors. The common form every widened high-origin contract takes. -/
def HighOrCovered (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (g a b : Time)
    (E : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  (∃ x i j B, HighOrigin tr H g x i j B ∧ tr.time i ≤ b ∧ Anc (tr.HonestBlocksAt H) E B) ∨
  (HighSourceCover tr H g a b ∧
    Compose.Growing.OnHealedChain tr H g (healedLockFloor sp a) (healedOriginFloor sp a) E b)

theorem highOrCovered_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {g a b : Time}
    {E : AC.Blk sp.n (List (FG.Att sp.n))} :
    HighOrCovered tr H g a b E ↔
      ((∃ x i j B, HighOrigin tr H g x i j B ∧ tr.time i ≤ b ∧ Anc (tr.HonestBlocksAt H) E B) ∨
      (HighSourceCover tr H g a b ∧
        Compose.Growing.OnHealedChain tr H g (healedLockFloor sp a) (healedOriginFloor sp a) E
          b)) :=
  Iff.rfl

/-- **`E` is covered up to the label `m`**: the high-source cover through `b` holds and `E` is
below a member of the healed family of the reset `a` (at its floors) of label at most `m`. The
label-bounded cover arm of a widened high-origin contract: S2 extends such a member by the honest
votes of every slot after `m`. -/
def CoveredUpTo (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (g a b : Time) (m : Nat)
    (E : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  HighSourceCover tr H g a b ∧ ∃ C s,
    Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C s b ∧
      s ≤ m ∧ Anc (tr.HonestBlocksAt H) E C

theorem coveredUpTo_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {g a b : Time}
    {m : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))} :
    CoveredUpTo tr H g a b m E ↔ HighSourceCover tr H g a b ∧ ∃ C s,
      Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C s b ∧
        s ≤ m ∧ Anc (tr.HonestBlocksAt H) E C :=
  Iff.rfl

/-- **A member of the healed family written before the cut `k`**: an origin of label at least the
origin floor, a lock write of label at least the lock floor, or a high origin, each at a cut
before `k` and a time `≤ b`. -/
def HealedMemberBefore (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (g a b : Time)
    (C : AC.Blk sp.n (List (FG.Att sp.n))) (s k : Nat) : Prop :=
  (healedOriginFloor sp a ≤ s ∧ ∃ x i CV, i < k ∧ x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      (AC.ResultAt tr.projAC x i s C CV ∨ AC.OptimisticLockAt tr.projAC x i s C CV)) ∨
  (healedLockFloor sp a ≤ s ∧ ∃ x i, i < k ∧ x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
      ((∃ CV, AC.FastLockAt tr.projAC x i s C CV) ∨ AC.SlowLockAt tr.projAC x i s C)) ∨
  ∃ x i, i < k ∧ tr.time i ≤ b ∧ HighOrigin tr H g x i s C

theorem healedMemberBefore_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {g a b : Time} {C : AC.Blk sp.n (List (FG.Att sp.n))} {s k : Nat} :
    HealedMemberBefore tr H g a b C s k ↔
      (healedOriginFloor sp a ≤ s ∧ ∃ x i CV, i < k ∧ x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
          (AC.ResultAt tr.projAC x i s C CV ∨ AC.OptimisticLockAt tr.projAC x i s C CV)) ∨
      (healedLockFloor sp a ≤ s ∧ ∃ x i, i < k ∧ x ∈ H (tr.time i) ∧ tr.time i ≤ b ∧
          ((∃ CV, AC.FastLockAt tr.projAC x i s C CV) ∨ AC.SlowLockAt tr.projAC x i s C)) ∨
      ∃ x i, i < k ∧ tr.time i ≤ b ∧ HighOrigin tr H g x i s C :=
  Iff.rfl

/-- A member written before `k` is a member of the healed family. -/
theorem HealedMemberBefore.healedOrigin {C : AC.Blk sp.n (List (FG.Att sp.n))} {s k : Nat}
    (h : HealedMemberBefore tr H g a b C s k) :
    Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C s b := by
  rcases h with ⟨hs, x, i, CV, -, hx, hib, h⟩ | ⟨hs, x, i, -, hx, hib, h⟩ | ⟨x, i, -, hib, ho⟩
  · exact Compose.Growing.healedOrigin_iff.2
      (Or.inl ⟨hs, Compose.Growing.originWithin_iff.2 ⟨x, i, CV, hx, hib, h⟩⟩)
  · exact Compose.Growing.healedOrigin_iff.2 (Or.inr (Or.inl ⟨hs,
      Compose.Growing.lockWithin_iff.2 ⟨x, i, hx, hib, h⟩⟩))
  · exact Compose.Growing.HealedOrigin.of_high hib ho

/-- A member written before `k` is written before every later cut. -/
theorem HealedMemberBefore.mono {C : AC.Blk sp.n (List (FG.Att sp.n))} {s k k' : Nat}
    (h : HealedMemberBefore tr H g a b C s k) (hk : k ≤ k') :
    HealedMemberBefore tr H g a b C s k' := by
  rcases h with ⟨hs, x, i, CV, hi, h⟩ | ⟨hs, x, i, hi, h⟩ | ⟨x, i, hi, h⟩
  · exact Or.inl ⟨hs, x, i, CV, by omega, h⟩
  · exact Or.inr (Or.inl ⟨hs, x, i, by omega, h⟩)
  · exact Or.inr (Or.inr ⟨x, i, by omega, h⟩)

/-- **`E` is covered up to the label `m` by a member written before the cut `k`**: the
cut-indexed form of `CoveredUpTo`. -/
def CoveredBefore (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (g a b : Time)
    (m k : Nat) (E : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  HighSourceCover tr H g a b ∧ ∃ C s, HealedMemberBefore tr H g a b C s k ∧ s ≤ m ∧
    Anc (tr.HonestBlocksAt H) E C

theorem coveredBefore_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {g a b : Time} {m k : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))} :
    CoveredBefore tr H g a b m k E ↔ HighSourceCover tr H g a b ∧ ∃ C s,
      HealedMemberBefore tr H g a b C s k ∧ s ≤ m ∧ Anc (tr.HonestBlocksAt H) E C :=
  Iff.rfl

/-- A block covered before `k` is covered. -/
theorem CoveredBefore.coveredUpTo {m k : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredBefore tr H g a b m k E) : CoveredUpTo tr H g a b m E :=
  let ⟨hc, C, s, hC, hs, hEC⟩ := h
  ⟨hc, C, s, hC.healedOrigin, hs, hEC⟩

/-- A block covered before `k` is covered before every later cut and at every larger label. -/
theorem CoveredBefore.mono {m m' k k' : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredBefore tr H g a b m k E) (hm : m ≤ m') (hk : k ≤ k') :
    CoveredBefore tr H g a b m' k' E :=
  let ⟨hc, C, s, hC, hs, hEC⟩ := h
  ⟨hc, C, s, hC.mono hk, hs.trans hm, hEC⟩

/-- A block below a block covered before `k` is covered before `k`. -/
theorem CoveredBefore.of_anc {m k : Nat} {B E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredBefore tr H g a b m k E) (hBE : Anc (tr.HonestBlocksAt H) B E) :
    CoveredBefore tr H g a b m k B :=
  let ⟨hc, C, s, hC, hs, hEC⟩ := h
  ⟨hc, C, s, hC, hs, hBE.trans hEC⟩

/-- A covered block is covered at every larger label. -/
theorem CoveredUpTo.mono {m m' : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredUpTo tr H g a b m E) (hm : m ≤ m') : CoveredUpTo tr H g a b m' E :=
  let ⟨hc, C, s, hC, hs, hEC⟩ := h
  ⟨hc, C, s, hC, hs.trans hm, hEC⟩

/-- A block below a covered block is covered. -/
theorem CoveredUpTo.of_anc {m : Nat} {B E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredUpTo tr H g a b m E) (hBE : Anc (tr.HonestBlocksAt H) B E) :
    CoveredUpTo tr H g a b m B :=
  let ⟨hc, C, s, hC, hs, hEC⟩ := h
  ⟨hc, C, s, hC, hs, hBE.trans hEC⟩

/-- A covered block is on the healed chain: the right arm of `HighOrCovered`. -/
theorem CoveredUpTo.onHealedChain {m : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredUpTo tr H g a b m E) :
    Compose.Growing.OnHealedChain tr H g (healedLockFloor sp a) (healedOriginFloor sp a) E b :=
  let ⟨_, C, s, hC, _, hEC⟩ := h
  Compose.Growing.onHealedChain_iff.2 ⟨C, s, hC, hEC⟩

/-- `CoveredUpTo.compatible_highOrigin` over the run-facts bundle. -/
theorem _root_.Consensus.Goldilocks.GoldilocksRunCore.compatible_highOrigin_of_covered
    {uf : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))} {ini}
    (rc : GoldilocksRunCore uf frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {m : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredUpTo tr H g a b m E) {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hib : tr.time i ≤ b)
    (ho : HighOrigin tr H g x i j B) : Compatible (tr.HonestBlocksAt H) E B :=
  let ⟨hc, C, s, hC, _, hEC⟩ := h
  Compose.Growing.compatible_of_anc_left (rc.coherent hnc) hEC
    (hc.s1 C s B j hC (Compose.Growing.HealedOrigin.of_high hib ho))

/-- **A covered block is compatible with every high origin written by `b`** (S1, the high
origin being a member of the healed family). -/
theorem CoveredUpTo.compatible_highOrigin {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {m : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredUpTo tr H g a b m E) {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hib : tr.time i ≤ b)
    (ho : HighOrigin tr H g x i j B) : Compatible (tr.HonestBlocksAt H) E B :=
  hrun.toCore.compatible_highOrigin_of_covered hnc h hib ho

/-- **A high report is a stored high origin, or on the healed chain under the cover.** For a high
report `C` of a node honest at its report and at `c_z`, within `b`: either the quarantine form of
`high_report_origin_of_quarantine_at` holds, or the bundle carries the high-source cover and `C` is
on the healed chain of the reset `a` at its floors. -/
theorem ResetPremisesUpTo.high_source_cover_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {r : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time r)))
    {ell : ACLabel (goldilocksNode sp ro)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrep : AC.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h) :
    (∃ io < r, ∃ jo O D CV, HighOrigin tr H g z io jo O ∧ tr.time io ≤ b ∧
        AC.FastLockAt tr.projAC z io jo D CV ∧ Anc (tr.HonestBlocksAt H) C O ∧
        Anc (tr.HonestBlocksAt H) O D) ∨
    (HighSourceCover tr H g a b ∧
      Compose.Growing.OnHealedChain tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C
        b) := by
  by_cases hq : ∀ D, sp.deepDepth = some D → tr.time r ≤ cutZ sp.toParams g + 4 * D * sp.Δ
  · exact Or.inl (hp.high_report_origin_of_quarantine_at hzz hrep hrb hhC hq)
  right
  push Not at hq
  obtain ⟨D, hD, hlt⟩ := hq
  rcases hp.deepCover D hD with hbq | hc
  · exact absurd (hrb.trans hbq) (not_le.2 hlt)
  have hΔ := sp.toParams.hΔ
  have hdrain := hc.drain_le D hD
  refine ⟨hc, Compose.Growing.deep_source_on_healed_chain_at hp.run hp.noColl
    (hp.run.antitone (le_max_right _ _) hzz) ?_ hrb hrep⟩
  linarith

/-- **A high report is `HighOrCovered`**: the report `C` of a node honest at its report and at
`c_z`, within `b`, is below a stored high origin, or on the healed chain under the cover. -/
theorem ResetPremisesUpTo.high_or_covered_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {r : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time r)))
    {ell : ACLabel (goldilocksNode sp ro)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrep : AC.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h) :
    HighOrCovered tr H g a b C := by
  rcases hp.high_source_cover_at hzz hrep hrb hhC with
    ⟨_, _, _, O, _, _, ho, hiob, _, hCO, _⟩ | hc
  · exact Or.inl ⟨z, _, _, O, ho, hiob, hCO⟩
  · exact Or.inr hc

end Consensus.Goldilocks.Healing.Growing

end
