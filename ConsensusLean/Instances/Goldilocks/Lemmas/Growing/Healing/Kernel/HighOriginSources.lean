module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock

public section

/-! # High-origin sources independent of retained-vote induction

Raw heads and the snapshot cutoff use only historical local provenance. They
must remain below the retained-vote assembly in the import graph.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g : Time}
variable {hold : Time}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- `ts_le_of_fastLock_at` over the run-facts bundle. -/
theorem _root_.Consensus.Goldilocks.GoldilocksRunCore.ts_le_of_fastLock_at {ini}
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {x : Fin sp.n} {r l : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (hf : AC.FastLockAt tr.projAC x r l D CV) :
    sp.ts l ≤ tr.time r := by
  rcases hf with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hs, _⟩
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    rw [ht']
    have := sp.toParams.hΔ
    linarith
  · change sp.slot (tr.time r) = l at hs
    exact (AC.ts_le_iff_le_slot sp (rc.time_nonneg r) l).mpr (by omega)

/-- Every fast-lock write is at or after its label's slot start. -/
theorem ts_le_of_fastLock_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} {r l : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (hf : AC.FastLockAt tr.projAC x r l D CV) :
    sp.ts l ≤ tr.time r :=
  hrun.toCore.ts_le_of_fastLock_at hf

/-- `label_lt_of_old_at` over the run-facts bundle. -/
theorem _root_.Consensus.Goldilocks.GoldilocksRunCore.label_lt_of_old_at {ini}
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {x : Fin sp.n} {r l u' : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (ht : tr.time r < sp.ts u') : l < u' := by
  obtain ⟨_, _, ⟨CV, ell, D, _, hf, _⟩, _⟩ := ho
  exact_mod_cast (AC.ts_lt_iff sp).mp ((rc.ts_le_of_fastLock_at hf).trans_lt ht)

/-- An origin written strictly before a proposal's slot has a strictly older label. -/
theorem label_lt_of_old_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {x : Fin sp.n} {r l u : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (ht : tr.time r < sp.ts u) : l < u :=
  hrun.toCore.label_lt_of_old_at ho ht

/-- `highOrigin_raw_head_at` over the run-facts bundle. -/
theorem _root_.Consensus.Goldilocks.GoldilocksRunCore.highOrigin_raw_head_at {ini}
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {r l : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) :
    ∃ ell D CV, tr.projAC.CallAt x r ell ∧ AC.FastLockAt tr.projAC x r l D CV ∧
      Anc (tr.HonestBlocksAt H) O D := by
  obtain ⟨hxz, _, ⟨CV, ell, D, hc, hf, rfl⟩, _⟩ := ho
  have hx := rc.antitone (le_max_right _ _) hxz
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hf
  obtain rfl : ell = ell' := Option.some.inj (hc.2.symm.trans hc'.2)
  obtain ⟨hok, hsub⟩ := rc.frame_tree_subset_at hnc hx hc
  refine ⟨ell, D, CV, hc, hf, (AC.viableAncestor_anc hok hD).2.mono ?_⟩
  exact fun _ hB => ⟨x, r, tr.time r, rc.time_nonneg r,
    fun _ hq => rc.time_mono hq.le, hx, hsub hB⟩

/-- A high origin lies below its raw fast-lock head in the historical universe. -/
theorem highOrigin_raw_head_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {r l : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) :
    ∃ ell D CV, tr.projAC.CallAt x r ell ∧ AC.FastLockAt tr.projAC x r l D CV ∧
      Anc (tr.HonestBlocksAt H) O D :=
  hrun.toCore.highOrigin_raw_head_at hnc ho

variable {ΔF a b : Time}

/-- `cutZ_lt_of_anc_at` over the run-facts bundle. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.ResetRunCore.cutZ_lt_of_anc_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {z : Fin sp.n} {k : Nat}
    (hz : z ∈ H (max (tr.time k) (cutZ sp.toParams g)))
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z k).fg.tree)
    (hBW : Anc (tr.HonestBlocksAt H) B W) :
    cutZ sp.toParams g < tr.time k := by
  classical
  have rc := hp.core
  by_contra h
  have hkZ : tr.time k ≤ cutZ sp.toParams g := not_lt.mp h
  have hzZ : z ∈ H (cutZ sp.toParams g) := by
    rwa [max_eq_right hkZ] at hz
  have hZ0 : 0 ≤ cutZ sp.toParams g := (rc.time_nonneg k).trans hkZ
  have hhigh := hp.high_of_anc_at ho hZ0
    (fun _ hq => (rc.time_mono hq.le).trans hkZ) hzZ hW hBW
  obtain ⟨c, hc, _⟩ := hp.snapshot
  have hkc : k ≤ c := by
    by_contra hn
    exact (not_lt_of_ge hkZ) (hc.2.trans_le (rc.time_mono (by omega)))
  have hWc := rc.tree_mono_at hZ0 hzZ hc.1 hkc hW
  have hs := rc.σ_eq_honest_at hp.noColl hZ0
    (fun _ hq => (rc.time_mono hq.le).trans hkZ) hzZ hZ0 hc.1 hzZ hW hWc
  have hbnd := (Store.cache_invariants_with rc.finalitySpec
    (rc.reachable_at hZ0 hzZ hc.1)).2.2.2.2.1 W hWc
  have hmax : (tr.state z c).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun v => (tr.state v c).fg.hmax).subset ?_).bddAbove)
      ⟨z, hzZ, c, hc, rfl⟩
    rintro _ ⟨v, _, c', hc', rfl⟩
    obtain rfl := hc'.unique hc
    exact ⟨v, rfl⟩
  rw [← hs] at hbnd
  omega

/-- A high descendant cannot be held before the snapshot by a holder still honest there.
Honesty only at the earlier read would not suffice: that holder can disappear from HZ. -/
theorem cutZ_lt_of_anc_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) {z : Fin sp.n} {k : Nat}
    (hz : z ∈ H (max (tr.time k) (cutZ sp.toParams g)))
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z k).fg.tree)
    (hBW : Anc (tr.HonestBlocksAt H) B W) :
    cutZ sp.toParams g < tr.time k :=
  hp.toCore.cutZ_lt_of_anc_at ho hz hW hBW

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
