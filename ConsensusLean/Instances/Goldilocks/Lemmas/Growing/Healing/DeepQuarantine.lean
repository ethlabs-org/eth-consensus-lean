module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.StaticCoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Deep FG sources: the quarantine after `c_z`

With deep FG sources on (`deepDepth = some D`), `ac_to_fg` falls back to a deep candidate, whose
stamp at the caller is at most `t_{slot(t) − D}`. A block of state height `≥ H_z + 1` is held by no
node honest at `c_z` after all events at `c_z`, so an honest caller accepted it after `c_z`, and
its stamp is later than `c_z` (`cut_lt_blockStamp_of_late`). The two bounds exclude it as a deep
source until `c_z + 4DΔ` (equality included): before that, the source of a high report is a
fast-lock candidate (`high_toFG_fast_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- At an honest `ac_to_fg` call, a block other than genesis of the caller's tree that the caller
did not hold after any cut at a time `≤ c` has a stamp later than `c` (it was accepted at a later
cut, and a stamp is at least the acceptance time). -/
private theorem cut_lt_blockStamp_of_late {Hs : Set (Fin sp.n)} {T : GoldilocksTrace sp ro}
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    {u frameOf} (hrun : StaticRunCore u frameOf proposer dg Hs T ini)
    (hnc : Compose.NoCollRun dg T)
    {x : Fin sp.n} (hx : x ∈ Hs) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : T.projAC.CallAt x i ℓ) (hcall : ℓ.call = .toFG) {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hCt : C ∈ (T.state x i).fg.tree) (hg : C.root ≠ sp.genesisRoot) {c : Time}
    (hlate : ∀ k < i, T.time k ≤ c → C ∉ (T.state x (k + 1)).fg.tree) :
    AC.ETime.of c < (T.state x i).ac.blockStamp C.root := by
  have hacr := hrun.acRun hnc
  rcases hrun.tree_accepted x hx hCt with rfl | ⟨k, hki, hA⟩
  · exact absurd rfl hg
  obtain ⟨hA', ht', -⟩ := hrun.ac_block_after x hx hA
  obtain ⟨ℓ', hc', hcall'⟩ := hA'
  have hk1 : k + 1 < i := by
    rcases (Nat.succ_le_of_lt hki).lt_or_eq with h | h
    · exact h
    · subst h
      have hl := hc.2
      rw [hc'.2] at hl
      cases Option.some.inj hl
      rw [hcall'] at hcall
      cases hcall
  have hkc : c < T.time k := by
    by_contra hle
    exact hlate k hki (not_lt.1 hle) (hrun.accept_mem hx hA)
  have hge := Compose.blockStamp_ge_of_accept hacr.localRun hx
    ⟨ℓ', hc', hcall'⟩ hg i hk1
  rw [hrun.projAC_state x hx i] at hge
  change AC.ETime.of (T.time (k + 1)) ≤ _ at hge
  rw [ht'] at hge
  exact lt_of_lt_of_le (AC.etime_of_lt_of.2 hkc) hge

variable {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **The deep quarantine.** Before `c_z + 4DΔ` (for deep sources on at depth `D`), the source
that `ac_to_fg` returns at a node honest at it and at `c_z`, of state height `≥ H_z + 1`, is a
fast-lock candidate: a deep candidate there would be stamped after `c_z` (it is held by no node
honest at `c_z` after all events at `c_z`) and at most at `t_{slot(t) − D} ≤ c_z`. -/
theorem high_toFG_fast_at_core {ini u frameOf}
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time}
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    {z : Fin sp.n} {r : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time r)))
    {ell : ACLabel (goldilocksNode sp ro)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrep : AC.ToFGAt tr.projAC z r ell C)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h)
    (hq : ∀ D, sp.deepDepth = some D → tr.time r ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    C ∈ AC.toFGCandidates sp (tr.state z r).ac ell.frame (tr.time r) := by
  have hΔ := sp.toParams.hΔ
  have hm := hrun.time_mono
  have hz : z ∈ H (tr.time r) := hrun.antitone (le_max_right _ _) hzz
  have hzc : z ∈ H (cutZ sp.toParams g) := hrun.antitone (le_max_left _ _) hzz
  obtain ⟨hc, hcall, hC⟩ := hrep
  rw [hrun.projAC_state_at hz] at hC
  obtain ⟨hCv, hfast | ⟨D, a, hD, -, -, hdeep⟩⟩ := AC.toFG_source hC
  · exact hfast
  exfalso
  obtain ⟨j, hj⟩ := hsnap
  -- the prefix through `d = max c_z t_r`, a static run for the validators honest at `d`
  set d := max (cutZ sp.toParams g) (tr.time r) with hd
  have hd0 : 0 ≤ d := (hrun.time_nonneg r).trans (le_max_right _ _)
  have hrun' := hrun.upTo hd0
  have hnc' := hnc.upTo d
  have hst : ∀ m, (∀ k < m, tr.time k ≤ d) → (tr.upTo d).state z m = tr.state z m :=
    fun m h => Trace.upTo_state tr z h
  have hjd : ∀ k < j, tr.time k ≤ d := fun k hk => (hj.1 k hk).trans (le_max_left _ _)
  have hrd : ∀ k < r, tr.time k ≤ d := fun k hk => (hm hk.le).trans (le_max_right _ _)
  have hinj := (hrun'.acRun hnc').localRun.coherent.1
  have hreach : ∀ m, (∀ k < m, tr.time k ≤ d) →
      Store.ReachableWith u (goldilocksNode sp ro).genesisPayload (tr.state z m).fg := fun m h => by
    rw [← hst m h]; exact hrun'.reachable z hzz m
  -- `Σ.h_max` of `z` after all events at `c_z` is at most `H_z`
  have hHZ : (tr.state z j).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun y => (tr.state y j).fg.hmax).subset ?_).bddAbove)
      ⟨z, hzc, j, hj, rfl⟩
    rintro _ ⟨y, -, j', hj', rfl⟩
    obtain rfl := hj'.unique hj
    exact ⟨y, rfl⟩
  -- the frame's tree is the caller's
  have hfr := hrun.frame_of_projAC_at hz hc
  have hCt : C ∈ (tr.state z r).fg.tree := by
    have h := hdeep.1.1
    rw [hfr] at h
    exact ((hrun.frameOf_tree _ C).mp h).1
  -- no state of `z` after a cut at a time `≤ c_z` holds `C`
  have hlate : ∀ k < r, tr.time k ≤ cutZ sp.toParams g →
      C ∉ ((tr.upTo d).state z (k + 1)).fg.tree := by
    intro k hkr hk hCk
    have hkj : k + 1 ≤ j := by
      by_contra h
      have := hm (show j ≤ k by omega)
      linarith [hj.2]
    have hk1d : ∀ q < k + 1, tr.time q ≤ d := fun q hq => hrd q (by omega)
    rw [hst _ hk1d] at hCk
    obtain ⟨-, -, -, -, hge, -, -⟩ := Store.cache_invariants_with hrun.finalitySpec (hreach _ hk1d)
    have hmono := hrun'.hmax_mono hzz hkj
    simp only at hmono
    rw [hst _ hk1d, hst _ hjd] at hmono
    have hσ := Store.σ_eq_of_mem_with (hreach _ hk1d) hrun.finalitySpec (hreach r hrd) hinj
      (fun B hB => ⟨z, hzz, k + 1, by rw [hst _ hk1d]; exact hB⟩)
      (fun B hB => ⟨z, hzz, r, by rw [hst r hrd]; exact hB⟩) hCk hCt
    have := (hge C hCk).trans (hmono.trans hHZ)
    rw [hσ] at this
    omega
  have hc' : (tr.upTo d).projAC.CallAt z r ell := by
    rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le _ (le_max_right _ _)).mpr hc
  have hstamp := cut_lt_blockStamp_of_late hrun' hnc' hzz hc' hcall
    (by rw [hst r hrd]; exact hCt) hdeep.2.2.1 hlate
  rw [hst r hrd] at hstamp
  -- `t_{slot(t_r) − D} ≤ c_z`
  have hup := hdeep.2.2.2
  have hcz := Healing.cutZ_eq (sp := sp) g
  have htr := hq D hD
  have hle : sp.ts ((sp.slot (tr.time r) : Int) - D) ≤ cutZ sp.toParams g := by
    rw [hcz]
    apply (AC.ts_le_iff sp).2
    have h1 : tr.time r < sp.ts ((sp.slot (gbar g) + 3 + D + 1 : Nat) : Int) := by
      have : sp.ts ((sp.slot (gbar g) + 3 + D + 1 : Nat) : Int) =
          cutZ sp.toParams g + 4 * D * sp.Δ + 4 * sp.Δ := by
        rw [hcz]; simp only [ACParams.ts]; push_cast; ring
      linarith
    have h2 : (sp.slot (tr.time r) : Int) < (sp.slot (gbar g) + 3 + D + 1 : Nat) := by
      by_contra h
      have := ((AC.ts_le_iff_le_slot sp (hrun.time_nonneg r)) _).2 (not_lt.1 h)
      linarith
    push_cast at h2 ⊢
    omega
  have hlt : cutZ sp.toParams g < sp.ts ((sp.slot (tr.time r) : Int) - D) :=
    AC.etime_of_lt_of.1 (lt_of_lt_of_le hstamp hup)
  linarith

/-- Stock specialization of the finality-parametric deep quarantine. -/
theorem high_toFG_fast_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time}
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    {z : Fin sp.n} {r : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time r)))
    {ell : ACLabel (goldilocksNode sp ro)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrep : AC.ToFGAt tr.projAC z r ell C)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h)
    (hq : ∀ D, sp.deepDepth = some D → tr.time r ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    C ∈ AC.toFGCandidates sp (tr.state z r).ac ell.frame (tr.time r) :=
  high_toFG_fast_at_core hrun.toCore hnc hsnap hzz hrep hhC hq

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
