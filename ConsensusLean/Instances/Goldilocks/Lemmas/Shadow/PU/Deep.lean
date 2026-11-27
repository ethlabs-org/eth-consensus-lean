module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireSources
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.DeepQuarantine
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports

public section

/-! # Deep FG sources over the P-U shadow node (V-B10, D3(c))

Under D3(c) the shadow frame `Node.frame'` keeps `toFGCandidates` and `toFGDeepCandidates`
unchanged, read over `toFrame'`: in top-`J` frames the path blocks between `F` and `J` become
candidates, and a path fast candidate can pre-empt the deep arm. The stock proofs read the sources
only through frame-generic facts: the source split `AC.toFG_source`, the frame's tree (the same set
for `toFrame'` and `toFrame`), the AC lock invariant over lawful frames, and the fast arm firing
when a fast candidate exists. No proof needs the deep arm to fire. The proofs below are therefore
the stock ones over `GoldilocksRun'`.

The AC projection `Compose.goldilocks_ac_projection_from'` (B0b, `Shadow/PU/ACProjection`) still
rests on pending suppliers there: a theorem reading it is unresolved (`sorryAx`) until they land.
-/

namespace Consensus.Goldilocks.Shadow.PU

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- A source of an honest node is in its FG tree (`Healing.toFG_mem_tree`): the shadow frame's
tree is the store's tree above `F`. -/
theorem toFG_mem_tree' (hrun : GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode' sp ro)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hto : AC.ToFGAt tr.projAC y k ℓ C) : C ∈ (tr.state y k).fg.tree := by
  have h := Healing.toFG_mem_frame hto.2.2
  rw [Node.frame_of_projAC_at' hrun.toLocalRun' hy hto.1, Node.frame'_eq,
    Store.toFrame'_tree] at h
  exact h.1

/-- **Candidates at one honest call are compatible** (`Healing.toFG_candidates_compatible_at_call`),
path candidates included: the AC lock invariant holds for every lawful frame. -/
theorem toFG_candidates_compatible_at_call' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y i ell)
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) :
    ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Compatible (tr.HonestBlocks H) C P := by
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnc).localRun
  have hPhi := AC.frameIn_of_callAt hr hy hc
  obtain ⟨Phi, t, hreach, _, hok⟩ := Compose.pre_reachable hr hy hc
  obtain ⟨hin, _, hinv⟩ := AC.lockInv_of_reachable hr.coherent (hrun.vstart y) hreach
  have hinv' := hinv.callOK hr.coherent hin hok
  have hlock {B : AC.Blk sp.n (List (FG.Att sp.n))}
      (hB : B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) :
      B ∈ AC.liveLockBlocks sp (tr.projAC.state y i).locks ell.frame (tr.time i) := by
    obtain ⟨hv, l, hl, hr, _⟩ := hB
    exact ⟨hv.1, l, hl, hr⟩
  intro C hC
  exact (hinv'.liveBlocks_chain hr.coherent hPhi.1 hPhi.2 C (hlock hC) P (hlock hP)).elim
    (fun h => Or.inl (Anc.mono hPhi.2 h)) (fun h => Or.inr (Anc.mono hPhi.2 h))

/-- With a fast-lock candidate, `ac_to_fg` considers the deepest one, deep sources on or off. -/
private theorem fgSource_of_fast {FGP : Type} {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    {t : Time} {C : AC.Blk sp.n FGP}
    (h : AC.deepest Φ (AC.toFGCandidates sp A Φ t) = some C) :
    AC.fgSource sp A Φ t = some C := by
  unfold AC.fgSource
  split <;> simp [h]

/-- A deepest candidate extending a non-genesis block gives an actual report by this call's
time (`Healing.report_of_deepest_candidate_of_run`). -/
theorem report_of_deepest_candidate_of_run'
    (hrun : GoldilocksRun' proposer dg H tr ini) (hnoColl : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : AC.joined sp (tr.projAC.state y j) (tr.time j))
    {P C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPg : P.root ≠ sp.genesisRoot)
    (hC : AC.deepest ell.frame (AC.toFGCandidates sp (tr.projAC.state y j)
      ell.frame (tr.time j)) = some C) (hPC : ell.frame.Anc P C) :
    ∃ r ell' R, AC.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnoColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc
  by_cases hrep : AC.AncR ell.frame C (tr.projAC.state y j).fgReported
  · obtain ⟨R, hRt, hRr, hCR⟩ := hrep
    have hPR : ell.frame.Anc P R := hPC.trans hCR
    rcases Healing.fgReported_origin hr hrun.vstart hy j with hgen | ⟨r, hrj, ell', R', hto, hR'r⟩
    · have hG := Store.genesis_mem_with Store.finalitySpec_updateFinality'
        (Node.fg_reachable_at' hrun.toLocalRun' hy j).reachableWith
      have he := hr.coherent.1 (hPhiU hRt) ⟨y, hy, j, hG⟩ (hRr.trans hgen)
      rw [he] at hPR
      rcases Relation.ReflTransGen.cases_tail hPR with heq | ⟨Y, _, hY⟩
      · exact False.elim (hPg (by rw [← heq]; rfl))
      · exact False.elim (Option.some_ne_none _ (hY.2.2.symm.trans rfl))
    have hR't := toFG_mem_tree' hrun hy hto
    obtain rfl : R' = R := hr.coherent.1 ⟨y, hy, r, hR't⟩ (hPhiU hRt)
      (hR'r.trans hRr.symm)
    exact ⟨r, ell', R', hto, hrun.time_mono hrj.le, hPR.mono hPhiU⟩
  · refine ⟨j, ell, C, ⟨hc, hcall, ?_⟩, le_rfl, hPC.mono hPhiU⟩
    change (AC.acToFG sp (tr.projAC.state y j) ell.frame (tr.time j)).2 = some C
    unfold AC.acToFG
    simp only [hjoin, not_true_eq_false, ↓reduceIte, fgSource_of_fast hC, hrep]

/-- **A live report candidate compatible with every other candidate gives an actual report**
extending it (`Healing.report_of_compatible_candidate_of_run`). Path candidates only enlarge the
candidate set; the deepest candidate still extends `P`. -/
theorem report_of_compatible_candidate_of_run'
    (hrun : GoldilocksRun' proposer dg H tr ini) (hnoColl : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : AC.joined sp (tr.projAC.state y j) (tr.time j))
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPg : P.root ≠ sp.genesisRoot)
    (hPc : P ∈ AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j))
    (hcompat : ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) C P) :
    ∃ r ell' R, AC.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnoColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc
  have hsub : AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j) ⊆
      ell.frame.tree := fun _ h => h.1.1
  obtain ⟨C, hC⟩ := AC.exists_deepest hPhi hsub ⟨P, hPc⟩
  obtain ⟨hCc, hmax⟩ := AC.deepest_mem hC
  apply report_of_deepest_candidate_of_run' hrun hnoColl hy hc hcall hjoin hPg hC
  rcases hcompat C hCc with hCP | hPC
  · by_cases he : P = C
    · exact he ▸ .refl
    have hCPf := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU (hsub hCc) hCP (hsub hPc)
    have hlt := AC.depth_lt_of_anc hPhi hCPf (Ne.symm he) (hsub hPc)
    rcases hmax P hPc he with h | ⟨h, _⟩ <;> omega
  · exact AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU (hsub hPc) hPC (hsub hCc)

/-! ## The deep quarantine over the shadow run (`DeepQuarantine.high_toFG_fast_at`) -/

/-- At an honest `ac_to_fg` call, a non-genesis block of the caller's tree that the caller did not
hold after any cut at a time `≤ c` has a stamp later than `c` (`cut_lt_blockStamp_of_late`). -/
private theorem cut_lt_blockStamp_of_late' {Hs : Set (Fin sp.n)}
    (hrun : GoldilocksRun' proposer dg Hs tr ini) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ Hs) {i : Nat} {ℓ : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt x i ℓ) (hcall : ℓ.call = .toFG)
    {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hCt : C ∈ (tr.state x i).fg.tree) (hg : C.root ≠ sp.genesisRoot) {c : Time}
    (hlate : ∀ k < i, tr.time k ≤ c → C ∉ (tr.state x (k + 1)).fg.tree) :
    AC.ETime.of c < (tr.state x i).ac.blockStamp C.root := by
  have hacr := Compose.goldilocks_ac_projection_from' hrun hnc
  rcases Coherence.tree_accepted' hrun.toLocalRun' hx hCt with rfl | ⟨k, hki, hA⟩
  · exact absurd rfl hg
  obtain ⟨ℓ', hc', hcall', ht'⟩ := Coherence.accept_next' hrun.toLocalRun' hx hA
  have hk1 : k + 1 < i := by
    rcases (Nat.succ_le_of_lt hki).lt_or_eq with h | h
    · exact h
    · subst h
      obtain ⟨-, hl⟩ := Compose.projAC_callAt.1 hc
      rw [hc'.2] at hl
      cases Option.some.inj hl
      rw [hcall'] at hcall
      cases hcall
  have hkc : c < tr.time k := by
    by_contra hle
    exact hlate k hki (not_lt.1 hle) (Coherence.accept_mem_from' hrun.toLocalRun' hx hA)
  have hge := Compose.blockStamp_ge_of_accept hacr.localRun hx
    ⟨ℓ', Compose.projAC_callAt.2 hc', hcall'⟩ hg i hk1
  rw [Compose.projAC_state' hrun.toLocalRun' hx i] at hge
  change AC.ETime.of (tr.time (k + 1)) ≤ _ at hge
  rw [ht'] at hge
  exact lt_of_lt_of_le (AC.etime_of_lt_of.2 hkc) hge

end Consensus.Goldilocks.Shadow.PU

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing (FirstCutAfter cutZ)
open Consensus.Goldilocks.Healing.Growing (HZ)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- The AC state of a node honest at its cut is its projection (`projAC_state_at`). -/
theorem projAC_state_at' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    tr.projAC.state y i = (tr.state y i).ac := by
  have h := Compose.projAC_state' (hrun.upTo (hrun.time_nonneg i)).toLocalRun' hy i
  rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y (fun k hk => hrun.time_mono hk.le),
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- The frame of an AC call of a node honest at it is the shadow frame (`frame_of_projAC_at`). -/
theorem frame_of_projAC_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) : ℓ.frame = Node.frame' (tr.state y i) := by
  have h := Node.frame_of_projAC_at' (hrun.upTo (hrun.time_nonneg i)).toLocalRun' hy
    (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- **The deep quarantine over the shadow run** (`high_toFG_fast_at`). Before `c_z + 4DΔ`, the
source that `ac_to_fg` returns at a node honest at it and at `c_z`, of state height `≥ H_z + 1`, is
a fast-lock candidate of the shadow frame. Path candidates are fast-lock candidates too; the proof
reads only the source split, the frame's tree and the stamps. -/
theorem high_toFG_fast_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time}
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    {z : Fin sp.n} {r : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time r)))
    {ell : ACLabel (goldilocksNode' sp ro)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrep : AC.ToFGAt tr.projAC z r ell C)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h)
    (hq : ∀ D, sp.deepDepth = some D → tr.time r ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    C ∈ AC.toFGCandidates sp (tr.state z r).ac ell.frame (tr.time r) := by
  have hΔ := sp.toParams.hΔ
  have hm := hrun.time_mono
  have hz : z ∈ H (tr.time r) := hrun.antitone (le_max_right _ _) hzz
  have hzc : z ∈ H (cutZ sp.toParams g) := hrun.antitone (le_max_left _ _) hzz
  obtain ⟨hc, hcall, hC⟩ := hrep
  rw [projAC_state_at' hrun hz] at hC
  obtain ⟨hCv, hfast | ⟨D, a, hD, -, -, hdeep⟩⟩ := AC.toFG_source hC
  · exact hfast
  exfalso
  obtain ⟨j, hj⟩ := hsnap
  set d := max (cutZ sp.toParams g) (tr.time r) with hd
  have hd0 : 0 ≤ d := (hrun.time_nonneg r).trans (le_max_right _ _)
  have hrun' := hrun.upTo hd0
  have hnc' := hnc.upTo d
  have hst : ∀ m, (∀ k < m, tr.time k ≤ d) → (tr.upTo d).state z m = tr.state z m :=
    fun m h => Trace.upTo_state tr z h
  have hjd : ∀ k < j, tr.time k ≤ d := fun k hk => (hj.1 k hk).trans (le_max_left _ _)
  have hrd : ∀ k < r, tr.time k ≤ d := fun k hk => (hm hk.le).trans (le_max_right _ _)
  have hinj :=
    (Compose.goldilocks_ac_projection_from' hrun' hnc').localRun.coherent.1
  have hreach : ∀ m, (∀ k < m, tr.time k ≤ d) → (tr.state z m).fg.Reachable' _ := fun m h => by
    rw [← hst m h]; exact Node.fg_reachable_at' hrun'.toLocalRun' hzz m
  have hHZ : (tr.state z j).fg.hmax ≤ HZ tr H g := by
    refine le_csSup (((Set.finite_range fun y => (tr.state y j).fg.hmax).subset ?_).bddAbove)
      ⟨z, hzc, j, hj, rfl⟩
    rintro _ ⟨y, -, j', hj', rfl⟩
    obtain rfl := hj'.unique hj
    exact ⟨y, rfl⟩
  have hfr := frame_of_projAC_at' hrun hz hc
  have hCt : C ∈ (tr.state z r).fg.tree := by
    have h := hdeep.1.1
    rw [hfr, Node.frame'_eq, Store.toFrame'_tree] at h
    exact h.1
  have hlate : ∀ k < r, tr.time k ≤ cutZ sp.toParams g →
      C ∉ ((tr.upTo d).state z (k + 1)).fg.tree := by
    intro k hkr hk hCk
    have hkj : k + 1 ≤ j := by
      by_contra h
      have := hm (show j ≤ k by omega)
      linarith [hj.2]
    have hk1d : ∀ q < k + 1, tr.time q ≤ d := fun q hq => hrd q (by omega)
    rw [hst _ hk1d] at hCk
    obtain ⟨-, -, -, -, hge, -, -⟩ := Store.cache_invariants' (hreach _ hk1d)
    have hmono := Coherence.hmax_mono' hrun'.toLocalRun' hzz hkj
    simp only at hmono
    rw [hst _ hk1d, hst _ hjd] at hmono
    have hσ := Store.σ_eq_of_mem_with (hreach _ hk1d).reachableWith
      Store.finalitySpec_updateFinality' (hreach r hrd).reachableWith hinj
      (fun B hB => ⟨z, hzz, k + 1, by rw [hst _ hk1d]; exact hB⟩)
      (fun B hB => ⟨z, hzz, r, by rw [hst r hrd]; exact hB⟩) hCk hCt
    have := (hge C hCk).trans (hmono.trans hHZ)
    rw [hσ] at this
    omega
  have hc' : (tr.upTo d).projAC.CallAt z r ell := by
    rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt_of_le _ (le_max_right _ _)).mpr hc
  have hstamp := cut_lt_blockStamp_of_late' hrun' hnc' hzz hc' hcall
    (by rw [hst r hrd]; exact hCt) hdeep.2.2.1 hlate
  rw [hst r hrd] at hstamp
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

/-! ## `FollowLocal` over the shadow run -/

/-- Stub (Lane C, `Shadow/PU/Run`): `Compose.Growing.anc_upTo_of_right` over the shadow run. -/
theorem anc_upTo_of_right_stub {P : Params} {A : NodeAC P} {tr : RunTrace A} {d : Time}
    {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
    {H : Time → Set (Fin P.n)} {sg : A.Msg → Fin P.n} {ini}
    (_hrun : Consensus.Goldilocks.Growing.LocalRun' proposer dg H sg tr ini)
    (_hnc : Compose.NoCollRun dg tr) (_hd : 0 ≤ d)
    {B C : A.Blk} (_hC : C ∈ (tr.upTo d).HonestBlocks (H d))
    (_h : Anc (tr.HonestBlocksAt H) B C) : Anc ((tr.upTo d).HonestBlocks (H d)) B C := by
  sorry

/-- A warm node is joined at the vote deadline (`joined_voteTime_of_warm_frame_at`). -/
theorem joined_voteTime_of_warm_frame_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {g : Time} {s₀ u : Nat} (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hs : s₀ + 1 ≤ u)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts u + sp.Δ)) :
    AC.JoinedAt tr.projAC y (sp.ts u + sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  have hslot : sp.slot (sp.ts u + sp.Δ) = u := by
    apply AC.slot_of_mem sp u
    all_goals simp only [ACParams.ts]; push_cast; linarith
  intro i hi hit
  change tr.time i ≤ sp.ts ((sp.slot (sp.ts u + sp.Δ) : Int) - 1)
  rw [hslot]
  have hiy : y ∈ H (tr.time i) := hrun.antitone hit hy
  have hrestart := hnr y i hiy (Compose.projAC_restartAt.mp hi)
  have ht := (AC.ts_le_iff sp).2 (show (s₀ : Int) ≤ (u : Int) - 1 by omega)
  exact hrestart.trans (by linarith)

/-- `joined_voteTime_of_warm_frame_at'` with restarts bounded only up to `b`
(`joined_voteTime_of_warm_frame_upTo_at`). -/
theorem joined_voteTime_of_warm_frame_upTo_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {g b : Time} {s₀ u : Nat} (hnr : Healing.Growing.NoRestartUpTo tr H (gbar g) b)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hs : s₀ + 1 ≤ u) (hb : sp.ts u + sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts u + sp.Δ)) :
    AC.JoinedAt tr.projAC y (sp.ts u + sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  have hslot : sp.slot (sp.ts u + sp.Δ) = u := by
    apply AC.slot_of_mem sp u
    all_goals simp only [ACParams.ts]; push_cast; linarith
  intro i hi hit
  change tr.time i ≤ sp.ts ((sp.slot (sp.ts u + sp.Δ) : Int) - 1)
  rw [hslot]
  have hiy : y ∈ H (tr.time i) := hrun.antitone hit hy
  have hrestart := Healing.Growing.noRestartUpTo_iff.mp hnr y i hiy
    (Compose.projAC_restartAt.mp hi) (hit.trans hb)
  have ht := (AC.ts_le_iff sp).2 (show (s₀ : Int) ≤ (u : Int) - 1 by omega)
  exact hrestart.trans (by linarith)

/-- **Candidates at one honest call are compatible** in the historical block universe
(`toFG_candidates_compatible_at_call_at`), path candidates included. -/
theorem toFG_candidates_compatible_at_call_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt y i ell) {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) :
    ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) C P := by
  have hd := hrun.time_nonneg i
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt y i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hp' : P ∈ AC.toFGCandidates sp ((tr.upTo (tr.time i)).projAC.state y i)
      ell.frame ((tr.upTo (tr.time i)).time i) := by
    simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hP
  intro C hC
  have hcand : C ∈ AC.toFGCandidates sp ((tr.upTo (tr.time i)).projAC.state y i)
      ell.frame ((tr.upTo (tr.time i)).time i) := by
    simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hC
  rcases toFG_candidates_compatible_at_call' (hrun.upTo hd)
    (hnc.upTo (tr.time i)) hy hc' hp' C hcand with h | h
  · exact Or.inl (h.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd))
  · exact Or.inr (h.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd))

/-- **An actual report above a slot-`u` block cannot precede slot `u`**
(`toFG_time_ge_of_ancestor_slot_at`). -/
theorem toFG_time_ge_of_ancestor_slot_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i u : Nat}
    (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} {P R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.ToFGAt tr.projAC y i ell R) (hPs : P.slot = u)
    (hPR : Anc (tr.HonestBlocksAt H) P R) :
    sp.ts u ≤ tr.time i := by
  have hd := hrun.time_nonneg i
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  have hR' : AC.ToFGAt (tr.upTo (tr.time i)).projAC y i ell R := by
    refine ⟨?_, hR.2.1, ?_⟩
    · rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hR.1⟩
    · simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hR.2.2
  have hac := Compose.goldilocks_ac_projection_from' (hrun.upTo hd) (hnc.upTo (tr.time i))
  have hRc := (AC.toFG_source hR'.2.2).1.1
  have hRs : R.slot ≤ sp.slot (tr.time i) := AC.frame_slot_leU sp hac.localRun.toU hy hR'.1 R hRc
  have hPR' := anc_upTo_of_right_stub hrun.toLocalRun' hnc hd
    ((AC.frameIn_of_callAt hac.localRun hy hR'.1).2 hRc) hPR
  have hPRs := (Anc.slot_le hac.localRun.coherent hPR').1
  exact (AC.ts_le_iff_le_slot sp hd _).2 (by omega)

/-! ## `CandidateReport` over the shadow run -/

/-- The frame of an honest call is well formed and its tree is the caller's
(`frame_tree_subset_at`). -/
theorem frame_tree_subset_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ℓ : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y k ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ (tr.state y k).fg.tree := by
  have hd := hrun.time_nonneg k
  have hr := (Compose.goldilocks_ac_projection_from' (hrun.upTo hd) (hnc.upTo _)).localRun
  have hc' : (tr.upTo (tr.time k)).projAC.CallAt y k ℓ := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  refine ⟨(AC.frameIn_of_callAt hr hy hc').1, ?_⟩
  rw [frame_of_projAC_at' hrun hy hc, Node.frame'_eq, Store.toFrame'_tree]
  exact fun B hB => hB.1

/-- **A live report candidate compatible with every other candidate gives an actual report**
extending it, by the call, for a node honest at the call
(`report_of_compatible_candidate_of_run_at`), path candidates included. -/
theorem report_of_compatible_candidate_of_run_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y j ell)
    (hcall : ell.call = .toFG) (hjoin : AC.joined sp (tr.projAC.state y j) (tr.time j))
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPg : P.root ≠ sp.genesisRoot)
    (hPc : P ∈ AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j))
    (hcompat : ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j),
      Compatible (tr.HonestBlocksAt H) C P) :
    ∃ r ell' R, AC.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocksAt H) P R := by
  have hd := hrun.time_nonneg j
  have hst : (tr.upTo (tr.time j)).projAC.state y j = tr.projAC.state y j := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  have hU : ∀ X ∈ ell.frame.tree, X ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) :=
    fun X hX => ⟨y, hy, j, by
      rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl]
      exact (frame_tree_subset_at' hrun hnc hy hc).2 hX⟩
  obtain ⟨r, ell', R, hto, hrt, hPR⟩ := report_of_compatible_candidate_of_run'
    (hrun.upTo hd) (hnc.upTo _) hy hc' hcall (by rw [hst]; exact hjoin) hPg
    (by rw [hst]; exact hPc)
    (fun C hC => by
      rw [hst] at hC
      exact (hcompat C hC).imp
        (anc_upTo_of_right_stub hrun.toLocalRun' hnc hd (hU P hPc.1.1))
        (anc_upTo_of_right_stub hrun.toLocalRun' hnc hd (hU C hC.1.1)))
  have hrj : tr.time r ≤ tr.time j := hrt
  exact ⟨r, ell', R, (Healing.Growing.toFGAt_upTo_iff hrun.time_mono hrj).mp hto, hrj,
    hPR.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd)⟩

end Consensus.Goldilocks.Shadow.PU.Growing

end
