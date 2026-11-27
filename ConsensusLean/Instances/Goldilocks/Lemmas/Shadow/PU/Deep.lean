module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireSources

public section

/-! # Deep FG sources over the P-U shadow node (V-B10, D3(c))

Under D3(c) the shadow frame `Node.frame'` keeps `toFGCandidates` and `toFGDeepCandidates`
unchanged, read over `toFrame'`: in top-`J` frames the path blocks between `F` and `J` become
candidates, and a path fast candidate can pre-empt the deep arm. The stock proofs read the sources
only through frame-generic facts: the source split `AC.toFG_source`, the frame's tree (the same set
for `toFrame'` and `toFrame`), the AC lock invariant over lawful frames, and the fast arm firing
when a fast candidate exists. No proof needs the deep arm to fire. The proofs below are therefore
the stock ones over `GoldilocksRun'`.

Suppliers not yet published by other lanes are named `sorry` stubs in `Shadow.PU.Stub`, with the
stock signatures: until each is replaced, a theorem using one is unresolved (`sorryAx`). -/

namespace Consensus.Goldilocks.Shadow.PU.Stub

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- Stub (B0b, `Shadow/PU/Trace`): the AC projection of a shadow run is an AC run. -/
theorem goldilocks_ac_projection_from' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) :
    AC.ACRun proposer tr.projAC H (tr.HonestBlocks H) ini := by
  sorry

/-- Stub (C0, `Shadow/PU/Cache`): genesis is in every shadow-reachable store's tree. -/
theorem genesis_mem' {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable' acp₀) : P.genesisBlock acp₀ ∈ st.tree := by
  sorry

end Consensus.Goldilocks.Shadow.PU.Stub

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
  have hr := (Stub.goldilocks_ac_projection_from' hrun hnc).localRun
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
  have hr := (Stub.goldilocks_ac_projection_from' hrun hnoColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc
  by_cases hrep : AC.AncR ell.frame C (tr.projAC.state y j).fgReported
  · obtain ⟨R, hRt, hRr, hCR⟩ := hrep
    have hPR : ell.frame.Anc P R := hPC.trans hCR
    rcases Healing.fgReported_origin hr hrun.vstart hy j with hgen | ⟨r, hrj, ell', R', hto, hR'r⟩
    · have hG := Stub.genesis_mem' (Node.fg_reachable_at' hrun.toLocalRun' hy j)
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
  have hr := (Stub.goldilocks_ac_projection_from' hrun hnoColl).localRun
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

end Consensus.Goldilocks.Shadow.PU

end
