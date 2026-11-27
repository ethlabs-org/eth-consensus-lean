module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # V-B4b: the stock `FrameWindow` consumers of persistence over shadow runs

Route (i) of plan rev 11 §D: persistence is needed only within one per-node regime.

* `Store.isViable'_of_floor`: at one store, a block at or above the stock head-height floor is
  P-U viable, provided in a top-clean store it is above the floor or extends `Σ.J`.
* `FrameWindow.viableHead_persists_or_contest_gap'`: over the stock `FrameWindow`, a P-U viable
  head of an earlier call frame stays a viable head of the shadow frame, **or** it is a P-U-only
  head of a contest at the earlier cut (`σ(Q).h + 1 = floor = h_max`) and the reader has since
  entered the gap `h_max = floor + 1`. A same-height contest keeps its `J` by safety, so the J-side
  head persists there; only the contest → gap switch remains.
* `FrameWindow.root_witness_of_earlier_call_stock'`: the stock H-wit consumer, proved over the
  stock window: its witness has maximum height, so it never is the P-U-only head.
-/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- A block at or above the stock head-height floor is P-U viable, if in a top-clean store it is
above the floor or extends `Σ.J`. -/
theorem isViable'_of_floor (st : Store P ACP) (hjm : st.hj < st.hmax) {Q : NodeBlock P ACP}
    (hfl : st.headHeightFloor ≤ (st.σ Q.root).h)
    (hk : st.hmax = st.hj + 1 → ¬ st.Contest →
      st.headHeightFloor + 1 ≤ (st.σ Q.root).h ∨ st.Anc st.J Q) :
    st.IsViable' Q := by
  classical
  rw [isViable'_iff]
  have hb := headHeightFloor_bounds st
  by_cases hge : st.hmax ≤ (st.σ Q.root).h
  · exact Or.inl hge
  have hfl1 : st.headHeightFloor = st.hmax - 1 := by omega
  have hc : ¬ st.Contest := fun hc => by
    have : st.headHeightFloor = st.hmax := ite_eq_left hc
    omega
  by_cases htop : st.hmax = st.hj + 1
  · rcases hk htop hc with h | h
    · omega
    · exact Or.inr ⟨by omega, Or.inr h⟩
  · exact Or.inr ⟨by omega, Or.inl (by omega)⟩

/-- **The contest → gap residue dichotomy** (store level). In a P-U store at `h_max = floor + 1`
the viable heads are exactly the blocks of height at least `floor`: a block `Q` is in the
viable tree of the shadow frame only below such a viable head `W`; otherwise it is outside that
viable tree. -/
theorem contest_gap_residue' (st : Store P ACP) {floor : Nat} (hgap : st.hmax = floor + 1)
    (Q : NodeBlock P ACP) :
    (∃ W ∈ st.toFrame'.viableHeads, st.Anc Q W ∧ floor ≤ (st.σ W.root).h) ∨
      Q ∉ st.toFrame'.viableTree st.toFrame'.tree := by
  by_cases h : Q ∈ st.toFrame'.viableTree st.toFrame'.tree
  · obtain ⟨-, -, W, -, hWv, hQW⟩ := h
    refine Or.inl ⟨W, hWv, hQW.mono fun _ hB => ?_, ?_⟩
    · rw [toFrame'_tree] at hB
      exact hB.1
    · rw [toFrame'_viableHeads] at hWv
      rcases (isViable'_iff st W).mp hWv.2.2 with hh | ⟨hh, -⟩ <;> omega
  · exact Or.inr h

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks

variable {n : Nat} {FGP ACP : Type}

/-- **Locks above a block outside the viable tree project strictly below it.** In a well-formed
frame, if `Q` is in the tree, not at or below `fc_root`, and outside the viable tree of the whole
tree, then every block `B ⪰ Q` of the tree has its viable ancestor strictly below `Q` (the
viable-ancestor candidates are at or below `fc_root` or in the whole-tree viable tree). So every
live lock on a block at or above `Q` is moved strictly below `Q` (`AC.liveLocks`). -/
theorem viableAncestor_lt_of_not_viableTree {Φ : Frame n FGP ACP} (hΦ : FrameOK Φ)
    {Q B : Block n FGP ACP} (hQ : Q ∈ Φ.tree) (hQF : ¬ Φ.Anc Q Φ.fcRoot)
    (hnv : Q ∉ Φ.viableTree Φ.tree) (hB : B ∈ Φ.tree) (hQB : Φ.Anc Q B) :
    Φ.Anc (Φ.viableAncestor B) Q ∧ Φ.viableAncestor B ≠ Q := by
  obtain ⟨hAB, hcand, -⟩ := AC.viableAncestor_spec hΦ hB
  have hup : ¬ Φ.Anc Q (Φ.viableAncestor B) := by
    intro hQA
    rcases hcand with hAF | ⟨-, hFA, W, hW, hWv, hAW⟩
    · exact hQF (hQA.trans hAF)
    · apply hnv
      refine ⟨hQ, ?_, W, hW, hWv, hQA.trans hAW⟩
      rcases Anc.total hΦ.coherent hFA hQA with h | h
      · exact h
      · exact absurd h hQF
  rcases Anc.total hΦ.coherent hAB hQB with h | h
  · exact ⟨h, fun he => hup (he ▸ .refl)⟩
  · exact absurd h hup

end Consensus.Goldilocks

namespace Consensus.Goldilocks.Store

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- **Persistence over the stock window, per regime, with the stock witness.** A P-U viable head
`Q` of an earlier call frame inside a stock `FrameWindow` is, at the later cut,
(A) a viable head of the shadow frame with the stock witness `floor ≤ σ(Q).h ∧ (kindJ → J ⪯ Q)`;
(B) a viable head of the shadow frame below the floor, `σ(Q).h + 1 = floor`, in a contest at
`h_max = floor` with `Σ.J ⪯ Q` (the P-U-only head, kept by safety); or
(C) the P-U-only head of a contest at the call whose reader has since entered the gap
`h_max = floor + 1`. -/
theorem FrameWindow.viableHead_persists_stock' {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun' proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y a ell)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hv : Q ∈ ell.frame.viableHeads) :
    ((Q ∈ (Node.frame' (tr.state y i)).tree ∧
      (Node.frame' (tr.state y i)).Anc (Node.frame' (tr.state y i)).fcRoot Q ∧
      Q ∈ (Node.frame' (tr.state y i)).viableHeads) ∧
      ((floor ≤ ((tr.state y i).fg.σ Q.root).h ∧ (kindJ → Anc (tr.HonestBlocks H) J Q)) ∨
        (((tr.state y i).fg.σ Q.root).h + 1 = floor ∧ (tr.state y i).fg.Contest ∧
          (tr.state y i).fg.hmax = floor ∧ (tr.state y i).fg.Anc (tr.state y i).fg.J Q))) ∨
    ((tr.state y a).fg.Contest ∧ (tr.state y a).fg.hmax = floor ∧
      ((tr.state y a).fg.σ Q.root).h + 1 = floor ∧ (tr.state y i).fg.hmax = floor + 1) := by
  classical
  have htime := hrun.time_mono hai
  rw [Node.frame_of_projAC_at' hrun.toLocalRun' hy hc, Node.frame'_eq,
    Store.toFrame'_viableHeads] at hv
  obtain ⟨hQa, -, hva⟩ := hv
  set sa := (tr.state y a).fg with hsa
  set si := (tr.state y i).fg with hsi
  have hQi : Q ∈ si.tree := Compose.tree_mono' hrun.toLocalRun' hy hai hQa
  have hsub : si.tree ⊆ tr.HonestBlocks H := fun B hB => ⟨y, hy, i, hB⟩
  have hRa := Node.fg_reachable_at' hrun.toLocalRun' hy a
  have hRi := Node.fg_reachable_at' hrun.toLocalRun' hy i
  have hu := Store.finalitySpec_updateFinality' (P := sp.toParams) (ACP := Payload sp.n)
  have hσ : si.σ Q.root = sa.σ Q.root :=
    (Store.σ_eq_of_mem_with hRa.reachableWith hu hRi.reachableWith
      (Coherence.honest_blocks_coherent' hrun.toLocalRun' hnc).1
      (fun _ hB => ⟨y, hy, a, hB⟩) hsub hQa hQi).symm
  have hh : (si.σ Q.root).h = (sa.σ Q.root).h := by rw [hσ]
  have hfa : sa.headHeightFloor = floor := hframe.floor_eq y hy a halo (htime.trans hihi)
  have hfi : si.headHeightFloor = floor := hframe.floor_eq y hy i (halo.trans htime) hihi
  have hka := hframe.kind_iff y hy a halo (htime.trans hihi)
  have hki := hframe.kind_iff y hy i (halo.trans htime) hihi
  have hba := Store.headHeightFloor_bounds sa
  have hbi := Store.headHeightFloor_bounds si
  have hja := hj_lt_hmax' hrun hy a
  have hji := hj_lt_hmax' hrun hy i
  have hcontest : ∀ {st : Store sp.toParams (Payload sp.n)}, st.Contest →
      st.headHeightFloor = st.hmax := fun hc => ite_eq_left hc
  have hnocontest : ∀ {st : Store sp.toParams (Payload sp.n)}, ¬ st.Contest →
      st.headHeightFloor = st.hmax - 1 := fun hc => ite_eq_right hc
  -- the viable alternative from P-U viability at the later store
  have finish : si.IsViable' Q →
      (Q ∈ (Node.frame' (tr.state y i)).tree ∧
        (Node.frame' (tr.state y i)).Anc (Node.frame' (tr.state y i)).fcRoot Q ∧
        Q ∈ (Node.frame' (tr.state y i)).viableHeads) := by
    intro hvi
    have hFQ := finalized_below_viable' hRi
      (Coherence.honest_blocks_coherent' hrun.toLocalRun' hnc) hsub hf
      (fun a b ha hb hv => held_atts_safe' hrun hnc hy hy i i a b ha hb hv) hQi hvi
    refine ⟨?_, ?_, ?_⟩
    · rw [Node.frame'_eq, Store.toFrame'_tree]
      exact ⟨hQi, hFQ⟩
    · rw [Node.frame'_eq, Store.toFrame'_fcRoot]
      change Anc (tr.state y i).fg.toFrame'.tree _ _
      rw [Store.toFrame'_tree]
      exact Anc.restrict .refl hFQ
    · rw [Node.frame'_eq, Store.toFrame'_viableHeads]
      exact ⟨hQi, hFQ, hvi⟩
  -- a kind-J later store has the earlier `J` and the earlier height
  have hkind : si.hmax = si.hj + 1 → ¬ si.Contest →
      sa.hmax = sa.hj + 1 ∧ ¬ sa.Contest ∧ si.J = sa.J := fun h1 h2 => by
    have hk := hki.mp ⟨h1, h2⟩
    obtain ⟨g1, g2⟩ := hka.mpr hk
    exact ⟨g1, g2, (hframe.root_eq y hy i (halo.trans htime) hihi hk).trans
      (hframe.root_eq y hy a halo (htime.trans hihi) hk).symm⟩
  have hJmono : sa.Anc sa.J Q → si.Anc sa.J Q :=
    fun h => h.mono (Compose.tree_mono' hrun.toLocalRun' hy hai)
  have hkJ : kindJ → si.J = J := fun hk => hframe.root_eq y hy i (halo.trans htime) hihi hk
  have hJH : si.Anc si.J Q → kindJ → Anc (tr.HonestBlocks H) J Q :=
    fun h hk => hkJ hk ▸ h.mono hsub
  have hkind' : kindJ → sa.hmax = sa.hj + 1 ∧ ¬ sa.Contest ∧ si.J = sa.J := fun hk => by
    obtain ⟨g1, g2⟩ := hka.mpr hk
    exact ⟨g1, g2, (hkJ hk).trans
      (hframe.root_eq y hy a halo (htime.trans hihi) hk).symm⟩
  rcases (Store.isViable'_iff sa Q).mp hva with hge | ⟨heq, hgap | hJQ⟩
  · -- at or above `h_max`
    refine Or.inl ⟨finish (Store.isViable'_of_floor si hji (by omega) fun h1 h2 => ?_),
      Or.inl ⟨by omega, fun hk => ?_⟩⟩
    · obtain ⟨g1, g2, -⟩ := hkind h1 h2
      have := hnocontest g2
      exact Or.inl (by omega)
    · -- top clean at the call: a maximum-height block above `F` extends `J`
      obtain ⟨g1, g2, hJ⟩ := hkind' hk
      have hle : (sa.σ Q.root).h ≤ sa.hmax := (Store.cache_invariants' hRa).2.2.2.2.1 Q hQa
      have hFQ := finalized_below_viable' hRa
        (Coherence.honest_blocks_coherent' hrun.toLocalRun' hnc) (fun _ hB => ⟨y, hy, a, hB⟩) hf
        (fun x z hx hz hv => held_atts_safe' hrun hnc hy hy a a x z hx hz hv) hQa hva
      have hJQ : sa.Anc sa.J Q := by
        by_contra hn
        exact g2 ⟨g1, Q, hQa, hFQ, by omega, hn⟩
      exact hJH (hJ ▸ hJmono hJQ) hk
  · -- a gap at the call
    have hnc' : ¬ sa.Contest := fun h => by have := h.1; omega
    have := hnocontest hnc'
    refine Or.inl ⟨finish (Store.isViable'_of_floor si hji (by omega) fun h1 h2 => ?_),
      Or.inl ⟨by omega, fun hk => ?_⟩⟩
    · obtain ⟨g1, -, -⟩ := hkind h1 h2
      omega
    · obtain ⟨g1, -, -⟩ := hkind' hk
      omega
  · by_cases hca : sa.Contest
    · -- the P-U-only head of a contest
      have hfl := hcontest hca
      have hhj := hca.1
      by_cases hgi : si.hmax = floor + 1
      · exact Or.inr ⟨hca, by omega, by omega, hgi⟩
      have hmi : si.hmax = floor := by omega
      have hci : si.Contest := by
        by_contra h
        have := hnocontest h
        omega
      have hhji := hci.1
      -- same justified height: the same `J` (safety)
      obtain ⟨-, hJa, -, ⟨Ba, hBa, hBaJ, hBahj⟩, -⟩ := Store.cache_invariants' hRa
      obtain ⟨-, hJi, -, ⟨Bi, hBi, hBiJ, hBihj⟩, -⟩ := Store.cache_invariants' hRi
      have hjeq : sa.hj = si.hj := by omega
      have hroots := Store.J_eq_of_hj_eq_of_safe_with hu hRa.reachableWith hRi.reachableWith
        hf (fun x z hx hz hv => held_atts_safe' hrun hnc hy hy a i x z hx hz hv) hBa hBi
        (by rw [hBahj, hBihj]; exact hjeq)
      rw [hBaJ, hBiJ] at hroots
      have hJeq : sa.J = si.J :=
        (Coherence.honest_blocks_coherent' hrun.toLocalRun' hnc).1
          ⟨y, hy, a, hJa⟩ (hsub hJi) hroots
      have hJQi : si.Anc si.J Q := hJeq ▸ hJmono hJQ
      exact Or.inl ⟨finish ((Store.isViable'_iff si Q).mpr (Or.inr ⟨by omega, Or.inr hJQi⟩)),
        Or.inr ⟨by omega, hci, hmi, hJQi⟩⟩
    · have hfl := hnocontest hca
      refine Or.inl ⟨finish (Store.isViable'_of_floor si hji (by omega) fun h1 h2 => ?_),
        Or.inl ⟨by omega, fun hk => ?_⟩⟩
      · obtain ⟨-, -, hJ⟩ := hkind h1 h2
        exact Or.inr (hJ ▸ hJmono hJQ)
      · obtain ⟨-, -, hJ⟩ := hkind' hk
        exact hJH (hJ ▸ hJmono hJQ) hk

/-- **Persistence over the stock window, per regime.** A P-U viable head of an earlier call
frame inside a stock `FrameWindow` is a viable head of the later shadow frame, or it is the
P-U-only head of a contest at the call and the reader has since left that contest into the gap
`h_max = floor + 1`. -/
theorem FrameWindow.viableHead_persists_or_contest_gap' {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun' proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y a ell)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))} (hv : Q ∈ ell.frame.viableHeads) :
    (Q ∈ (Node.frame' (tr.state y i)).tree ∧
      (Node.frame' (tr.state y i)).Anc (Node.frame' (tr.state y i)).fcRoot Q ∧
      Q ∈ (Node.frame' (tr.state y i)).viableHeads) ∨
    ((tr.state y a).fg.Contest ∧ (tr.state y a).fg.hmax = floor ∧
      ((tr.state y a).fg.σ Q.root).h + 1 = floor ∧ (tr.state y i).fg.hmax = floor + 1) :=
  (hframe.viableHead_persists_stock' hrun hnc hf hy hai halo hihi hc hv).imp_left (·.1)

/-- **H-wit over the stock window, with the stock witness**
(`FrameWindow.root_witness_of_earlier_call` for shadow runs, route (i)). An earlier action cut
supplies a frozen viable descendant of the shadow root `F`, with the stock witness. The
witness has maximum height at the earlier cut, so the contest → gap alternative cannot occur, and
the stock non-kind-J premise is not needed. -/
theorem FrameWindow.root_witness_stock' {lo hi g : Time} {floor : Nat}
    {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun' proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (AC.gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    {ell₀ ell : ACLabel (goldilocksNode' sp ro)}
    (ha : tr.projAC.CallAt y a ell₀) {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    (hat : tr.time a < AC.freeze sp e.msg.slot)
    (hgf : AC.gbar g < AC.freeze sp e.msg.slot) :
    ∃ Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc ell.frame.fcRoot Q ∧
      floor ≤ ((tr.state y i).fg.σ Q.root).h ∧ (kindJ → Anc (tr.HonestBlocks H) J Q) := by
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnc).localRun
  have hR := Node.fg_reachable_at' hrun.toLocalRun' hy a
  obtain ⟨-, -, -, -, -, ⟨Q, hQ, hQh⟩, -⟩ := Store.cache_invariants' hR
  have hv : (tr.state y a).fg.IsViable' Q :=
    (Store.isViable'_iff _ _).mpr (Or.inl hQh.ge)
  have hFQ := finalized_below_viable' hR
    (Coherence.honest_blocks_coherent' hrun.toLocalRun' hnc)
    (fun B hB => ⟨y, hy, a, hB⟩) hf
    (fun b c h₁ h₂ hv => held_atts_safe' hrun hnc hy hy a a b c h₁ h₂ hv) hQ hv
  have hQt : Q ∈ ell₀.frame.tree := by
    rw [Node.frame_of_projAC_at' hrun.toLocalRun' hy ha, Node.frame'_eq,
      Store.toFrame'_tree]
    exact ⟨hQ, hFQ⟩
  have hv₀ : Q ∈ ell₀.frame.viableHeads := by
    rw [Node.frame_of_projAC_at' hrun.toLocalRun' hy ha, Node.frame'_eq,
      Store.toFrame'_viableHeads]
    exact ⟨hQ, hFQ, hv⟩
  have hfa := hframe.floor_eq y hy a halo ((hrun.time_mono hai).trans hihi)
  have hba := Store.headHeightFloor_bounds (tr.state y a).fg
  have hσ : (tr.state y i).fg.σ Q.root = (tr.state y a).fg.σ Q.root :=
    (Store.σ_eq_of_mem_with hR.reachableWith Store.finalitySpec_updateFinality'
      (Node.fg_reachable_at' hrun.toLocalRun' hy i).reachableWith
      (Coherence.honest_blocks_coherent' hrun.toLocalRun' hnc).1
      (fun _ hB => ⟨y, hy, a, hB⟩) (fun _ hB => ⟨y, hy, i, hB⟩) hQ
      (Compose.tree_mono' hrun.toLocalRun' hy hai hQ)).symm
  have hhσ : ((tr.state y i).fg.σ Q.root).h = ((tr.state y a).fg.σ Q.root).h := by rw [hσ]
  rcases hframe.viableHead_persists_stock' hrun hnc hf hy hai halo hihi ha hv₀ with
    ⟨⟨hQi, hrooti, hvi⟩, ⟨hfl, hk⟩ | ⟨hlow, -⟩⟩ | ⟨hca, hma, hQf, -⟩
  · rw [← Node.frame_of_projAC_at' hrun.toLocalRun' hy hc.1] at hQi hrooti hvi
    refine ⟨Q, ⟨hQi, Or.inl ?_⟩, hvi, hrooti, hfl, hk⟩
    apply AC.readPoint_blockStamp_lt_of_earlier_frame hr hrun.vstart hy ha hc hQt hQi hat
    intro r _ hrs
    exact (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans_lt hgf
  · exfalso
    omega
  · exfalso
    omega

/-- **H-wit over the stock window** (`FrameWindow.root_witness_of_earlier_call` for shadow runs,
route (i)). An earlier action cut supplies a frozen viable descendant of the shadow root `F`. The
witness has maximum height at the earlier cut, so the contest → gap alternative cannot occur, and
the stock non-kind-J premise is not needed. -/
theorem FrameWindow.root_witness_of_earlier_call_stock' {lo hi g : Time} {floor : Nat}
    {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun' proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (AC.gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {a i : Nat} (hai : a ≤ i)
    {ell₀ ell : ACLabel (goldilocksNode' sp ro)}
    (ha : tr.projAC.CallAt y a ell₀) {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    (hat : tr.time a < AC.freeze sp e.msg.slot)
    (hgf : AC.gbar g < AC.freeze sp e.msg.slot) :
    ∃ Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Q ∈ ell.frame.viableHeads ∧ ell.frame.Anc ell.frame.fcRoot Q :=
  let ⟨Q, hQ, hv, hr, _⟩ :=
    hframe.root_witness_stock' hrun hnc hf hnr hy hai ha hc halo hihi hat hgf
  ⟨Q, hQ, hv, hr⟩

/-- **The stored-lock witness over the stock window** (`FrameWindow.old_lock_witness`, route
(i)): the stock conclusion, or the writer's frozen witness is the P-U-only J-side head of a contest
at the write and the voter has since entered the gap `h_max = floor + 1` (the one regime switch
that the stock window allows and that P-U persistence does not survive). -/
theorem FrameWindow.old_lock_witness_or_contest_gap' {s₀ floor : Nat} {hi g : Time}
    {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) hi floor kindJ J)
    (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (AC.gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi)
    (hgf : AC.gbar g < AC.freeze sp e.msg.slot)
    {l : AC.Lock} (hl : l ∈ (tr.projAC.state y i).locks)
    (hlabel : s₀ ≤ l.slot) (hold : l.slot < e.msg.slot)
    {L : AC.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ell.frame.tree)
    (hLr : L.root = l.block) (hstrict : ¬ Anc (tr.HonestBlocks H) L ell.frame.fcRoot) :
    (∃ a < i, ∃ ell₀ D Q,
      tr.projAC.CallAt y a ell₀ ∧ sp.ts s₀ ≤ tr.time a ∧
      tr.time a < AC.freeze sp e.msg.slot ∧
      ((∃ CV, AC.OptimisticLockAt tr.projAC y a l.slot D CV) ∨
        ∃ ell', AC.UpdateAt tr.projAC y a l.slot ell') ∧
      Q ∈ ell₀.frame.viableHeads ∧ Anc (tr.HonestBlocks H) L Q ∧
      Q ∈ ell.frame.viableHeads ∧
      Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) ∨
    ∃ a < i, ∃ ell₀ Q, tr.projAC.CallAt y a ell₀ ∧ sp.ts s₀ ≤ tr.time a ∧
      tr.time a < AC.freeze sp e.msg.slot ∧ Q ∈ ell₀.frame.viableHeads ∧
      Anc (tr.HonestBlocks H) L Q ∧
      (tr.state y a).fg.Contest ∧ (tr.state y a).fg.hmax = floor ∧
      ((tr.state y a).fg.σ Q.root).h + 1 = floor ∧ (tr.state y i).fg.hmax = floor + 1 := by
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnc).localRun
  have htvote := AC.vote_time_leU hr.toU hy ⟨ell, hc⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at htvote
  have hslot : e.msg.slot = sp.slot (tr.time i) := (AC.castAt_specU hr.toU hy hc).2.1
  rw [← hslot] at htvote
  obtain ⟨a, hai, ell₀, D, A, ha, hD, hAeq, ho, ⟨B, hB, hBr, hBA⟩, hcase⟩ :=
    AC.lock_write_witness hr hrun.vstart hy hl
  have hPhiU := (AC.frameIn_of_callAt hr hy hc.1).2
  have hPhi₀ := AC.frameIn_of_callAt hr hy ha
  obtain rfl : B = L := hr.coherent.1 hB (hPhiU hL) (hBr.trans hLr.symm)
  have htime : sp.ts s₀ ≤ tr.time a ∧ tr.time a < AC.freeze sp e.msg.slot := by
    rcases ho with ⟨CV, ell', B, hp, hs, hsel, -⟩ | ⟨ell', hu⟩
    · have hlo := (AC.ts_le_iff_le_slot sp (hr.time_nonneg a) (s₀ : Int)).mpr
        (by rw [hs]; exact_mod_cast hlabel)
      have hlt : tr.time a < sp.ts l.slot + 2 * sp.Δ := by
        unfold AC.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel with hn
        exact lt_of_not_ge (fun ht => hn (Or.inr (Or.inr (Or.inl (hs ▸ ht)))))
      have hts := (AC.ts_le_iff sp).mpr (show (l.slot : Int) ≤ (e.msg.slot : Int) - 1 by omega)
      refine ⟨hlo, ?_⟩
      unfold AC.freeze
      exact hlt.trans_le
        (add_le_add hts (mul_le_mul_of_nonneg_right (by norm_num) sp.toParams.hΔ.le))
    · have ht := hu.2.2.1
      change tr.time a = _ at ht
      have hts₀ := (AC.ts_le_iff sp).mpr (show (s₀ : Int) ≤ l.slot by exact_mod_cast hlabel)
      have hlabel' : l.slot + 2 ≤ e.msg.slot :=
        Compose.ts_add_two_le ((ht.symm.trans_le (hrun.time_mono hai.le)).trans htvote)
      refine ⟨hts₀.trans ((le_add_of_nonneg_right
        (mul_nonneg (by norm_num) sp.toParams.hΔ.le)).trans_eq ht.symm), ?_⟩
      have hts := (AC.ts_le_iff sp).mpr
        (show (l.slot : Int) + 1 ≤ (e.msg.slot : Int) - 1 by omega)
      unfold AC.freeze
      simp only [ACParams.ts] at ht hts ⊢
      linarith [sp.toParams.hΔ]
  rcases hcase with hbelow | ⟨Q, hQ, hv, hAQ⟩
  · exfalso
    apply hstrict
    have hroot := Healing.fcRoot_mono' hrun hy hai.le
    rw [← Node.frame_of_projAC_at' hrun.toLocalRun' hy ha,
      ← Node.frame_of_projAC_at' hrun.toLocalRun' hy hc.1] at hroot
    exact hBA.trans ((hbelow.mono hPhi₀.2).trans hroot)
  · rcases hframe.viableHead_persists_or_contest_gap' hrun hnc hf hy hai.le htime.1 hihi ha hv
      with ⟨hQt, -, hvQ⟩ | ⟨hca, hma, hQf, hmi⟩
    · rw [← Node.frame_of_projAC_at' hrun.toLocalRun' hy hc.1] at hQt hvQ
      refine Or.inl ⟨a, hai, ell₀, D, Q, ha, htime.1, htime.2, ho, hv,
        hBA.trans (hAQ.mono hPhi₀.2), hvQ, hQt, Or.inl ?_⟩
      apply AC.readPoint_blockStamp_lt_of_earlier_frame hr hrun.vstart hy ha hc hQ hQt htime.2
      intro r _ hrs
      exact (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans_lt hgf
    · exact Or.inr ⟨a, hai, ell₀, Q, ha, htime.1, htime.2, hv,
        hBA.trans (hAQ.mono hPhi₀.2), hca, hma, hQf, hmi⟩

/-- **The stored-lock witness over the stock window, three cases** (`FrameWindow.old_lock_witness`,
route (i)). The writer's frozen witness `Q` is (A) viable at the voter with the stock witness,
(B) viable at the voter as the P-U-only J-side head of the voter's contest, or (C) the P-U-only
head of a contest at the write while the voter is in the gap `h_max = floor + 1`. -/
theorem FrameWindow.old_lock_witness_stock' {s₀ floor : Nat} {hi g : Time}
    {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) hi floor kindJ J)
    (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hnr : NoRestartAfter tr H (AC.gbar g))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hihi : tr.time i ≤ hi)
    (hgf : AC.gbar g < AC.freeze sp e.msg.slot)
    {l : AC.Lock} (hl : l ∈ (tr.projAC.state y i).locks)
    (hlabel : s₀ ≤ l.slot) (hold : l.slot < e.msg.slot)
    {L : AC.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ell.frame.tree)
    (hLr : L.root = l.block) (hstrict : ¬ Anc (tr.HonestBlocks H) L ell.frame.fcRoot) :
    ∃ a < i, ∃ ell₀ D Q,
      tr.projAC.CallAt y a ell₀ ∧ sp.ts s₀ ≤ tr.time a ∧
      tr.time a < AC.freeze sp e.msg.slot ∧
      ((∃ CV, AC.OptimisticLockAt tr.projAC y a l.slot D CV) ∨
        ∃ ell', AC.UpdateAt tr.projAC y a l.slot ell') ∧
      Q ∈ ell₀.frame.viableHeads ∧ Anc (tr.HonestBlocks H) L Q ∧
      ((Q ∈ ell.frame.viableHeads ∧
          Q ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot ∧
          ((floor ≤ ((tr.state y i).fg.σ Q.root).h ∧ (kindJ → Anc (tr.HonestBlocks H) J Q)) ∨
            (((tr.state y i).fg.σ Q.root).h + 1 = floor ∧ (tr.state y i).fg.Contest ∧
              (tr.state y i).fg.hmax = floor ∧
              (tr.state y i).fg.Anc (tr.state y i).fg.J Q))) ∨
        ((tr.state y a).fg.Contest ∧ (tr.state y a).fg.hmax = floor ∧
          ((tr.state y a).fg.σ Q.root).h + 1 = floor ∧ (tr.state y i).fg.hmax = floor + 1)) := by
  have hr := (Compose.goldilocks_ac_projection_from' hrun hnc).localRun
  have htvote := AC.vote_time_leU hr.toU hy ⟨ell, hc⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at htvote
  have hslot : e.msg.slot = sp.slot (tr.time i) := (AC.castAt_specU hr.toU hy hc).2.1
  rw [← hslot] at htvote
  obtain ⟨a, hai, ell₀, D, A, ha, hD, hAeq, ho, ⟨B, hB, hBr, hBA⟩, hcase⟩ :=
    AC.lock_write_witness hr hrun.vstart hy hl
  have hPhiU := (AC.frameIn_of_callAt hr hy hc.1).2
  have hPhi₀ := AC.frameIn_of_callAt hr hy ha
  obtain rfl : B = L := hr.coherent.1 hB (hPhiU hL) (hBr.trans hLr.symm)
  have htime : sp.ts s₀ ≤ tr.time a ∧ tr.time a < AC.freeze sp e.msg.slot := by
    rcases ho with ⟨CV, ell', B, hp, hs, hsel, -⟩ | ⟨ell', hu⟩
    · have hlo := (AC.ts_le_iff_le_slot sp (hr.time_nonneg a) (s₀ : Int)).mpr
        (by rw [hs]; exact_mod_cast hlabel)
      have hlt : tr.time a < sp.ts l.slot + 2 * sp.Δ := by
        unfold AC.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel with hn
        exact lt_of_not_ge (fun ht => hn (Or.inr (Or.inr (Or.inl (hs ▸ ht)))))
      have hts := (AC.ts_le_iff sp).mpr (show (l.slot : Int) ≤ (e.msg.slot : Int) - 1 by omega)
      refine ⟨hlo, ?_⟩
      unfold AC.freeze
      exact hlt.trans_le
        (add_le_add hts (mul_le_mul_of_nonneg_right (by norm_num) sp.toParams.hΔ.le))
    · have ht := hu.2.2.1
      change tr.time a = _ at ht
      have hts₀ := (AC.ts_le_iff sp).mpr (show (s₀ : Int) ≤ l.slot by exact_mod_cast hlabel)
      have hlabel' : l.slot + 2 ≤ e.msg.slot :=
        Compose.ts_add_two_le ((ht.symm.trans_le (hrun.time_mono hai.le)).trans htvote)
      refine ⟨hts₀.trans ((le_add_of_nonneg_right
        (mul_nonneg (by norm_num) sp.toParams.hΔ.le)).trans_eq ht.symm), ?_⟩
      have hts := (AC.ts_le_iff sp).mpr
        (show (l.slot : Int) + 1 ≤ (e.msg.slot : Int) - 1 by omega)
      unfold AC.freeze
      simp only [ACParams.ts] at ht hts ⊢
      linarith [sp.toParams.hΔ]
  rcases hcase with hbelow | ⟨Q, hQ, hv, hAQ⟩
  · exfalso
    apply hstrict
    have hroot := Healing.fcRoot_mono' hrun hy hai.le
    rw [← Node.frame_of_projAC_at' hrun.toLocalRun' hy ha,
      ← Node.frame_of_projAC_at' hrun.toLocalRun' hy hc.1] at hroot
    exact hBA.trans ((hbelow.mono hPhi₀.2).trans hroot)
  · refine ⟨a, hai, ell₀, D, Q, ha, htime.1, htime.2, ho, hv,
      hBA.trans (hAQ.mono hPhi₀.2), ?_⟩
    rcases hframe.viableHead_persists_stock' hrun hnc hf hy hai.le htime.1 hihi ha hv
      with ⟨⟨hQt, -, hvQ⟩, hw⟩ | hres
    · rw [← Node.frame_of_projAC_at' hrun.toLocalRun' hy hc.1] at hQt hvQ
      refine Or.inl ⟨hvQ, ⟨hQt, Or.inl ?_⟩, hw⟩
      apply AC.readPoint_blockStamp_lt_of_earlier_frame hr hrun.vstart hy ha hc hQ hQt htime.2
      intro r _ hrs
      exact (hnr y hy r (Compose.projAC_restartAt.mp hrs)).trans_lt hgf
    · exact Or.inr hres


/-- **The C′ case: a same-height contest keeps `J`.** Two cuts of honest nodes (writer `y` at
`a`, reader `x` at `i`) whose stores are both at `h_max = h_j + 1` with the same `h_max` have the
same justification cache `J` (safety, `J_eq_of_hj_eq_of_safe_with`). Combined with
`FrameWindow.viableHead_persists_stock'` case (B): a reader still in the contest at
`h_max = floor` keeps the writer's `J`, and the P-U-only head `Q` at `floor − 1` stays viable. -/
theorem J_eq_of_top_same_hmax' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {a i : Nat}
    (hta : (tr.state y a).fg.hmax = (tr.state y a).fg.hj + 1)
    (hti : (tr.state x i).fg.hmax = (tr.state x i).fg.hj + 1)
    (hm : (tr.state y a).fg.hmax = (tr.state x i).fg.hmax) :
    (tr.state y a).fg.J = (tr.state x i).fg.J := by
  have hRa := Node.fg_reachable_at' hrun.toLocalRun' hy a
  have hRi := Node.fg_reachable_at' hrun.toLocalRun' hx i
  have hu := Store.finalitySpec_updateFinality' (P := sp.toParams) (ACP := Payload sp.n)
  obtain ⟨-, hJa, -, ⟨Ba, hBa, hBaJ, hBahj⟩, -⟩ := Store.cache_invariants' hRa
  obtain ⟨-, hJi, -, ⟨Bi, hBi, hBiJ, hBihj⟩, -⟩ := Store.cache_invariants' hRi
  have hroots := Store.J_eq_of_hj_eq_of_safe_with hu hRa.reachableWith hRi.reachableWith
    hf (fun u v hu' hv' hval => held_atts_safe' hrun hnc hy hx a i u v hu' hv' hval) hBa hBi
    (by rw [hBahj, hBihj]; omega)
  rw [hBaJ, hBiJ] at hroots
  exact (Coherence.honest_blocks_coherent' hrun.toLocalRun' hnc).1
    ⟨y, hy, a, hJa⟩ ⟨x, hx, i, hJi⟩ hroots

end Consensus.Goldilocks.Healing

end
