module
public import AvailableChainPCSAProofs.Proofs.Shared.HeadCover
public import AvailableChainFGSA.Proofs.Head.Pool
public import AvailableChainGeneric.Proofs.Pure.SupportCounts

public section

/-! CL1 and CL3 on resolved vote counts (pcsa34-r4.3 §§5.0, 5.2.1). -/

namespace AvailableChain.PCSA

open Gen.Pure

/-- An actual gate result is a strict majority of its late participants. -/
theorem pcsa_gate_result_majority (p : Params) (v : GridCO.State p.n .root)
    (a X : Block) (s : Slot) (h : SA.Root.confirmationFrom p.toParams a v s = some X) :
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s X := by
  unfold SA.Root.confirmationFrom GridCO.confirmationFrom at h
  dsimp only at h
  split at h
  · rename_i htest
    cases h
    exact htest
  · contradiction

/-- CL1: majority support sets from one label give compatible results when
relay puts their union in both denominators and shared seats resolve one head. -/
theorem pcsa_cl1_results_compatible {n : Nat} (X Y : Block)
    (SX SY Lx Ly : Finset (Fin n)) (heads : Fin n → Block)
    (hLx : SX ∪ SY ⊆ Lx) (hLy : SX ∪ SY ⊆ Ly)
    (hX : Lx.card < 2 * SX.card) (hY : Ly.card < 2 * SY.card)
    (hSX : ∀ i ∈ SX, Block.Preceq X (heads i))
    (hSY : ∀ i ∈ SY, Block.Preceq Y (heads i)) :
    Block.Compatible X Y := by
  obtain ⟨i, hi⟩ := two_majorities_intersect hLx hLy hX hY
  obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hi
  exact block_compatible_of_common (hSX i hx) (hSY i hy)

/-- CL1 applies to actual same-label gate results once their support counts
and common resolved heads have been supplied. -/
theorem pcsa_cl1_gate_results_compatible (p : Params)
    (left right : GridCO.State p.n .root) (a b X Y : Block) (s : Slot)
    (SX SY : Finset (Fin p.n)) (heads : Fin p.n → Block)
    (hX : SA.Root.confirmationFrom p.toParams a left s = some X)
    (hY : SA.Root.confirmationFrom p.toParams b right s = some Y)
    (hSX : SX.card = SA.Root.prefixSupport p.toParams left s X)
    (hSY : SY.card = SA.Root.prefixSupport p.toParams right s Y)
    (hleft : SX ∪ SY ⊆ (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine left s)).toFinset)
    (hright : SX ∪ SY ⊆ (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine right s)).toFinset)
    (hheadsX : ∀ i ∈ SX, Block.Preceq X (heads i))
    (hheadsY : ∀ i ∈ SY, Block.Preceq Y (heads i)) : Block.Compatible X Y := by
  have hmajX := pcsa_gate_result_majority p left a X s hX
  have hmajY := pcsa_gate_result_majority p right b Y s hY
  rw [Gen.AC.Root.vote_pool_voterCount_card, ← hSX] at hmajX
  rw [Gen.AC.Root.vote_pool_voterCount_card, ← hSY] at hmajY
  exact pcsa_cl1_results_compatible X Y SX SY _ _ heads hleft hright hmajX hmajY hheadsX hheadsY

/-- Stage 1 leaves all stored blocks active. The resolution domain stays
cumulative, as required by the root wire model. -/
theorem pcsa_actView_blocks_of_genesis (st : State n)
    (hF : st.fg.F = SimplexFG.FGBlock.genesis) : (actView st).blocks = st.base.blocks := by
  unfold actView activeCompatible
  rw [hF]
  dsimp only [eraseFG]
  apply List.filter_eq_self.mpr
  intro B _
  rw [block_compatible_comm]
  exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)

/-- In stage 1, ordinary scores equal the gate's pinned-domain scores. -/
theorem pcsa_gate_score_of_genesis (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (hF : st.fg.F = SimplexFG.FGBlock.genesis) (hd : st.base.headDomain = none) :
    SA.Root.prefixSupport p.toParams (actView st) s B =
      GridCO.goldfishScore st.base.blocks
        (GridCO.cleanSupport p.toParams.engine (actView st) s)
        (GridCO.cleanSupport p.toParams.engine (actView st) s) B := by
  unfold SA.Root.prefixSupport GridCO.prefixSupport GridCO.goldfishScore
  rw [pcsa_actView_blocks_of_genesis st hF]
  change GridCO.goldfishScoreOn (GridCO.resolutionTree st.base) _ _ _ _ = _
  simp only [GridCO.resolutionTree, hd, Option.getD_none]

/-- CL3: a gate result is below the head over the same late votes and support.
The explicit path premise permits the full tree or a retained voter tree. -/
theorem pcsa_cl3_result_below_head
    (p : Params) (st : State p.n) (c : Option (PC p.n)) (s : Slot) (X : Block)
    (tree : List Block) (support : List (GridCO.Wire p.n .root))
    (hF : st.fg.F = SimplexFG.FGBlock.genesis) (hd : st.base.headDomain = none)
    (hresult : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
      (actView st) s = some X)
    (hsupport : support ⊆ GridCO.lateVotes p.toParams.engine (actView st) s)
    (hforward : GridCO.cleanSupport p.toParams.engine (actView st) s ⊆ support)
    (hanchor : Block.Compatible (liveRoot p st c) X)
    (hpath : ∀ C, Block.Prec (liveRoot p st c) C → Block.Preceq C X → C ∈ tree) :
    Block.Preceq X (headInTree p st c tree
      (GridCO.lateVotes p.toParams.engine (actView st) s) support) := by
  let v := actView st
  let P := GridCO.cleanSupport p.toParams.engine v s
  let L := GridCO.lateVotes p.toParams.engine v s
  have hPL : P ⊆ L := fun _ ho =>
    FGSA.fgsa_early_subset_late p v s (List.mem_filter.mp ho).1
  have hc : ∀ o ∈ P, ∀ i, GridCO.headSeat? o = some i →
      GridCO.equivocates L i = false := by
    intro o ho i hi
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨a, ha, b, hb, hne, hia, hib⟩ := (Gen.AC.Root.cap_pair L i).mp he
    have hunique : ∀ u ∈ L, GridCO.headSeat? u = some i → u = o := by
      intro u hu hui
      have hlabel : ∀ w ∈ L, GridCO.headLabel? w = some s := by
        intro w hw
        simpa only [GridCO.votesAt, List.mem_filter, beq_iff_eq] using
          (List.mem_filter.mp (List.mem_filter.mp hw).1).2
      have hsame : GridCO.sameSeat u o = true := by
        have hu' := hlabel u hu
        have ho' := hlabel o (hPL ho)
        cases u with | mk au pu =>
          cases o with | mk ao po =>
            cases au <;> cases pu <;> cases ao <;> cases po <;>
              dsimp only [GridCO.headLabel?, GridCO.headSeat?, GridCO.sameSeat]
                at hui hi hu' ho' ⊢ <;>
              simp_all
      have hnot := (List.mem_filter.mp ho).2
      have hfalse : L.any (fun u => GridCO.sameSeat u o && u != o) = false := by
        simpa only [Bool.not_eq_true'] using hnot
      have hf := List.any_eq_false.mp hfalse u hu
      simpa only [hsame, Bool.true_and, bne_iff_ne, not_not] using hf
    exact hne ((hunique a ha hia).trans (hunique b hb hib).symm)
  have hmaj := pcsa_gate_result_majority p v _ X s hresult
  rw [pcsa_gate_score_of_genesis p st s X hF hd] at hmaj
  apply pcsa_cl2_head_extends_majority p st c tree st.base.blocks P L L support X
    hPL hc _ _ hsupport hmaj hanchor hpath
  · intro o ho i _ hv
    exact Or.inl ⟨hforward ho, hv⟩
  · intro o ho i _
    exact Or.inl ho

/-- Early clean support is in the resolved support used by the same-label head. -/
theorem pcsa_cleanSupport_subset_headSupport (p : Params) (st : State p.n) (s : Slot) :
    GridCO.cleanSupport p.toParams.engine (actView st) s ⊆
      (GridCO.votesAt st.base s).filter (fun o =>
        match GridCO.resolvedHead? (actView st) o with
        | some B => decide (B.slot ≤ s)
        | none => false) := by
  intro o ho
  obtain ⟨hm, hr⟩ := List.mem_filter.mp (List.mem_filter.mp ho).1
  have hlabel : GridCO.headLabel? o = some s := by
    simpa only [beq_iff_eq] using (List.mem_filter.mp hm).2
  refine List.mem_filter.mpr ⟨hm, ?_⟩
  cases hh : GridCO.resolvedHead? (actView st) o with
  | none =>
    dsimp only [GridCO.resolvedBefore] at hr
    rw [hh] at hr
    dsimp only at hr
    simp only [Bool.false_eq_true] at hr
  | some B =>
    dsimp only [GridCO.resolvedBefore] at hr
    rw [hh] at hr
    dsimp only at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq,
      hlabel, Option.getD_some] at hr
    simp only [decide_eq_true_eq]
    exact hr.1.1

/-- CL3 for an explicit same-label head over the gate's late votes.
Root compatibility and retained path membership come from the clean induction.
The current slot need not equal the gate label. -/
theorem pcsa_cl3_result_below_getHead (p : Params) (st : State p.n) (s : Slot) (X : Block)
    (hF : st.fg.F = SimplexFG.FGBlock.genesis) (hd : st.base.headDomain = none)
    (hresult : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
      (actView st) s = some X)
    (hanchor : Block.Compatible (liveRoot p st (proposerPC p st)) X)
    (hpath : ∀ C, Block.Prec (liveRoot p st (proposerPC p st)) C → Block.Preceq C X →
      C ∈ erasedList st (fullTree p st)) :
    Block.Preceq X (getHead p st (proposerPC p st)
      (GridCO.lateVotes p.toParams.engine (actView st) s)
      ((GridCO.lateVotes p.toParams.engine (actView st) s).filter (fun o =>
        match GridCO.resolvedHead? (actView st) o with
        | some B => decide (B.slot ≤ s)
        | none => false))) := by
  unfold getHead
  refine pcsa_cl3_result_below_head p st (proposerPC p st) s X _ _ hF hd hresult
    ?_ ?_ hanchor hpath
  · intro o ho
    exact (List.mem_filter.mp ho).1
  · intro o ho
    have hsub := pcsa_cleanSupport_subset_headSupport p st s ho
    have hr := (List.mem_filter.mp hsub).2
    apply List.mem_filter.mpr
    refine ⟨FGSA.fgsa_early_subset_late p (actView st) s (List.mem_filter.mp ho).1, ?_⟩
    cases hh : GridCO.resolvedHead? (actView st) o with
    | none => simpa only [hh] using hr
    | some B => simpa only [hh] using hr

/-- At the gate for label `s`, the executable finality head reads label `s + 1`.
CL3 above uses label `s`; it gives no prefix bound for this different vote pool. -/
theorem pcsa_fgHead_eq_getHead_at_gate (p : Params) (st : State p.n) (s : Slot)
    (hslot : st.slot p = s + 1) :
    fgHead p st = getHead p st (proposerPC p st) (GridCO.votesAt st.base (s + 1))
      ((GridCO.votesAt st.base (s + 1)).filter (fun o =>
        match GridCO.resolvedHead? (actView st) o with
        | some B => decide (B.slot ≤ s + 1)
        | none => false)) := by
  unfold fgHead
  rw [hslot]
  rfl

end AvailableChain.PCSA
end
