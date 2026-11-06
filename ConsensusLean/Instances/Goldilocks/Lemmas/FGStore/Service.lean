module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut

public section

/-! # Goldilocks FG store: the FG service lemmas (G1.6–G1.8, G1.9 (a))

G1.6 and G1.7's first window are theorem A's core (`window_justifies`); G1.7's second window is
the core again at the actual entry `X`, whose state is the same at every honest node
(`σ_eq_of_held`), so its `P_E` is `(h, T_h)`. G1.8 (a): from slot `u + max(δ_t, r)` on, the
honest proposal of each `g`-slot window includes a progress quorum of current-entry attestations,
with a mature entry, so the height is left there at the latest. G1.8 (b) is G1.7 with `T₁ ⪯ T_h`.
G1.9 (a): the justification step does not raise the head height floor for `σ = σ[B]`. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-! ## One block of the state transition -/

/-- Counting attestations keeps the progress bits and sets those of the attestations on the entry.
-/
theorem mem_foldl_prog_of {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ σ.prog ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) :
    v ∈ (atts.foldl FG.ChainState.processAtt σ).prog := by
  induction atts generalizing σ with
  | nil => exact h.resolve_right (by simp)
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    have key : σ.prog ⊆ (σ.processAtt a).prog ∧
        (a.h = σ.h ∧ a.T = σ.Th → a.val ∈ (σ.processAtt a).prog) := by
      clear * - σ a
      unfold FG.ChainState.processAtt
      rcases hf : a.fin with _ | q <;> dsimp only <;> split_ifs <;> simp_all
    rw [List.foldl_cons]
    refine ih ?_
    rw [hh, hT]
    rcases h with h | ⟨b, hb, hbv, hbh, hbT⟩
    · exact Or.inl (key.1 h)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl (hbv ▸ key.2 ⟨hbh, hbT⟩)
      · exact Or.inr ⟨b, hb, hbv, hbh, hbT⟩

/-- One accepted block keeps the height, the entry (and its slot) and the progress bits, adds
the bits of its attestations on the entry, and does not time out; or it enters the next height. -/
theorem step_entry {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ σ'.ThSlot = σ.ThSlot ∧
      (∀ v, (v ∈ σ.prog ∨ ∃ a ∈ B.atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) → v ∈ σ'.prog) ∧
      ¬ (gp.q ≤ σ'.prog.card ∧ σ.ThSlot + gp.δt ≤ B.slot)) ∨
    (σ'.h = σ.h + 1 ∧ σ'.Th = B.root ∧ σ'.ThSlot = B.slot) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  have hP := fun v (hv : v ∈ σ.prog ∨ ∃ a ∈ B.atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) =>
    mem_foldl_prog_of (σ := { σ with s := B.slot }) hv
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hP ⊢
  dsimp only at hP ⊢
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, hto, he'⟩ <;> rw [he']
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, hP, hto⟩

/-! ## The tree of an honest node -/

/-- Ancestry at one honest node holds at another that holds the descendant. -/
theorem anc_transfer (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n} (hy : y ∈ H)
    (hz : z ∈ H) {i j : Nat} {A B : NodeBlock P ACP} (h : (tr.store y i).Anc A B)
    (hB : B ∈ (tr.store z j).tree) : (tr.store z j).Anc A B := by
  induction h with
  | refl => exact .refl
  | tail _ hYB ih =>
    obtain ⟨Z, hZ⟩ := parent_held hr hz hB hYB.2.2
    obtain rfl : Z = _ := hr.coherent.1 (hr.tree_subset z hz j hZ.1)
      (hr.tree_subset y hy i hYB.1) (Option.some.inj (hZ.2.2.symm.trans hYB.2.2))
    exact (ih hZ.1).tail hZ

/-- Along ancestry the height does not decrease; while it stays, the entry and the progress
bits stay. -/
theorem anc_h (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A W : NodeBlock P ACP} (h : (tr.store y i).Anc A W) :
    ((tr.store y i).σ A.root).h ≤ ((tr.store y i).σ W.root).h ∧
      (((tr.store y i).σ W.root).h = ((tr.store y i).σ A.root).h →
        ((tr.store y i).σ W.root).Th = ((tr.store y i).σ A.root).Th ∧
        ((tr.store y i).σ A.root).prog ⊆ ((tr.store y i).σ W.root).prog) := by
  induction h with
  | refl => exact ⟨le_rfl, fun _ => ⟨rfl, subset_rfl⟩⟩
  | tail _ hYW ih =>
    have := ih.1
    rcases step_entry (step_σ hr hy hYW.2.1 hYW.2.2) with ⟨hh, hT, -, hp, -⟩ | ⟨hh, -, -⟩
    · refine ⟨by omega, fun he => ?_⟩
      obtain ⟨h1, h2⟩ := ih.2 (by omega)
      exact ⟨hT.trans h1, fun v hv => hp v (Or.inl (h2 hv))⟩
    · exact ⟨by omega, fun _ => by omega⟩

/-- The entry of a held block's state is a held block at the entry slot. -/
theorem entry_slot (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {W : NodeBlock P ACP} (hW : W ∈ (tr.store y i).tree) :
    ∃ E ∈ (tr.store y i).tree, E.root = ((tr.store y i).σ W.root).Th ∧
      E.slot = ((tr.store y i).σ W.root).ThSlot := by
  have hreach := store_reachable hr hy i
  have hg := (accepted_tree P ACP acp₀ _ hreach).2.2.1
  have hA := (accepted_tree P ACP acp₀ _ hreach).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr hy]
    exact ⟨_, hg, rfl, rfl⟩
  | tail _ hYW ih =>
    rcases step_entry (step_σ hr hy hYW.2.1 hYW.2.2) with ⟨-, hT, hs, -⟩ | ⟨-, hT, hs⟩
    · obtain ⟨E, hE, h1, h2⟩ := ih
      exact ⟨E, hE, h1.trans hT.symm, h2.trans hs.symm⟩
    · exact ⟨_, hYW.2.1, hT.symm, hs.symm⟩

/-- An entry block is one height above its parent. -/
theorem entry_parent (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {T T' : NodeBlock P ACP} (hT : ((tr.store y i).σ T.root).Th = T.root)
    (hp : ParentIn (tr.store y i).tree T' T) :
    ((tr.store y i).σ T'.root).h < ((tr.store y i).σ T.root).h := by
  have coh : Coherent (tr.store y i).tree := hr.coherent.mono (hr.tree_subset y hy i)
  rcases step_entry (step_σ hr hy hp.2.1 hp.2.2) with ⟨-, hTh, -⟩ | ⟨hh, -⟩
  · obtain ⟨E, hE, h1, hET, -⟩ :=
      (entry_state_of_source P ACP acp₀ _ (store_reachable hr hy i) T' hp.1).1
    have he : E = T := coh.1 hE hp.2.1 (h1.trans (hTh.symm.trans hT))
    rw [he] at hET
    have := (Goldilocks.Anc.slot_le coh hET).1
    have := coh.2 _ hp.1 _ hp.2.1 hp.2.2
    omega
  · omega

/-- An attestation of a held block is valid against its parent's state, so its height is at most the
parent's. -/
theorem row_parent (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {X : NodeBlock P ACP} (hX : X ∈ (tr.store y i).tree) {x : FG.Att P.n}
    (hx : x ∈ X.fgPayload) :
    ∃ X', ParentIn (tr.store y i).tree X' X ∧ x.h ≤ ((tr.store y i).σ X'.root).h := by
  rcases ((accepted_tree P ACP acp₀ _ (store_reachable hr hy i)).2.2.2 X hX).cases_tail with
    rfl | ⟨X', -, hX'⟩
  · exact absurd hx (by simp [Params.genesisBlock])
  · obtain ⟨⟨-, hv⟩, -⟩ := P.fg.stateTransition_eq_some.1 (step_σ hr hy hX'.2.1 hX'.2.2)
    refine ⟨X', hX', ?_⟩
    rcases (hv x hx).2 with ⟨h, -⟩ | ⟨-, -, -, -, h⟩
    · exact h.le
    · exact h.le

/-! ## Cache acceptance -/

/-- `afterJustification` changes only `h_max` (to `max Σ.h_max σ.h`) and, when the justification
step fires, `J` and `h_j` (to `σ.h_j`). -/
private theorem afterJustification_eq (st : Store P ACP) (σ : FG.ChainState P.n) :
    (afterJustification P ACP st σ).blocks = st.blocks ∧
      (afterJustification P ACP st σ).σ = st.σ ∧ (afterJustification P ACP st σ).F = st.F ∧
      (afterJustification P ACP st σ).hmax = max st.hmax σ.h ∧
      ((afterJustification P ACP st σ) = { st with hmax := max st.hmax σ.h } ∨
        (afterJustification P ACP st σ).hj = σ.hj) := by
  unfold afterJustification; dsimp only
  split <;> (try split) <;> first | exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩ |
    exact ⟨rfl, rfl, rfl, rfl, Or.inr rfl⟩

/-- The head height floor is `h_max` or `h_max − 1`. -/
theorem headHeightFloor_bounds (st : Store P ACP) :
    st.hmax - 1 ≤ st.headHeightFloor ∧ st.headHeightFloor ≤ st.hmax := by
  unfold headHeightFloor; split <;> omega

/-- A viable block's state height is at least `h_max − 1`: every `h ≤ h_max` is at most one above
it. -/
theorem height_le_of_isViable {st : Store P ACP} {B : NodeBlock P ACP} {h : Nat}
    (hv : st.IsViable B) (hh : h ≤ st.hmax) : h ≤ (st.σ B.root).h + 1 := by
  have hb := headHeightFloor_bounds st
  change st.headHeightFloor ≤ (st.σ B.root).h at hv
  omega

/-- The finalization step of `update_finality` moves `Σ.F` to `X` when its four tests pass on
the state after the justification step. -/
private theorem updateFinality_F (st : Store P ACP) (σ : FG.ChainState P.n)
    (X : NodeBlock P ACP) (hX : st.blocks σ.F = some X) (hFX : st.Anc st.F X) (hne : st.F ≠ X)
    (hJ : (afterJustification P ACP st σ).Anc X (afterJustification P ACP st σ).J)
    (hV : (afterJustification P ACP st σ).HasViableDescendant X) :
    (st.updateFinality σ).F = X := by
  obtain ⟨hb, -, hF, -⟩ := afterJustification_eq st σ
  unfold updateFinality
  extract_lets st₁ st₂
  have h2 : st₂ = afterJustification P ACP st σ := rfl
  have ht : st₂.tree = st.tree := by unfold Store.tree; rw [h2, hb]
  rw [show st₂.blocks σ.F = some X by rw [h2, hb, hX]]
  dsimp only
  rw [ite_eq_left ⟨by rw [Store.Anc, ht, h2, hF]; exact hFX, by rw [h2, hF]; exact hne,
    by rw [h2]; exact hJ, by rw [h2]; exact hV⟩]

variable (P ACP)

/-- **G1.6.** -/
theorem previousHeightJustified_entry : PreviousHeightJustifiedEntry P ACP := by
  intro acp₀ H U tr hr cF T a kF p i Bs Pr R hw hb
  obtain ⟨X, hJ, hXB, -, -, -, hfin⟩ := window_justifies hr hw
  exact ⟨X, hJ, hXB, (hfin hb).1, (hfin hb).2⟩

/-- **G1.7.** -/
theorem previousHeightNotJustified_entry : PreviousHeightNotJustifiedEntry P ACP := by
  intro acp₀ H U tr hr cF T a₀ kF p i Bs Pr R hw _
  obtain ⟨X, hJ, hXB, hh, hTh, hpend, -⟩ := window_justifies hr hw
  have hp := hw.proposal.1
  have h1 := (one_le_h hr hp hw.entry.1).1
  have hb : ((tr.store p (i + 1)).σ X.root).previousHeightJustified :=
    ⟨by rw [hJ.2.2.1]; omega, by rw [hJ.2.2.1, hh]⟩
  refine ⟨X, hJ, hXB, hpend, hh, hTh, hb, ?_⟩
  intro a₁ p₁ i₁ Bs₁ Pr₁ R₁ hw₁
  obtain ⟨Z, hJZ, hZB, -, -, -, hfin⟩ := window_justifies hr hw₁
  rw [σ_eq_of_held hr hw₁.proposal.1 hp hw₁.entry.1 hJ.1] at hfin
  obtain ⟨hF, hhF⟩ := hfin hb
  exact ⟨Z, hJZ.1, hZB, hF.trans hJ.2.2.2.1, hhF.trans hJ.2.2.1⟩

/-- **G1.8 (a).** -/
theorem crossing : Crossing P ACP := by
  intro acp₀ H U tr hr y hy k C T g r hC hT hTC _ _ hCs hw
  have coh : Coherent (tr.store y k).tree := hr.coherent.mono (hr.tree_subset y hy k)
  have hM := le_max_left P.δt r
  have hM' := le_max_right P.δt r
  obtain ⟨Y, Pr, p, j, hP, hYC, hwY, hYw, hq⟩ := hw (T.slot + max P.δt r) (by omega) (by omega)
  have hq' := hq (by omega)
  have hYt : Y ∈ (tr.store y k).tree := by
    by_cases hYC' : Y = C
    exacts [hYC' ▸ hC, (Goldilocks.Anc.mem hYC hYC').1]
  have hTY : (tr.store y k).Anc T Y := by
    rcases Goldilocks.Anc.total coh hTC hYC with h | h
    · exact h
    · have := (Goldilocks.Anc.slot_le coh h).1
      omega
  have hTne : Y ≠ T := by rintro rfl; omega
  obtain ⟨Pr', hTPr, hPrY⟩ := hTY.cases_tail.resolve_left hTne
  obtain ⟨hpH, -, -, -, hPrp, hYpar, hP5⟩ := hP
  have he : Pr' = Pr := hr.coherent.1 (hr.tree_subset y hy k hPrY.1)
    (hr.tree_subset p hpH j hPrp) (Option.some.inj (hPrY.2.2.symm.trans hYpar))
  rw [he] at hTPr hPrY
  have hPrt := hPrY.1
  have hle := anc_h hr hy hTPr
  by_cases hPh : ((tr.store y k).σ Pr.root).h = ((tr.store y k).σ T.root).h
  swap
  · have := (Goldilocks.Anc.slot_le coh (.single hPrY)).1
    exact ⟨Pr, hPrt, hTPr, (Relation.ReflTransGen.single hPrY).trans hYC, by omega, by omega⟩
  refine ⟨Y, hYt, hTY, hYC, ?_, by omega⟩
  have hPrTh : ((tr.store y k).σ Pr.root).Th = T.root := (hle.2 hPh).1.trans hT.2
  obtain ⟨E, hE, hEr, hEs⟩ := entry_slot hr hy hPrt
  rw [coh.1 hE hT.1 (hEr.trans hPrTh)] at hEs
  -- Every pooled current-entry attestation is counted at `Pr` already, or included in `Y`.
  have hrows : ∀ x ∈ (tr.store p j).atts, x.h = ((tr.store y k).σ T.root).h → x.T = T.root →
      x.val ∈ ((tr.store y k).σ Pr.root).prog ∨ ∃ a ∈ Y.fgPayload, a.val = x.val ∧
        a.h = ((tr.store y k).σ Pr.root).h ∧ a.T = ((tr.store y k).σ Pr.root).Th := by
    intro x hx hxh hxT
    by_cases hon : (tr.store p j).OnChain Pr x
    · left
      obtain ⟨X, -, hXPr, hxX⟩ := hon
      have hXPr' := anc_transfer hr hpH hy hXPr hPrt
      have hXt : X ∈ (tr.store y k).tree := by
        by_cases hXe : X = Pr
        exacts [hXe ▸ hPrt, (Goldilocks.Anc.mem hXPr' hXe).1]
      obtain ⟨X', hX'X, hxX'⟩ := row_parent hr hy hXt hxX
      rcases Goldilocks.Anc.total coh hXPr' hTPr with hXT | hTX
      · exfalso
        rcases (Relation.ReflTransGen.head hX'X hXT).cases_tail with rfl | ⟨T', hX'T', hT'T⟩
        · have := (Goldilocks.Anc.slot_le coh hXT).1
          have := coh.2 _ hX'X.1 _ hX'X.2.1 hX'X.2.2
          omega
        · have := (anc_h hr hy hX'T').1
          have := entry_parent hr hy hT.2 hT'T
          omega
      have hTX' : (tr.store y k).Anc T X' := by
        rcases hTX.cases_tail with rfl | ⟨Z, hTZ, hZX⟩
        · have := entry_parent hr hy hT.2 hX'X
          omega
        · obtain rfl : Z = X' :=
            coh.1 hZX.1 hX'X.1 (Option.some.inj (hZX.2.2.symm.trans hX'X.2.2))
          exact hTZ
      have h1 := anc_h hr hy hTX'
      have h2 := (anc_h hr hy ((Relation.ReflTransGen.single hX'X).trans hXPr')).1
      have hX'h : ((tr.store y k).σ X'.root).h = ((tr.store y k).σ T.root).h := by omega
      have hX'T := (h1.2 hX'h).1
      have h3 := anc_h hr hy hXPr'
      rcases step_entry (step_σ hr hy hX'X.2.1 hX'X.2.2) with ⟨hh, -, -, hp, -⟩ | ⟨hh, -, -⟩
      · exact (h3.2 (by omega)).2 (hp _ (Or.inr ⟨x, hxX, rfl, by omega,
          hxT.trans (hT.2.symm.trans hX'T.symm)⟩))
      · omega
    · right
      have hv : ((tr.store p j).σ Pr.root).validAtt x := by
        rw [σ_eq_of_held hr hpH hy hPrp hPrt]
        exact Or.inl ⟨by omega, hxT.trans hPrTh.symm⟩
      exact ⟨x, hP5 x hx hv hon, rfl, by omega, hxT.trans hPrTh.symm⟩
  rcases step_entry (step_σ hr hy hYt hYpar) with ⟨-, -, -, hp, hto⟩ | ⟨hh, -, -⟩
  · refine absurd ⟨le_trans hq' (Finset.card_le_card fun v hv => ?_), ?_⟩ hto
    · simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hv
      obtain ⟨x, ⟨hx, hxh, hxT⟩, rfl⟩ := hv
      exact hp _ (hrows x hx hxh hxT)
    · change ((tr.store y k).σ Pr.root).ThSlot + P.δt ≤ Y.slot
      omega
  · omega

/-- **G1.8 (b).** -/
theorem coverage : Coverage P ACP := by
  intro acp₀ H U tr hr cF T₁ T a₀ kF p i Bs Pr R hw hnb _ hT₁T _ _ X hJX hXB a₁ p₁ i₁ Bs₁ Pr₁ R₁
    hw₁
  obtain ⟨X', hJ', hX'B, -, hh', -, -, hZ⟩ :=
    previousHeightNotJustified_entry P ACP acp₀ H U tr hr cF T a₀ kF p i Bs Pr R hw hnb
  have hp := hw.proposal.1
  have hp₁ := hw₁.proposal.1
  have coh : ∀ {z} (_ : z ∈ H) (m : Nat), Coherent (tr.store z m).tree :=
    fun hz m => hr.coherent.mono (hr.tree_subset _ hz m)
  have hXX : X = X' := by
    rcases Goldilocks.Anc.total (coh hp (i + 1)) hXB hX'B with h | h
    · by_contra hne
      have := (hJ'.2.2.2.2 X hJX.1 hJX.2.1 h hne).1
      have := (one_le_h hr hp hJX.1).2
      have := hJX.2.2.1
      omega
    · by_contra hne
      have := (hJX.2.2.2.2 X' hJ'.1 hJ'.2.1 h (Ne.symm hne)).1
      have := (one_le_h hr hp hJ'.1).2
      have := hJ'.2.2.1
      omega
  rw [← hXX] at hZ
  obtain ⟨Z, hZt, hZB, hF, -⟩ := hZ a₁ p₁ i₁ Bs₁ Pr₁ R₁ hw₁
  have hX₁ := (held_mono hr hp₁ (Nat.le_succ i₁) hw₁.entry.1).1
  have hTX := anc_transfer hr hp hp₁ hJX.2.1 hX₁
  have hTt : T ∈ (tr.store p₁ (i₁ + 1)).tree := by
    by_cases hTe : T = X
    exacts [hTe ▸ hX₁, (Goldilocks.Anc.mem hTX hTe).1]
  refine ⟨Z, hZt, hZB, ?_, T, hTt, hF.symm, anc_transfer hr hp hp₁ hT₁T hTt⟩
  have := (Goldilocks.Anc.slot_le (coh hp₁ _) hZB).1
  have := (Goldilocks.Anc.slot_le (coh hp _) hXB).1
  have := (Goldilocks.Anc.slot_le (coh hp _) hT₁T).1
  have := hw.window.2
  have := hw₁.window.2
  omega

/-- **G1.9 (a).** The finalization step reads viability after the justification step: if
`σ.h ≥ Σ.h_max`, `B` itself is viable there (the floor is at most `h_max = σ.h`) and extends
`X`; otherwise `h_max` is unchanged, and a fired justification step sets `h_j := σ.h_j` with
`σ.h_j + 1 ≤ σ.h < h_max`, so there is no contest, the floor `h_max − 1` is at most the floor
after the `h_max` step, and the given viable descendant stays viable. So the four tests pass and
`Σ.F` moves to `X`. -/
theorem cache_acceptance : CacheAcceptance P ACP := by
  intro st B X hB hlt hX hXB hFX hne hJ hV
  obtain ⟨hb, hσ, -, hm, hj⟩ := afterJustification_eq st (st.σ B.root)
  have ht : (afterJustification P ACP st (st.σ B.root)).tree = st.tree := by
    unfold Store.tree; rw [hb]
  have hfA := headHeightFloor_bounds (afterJustification P ACP st (st.σ B.root))
  have hV' : (afterJustification P ACP st (st.σ B.root)).HasViableDescendant X := by
    by_cases hle : st.hmax ≤ (st.σ B.root).h
    · rw [Nat.max_eq_right hle] at hm
      refine ⟨B, ht ▸ hB, by rw [Store.Anc, ht]; exact hXB, ?_⟩
      unfold IsViable; rw [hσ]; omega
    · rw [Nat.max_eq_left (Nat.le_of_not_le hle)] at hm
      obtain ⟨B', hB', hanc, hv⟩ := hV
      have h₁ := headHeightFloor_bounds ({ st with hmax := max st.hmax (st.σ B.root).h } :
        Store P ACP)
      have hs₁ : ({ st with hmax := max st.hmax (st.σ B.root).h } : Store P ACP).hmax =
          st.hmax := Nat.max_eq_left (Nat.le_of_not_le hle)
      have hfl : (afterJustification P ACP st (st.σ B.root)).headHeightFloor ≤
          ({ st with hmax := max st.hmax (st.σ B.root).h } : Store P ACP).headHeightFloor := by
        rcases hj with h | h
        · rw [h]
        · have hc : ¬ (afterJustification P ACP st (st.σ B.root)).Contest := fun hc => by
            have := hc.1; omega
          rw [headHeightFloor, ite_eq_right hc]
          omega
      refine ⟨B', ht ▸ hB', by rw [Store.Anc, ht]; exact hanc, ?_⟩
      unfold IsViable at hv ⊢; rw [hσ]; exact hfl.trans hv
  rw [updateFinality_F st _ X hX hFX hne hJ hV']
  exact Relation.ReflTransGen.refl

end Consensus.Goldilocks.Store

end
