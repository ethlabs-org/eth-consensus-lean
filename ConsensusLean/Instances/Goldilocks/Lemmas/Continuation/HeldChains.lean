module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable

public section

/-! # Crossing sets on held chains, without a fault bound

The chain-level G1.1 and G1.2 arguments at two reachable FG stores, stopped before the step that
needs an honest validator: they return the crossing set of at least `2q − n` validators, each
with a slashable pair among the attestations on the chains of the two held blocks. The
continuation's conviction bridge (`Continuation/Accountable`) excludes that set with
`ChainConvictedBelow` in place of the healthy fault bound.

* `Store.held_chain`: the chain of a held block of a reachable store, its state, and its
  attestations on the blocks at or below it;
* `Store.justified_crossing`: two held blocks with the same `h_j ≥ 1` and different `J` (the
  E2 pairs of two justification quorums);
* `Store.finalized_crossing`: a block finalized by a held `X` at height `h_F`, not on the chain
  of a held `W` of state height above `h_F` (G1.2's finality and crossing quorums). -/

namespace Consensus.Goldilocks.Store

/-- A target bit after counting is old or set by a counted non-timeout attestation on the
entry. -/
private theorem mem_foldl_target {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ (atts.foldl FG.ChainState.processAtt σ).target) :
    v ∈ σ.target ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.target ∨ (a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) := by
        unfold FG.ChainState.processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals aesop
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · rw [hh, hT] at hb'
      exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

/-- A justification `(h_j, J)` with `h_j ≥ 1` has a quorum of non-timeout attestations on the
chain with height pair `(h_j, J)` (with each target bit's attestation, for the induction). -/
private theorem justification_quorum (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)}
    {σ : FG.ChainState gp.n} (h : gp.chainState c = some σ) :
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false) := by
  refine gp.chainState_induction (P := fun c σ =>
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false))
    ⟨by simp [FG.ChainState.init], by simp [FG.ChainState.init]⟩ ?_ h
  intro c σ B σ' _ ⟨ht, hq⟩ hB
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append] at h ⊢
    exact Or.inl h
  have liftB : ∀ {a}, a ∈ B.atts → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append]
    exact Or.inr (by simpa using h)
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 hB
  have hT := fun v => @mem_foldl_target _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hT ⊢
  dsimp only at hT
  have ht₀ : ∀ v ∈ t, ∃ a ∈ gp.chainAtts (c ++ [B]),
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
    intro v hv
    rcases hT v hv with hv | ⟨a, ha, h'⟩
    · obtain ⟨a, ha, h'⟩ := ht v hv
      exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, liftB ha, h'⟩
  have hq₀ : 1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
      ∀ v ∈ Q, ∃ a ∈ gp.chainAtts (c ++ [B]),
        a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false := fun h1 =>
    let ⟨Q, hQ, hv⟩ := hq h1
    ⟨Q, hQ, fun v h => let ⟨a, ha, h'⟩ := hv v h; ⟨a, liftA ha, h'⟩⟩
  obtain ⟨F, hF', σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨⟨hq', -⟩, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨by simp [FG.ChainState.advance], fun _ => ⟨t, hq', ht₀⟩⟩
  · exact ⟨by simp [FG.ChainState.advance], hq₀⟩
  · exact ⟨ht₀, hq₀⟩

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- **The chain of a held block.** A block `B` of a reachable store has a chain from genesis
whose state is `B`'s, every block of which (and genesis) is at or below `B` in the store, and
whose attestations are on blocks at or below `B`. -/
theorem held_chain {st : Store P ACP} (hR : st.Reachable acp₀) {B : NodeBlock P ACP}
    (hB : B ∈ st.tree) :
    ∃ c : List (NodeBlock P ACP), P.fg.chainState (c.map Block.fgView) = some (st.σ B.root) ∧
      (∀ X ∈ P.genesisBlock acp₀ :: c, X ∈ st.tree ∧ st.Anc X B) ∧
      ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), ∃ Y ∈ st.tree, st.Anc Y B ∧ a ∈ Y.fgPayload := by
  obtain ⟨c, hc, hl, hlast, hσ⟩ := chain_state_of_chain P ACP acp₀ _ hR B hB
  obtain ⟨-, -, hg, -⟩ := accepted_tree P ACP acp₀ _ hR
  have hanc := anc_of_linked c _ hg hc hl B (by
    rcases hlast with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  refine ⟨c, hσ, fun X hX => ⟨?_, hanc X hX⟩, fun a ha => ?_⟩
  · rcases List.mem_cons.1 hX with rfl | h
    exacts [hg, hc _ h]
  · obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
    obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
    exact ⟨X, hc X hXc, hanc X (List.mem_cons_of_mem _ hXc), haX⟩

/-- **Two justifications at one height cross.** Held blocks of two reachable stores with the
same `h_j` and different `J` give at least `2q − n` validators, each with an E2 pair among the
attestations on blocks at or below the two held blocks. -/
theorem justified_crossing {st₁ st₂ : Store P ACP} (hR₁ : st₁.Reachable acp₀)
    (hR₂ : st₂.Reachable acp₀) {B B' : NodeBlock P ACP} (hB : B ∈ st₁.tree) (hB' : B' ∈ st₂.tree)
    (he : (st₁.σ B.root).hj = (st₂.σ B'.root).hj) (hne : (st₁.σ B.root).J ≠ (st₂.σ B'.root).J) :
    ∃ W : Finset (Fin P.n), 2 * P.fg.q - P.n ≤ W.card ∧ ∀ v ∈ W,
      ∃ a, (∃ Y ∈ st₁.tree, st₁.Anc Y B ∧ a ∈ Y.fgPayload) ∧
        ∃ b, (∃ Y ∈ st₂.tree, st₂.Anc Y B' ∧ b ∈ Y.fgPayload) ∧ a.val = v ∧ FG.slashable a b := by
  obtain ⟨c₁, h₁, -, ha₁⟩ := held_chain hR₁ hB
  obtain ⟨c₂, h₂, -, ha₂⟩ := held_chain hR₂ hB'
  have h0 : 1 ≤ (st₁.σ B.root).hj := by
    by_contra h0
    exact hne ((FG.chain_invariants P.fg _ _ h₁).2.2.2.1 (by omega) |>.trans
      ((FG.chain_invariants P.fg _ _ h₂).2.2.2.1 (by omega)).symm)
  obtain ⟨Q₁, hQ₁, hv₁⟩ := (justification_quorum P.fg h₁).2 h0
  obtain ⟨Q₂, hQ₂, hv₂⟩ := (justification_quorum P.fg h₂).2 (he ▸ h0)
  refine ⟨Q₁ ∩ Q₂, (FG.quorum_intersection P.fg Q₁ Q₂ hQ₁ hQ₂).1, fun v hv => ?_⟩
  obtain ⟨a, ha, rfl, hah, haT, hat⟩ := hv₁ v (Finset.mem_inter.1 hv).1
  obtain ⟨b, hb, hvb, hbh, hbT, hbt⟩ := hv₂ a.val (Finset.mem_inter.1 hv).2
  exact ⟨a, ha₁ a ha, b, ha₂ b hb, rfl,
    ⟨hvb.symm, Or.inr (Or.inr ⟨by rw [hah, hbh, he], hat, hbt, by rw [haT, hbT]; exact hne⟩)⟩⟩

/-- **A finalization off a higher chain crosses it** (G1.2 at chain level). A block `F`
finalized by the state of a held `X` of one reachable store, whose root is not the root of any
block at or below a held `W` of another reachable store with a state height above the finalized
height, gives at least `2q − n` validators, each with a slashable pair among the attestations on
blocks at or below `X` and at or below `W`. -/
theorem finalized_crossing {st₁ st₂ : Store P ACP} (hR₁ : st₁.Reachable acp₀)
    (hR₂ : st₂.Reachable acp₀) {X F W : NodeBlock P ACP} (hX : X ∈ st₁.tree)
    (hFr : F.root = (st₁.σ X.root).F) (hW : W ∈ st₂.tree)
    (hlt : (st₁.σ X.root).hF < (st₂.σ W.root).h)
    (hoff : ∀ Y ∈ st₂.tree, st₂.Anc Y W → Y.root ≠ F.root) :
    ∃ S : Finset (Fin P.n), 2 * P.fg.q - P.n ≤ S.card ∧ ∀ v ∈ S,
      ∃ a, (∃ Y ∈ st₁.tree, st₁.Anc Y X ∧ a ∈ Y.fgPayload) ∧
        ∃ b, (∃ Y ∈ st₂.tree, st₂.Anc Y W ∧ b ∈ Y.fgPayload) ∧ a.val = v ∧ FG.slashable a b := by
  obtain ⟨c₁, hσ₁, -, ha₁⟩ := held_chain hR₁ hX
  obtain ⟨c₂, hσ₂, hc₂, ha₂⟩ := held_chain hR₂ hW
  have hnot : (st₁.σ X.root).F ∉ P.fg.roots (c₂.map Block.fgView) := by
    intro hmem
    rw [← hFr] at hmem
    obtain ⟨Y, hY, hYF⟩ : ∃ Y ∈ P.genesisBlock acp₀ :: c₂, Y.root = F.root := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hmem
    exact hoff Y (hc₂ Y hY).1 (hc₂ Y hY).2 hYF
  have hF1 : 1 ≤ (st₁.σ X.root).hF := by
    by_contra h0
    apply hnot
    rw [(FG.chain_invariants P.fg _ _ hσ₁).2.2.2.2.1 (by omega)]
    exact List.mem_cons_self
  obtain ⟨S, hS, hSv⟩ := P.fg.finalization_meets_crossing hσ₁ hσ₂ hF1 hlt hnot
  refine ⟨S, hS, fun v hv => ?_⟩
  obtain ⟨a, ha, b, hb, hav, hab⟩ := hSv v hv
  exact ⟨a, ha₁ a ha, b, ha₂ b hb, hav, hab⟩

end Consensus.Goldilocks.Store

end
