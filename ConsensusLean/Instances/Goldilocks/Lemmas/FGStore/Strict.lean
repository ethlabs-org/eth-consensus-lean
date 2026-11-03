module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks FG store: the finalized block is strictly below its finalizer

In a reachable store, `Σ.F` other than genesis is finalized by the state of a strict descendant
in the tree (`F_lt_finalizer`): the finality votes for the pair `(h_F, F)` are counted only in
blocks of a greater height, which strictly extend `F` (workbench#12 §4). (`Σ.F = Σ.J` itself is
possible away from genesis: a chain state can finalize its latest justified pair, and
`update_finality` then moves `Σ.F` onto `Σ.J`.) Used by `Compose/Service/Held`
(`updater_F_anc_proposal_before`).

The proof: a state's finalization is its parent's or one of its parent's pending pairs, all
roots of the chain below the block; that chain's blocks are at lower slots, so a block other
than genesis is never the finalization of its own state. -/

namespace Consensus.Goldilocks.FG.FGParams

variable (gp : FGParams)

/-- The height events keep the latest block; they keep the entry or enter a new height with the
latest block; the entry, finalization and pending pairs stay among the old entry, finalization,
latest block and pending pairs. -/
private theorem heightEvents_fields (σ : ChainState gp.n) :
    (gp.heightEvents σ).L = σ.L ∧
      ∀ R : Nat → Prop, R σ.Th → R σ.F → R σ.L → (∀ p ∈ σ.pending, R p.2) →
        R (gp.heightEvents σ).Th ∧ R (gp.heightEvents σ).F ∧
          ∀ p ∈ (gp.heightEvents σ).pending, R p.2 := by
  obtain ⟨F, hF, σ₁, rfl, hc, hcase⟩ := gp.heightEvents_cases σ
  have hF' : ∀ R : Nat → Prop, R σ.F → (∀ p ∈ σ.pending, R p.2) → R F := by
    intro R h1 h2
    rcases hc with ⟨rfl, -⟩ | ⟨hm, -⟩
    · exact h1
    · exact h2 _ hm
  have hp' : ∀ p ∈ σ.pending.filter (fun p => hF < p.1), p ∈ σ.pending :=
    fun p hp => List.mem_of_mem_filter hp
  rcases hcase with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ <;> rw [he] <;>
    dsimp only [ChainState.advance]
  · refine ⟨rfl, fun R hTh hFR hL hp => ⟨hL, hF' R hFR hp, ?_⟩⟩
    intro q hq
    rcases List.mem_append.1 (List.mem_of_mem_drop hq) with hq | hq
    · exact hp q (hp' q hq)
    · simp only [List.mem_singleton] at hq
      subst hq
      exact hTh
  · exact ⟨rfl, fun R _ hFR hL hp => ⟨hL, hF' R hFR hp, fun q hq => hp q (hp' q hq)⟩⟩
  · exact ⟨rfl, fun R hTh hFR _ hp => ⟨hTh, hF' R hFR hp, fun q hq => hp q (hp' q hq)⟩⟩

/-- An accepted block's state: the counted state with the block as latest block, through the
height events; its finalization is the old one or a pending pair's. -/
private theorem stateTransition_fields {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.F = σ.F ∨ ∃ p ∈ σ.pending, p.2 = σ'.F) ∧ ∃ σ₀ : ChainState gp.n, σ₀.L = B.root ∧
      σ₀.Th = σ.Th ∧ σ₀.F = σ.F ∧ σ₀.pending = σ.pending ∧ gp.heightEvents σ₀ = σ' := by
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he
  refine ⟨?_, { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }, rfl, rfl,
    rfl, rfl, he⟩
  obtain ⟨F, hF, σ₁, rfl, hc, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hF : σ'.F = F := by
    rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [← he, he'] <;> rfl
  rcases hc with ⟨hc, -⟩ | ⟨hc, -⟩
  · exact Or.inl (hF.trans hc)
  · exact Or.inr ⟨_, hc, hF.symm⟩

/-- The finalization and the pending pairs of a chain's state are roots of the chain. -/
private theorem mem_roots_F_pending {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (h : gp.chainState c = some σ) : σ.F ∈ gp.roots c ∧ ∀ p ∈ σ.pending, p.2 ∈ gp.roots c := by
  suffices σ.Th ∈ gp.roots c ∧ σ.F ∈ gp.roots c ∧ σ.L ∈ gp.roots c ∧
      ∀ p ∈ σ.pending, p.2 ∈ gp.roots c from ⟨this.2.1, this.2.2.2⟩
  refine gp.chainState_induction (P := fun c σ => σ.Th ∈ gp.roots c ∧
    σ.F ∈ gp.roots c ∧ σ.L ∈ gp.roots c ∧ ∀ p ∈ σ.pending, p.2 ∈ gp.roots c)
    (by simp [ChainState.init, roots]) (fun c σ B σ' _ ih hB => ?_) h
  obtain ⟨hTh, hF, -, hp⟩ := ih
  have lift : ∀ r ∈ gp.roots c, r ∈ gp.roots (c ++ [B]) := fun r hr => by
    simp only [roots, List.map_append, List.map_cons, List.map_nil, List.mem_cons,
      List.mem_append] at hr ⊢
    tauto
  have hB' : B.root ∈ gp.roots (c ++ [B]) := by simp [roots]
  obtain ⟨-, σ₀, hL₀, hTh₀, hF₀, hp₀, rfl⟩ := gp.stateTransition_fields hB
  obtain ⟨hL', hR⟩ := gp.heightEvents_fields σ₀
  obtain ⟨h1, h2, h3⟩ := hR (· ∈ gp.roots (c ++ [B])) (hTh₀ ▸ lift _ hTh) (hF₀ ▸ lift _ hF)
    (hL₀ ▸ hB') (hp₀ ▸ fun p hq => lift _ (hp p hq))
  exact ⟨h1, h2, hL' ▸ hL₀ ▸ hB', h3⟩

/-- The blocks of a chain are at most at the slot of its state. -/
private theorem slot_le_of_chainState {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (h : gp.chainState c = some σ) : ∀ X ∈ c, X.slot ≤ σ.s := by
  refine gp.chainState_induction (P := fun c σ => ∀ X ∈ c, X.slot ≤ σ.s)
    (by simp) (fun c σ B σ' _ ih hB => ?_) h
  obtain ⟨-, hs, hlt⟩ := gp.stateTransition_L_s hB
  intro X hX
  rcases List.mem_append.1 hX with hX | hX
  · exact hs ▸ ((ih X hX).trans hlt.le)
  · rw [List.mem_singleton.1 hX, hs]

/-- A block whose root is not a root of the chain below it is not the finalization of its own
state. -/
private theorem F_ne_of_stateTransition {c : List (FGBlock gp.n)} {σ σ' : ChainState gp.n}
    {B : FGBlock gp.n} (hc : gp.chainState c = some σ) (hB : gp.stateTransition σ B = some σ')
    (hr : B.root ∉ gp.roots c) : σ'.F ≠ B.root := by
  intro he
  obtain ⟨hF, hp⟩ := gp.mem_roots_F_pending hc
  rcases (gp.stateTransition_fields hB).1 with h | ⟨p, hpm, h⟩
  · exact hr (he ▸ h ▸ hF)
  · exact hr (he ▸ h ▸ hp p hpm)

end Consensus.Goldilocks.FG.FGParams

namespace Consensus.Goldilocks.Store

/-- **The finalizer of `Σ.F` strictly extends it**. -/
theorem F_lt_finalizer {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) (hF : st.F ≠ P.genesisBlock acp₀) :
    ∃ B ∈ st.tree, (st.σ B.root).F = st.F.root ∧ st.Anc st.F B ∧ st.F ≠ B := by
  obtain ⟨hFt, -, -, -, -, -, B, hB, hBF⟩ := cache_invariants P ACP acp₀ st hr
  obtain ⟨-, ⟨X, hX, hXr, hXB⟩, -⟩ := entry_state_of_source P ACP acp₀ st hr B hB
  obtain ⟨-, ⟨hinj, -⟩, hg, -⟩ := accepted_tree P ACP acp₀ st hr
  have hXF : X = st.F := hinj hX hFt (hXr.trans hBF)
  refine ⟨B, hB, hBF, hXF ▸ hXB, ?_⟩
  rintro rfl
  obtain ⟨c, hc, -, hlast, hcs⟩ := chain_state_of_chain P ACP acp₀ st hr st.F hFt
  rcases hlast with ⟨-, h⟩ | hlast
  · exact hF h
  obtain ⟨c', rfl⟩ : ∃ c', c = c' ++ [st.F] :=
    ⟨c.dropLast, (List.dropLast_append_getLast? _ hlast).symm⟩
  have hca := (P.fg.chainState_append (c'.map Block.fgView) st.F.fgView).symm.trans
    ((congrArg P.fg.chainState (List.map_append ..)).symm.trans hcs)
  obtain ⟨σ, hσ, hstep⟩ := Option.bind_eq_some_iff.1 hca
  refine P.fg.F_ne_of_stateTransition hσ hstep (fun hm => ?_) hBF
  rcases List.mem_cons.1 hm with hm | hm
  · exact hF (hinj hFt hg hm)
  · obtain ⟨Y, hY, hm⟩ := List.mem_map.1 hm
    obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
    have hZF : Z = st.F := hinj (hc Z (List.mem_append_left _ hZ)) hFt hm
    have hle := P.fg.slot_le_of_chainState hσ _ (List.mem_map_of_mem hZ)
    rw [hZF] at hle
    exact absurd (P.fg.stateTransition_L_s hstep).2.2 hle.not_gt

end Consensus.Goldilocks.Store

end
