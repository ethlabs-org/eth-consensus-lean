module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows

public section

/-! # Goldilocks Healing, HR.4: the prefix-local quorum-free core

The core of `Store.quorum_free_entries` (G1.10) at one reachable FG store, with the time bounds
replaced by a premise on the store itself (`hr4-cut-scope.md` §2): if no attestation of an
honest signer on a block of the store names the entry `E`, then the progress set of every state
with entry `E` holds faulty validators only (fewer than `q`), so no block above an ancestor with
entry `E` leaves its height or entry (`entry_kept`). The justification of a state names its
entry at the justified height (`J_entry_of_reachable`), so a store's `Σ.J` whose entry is kept
would have a state of height `h_j`, against `h_j < h` (`J_compatible_of_rows`). -/

namespace Consensus.Goldilocks.Healing

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- One accepted block keeps the height and the entry, or enters the next height by itself; it
keeps the justification, or justifies the parent's entry at the parent's height. -/
private theorem step_fields' {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ((σ'.h = σ.h ∧ σ'.Th = σ.Th) ∨ (σ'.h = σ.h + 1 ∧ σ'.Th = B.root)) ∧
      ((σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h)) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- The state of a held block is above its justification: `h_j < h`. -/
theorem hj_lt_h (hr : st.Reachable acp₀) {B : NodeBlock P ACP} (hB : B ∈ st.tree) :
    (st.σ B.root).hj < (st.σ B.root).h := by
  obtain ⟨c, -, -, -, hc⟩ := Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hr B hB
  exact (FG.chain_invariants P.fg _ _ hc).2.2.1

/-- The justification of a held block's state names a held ancestor: genesis, or the entry of
the justified height. -/
theorem J_entry_of_reachable (hr : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∃ E ∈ st.tree, E.root = (st.σ W.root).J ∧ st.Anc E W ∧ (E = P.genesisBlock acp₀ ∨
      ((st.σ E.root).h = (st.σ W.root).hj ∧ (st.σ E.root).Th = E.root)) := by
  have hg := genesis_mem hr
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr]
    exact ⟨_, hg, rfl, .refl, Or.inl rfl⟩
  | tail _ hYW ih =>
    obtain ⟨X, -, hXr, ht⟩ := step_σ hr hYW.2.1 hYW.2.2
    rcases (step_fields' ht).2 with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
    · obtain ⟨E, hE, h1, hEY, h2⟩ := ih
      refine ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, ?_⟩
      rw [hj]
      exact h2
    · obtain ⟨⟨E, hE, h1, hEY, h2, h3⟩, -⟩ :=
        Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
      exact ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, Or.inr ⟨h2.trans hj.symm, h3.trans h1.symm⟩⟩

/-- The block named by a justification has at least its recorded height, including genesis. -/
theorem J_height_le (hr : st.Reachable acp₀) {W J : NodeBlock P ACP}
    (hW : W ∈ st.tree) (hJ : J ∈ st.tree) (hJr : J.root = (st.σ W.root).J) :
    (st.σ W.root).hj ≤ (st.σ J.root).h := by
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 W hW
  clear hW
  induction hA generalizing J with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr]
    exact Nat.zero_le _
  | tail _ hYW ih =>
    obtain ⟨_, _, _, ht⟩ := step_σ hr hYW.2.1 hYW.2.2
    rcases (step_fields' ht).2 with ⟨hroot, hh⟩ | ⟨hroot, hh⟩
    · rw [hh]
      exact ih hJ (hJr.trans hroot)
    · obtain ⟨⟨E, hE, hEr, _, hEh, _⟩, _⟩ :=
        Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
      have he : J = E := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.1.1
        hJ hE ((hJr.trans hroot).trans hEr.symm)
      rw [he, hEh, hh]

/-- **The prefix-local quorum-free core** (`hr4-cut-scope.md` §2; the counting of
`Store.quorum_free_entries` at one store). If no honest signer has an attestation naming `E` on a
block of the store and the faulty validators are fewer than `q`, then every block above an
ancestor with entry `E` keeps that ancestor's height and the entry `E`. -/
theorem entry_kept (hr : st.Reachable acp₀) {H : Set (Fin P.n)} (hq : Hᶜ.ncard < P.fg.q)
    {E : NodeBlock P ACP}
    (hE : ∀ W ∈ st.tree, ∀ a ∈ W.fgPayload, a.T = E.root → a.val ∉ H)
    {A X : NodeBlock P ACP} (hAX : st.Anc A X) (hATh : (st.σ A.root).Th = E.root) :
    (st.σ X.root).h = (st.σ A.root).h ∧ (st.σ X.root).Th = E.root := by
  have hcard : ∀ p : Finset (Fin P.n), (∀ v ∈ p, v ∉ H) → p.card < P.fg.q := fun p hp => by
    have := Set.ncard_le_ncard (s := (p : Set (Fin P.n))) (t := Hᶜ) hp (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    omega
  -- the progress set of a state holds the signers of attestations on its chain on its entry
  have hU : ∀ W, st.Anc (P.genesisBlock acp₀) W →
      (st.σ W.root).target ⊆ (st.σ W.root).prog ∧ ∀ v ∈ (st.σ W.root).prog,
        ∃ W' ∈ st.tree, st.Anc W' W ∧ ∃ a ∈ W'.fgPayload, a.val = v ∧
          a.T = (st.σ W.root).Th := by
    intro W hW
    induction hW with
    | refl =>
      rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr]
      exact ⟨fun _ h => h, fun v hv => (Finset.notMem_empty v hv).elim⟩
    | tail _ hpar ih =>
      obtain ⟨-, h2, hp⟩ := id hpar
      obtain ⟨-, -, -, ht⟩ := step_σ hr h2 hp
      obtain ⟨htp, p, hpv, hcase⟩ := Goldilocks.Store.step_prog ht ih.1
      refine ⟨htp, ?_⟩
      rcases hcase with ⟨-, hTh, hpe⟩ | ⟨-, hpe⟩
      · rw [hpe, hTh]
        intro v hv
        rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
        · obtain ⟨W', hW't, hW', a, ha, h'⟩ := ih.2 v hv
          exact ⟨W', hW't, hW'.tail hpar, a, ha, h'⟩
        · exact ⟨_, h2, .refl, a, ha, hav, haT⟩
      · rw [hpe]
        exact fun v hv => (Finset.notMem_empty v hv).elim
  have hg := (Goldilocks.Store.accepted_tree P ACP acp₀ st hr).2.2.2
  induction hAX with
  | refl => exact ⟨rfl, hATh⟩
  | tail _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨-, -, -, ht⟩ := step_σ hr h2 hp
    obtain ⟨ihh, ihT⟩ := ih
    obtain ⟨-, p, hpv, hcase⟩ := Goldilocks.Store.step_prog ht (hU _ (hg _ h1)).1
    have hpn : ∀ v ∈ p, v ∉ H := by
      intro v hv
      rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
      · obtain ⟨W', hW't, -, a, ha, hav, haT⟩ := (hU _ (hg _ h1)).2 v hv
        exact hav ▸ hE W' hW't a ha (haT.trans ihT)
      · exact hav ▸ hE _ h2 a ha (haT.trans ihT)
    rcases hcase with ⟨hh, hTh, -⟩ | ⟨hq', -⟩
    · exact ⟨hh.trans ihh, hTh.trans ihT⟩
    · exact absurd hq' (not_le.2 (hcard p hpn))

/-- **A high `Σ.J` is compatible with `B`** (`hr4-cut-scope.md` §3) when, for every high entry of
the store that conflicts with `B`, no honest signer has an attestation naming it on a block of
the store: otherwise its entry is kept above it (`entry_kept`), against `h_j < h` at the block
whose state justifies it. A genesis `Σ.J` is below `B`. -/
theorem J_compatible_of_rows (hr : st.Reachable acp₀) {H : Set (Fin P.n)}
    (hq : Hᶜ.ncard < P.fg.q) {U : Set (NodeBlock P ACP)} (hU : Coherent U) (hsub : st.tree ⊆ U)
    {B : NodeBlock P ACP} (hgB : Goldilocks.Anc U (P.genesisBlock acp₀) B) {Hz : Nat}
    (hrow : ∀ E ∈ st.tree, Hz + 1 ≤ (st.σ E.root).h → (st.σ E.root).Th = E.root →
      ¬ Compatible U E B → ∀ W ∈ st.tree, ∀ a ∈ W.fgPayload, a.T = E.root → a.val ∉ H)
    (hj : Hz + 1 ≤ st.hj) : Compatible U st.J B := by
  obtain ⟨-, hJ, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants P ACP acp₀ st hr
  obtain ⟨E, hE, hEr, hEBj, hcase⟩ := J_entry_of_reachable hr hBj
  obtain rfl : E = st.J := hU.1 (hsub hE) (hsub hJ) (hEr.trans hBjJ)
  rcases hcase with he | ⟨hEh, hETh⟩
  · rw [he]
    exact Or.inl hgB
  · by_contra hc
    have h₁ := (entry_kept hr hq (hrow _ hE (by omega) hETh hc) hEBj hETh).1
    have h₂ := hj_lt_h hr hBj
    omega

end Store

end Consensus.Goldilocks.Healing

end
