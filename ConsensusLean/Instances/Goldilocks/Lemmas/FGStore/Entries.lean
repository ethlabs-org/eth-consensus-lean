module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run

public section

/-! # Goldilocks FG store: quorum-free entries (the core of G1.10)

Every attestation on the chain of `X` that counts for the entry `E` at height `h` (its height
pair is `(h, E)`) was processed by `y` before `T + Δ` (the own proposal is `y`'s first cut at
`T + Δ`, and its payload comes from the pool), so an honest one was signed before `T + Δ`, at a
public time, so at or before `T`, and (K1) at or before `T₀`: its signer is a namer of `E`. The
progress set of a state at height `h` with entry `E` holds only the signers of such attestations
on its chain, so it stays below `q` (and the target set, inside it): no block from `A` to `X`
justifies or times out, and the height and entry stay. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-! ## One block of the state transition -/

/-- A progress bit after counting is old or set by a counted attestation on the entry. -/
theorem mem_foldl_prog {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ (atts.foldl FG.ChainState.processAtt σ).prog) :
    v ∈ σ.prog ∨ ∃ a ∈ atts, a.val = v ∧ a.T = σ.Th := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.prog ∨ (a.val = v ∧ a.T = σ.Th) := by
        unfold FG.ChainState.processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals simp_all
        all_goals exact h.elim (fun h => Or.inr h.symm) Or.inl
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'.1, hT ▸ hb'.2⟩

/-- An accepted block counts its attestations into the progress set `p`; then the state keeps
its height, entry and progress set `p`, or (with a quorum in `p`) enters a new height with an
empty progress set. The target set stays inside the progress set. -/
theorem step_prog {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') (ht : σ.target ⊆ σ.prog) :
    σ'.target ⊆ σ'.prog ∧ ∃ p : Finset (Fin gp.n),
      (∀ v ∈ p, v ∈ σ.prog ∨ ∃ a ∈ B.atts, a.val = v ∧ a.T = σ.Th) ∧
      ((σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ σ'.prog = p) ∨ (gp.q ≤ p.card ∧ σ'.prog = ∅)) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  have hsub := FG.ChainState.foldl_processAtt_target_subset { σ with s := B.slot } B.atts ht
  have hP := fun v => @mem_foldl_prog _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hsub hP ⊢
  dsimp only at hsub hP ⊢
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  refine ⟨?_, p, hP, ?_⟩ <;>
    rcases hcase with ⟨hj, he'⟩ | ⟨-, hto, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact Finset.Subset.refl _
  · exact Finset.Subset.refl _
  · exact hsub
  · exact Or.inr ⟨hj.1.trans (Finset.card_le_card hsub), rfl⟩
  · exact Or.inr ⟨hto.1, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩

/-! ## The store of an honest node along the trace -/

/-- `fg_on_attestation` writes only the pool, adding at most its attestation. -/
theorem onAttestation_fields (st : Store P ACP) (b : FG.Att P.n) :
    (st.onAttestation b).blocks = st.blocks ∧ (st.onAttestation b).σ = st.σ ∧
      ∀ a ∈ (st.onAttestation b).atts, a ∈ st.atts ∨ a = b := by
  unfold onAttestation
  split_ifs
  · exact ⟨rfl, rfl, fun a ha => Or.inl ha⟩
  · exact ⟨rfl, rfl, fun a ha => by simpa using ha⟩

/-- `addAtts` writes only the pool, adding at most the attestations of its list. -/
theorem addAtts_fields (st : Store P ACP) (l : List (FG.Att P.n)) :
    (st.addAtts l).blocks = st.blocks ∧ (st.addAtts l).σ = st.σ ∧
      ∀ a ∈ (st.addAtts l).atts, a ∈ st.atts ∨ a ∈ l := by
  induction l generalizing st with
  | nil => exact ⟨rfl, rfl, fun a h => Or.inl h⟩
  | cons b l ih =>
    obtain ⟨h1, h2, h3⟩ := onAttestation_fields st b
    obtain ⟨h1', h2', h3'⟩ := ih (st.onAttestation b)
    refine ⟨h1'.trans h1, h2'.trans h2, fun a ha => ?_⟩
    rcases h3' a ha with ha | ha
    · rcases h3 a ha with ha | rfl
      · exact Or.inl ha
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ ha)

/-- An accepted block: its tests, its state transition, and the blocks, states and pool it
writes. -/
theorem onBlock_fields {st st' : Store P ACP} {B : NodeBlock P ACP}
    (h : st.onBlock B = some st') :
    ∃ (pr : Nat) (σ' : FG.ChainState P.n), st.blocks B.root = none ∧ (st.blocks pr).isSome ∧
      B.parent = some pr ∧
      P.fg.stateTransition (st.σ pr) B.fgView = some σ' ∧
      st'.blocks = Function.update st.blocks B.root (some B) ∧
      st'.σ = Function.update st.σ B.root σ' ∧ ∀ a ∈ st'.atts, a ∈ st.atts ∨ a ∈ B.fgPayload := by
  obtain ⟨pr, σ', hp, hn, hs, -, ht, rfl⟩ := onBlock_eq_some h
  let st₁ : Store P ACP :=
    { st with blocks := Function.update st.blocks B.root (some B),
              σ := Function.update st.σ B.root σ' }
  obtain ⟨hb, hσ, ha, -⟩ := updateFinality_spec st₁ σ'
  obtain ⟨h1, h2, h3⟩ := addAtts_fields (updateFinality st₁ σ') B.fgPayload
  refine ⟨pr, σ', hn, hs, hp, ht, h1.trans hb, h2.trans hσ, fun a h => ?_⟩
  rw [ha] at h3
  exact h3 a h

/-- An honest node starts from the initial store. -/
theorem store_zero (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) :
    tr.store y 0 = Store.init acp₀ := by
  simp [FGTrace.store, Trace.state, hr.init y hy]

/-- The store after an honest node's acceptance is the one that `fg_on_block` returns. -/
theorem accept_onBlock (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {k : Nat} {B : NodeBlock P ACP} (h : tr.AcceptAt y k B) :
    (tr.store y k).onBlock B = some (tr.store y (k + 1)) := by
  obtain ⟨rfl, hl⟩ := h
  rcases hr.exec k _ hl hy with ⟨-, h1, -⟩ | ⟨h2, -⟩
  · simpa [FGTrace.store, Trace.state, hl] using h1
  · cases h2

/-- One cut of an honest node: its store stays, accepts a block, or processes an attestation. -/
theorem store_step (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (m : Nat) :
    tr.store y (m + 1) = tr.store y m ∨
      (∃ B, tr.AcceptAt y m B ∧ (tr.store y m).onBlock B = some (tr.store y (m + 1))) ∨
      ∃ a, tr.CallAt y m (.attestation a) ∧
        tr.store y (m + 1) = (tr.store y m).onAttestation a := by
  by_cases hc : tr.node m = y ∧ tr.label m ≠ none
  · obtain ⟨rfl, hl⟩ := hc
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hl
    have hpost : tr.store (tr.node m) (m + 1) = (tr.post m).1 := by
      simp [FGTrace.store, Trace.state, hℓ]
    have hs := hr.exec m ℓ hℓ hy
    rw [hpost]
    cases ℓ with
    | block B acc =>
      rcases hs with ⟨rfl, h1, -⟩ | ⟨-, -, he⟩
      · exact Or.inr (Or.inl ⟨B, ⟨rfl, hℓ⟩, h1⟩)
      · exact Or.inl (by rw [he])
    | attestation a => exact Or.inr (Or.inr ⟨a, ⟨rfl, hℓ⟩, by rw [hs]⟩)
    | attest src signed => exact Or.inl hs.1
  · left
    simp only [FGTrace.store, Trace.state, hc, ↓reduceIte]

/-- A held root stays held, with the same block and state. -/
theorem held_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {k m : Nat}
    (hkm : k ≤ m) {r : Nat} {Z : NodeBlock P ACP} (hZ : (tr.store y k).blocks r = some Z) :
    (tr.store y m).blocks r = some Z ∧ (tr.store y m).σ r = (tr.store y k).σ r := by
  induction m, hkm using Nat.le_induction with
  | base => exact ⟨hZ, rfl⟩
  | succ m _ ih =>
    rcases store_step hr hy m with he | ⟨B, -, hB⟩ | ⟨a, -, he⟩
    · rwa [he]
    · obtain ⟨pr, σ', hn, -, -, -, hb, hσ, -⟩ := onBlock_fields hB
      have hne : r ≠ B.root := fun e => by rw [e, hn] at ih; cases ih.1
      rw [hb, hσ, Function.update_of_ne hne, Function.update_of_ne hne]
      exact ih
    · obtain ⟨h1, h2, -⟩ := onAttestation_fields (tr.store y m) a
      rw [he, h1, h2]
      exact ih

/-- An attestation in the pool of an honest node was processed by it at an earlier cut. -/
theorem pool_processed (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    (m : Nat) : ∀ a ∈ (tr.store y m).atts, ∃ k < m, tr.ProcessAt y k a := by
  induction m with
  | zero => simp [store_zero hr hy, Store.init]
  | succ m ih =>
    intro a ha
    have lift : ∀ a ∈ (tr.store y m).atts, ∃ k < m + 1, tr.ProcessAt y k a := fun a ha =>
      let ⟨k, hk, h⟩ := ih a ha; ⟨k, by omega, h⟩
    rcases store_step hr hy m with he | ⟨B, hB, hB'⟩ | ⟨b, hb, he⟩
    · exact lift a (he ▸ ha)
    · obtain ⟨-, -, -, -, -, -, -, -, h⟩ := onBlock_fields hB'
      rcases h a ha with ha | ha
      · exact lift a ha
      · exact ⟨m, by omega, _, hB, ha⟩
    · rw [he] at ha
      rcases (onAttestation_fields _ b).2.2 a ha with ha | rfl
      · exact lift a ha
      · exact ⟨m, by omega, _, hb, List.mem_singleton_self _⟩

/-- In an honest node's store, the state of a block is the transition of its parent's. -/
theorem step_σ (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {W : NodeBlock P ACP} (hW : W ∈ (tr.store y i).tree) {pr : Nat} (hp : W.parent = some pr) :
    P.fg.stateTransition ((tr.store y i).σ pr) W.fgView = some ((tr.store y i).σ W.root) := by
  rcases tree_accepted hr hy hW with rfl | ⟨k, hk, hA⟩
  · cases hp
  obtain ⟨pr', σ', -, hs, hp', ht, hb, hσ, -⟩ := onBlock_fields (accept_onBlock hr hy hA)
  rw [hp] at hp'
  cases hp'
  obtain ⟨Z, hZ⟩ := Option.isSome_iff_exists.1 hs
  have hWk : (tr.store y (k + 1)).blocks W.root = some W := by rw [hb]; simp
  rw [(held_mono hr hy hk.le hZ).2, (held_mono hr hy hk hWk).2, hσ, Function.update_self]
  exact ht

/-- In an honest node's store, genesis has the initial state. -/
theorem σ_genesis (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (m : Nat) :
    (tr.store y m).σ P.genesisRoot = FG.ChainState.init P.fg := by
  have h0 : (tr.store y 0).blocks P.genesisRoot = some (P.genesisBlock acp₀) := by
    simp [store_zero hr hy, Store.init]
  rw [(held_mono hr hy (Nat.zero_le m) h0).2, store_zero hr hy]
  rfl

/-- A multiple of `Δ` below `t + Δ`, `t` a multiple of `Δ`, is at most `t`. -/
private theorem le_of_dvd_lt {Δ x t : Int} (hΔ : 0 < Δ) (hx : Δ ∣ x) (ht : Δ ∣ t)
    (h : x < t + Δ) : x ≤ t := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := ht
  have : m < s + 1 := Int.lt_of_mul_lt_mul_left (by rw [Int.mul_add, Int.mul_one]; exact h) hΔ.le
  exact Int.mul_le_mul_of_nonneg_left (by omega) hΔ.le

variable (P ACP)

/-- **G1.10, the core.** -/
theorem quorum_free_entries : QuorumFreeEntries P ACP := by
  intro acp₀ H U tr 𝓔 T₀ T y hr _ hT hy hK hK' i X hX htime E hE h A hA hAX hAh hATh
  set st := tr.store y (i + 1)
  have hreach := store_reachable hr hy (i + 1)
  -- The attestations on the chain of `X` that name `E` are signed by namers of `E`.
  have hN : ∀ W ∈ st.tree, st.Anc W X → ∀ a ∈ W.fgPayload, a.T = E.root →
      a.val ∈ namers P ACP H tr T₀ E := by
    intro W hW _ a ha haT
    by_cases hv : a.val ∈ H
    swap
    · exact Or.inl hv
    have hlt : ∀ k < i, ∀ ℓ, tr.CallAt y k ℓ → tr.time k < T + P.Δ := by
      intro k hk ℓ hℓ
      rcases htime with ht | ⟨ht, hpX, hsX⟩
      · exact lt_of_le_of_lt (hr.time_mono hk.le) ht
      · exact ht ▸ hr.own_first y hy i X hX hpX (hsX.trans ht.symm) k hk ℓ hℓ
    have hproc : ∃ k, tr.ProcessAt y k a ∧ tr.time k < T + P.Δ := by
      rcases tree_accepted hr hy hW with rfl | ⟨k, hk, hacc⟩
      · cases ha
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact ⟨k, ⟨_, hacc, ha⟩, hlt k hk _ hacc⟩
      obtain rfl : W = X := by simpa using hacc.2.symm.trans hX.2
      rcases htime with ht | ⟨ht, hpX, hsX⟩
      · exact ⟨_, ⟨_, hacc, ha⟩, ht⟩
      obtain ⟨k, hk, hp⟩ := pool_processed hr hy _ a
        (hr.own_payload y hy _ W hacc hpX (hsX.trans ht.symm) a ha)
      exact ⟨k, hp, hlt k hk _ hp.choose_spec.1⟩
    obtain ⟨k, hp, hk⟩ := hproc
    obtain ⟨j, hj, src, hsign⟩ := hr.unforgeable y hy k a hp hv
    have hjT : tr.time j ≤ T := le_of_dvd_lt P.hΔ
      (hr.attest_public a.val hv j src (some a) hsign) hT
      (lt_of_le_of_lt (hr.time_mono hj.le) hk)
    exact Or.inr ⟨j, a, ⟨src, hsign⟩,
      not_lt.1 fun h' => hK' a.val hv j a ⟨src, hsign⟩ h' hjT E hE haT, haT⟩
  have hcard : ∀ p : Finset (Fin P.n), (∀ v ∈ p, v ∈ namers P ACP H tr T₀ E) →
      p.card < P.fg.q := fun p hp => by
    have := Set.ncard_le_ncard (s := (p : Set (Fin P.n))) hp (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    exact lt_of_le_of_lt this (hK E hE)
  -- The progress set of a state holds the signers of attestations on its chain on its entry.
  have hU : ∀ W, st.Anc (P.genesisBlock acp₀) W →
      (st.σ W.root).target ⊆ (st.σ W.root).prog ∧ ∀ v ∈ (st.σ W.root).prog,
        ∃ W' ∈ st.tree, st.Anc W' W ∧ ∃ a ∈ W'.fgPayload, a.val = v ∧ a.T = (st.σ W.root).Th := by
    intro W hW
    induction hW with
    | refl =>
      rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr hy]
      exact ⟨fun _ h => h, fun v hv => (Finset.notMem_empty v hv).elim⟩
    | tail _ hpar ih =>
      obtain ⟨-, h2, hp⟩ := id hpar
      obtain ⟨htp, p, hpv, hcase⟩ := step_prog (step_σ hr hy h2 hp) ih.1
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
  have hg := (accepted_tree P ACP acp₀ st hreach).2.2.2
  -- From `A` to `X`, no block leaves the height and entry.
  have hP : ∀ W, st.Anc A W → st.Anc W X →
      (st.σ W.root).h = h ∧ (st.σ W.root).Th = E.root := by
    intro W hAW
    induction hAW with
    | refl => exact fun _ => ⟨hAh, hATh⟩
    | tail hanc hpar ih =>
      intro hWX
      obtain ⟨h1, h2, hp⟩ := hpar
      have hW₁X := Relation.ReflTransGen.head ⟨h1, h2, hp⟩ hWX
      obtain ⟨ihh, ihT⟩ := ih hW₁X
      obtain ⟨-, p, hpv, hcase⟩ := step_prog (step_σ hr hy h2 hp) (hU _ (hg _ h1)).1
      have hpn : ∀ v ∈ p, v ∈ namers P ACP H tr T₀ E := by
        intro v hv
        rcases hpv v hv with hv | ⟨a, ha, hav, haT⟩
        · obtain ⟨W', hW't, hW', a, ha, hav, haT⟩ := (hU _ (hg _ h1)).2 v hv
          exact hav ▸ hN W' hW't (hW'.trans hW₁X) a ha (haT.trans ihT)
        · exact hav ▸ hN _ h2 hWX a ha (haT.trans ihT)
      rcases hcase with ⟨hh, hTh, -⟩ | ⟨hq, -⟩
      · exact ⟨hh.trans ihh, hTh.trans ihT⟩
      · exact absurd hq (not_le.2 (hcard p hpn))
  have hXt : X ∈ st.tree := by
    rcases hAX.cases_tail with rfl | ⟨_, -, -, hXt, -⟩
    · exact hA
    · exact hXt
  obtain ⟨hh, hTh⟩ := hP X hAX .refl
  refine ⟨hh, hTh, hcard _ fun v hv => ?_⟩
  obtain ⟨W', hW't, hW', a, ha, hav, haT⟩ := (hU X (hg X hXt)).2 v hv
  exact hav ▸ hN W' hW't hW' a ha (haT.trans hTh)

end Consensus.Goldilocks.Store

end
