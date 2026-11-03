module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Finality

public section

/-! # Goldilocks FG store: a good window justifies its entry (theorem A's core)

Under `GW(E, a, k_F)` (`GoodWindow`), the chain of the serving block `B*` justifies the entry `E` at
`B*` or earlier, at a block `X` before which the height is not left; `X` enters the next height as
its own entry, with `(h, T_h)` pending; and at an entry whose previous height is justified `X` has
finalized `P_E` (`window_justifies`, theorem.md §3). The rows of `GW` are on `B*`'s chain (on the
parent's, or pooled and so included by the honest proposal); while `h` is current they stay valid
and their target and finality bits persist; no block before `B*` is old enough to time out (`v* ≤ u
+ D ≤ u + δ_t`), and `B*` tests justification before the timeout. The state of a block is the same
at every honest node that holds it (`σ_eq_of_held`): it is the fold over the block's chain, which
the coherent `U` fixes. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-! ## One block at chain level -/

/-- Counting an attestation only adds bits; one on the entry sets its target bit (a target) and
its finality bit (for a pending pair). -/
private theorem processAtt_bits {n : Nat} (σ : FG.ChainState n) (a : FG.Att n) :
    (∀ k, σ.fin k ⊆ (σ.processAtt a).fin k) ∧ σ.target ⊆ (σ.processAtt a).target ∧
      (a.h = σ.h → a.T = σ.Th → (a.timeout = false → a.val ∈ (σ.processAtt a).target) ∧
        ∀ pr, a.fin = some pr → pr ∈ σ.pending → a.val ∈ (σ.processAtt a).fin pr.1) := by
  unfold FG.ChainState.processAtt
  rcases hf : a.fin with _ | pr
  · dsimp only
    split_ifs with h1 h2 <;> simp_all
  · have hu : ∀ k, σ.fin k ⊆ Function.update σ.fin pr.1 (insert a.val (σ.fin pr.1)) k := by
      intro k
      rcases eq_or_ne k pr.1 with rfl | hk
      · rw [Function.update_self]
        exact Finset.subset_insert _ _
      · rw [Function.update_of_ne hk]
    dsimp only
    split_ifs with h1 h2 h3 h3 <;> simp_all [Function.update_apply]

/-- Counting a list of attestations only adds bits; each one on the entry sets its target bit
(a target) and its finality bit (for a pending pair). -/
theorem foldl_bits {n : Nat} (σ : FG.ChainState n) (atts : List (FG.Att n)) :
    (∀ k, σ.fin k ⊆ (atts.foldl FG.ChainState.processAtt σ).fin k) ∧
      σ.target ⊆ (atts.foldl FG.ChainState.processAtt σ).target ∧
      ∀ a ∈ atts, a.h = σ.h → a.T = σ.Th →
        (a.timeout = false → a.val ∈ (atts.foldl FG.ChainState.processAtt σ).target) ∧
        ∀ pr, a.fin = some pr → pr ∈ σ.pending →
          a.val ∈ (atts.foldl FG.ChainState.processAtt σ).fin pr.1 := by
  induction atts generalizing σ with
  | nil => exact ⟨fun _ => subset_rfl, subset_rfl, by simp⟩
  | cons b l ih =>
    obtain ⟨f1, t1, r1⟩ := processAtt_bits σ b
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [b]
    have hh : (σ.processAtt b).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt b).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    have hp : (σ.processAtt b).pending = σ.pending := by
      simpa using congrArg FG.ChainState.pending he
    obtain ⟨f2, t2, r2⟩ := ih (σ.processAtt b)
    refine ⟨fun k => (f1 k).trans (f2 k), t1.trans t2, fun a ha hah haT => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · obtain ⟨h1, h2⟩ := r1 hah haT
      exact ⟨fun ht => t2 (h1 ht), fun pr hpr hm => f2 _ (h2 pr hpr hm)⟩
    · obtain ⟨h1, h2⟩ := r2 a ha (hah.trans hh.symm) (haT.trans hT.symm)
      exact ⟨h1, fun pr hpr hm => h2 pr hpr (hp ▸ hm)⟩

/-- An accepted block's rows are not above its parent's height; the block keeps the height and
entry (its pending pairs among the parent's, its bits those of the counting), or enters the
next height as its own entry. -/
private theorem step_shape {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (∀ a ∈ B.atts, a.h ≤ σ.h) ∧
      ((σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ σ'.ThSlot = σ.ThSlot ∧ (∀ pr ∈ σ'.pending, pr ∈ σ.pending) ∧
        σ'.target = (B.atts.foldl FG.ChainState.processAtt { σ with s := B.slot }).target ∧
        σ'.fin = (B.atts.foldl FG.ChainState.processAtt { σ with s := B.slot }).fin) ∨
      (σ'.h = σ.h + 1 ∧ σ'.Th = B.root ∧ σ'.ThSlot = B.slot)) := by
  obtain ⟨⟨-, hv⟩, he⟩ := gp.stateTransition_eq_some.1 h
  refine ⟨fun a ha => ?_, ?_⟩
  · rcases (hv a ha).2 with ⟨h1, -⟩ | ⟨pr, -, -, -, h2⟩
    · exact h1.le
    · exact h2.le
  obtain ⟨f, p, t, hf⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he ⊢
  subst he
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases _
  rcases hcase with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ <;> rw [he]
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, fun pr hpr => List.mem_of_mem_filter hpr, rfl, rfl⟩

/-- The height events of a counted state at the current entry `(h₀, Tr)` of slot `u`, with `(h_j, J)
= (j, Jr)` and, at a height whose previous height is justified, `(j, Jr)` pending or finalized:
before the entry is `δ_t` old the state keeps all of this or justifies the entry (finalized `(j,
Jr)` at a height whose previous height is justified); with a target quorum and (at a height whose
previous height is justified, `(j, Jr)` pending) a finality quorum for `j`, it justifies. -/
private theorem events_current {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    (he : gp.heightEvents σ = σ') {h₀ Tr u j Jr L : Nat}
    (hh : σ.h = h₀) (hT : σ.Th = Tr) (hu : σ.ThSlot = u) (hj : σ.hj = j) (hJ : σ.J = Jr)
    (hL : σ.L = L) (hFj : σ.hF ≤ σ.hj) (hpw : σ.pending.Pairwise (fun p r => p.1 < r.1))
    (hmem : ∀ p ∈ σ.pending, σ.hF < p.1 ∧ p.1 ≤ σ.hj)
    (hP : 0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ.pending ∨ σ.hF = j ∧ σ.F = Jr) :
    (σ.s < u + gp.δt →
      (σ'.h = h₀ ∧ σ'.Th = Tr ∧ σ'.ThSlot = u ∧ σ'.hj = j ∧ σ'.J = Jr ∧
        (0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ'.pending ∨ σ'.hF = j ∧ σ'.F = Jr)) ∨
      (σ'.h = h₀ + 1 ∧ σ'.Th = L ∧ σ'.hj = h₀ ∧ σ'.J = Tr ∧ (h₀, Tr) ∈ σ'.pending ∧
        (0 < j ∧ j + 1 = h₀ → σ'.F = Jr ∧ σ'.hF = j))) ∧
    (gp.q ≤ σ.target.card → (0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ.pending → gp.q ≤ (σ.fin j).card) →
      σ'.h = h₀ + 1 ∧ σ'.Th = L ∧ σ'.hj = h₀ ∧ σ'.J = Tr ∧ (h₀, Tr) ∈ σ'.pending ∧
        (0 < j ∧ j + 1 = h₀ → σ'.F = Jr ∧ σ'.hF = j)) := by
  subst he hh hT hu hj hJ hL
  have hfg := FG.finality_before_gate gp σ
  obtain ⟨F, hF, hfp, hc⟩ := gp.finalizePrune_eq σ
  -- After the finality step: `h_F ≤ j`, and `(j, Jr)` still pending or finalized.
  have hle : hF ≤ σ.hj := by
    rcases hc with ⟨-, rfl⟩ | ⟨hm, -⟩
    · exact hFj
    · exact (hmem _ hm).2
  have hP₁ : 0 < σ.hj ∧ σ.hj + 1 = σ.h →
      (σ.hj, σ.J) ∈ σ.pending.filter (fun p => hF < p.1) ∨ hF = σ.hj ∧ F = σ.J := by
    intro hb
    simp only [List.mem_filter, decide_eq_true_eq]
    rcases hP hb with hm | ⟨e1, e2⟩ <;> rcases hc with ⟨rfl, rfl⟩ | ⟨hm', -⟩
    · exact Or.inl ⟨hm, (hmem _ hm).1⟩
    · by_cases hlt : hF < σ.hj
      · exact Or.inl ⟨hm, hlt⟩
      · have he : hF = σ.hj := le_antisymm (hmem _ hm').2 (not_lt.1 hlt)
        have := FG.eq_of_pairwise_fst_lt hpw hm' hm he
        exact Or.inr ⟨he, (Prod.ext_iff.1 this).2⟩
    · exact Or.inr ⟨e1, e2⟩
    · have := hmem _ hm'
      omega
  -- Justifying: the next height, entered by `L`, with the entry pending.
  have hjust : gp.justifies (gp.finalizePrune σ) →
      (gp.heightEvents σ).h = σ.h + 1 ∧ (gp.heightEvents σ).Th = σ.L ∧
        (gp.heightEvents σ).hj = σ.h ∧ (gp.heightEvents σ).J = σ.Th ∧
        (σ.h, σ.Th) ∈ (gp.heightEvents σ).pending ∧
        (0 < σ.hj ∧ σ.hj + 1 = σ.h → (gp.heightEvents σ).F = σ.J ∧
          (gp.heightEvents σ).hF = σ.hj) := by
    intro hJ'
    unfold FG.FGParams.heightEvents
    simp only [hJ', ↓reduceIte]
    rw [hfp] at hJ' ⊢
    dsimp only [FG.ChainState.advance]
    obtain ⟨-, hJ'⟩ := hJ'
    refine ⟨rfl, rfl, rfl, rfl, ?_, fun hb => ?_⟩
    · apply List.mem_of_getLast?
      rw [List.getLast?_drop]
      simp [FG.FGParams.KW]
    · rcases hJ' with hnb | he
      · exact absurd hb hnb
      dsimp only at he
      rcases hP₁ hb with hm | ⟨-, hF'⟩
      · have := (List.mem_filter.1 hm).2
        simp only [decide_eq_true_eq] at this
        omega
      · exact ⟨hF', he⟩
  have htg : (gp.finalizePrune σ).target = σ.target := by rw [hfp]
  have hj₁ : (gp.finalizePrune σ).hj = σ.hj := by rw [hfp]
  refine ⟨fun hs => ?_, fun htq hfq => hjust ⟨htg ▸ htq, ?_⟩⟩
  · by_cases hJ' : gp.justifies (gp.finalizePrune σ)
    · exact Or.inr (hjust hJ')
    have hTO : ¬ gp.timesOut (gp.finalizePrune σ) := by
      rw [hfp]
      rintro ⟨-, h⟩
      dsimp only at h
      omega
    have e : gp.heightEvents σ = gp.finalizePrune σ := by
      unfold FG.FGParams.heightEvents
      simp only [hJ', hTO, ↓reduceIte]
    rw [e, hfp]
    exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hP₁⟩
  · by_cases hb : 0 < σ.hj ∧ σ.hj + 1 = σ.h
    · right
      by_cases hm : (σ.hj, σ.J) ∈ σ.pending
      · exact (hfg hb hm hpw (fun p hp => (hmem p hp).2) (hfq hb hm)).1.trans hj₁.symm
      rcases hP₁ hb with hm' | ⟨e, -⟩
      · exact absurd (List.mem_of_mem_filter hm') hm
      · rw [hfp]
        exact e
    · left
      rw [hfp]
      exact hb

/-- One accepted block at the current entry: `events_current` for its counted state. -/
theorem step_current {gp : FG.FGParams} {c : List (FG.FGBlock gp.n)}
    {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n} (hc : gp.chainState c = some σ)
    (hB : gp.stateTransition σ B = some σ') {h₀ Tr u j Jr : Nat}
    (hh : σ.h = h₀) (hT : σ.Th = Tr) (hu : σ.ThSlot = u) (hj : σ.hj = j) (hJ : σ.J = Jr)
    (hP : 0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ.pending ∨ σ.hF = j ∧ σ.F = Jr) :
    (B.slot < u + gp.δt →
      (σ'.h = h₀ ∧ σ'.Th = Tr ∧ σ'.ThSlot = u ∧ σ'.hj = j ∧ σ'.J = Jr ∧
        (0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ'.pending ∨ σ'.hF = j ∧ σ'.F = Jr)) ∨
      (σ'.h = h₀ + 1 ∧ σ'.Th = B.root ∧ σ'.hj = h₀ ∧ σ'.J = Tr ∧ (h₀, Tr) ∈ σ'.pending ∧
        (0 < j ∧ j + 1 = h₀ → σ'.F = Jr ∧ σ'.hF = j))) ∧
    (gp.q ≤ (B.atts.foldl FG.ChainState.processAtt { σ with s := B.slot }).target.card →
      (0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ.pending →
        gp.q ≤ ((B.atts.foldl FG.ChainState.processAtt { σ with s := B.slot }).fin j).card) →
      σ'.h = h₀ + 1 ∧ σ'.Th = B.root ∧ σ'.hj = h₀ ∧ σ'.J = Tr ∧ (h₀, Tr) ∈ σ'.pending ∧
        (0 < j ∧ j + 1 = h₀ → σ'.F = Jr ∧ σ'.hF = j)) := by
  obtain ⟨-, hFj, -, -, -, -, hpw, hmem, -, -⟩ := FG.chain_invariants gp c σ hc
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 hB
  obtain ⟨f, p, t, hf⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he ⊢
  exact events_current he hh hT hu hj hJ rfl hFj hpw hmem hP


/-! ## Along the tree of an honest node -/

/-- An ancestor of a block is the block itself or an ancestor of its parent. -/
private theorem anc_parent {st : Store P ACP} {X W W' : NodeBlock P ACP} (hW' : W' ∈ st.tree)
    (hp : W.parent = some W'.root) (h : st.Anc X W) : X = W ∨ st.Anc X W' := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨Z, hXZ, hZ, -, hZp⟩
  · exact Or.inl rfl
  · have hZ : st.blocks Z.root = some Z := hZ
    have hW' : st.blocks W'.root = some W' := hW'
    have hr : Z.root = W'.root := Option.some.inj (hZp.symm.trans hp)
    obtain rfl : Z = W' := Option.some.inj (hZ.symm.trans (hr ▸ hW'))
    exact Or.inr hXZ

/-- The rows on the chain of a held block are not above its height, and those on its entry have
set their target bits (targets) and their finality bits (for pairs still pending). -/
theorem rows_counted (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (m : Nat)
    {W : NodeBlock P ACP} (hW : W ∈ (tr.store y m).tree) :
    ∀ X, (tr.store y m).Anc X W → ∀ r ∈ X.fgPayload, r.h ≤ ((tr.store y m).σ W.root).h ∧
      (r.h = ((tr.store y m).σ W.root).h → r.T = ((tr.store y m).σ W.root).Th →
        (r.timeout = false → r.val ∈ ((tr.store y m).σ W.root).target) ∧
        ∀ pr, r.fin = some pr → pr ∈ ((tr.store y m).σ W.root).pending →
          r.val ∈ ((tr.store y m).σ W.root).fin pr.1) := by
  have hg := (accepted_tree P ACP acp₀ _ (store_reachable hr hy m)).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro X hX r hrX
    rcases Relation.ReflTransGen.cases_tail hX with rfl | ⟨Z, -, -, -, hZ⟩
    · cases hrX
    · cases hZ
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨hle, hcase⟩ := step_shape (step_σ hr hy h2 hp)
    intro X hX r hrX
    have hX' := anc_parent h1 hp hX
    have hrh : r.h ≤ ((tr.store y m).σ W'.root).h := by
      rcases hX' with rfl | hX'
      · exact hle r hrX
      · exact (ih X hX' r hrX).1
    rcases hcase with ⟨hh, hT, -, hpend, htg, hfin⟩ | ⟨hh, -, -⟩
    · refine ⟨hh ▸ hrh, fun hrh' hrT => ?_⟩
      rw [hh] at hrh'
      rw [hT] at hrT
      obtain ⟨bf, bt, brow⟩ :=
        foldl_bits { (tr.store y m).σ W'.root with s := W.slot } W.fgView.atts
      rw [htg, hfin]
      rcases hX' with rfl | hX'
      · obtain ⟨a1, a2⟩ := brow r hrX hrh' hrT
        exact ⟨a1, fun pr hpr hm => a2 pr hpr (hpend pr hm)⟩
      · obtain ⟨a1, a2⟩ := (ih X hX' r hrX).2 hrh' hrT
        exact ⟨fun ht => bt (a1 ht), fun pr hpr hm => bf _ (a2 pr hpr (hpend pr hm))⟩
    · exact ⟨by omega, fun h' => by omega⟩

/-- The state of an entry block entered its height at the block's slot; at a height whose previous
height is justified, its predecessor is pending there. -/
theorem entry_facts (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {m : Nat}
    {T : NodeBlock P ACP} (hT : T ∈ (tr.store y m).tree)
    (hTe : ((tr.store y m).σ T.root).Th = T.root) :
    ((tr.store y m).σ T.root).ThSlot = T.slot ∧ (((tr.store y m).σ T.root).previousHeightJustified →
      (((tr.store y m).σ T.root).hj, ((tr.store y m).σ T.root).J) ∈
        ((tr.store y m).σ T.root).pending) := by
  have hreach := store_reachable hr hy m
  obtain ⟨-, hcoh, -, hg⟩ := accepted_tree P ACP acp₀ _ hreach
  rcases Relation.ReflTransGen.cases_tail (hg T hT) with rfl | ⟨Z, -, hZ, -, hp⟩
  · rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr hy]
    exact ⟨rfl, fun h => absurd h.1 (lt_irrefl 0)⟩
  have hst := step_σ hr hy hT hp
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ _ hreach Z hZ
  rcases (step_shape hst).2 with ⟨-, hTh, -⟩ | ⟨hh, -, hs⟩
  · exfalso
    obtain ⟨⟨E, hE, hEr, hEZ, -⟩, -⟩ := entry_state_of_source P ACP acp₀ _ hreach Z hZ
    have hE' : (tr.store y m).blocks E.root = some E := hE
    have hT' : (tr.store y m).blocks T.root = some T := hT
    have hEr' : E.root = T.root := hEr.trans (hTh.symm.trans hTe)
    obtain rfl : E = T := Option.some.inj (hE'.symm.trans (hEr' ▸ hT'))
    have := (hEZ.slot_le hcoh).1
    have := hcoh.2 Z hZ E hT hp
    omega
  · refine ⟨hs, fun hb => ?_⟩
    obtain ⟨-, -, -, -, h5⟩ := FG.height_step P.fg _ _ _ _ hc hst
    exact List.mem_of_getLast? ((h5 hh).2.2 hb).2

/-- Two honest nodes that hold a block give it the same state. -/
theorem σ_eq_of_held (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n} (hy : y ∈ H) (hz : z ∈ H)
    {i j : Nat} {B : NodeBlock P ACP} (hBy : B ∈ (tr.store y i).tree)
    (hBz : B ∈ (tr.store z j).tree) : (tr.store y i).σ B.root = (tr.store z j).σ B.root := by
  have hgz := (accepted_tree P ACP acp₀ _ (store_reachable hr hz j)).2.2.2
  have hg := (accepted_tree P ACP acp₀ _ (store_reachable hr hy i)).2.2.2 B hBy
  clear hBy
  induction hg with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr hy,
      σ_genesis hr hz]
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    -- The parent is held at `z` too: roots are injective on `U`.
    have hW'z : W' ∈ (tr.store z j).tree := by
      rcases Relation.ReflTransGen.cases_tail (hgz W hBz) with he | ⟨Z, -, hZ, -, hZp⟩
      · rw [he] at hp
        cases hp
      · obtain rfl : Z = W' := hr.coherent.1 (hr.tree_subset z hz j hZ)
          (hr.tree_subset y hy i h1) (Option.some.inj (hZp.symm.trans hp))
        exact hZ
    have e := step_σ hr hy h2 hp
    rw [ih hW'z, step_σ hr hz hBz hp] at e
    exact (Option.some.inj e).symm

/-- **Theorem A's core.** A good window's serving block justifies the entry on its chain, at a
block `X ⪯ B*` before which the height is not left; `X` enters the next height as its own entry
with `(h, T_h)` pending; at an entry whose previous height is justified, `X` has finalized `P_E`. -/
theorem window_justifies (hr : FGLocalRun acp₀ H U tr) {cF : Nat} {T : NodeBlock P ACP}
    {a kF : Nat} {p : Fin P.n} {i : Nat} {Bs Pr : NodeBlock P ACP} {R : Finset (FG.Att P.n)}
    (hw : GoodWindow P ACP H tr cF T a kF p i Bs Pr R) :
    ∃ X, JustifiesEntry P ACP (tr.store p (i + 1)) T ((tr.store p i).σ T.root).h X ∧
      (tr.store p (i + 1)).Anc X Bs ∧
      ((tr.store p (i + 1)).σ X.root).h = ((tr.store p i).σ T.root).h + 1 ∧
      ((tr.store p (i + 1)).σ X.root).Th = X.root ∧
      (((tr.store p i).σ T.root).h, T.root) ∈ ((tr.store p (i + 1)).σ X.root).pending ∧
      (((tr.store p i).σ T.root).previousHeightJustified →
        ((tr.store p (i + 1)).σ X.root).F = ((tr.store p i).σ T.root).J ∧
        ((tr.store p (i + 1)).σ X.root).hF = ((tr.store p i).σ T.root).hj) := by
  obtain ⟨⟨hp, hacc, -, -, hPr, hpar, hincl⟩, ⟨hT, hTe⟩, hTPr, ⟨-, hwin⟩, hq, hrows, -, hpool,
    ⟨hD, -⟩⟩ := hw
  obtain ⟨-, -, -, -, -, -, hbl, -, -⟩ := onBlock_fields (accept_onBlock hr hp hacc)
  have hreach := store_reachable hr hp (i + 1)
  obtain ⟨-, hcoh, -, -⟩ := accepted_tree P ACP acp₀ _ hreach
  -- `p`'s store before (`st`) and after (`st'`) accepting `Bs`.
  set st := tr.store p i
  set st' := tr.store p (i + 1)
  have hsub : st.tree ⊆ st'.tree := fun X hX => (held_mono hr hp (Nat.le_succ i) hX).1
  have hσ : ∀ X ∈ st.tree, st'.σ X.root = st.σ X.root :=
    fun X hX => (held_mono hr hp (Nat.le_succ i) hX).2
  have hBs : Bs ∈ st'.tree := by
    change st'.blocks Bs.root = some Bs
    rw [hbl, Function.update_self]
  rw [← hσ T hT] at hrows hTe ⊢
  rw [← hσ Pr hPr] at hincl
  have hPrBs : ParentIn st'.tree Pr Bs := ⟨hsub hPr, hBs, hpar⟩
  have hTPr' : st'.Anc T Pr := hTPr.mono hsub
  have hslot : Pr.slot < Bs.slot := hcoh.2 Pr (hsub hPr) Bs hBs hpar
  obtain ⟨hTs, hPE⟩ := entry_facts hr hp (hsub hT) hTe
  set ε := st'.σ T.root
  -- Along the chain from `T` to `Pr`: the entry stays current, or some block justified it.
  have walk : ∀ W, st'.Anc T W → st'.Anc W Pr →
      ((st'.σ W.root).h = ε.h ∧ (st'.σ W.root).Th = T.root ∧ (st'.σ W.root).ThSlot = T.slot ∧
        (st'.σ W.root).hj = ε.hj ∧ (st'.σ W.root).J = ε.J ∧
        (0 < ε.hj ∧ ε.hj + 1 = ε.h → (ε.hj, ε.J) ∈ (st'.σ W.root).pending ∨
          (st'.σ W.root).hF = ε.hj ∧ (st'.σ W.root).F = ε.J)) ∧
        (∀ Y ∈ st'.tree, st'.Anc T Y → st'.Anc Y W →
          (st'.σ Y.root).h = ε.h ∧ (st'.σ Y.root).Th = T.root) ∨
      ∃ X, JustifiesEntry P ACP st' T ε.h X ∧ st'.Anc X Bs ∧ (st'.σ X.root).h = ε.h + 1 ∧
        (st'.σ X.root).Th = X.root ∧ (ε.h, T.root) ∈ (st'.σ X.root).pending ∧
        (ε.previousHeightJustified → (st'.σ X.root).F = ε.J ∧ (st'.σ X.root).hF = ε.hj) := by
    intro W hTW
    induction hTW with
    | refl =>
      refine fun _ => Or.inl ⟨⟨rfl, hTe, hTs, rfl, rfl, fun hb => Or.inl (hPE hb)⟩,
        fun Y _ hTY hYT => ?_⟩
      obtain rfl := hTY.antisymm hcoh hYT
      exact ⟨rfl, hTe⟩
    | @tail W' W hTW' hpW ih =>
      intro hWPr
      obtain ⟨h1, h2, hp'⟩ := hpW
      rcases ih (Relation.ReflTransGen.head ⟨h1, h2, hp'⟩ hWPr) with
        ⟨⟨hh, hTh, hu, hj, hJ, hP⟩, hkeep⟩ | hgoal
      swap
      · exact Or.inr hgoal
      obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ _ hreach W' h1
      have hWs : W.slot < T.slot + P.fg.δt := by
        have := (hWPr.slot_le hcoh).1
        change W.slot < T.slot + P.δt
        omega
      have hkeep' : ∀ Y ∈ st'.tree, st'.Anc T Y → st'.Anc Y W → Y ≠ W →
          (st'.σ Y.root).h = ε.h ∧ (st'.σ Y.root).Th = T.root := by
        intro Y hY hTY hYW hne
        rcases anc_parent h1 hp' hYW with rfl | hYW'
        · exact absurd rfl hne
        · exact hkeep Y hY hTY hYW'
      rcases (step_current hc (step_σ hr hp h2 hp') hh hTh hu hj hJ hP).1 hWs with
        hcur | ⟨hh', hTh', hj', hJ', hpend, hfin⟩
      · refine Or.inl ⟨hcur, fun Y hY hTY hYW => ?_⟩
        by_cases hne : Y = W
        · subst hne
          exact ⟨hcur.1, hcur.2.1⟩
        · exact hkeep' Y hY hTY hYW hne
      · exact Or.inr ⟨W, ⟨h2, hTW'.tail ⟨h1, h2, hp'⟩, hj', hJ', hkeep'⟩, hWPr.tail hPrBs, hh',
          hTh', hpend, hfin⟩
  rcases walk Pr hTPr' .refl with ⟨⟨hh, hTh, hu, hj, hJ, hP⟩, hkeep⟩ | hgoal
  swap
  · exact hgoal
  -- `Pr` still has the entry: `Bs` counts the rows of `R` that `Pr`'s chain has not counted.
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ _ hreach Pr (hsub hPr)
  obtain ⟨bf, bt, brow⟩ := foldl_bits { st'.σ Pr.root with s := Bs.slot } Bs.fgView.atts
  have hrc := rows_counted hr hp (i + 1) (hsub hPr)
  have hR : ∀ r ∈ R, r.val ∈
      (Bs.fgView.atts.foldl FG.ChainState.processAtt { st'.σ Pr.root with s := Bs.slot }).target ∧
      (ε.previousHeightJustified → (ε.hj, ε.J) ∈ (st'.σ Pr.root).pending → r.val ∈
        ((Bs.fgView.atts.foldl FG.ChainState.processAtt
          { st'.σ Pr.root with s := Bs.slot }).fin ε.hj)) := by
    intro r hrR
    obtain ⟨rh, rT, rto, rfin⟩ := hrows r hrR
    have rh' : r.h = (st'.σ Pr.root).h := rh.trans hh.symm
    have rT' : r.T = (st'.σ Pr.root).Th := rT.trans hTh.symm
    by_cases hon : st.OnChain Pr r
    · obtain ⟨X, -, hXPr, hrX⟩ := hon
      obtain ⟨a1, a2⟩ := (hrc X (hXPr.mono hsub) r hrX).2 rh' rT'
      exact ⟨bt (a1 rto), fun hb hm => bf _ (a2 _ (rfin hb) hm)⟩
    · have hin : r ∈ Bs.fgPayload :=
        hincl r ((hpool r hrR).resolve_left hon) (Or.inl ⟨rh', rT'⟩) hon
      obtain ⟨a1, a2⟩ := brow r hin rh' rT'
      exact ⟨a1 rto, fun hb hm => a2 _ (rfin hb) hm⟩
  have hcard : ∀ s : Finset (Fin P.n), (∀ r ∈ R, r.val ∈ s) → P.fg.q ≤ s.card := by
    intro s hs
    refine hq.trans (Finset.card_le_card fun v hv => ?_)
    obtain ⟨r, hrR, rfl⟩ := Finset.mem_image.1 hv
    exact hs r hrR
  obtain ⟨hh', hTh', hj', hJ', hpend, hfin⟩ :=
    (step_current hc (step_σ hr hp hBs hpar) hh hTh hu hj hJ hP).2
      (hcard _ fun r hr => (hR r hr).1) (fun hb hm => hcard _ fun r hr => (hR r hr).2 hb hm)
  refine ⟨Bs, ⟨hBs, hTPr'.tail hPrBs, hj', hJ', fun Y hY hTY hYB hne => ?_⟩, .refl, hh', hTh',
    hpend, hfin⟩
  rcases anc_parent (hsub hPr) hpar hYB with rfl | hYPr
  · exact absurd rfl hne
  · exact hkeep Y hY hTY hYPr

end Consensus.Goldilocks.Store

end
