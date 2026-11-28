module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FullFrameWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.HeldChains
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable

public section

/-! # Store-level proposal height bounds under P-U

The store-level bounds here support proposal viability over the fixed-maximum P-U window.

The only P-U-new walk head is a block `W` of height `h_j = h_max - 1` above `J` when
`h_max = h_j + 1`. An honest
proposal on it includes, from the proposer's pool, every attestation of `J`'s justification
quorum that is not already on `W`'s chain (`proposal_attestations`), and at an entry whose
previous height is justified every attestation of the finality quorum of the predecessor: both
quorums lie on the chain of a held justification of `J` (`proposal_crosses`). So the proposal
justifies `J`'s height and enters height `h_j + 1 = h_max`. The paper
candidates assumed the proposal carries fewer than `q` attestations; the inclusion rule and the
held justification exclude that.
-/

namespace Consensus.Goldilocks.Shadow.PU.Witness

open FG

/-! ## Chain facts -/

/-- A target bit after counting is old or set by a counted non-timeout entry attestation (a copy
of the private stock `mem_foldl_target`). -/
private theorem mem_foldl_target {n : Nat} {σ : ChainState n} {atts : List (Att n)}
    {v : Fin n} (h : v ∈ (atts.foldl ChainState.processAtt σ).target) :
    v ∈ σ.target ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg ChainState.Th he
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.target ∨ (a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) := by
        clear ih he hh hT
        unfold ChainState.processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals aesop
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · rw [hh, hT] at hb'
      exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

/-- A justification `h_j ≥ 1` has a quorum of target attestations `(h_j, J)` on the chain (a
copy of the private stock `justification_quorum`). -/
private theorem justification_quorum (gp : FGParams) {c : List (FGBlock gp.n)}
    {σ : ChainState gp.n} (h : gp.chainState c = some σ) :
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false) := by
  refine gp.chainState_induction (P := fun c σ =>
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false))
    ⟨by simp [ChainState.init], by simp [ChainState.init]⟩ ?_ h
  intro c σ B σ' _ ⟨ht, hq⟩ hB
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FGParams.chainAtts, List.flatMap_append, List.mem_append] at h ⊢
    exact Or.inl h
  have liftB : ∀ {a}, a ∈ B.atts → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FGParams.chainAtts, List.flatMap_append, List.mem_append]
    exact Or.inr (by simpa using h)
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 hB
  have hT := fun v => @mem_foldl_target _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
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
  · exact ⟨by simp [ChainState.advance], fun _ => ⟨t, hq', ht₀⟩⟩
  · exact ⟨by simp [ChainState.advance], hq₀⟩
  · exact ⟨ht₀, hq₀⟩

/-- On a chain, a finalized height equal to the justified height finalizes `J` itself. -/
private theorem F_eq_J_of_hF_eq_hj (gp : FGParams) {c : List (FGBlock gp.n)}
    {σ : ChainState gp.n} (h : gp.chainState c = some σ) : σ.hF = σ.hj → σ.F = σ.J := by
  refine gp.chainState_induction (P := fun _ σ => σ.hF = σ.hj → σ.F = σ.J)
    (fun _ => rfl) ?_ h
  intro c σ B σ' hc ih hB
  obtain ⟨-, -, -, -, -, -, hpw, hmem, hlast, -⟩ := chain_invariants gp c σ hc
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 hB
  obtain ⟨f, p, t, he⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  have hfJ : ∀ F hF, ((F = σ.F ∧ hF = σ.hF) ∨ ((hF, F) ∈ σ.pending ∧ gp.q ≤ (f hF).card)) →
      hF = σ.hj → F = σ.J := by
    rintro F hF (⟨rfl, rfl⟩ | ⟨hm, -⟩) e
    · exact ih e
    · have hlt := (hmem _ hm).1
      have hl := hlast (by omega)
      have := eq_of_pairwise_fst_lt hpw hm (List.mem_of_getLast? hl) (by simpa using e)
      simpa using congrArg Prod.snd this
  obtain ⟨F, hF', σ₁, rfl, hc₁, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · intro e
    simp only [ChainState.advance] at e
    exfalso
    obtain ⟨-, hFj, hjh, -⟩ := chain_invariants gp c σ hc
    dsimp only at hc₁
    rcases hc₁ with ⟨-, h2⟩ | ⟨hm, -⟩
    · omega
    · have := (hmem _ hm).2
      omega
  · simpa [ChainState.advance] using hfJ F hF' hc₁
  · simpa using hfJ F hF' hc₁

/-- One accepted block: its attestations are below or on the parent's entry; it enters the next
height or keeps the entry, with its pending pairs among the parent's and the counting's bits. -/
private theorem step_rows {gp : FGParams} {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (∀ a ∈ B.atts, a.WellFormed ∧ (a.h < σ.h ∨ (a.h = σ.h ∧ a.T = σ.Th))) ∧
    (σ'.h = σ.h + 1 ∨
      (σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ (∀ p ∈ σ'.pending, p ∈ σ.pending) ∧
        σ'.target = (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).target ∧
        σ'.fin = (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).fin)) := by
  obtain ⟨⟨-, hv⟩, he⟩ := gp.stateTransition_eq_some.1 h
  refine ⟨fun a ha => ⟨(hv a ha).1, ?_⟩, ?_⟩
  · rcases (hv a ha).2 with ⟨h1, h2⟩ | ⟨p, -, -, -, h3⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl h3
  · obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
    rw [hf] at he ⊢
    obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
      { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
    rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] at he <;> subst he
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, rfl, fun q hq => List.mem_of_mem_filter hq, rfl, rfl⟩

/-! ## Store facts over shadow-reachable stores -/

section Store

open Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

private theorem mem_onAttestation {a b : FG.Att P.n} (h : a ∈ st.atts ∨ a = b) :
    a ∈ (st.onAttestation b).atts := by
  unfold Store.onAttestation
  split_ifs with hb
  · rcases h with h | rfl
    exacts [h, hb]
  · simpa using h

private theorem mem_addAtts {a : FG.Att P.n} {l : List (FG.Att P.n)}
    (h : a ∈ st.atts ∨ a ∈ l) : a ∈ (st.addAtts l).atts := by
  induction l generalizing st with
  | nil => exact h.resolve_right (by simp)
  | cons b l ih =>
    change a ∈ ((st.onAttestation b).addAtts l).atts
    rcases h with h | h
    · exact ih (Or.inl (mem_onAttestation (Or.inl h)))
    · rcases List.mem_cons.1 h with rfl | h
      · exact ih (Or.inl (mem_onAttestation (Or.inr rfl)))
      · exact ih (Or.inr h)

/-- Every attestation carried by a held block is in the pool. -/
theorem payload_mem_atts (hr : st.Reachable acp₀) :
    ∀ B ∈ st.tree, ∀ a ∈ B.fgPayload, a ∈ st.atts := by
  rw [Store.reachable_eq] at hr
  induction hr with
  | refl =>
    intro B hB a ha
    have hB : (if B.root = P.genesisRoot then some (P.genesisBlock acp₀) else none) =
        some B := hB
    split_ifs at hB
    cases hB
    cases ha
  | @tail s s' _ hs ih =>
    rcases (Store.step_iff _ _).1 hs with ⟨B', hB'⟩ | ⟨b, rfl⟩
    · obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := Goldilocks.Store.onBlock_eq_some hB'
      intro B hB a ha
      set st₁ : Store P ACP :=
        { s with blocks := Function.update s.blocks B'.root (some B'),
                 σ := Function.update s.σ B'.root σ' } with hst₁
      obtain ⟨hb, -, hat, -⟩ := Goldilocks.Store.updateFinality_spec st₁ σ'
      obtain ⟨hb2, -⟩ := Goldilocks.Store.addAtts_fields (Store.updateFinality st₁ σ') B'.fgPayload
      have hB2 : (Function.update s.blocks B'.root (some B')) B.root = some B := by
        have : ((Store.updateFinality st₁ σ').addAtts B'.fgPayload).blocks B.root = some B := hB
        rw [hb2, hb] at this
        exact this
      by_cases hroot : B.root = B'.root
      · rw [hroot, Function.update_self] at hB2
        cases hB2
        exact mem_addAtts (Or.inr ha)
      · rw [Function.update_of_ne hroot] at hB2
        refine mem_addAtts (Or.inl ?_)
        rw [hat]
        exact ih B hB2 a ha
    · intro B hB a ha
      have hB' : s.blocks B.root = some B := by
        have : (s.onAttestation b).blocks B.root = some B := hB
        unfold Store.onAttestation at this
        split_ifs at this <;> exact this
      exact mem_onAttestation (Or.inl (ih B hB' a ha))

variable (hr : st.Reachable acp₀)
include hr

/-- The attestations on the chain of a held block are well formed and not above its height, and
those on its entry have set their target bits (targets) and finality bits (pending pairs). -/
theorem rows_at {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∀ X, st.Anc X W → ∀ r ∈ X.fgPayload, r.WellFormed ∧ (r.h < (st.σ W.root).h ∨
      (r.h = (st.σ W.root).h ∧ r.T = (st.σ W.root).Th ∧
        (r.timeout = false → r.val ∈ (st.σ W.root).target) ∧
        ∀ pr, r.fin = some pr → pr ∈ (st.σ W.root).pending →
          r.val ∈ (st.σ W.root).fin pr.1)) := by
  have hg := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro X hX r hrX
    rcases Relation.ReflTransGen.cases_tail hX with rfl | ⟨Z, -, -, -, hZ⟩
    · cases hrX
    · cases hZ
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨-, -, -, hst⟩ := Healing.Store.step_σ hr h2 hp
    obtain ⟨hval, hshape⟩ := step_rows hst
    obtain ⟨bf, bt, brow⟩ :=
      Store.foldl_bits { st.σ W'.root with s := W.slot } W.fgView.atts
    intro X hX r hrX
    rcases anc_parent h1 hp hX with rfl | hX'
    · obtain ⟨hwf, hcase⟩ := hval r hrX
      refine ⟨hwf, ?_⟩
      rcases hshape with hh | ⟨hh, hT, hpend, htg, hfin⟩
      · rcases hcase with hlt | ⟨he, -⟩ <;> exact Or.inl (by omega)
      · rcases hcase with hlt | ⟨he, heT⟩
        · exact Or.inl (by omega)
        · obtain ⟨a1, a2⟩ := brow r hrX he heT
          refine Or.inr ⟨by omega, by rw [hT]; exact heT, fun ht => ?_, fun pr hpr hm => ?_⟩
          · rw [htg]; exact a1 ht
          · rw [hfin]; exact a2 pr hpr (hpend pr hm)
    · obtain ⟨hwf, hcase⟩ := ih X hX' r hrX
      refine ⟨hwf, ?_⟩
      rcases hshape with hh | ⟨hh, hT, hpend, htg, hfin⟩
      · rcases hcase with hlt | ⟨he, -⟩ <;> exact Or.inl (by omega)
      · rcases hcase with hlt | ⟨he, heT, ht, hf⟩
        · exact Or.inl (by omega)
        · refine Or.inr ⟨by omega, by rw [hT]; exact heT, fun h' => ?_, fun pr hpr hm => ?_⟩
          · rw [htg]; exact bt (ht h')
          · rw [hfin]; exact bf _ (hf pr hpr (hpend pr hm))

omit hr in
/-- One block keeps the justification or justifies its parent's entry. -/
private theorem step_hj {gp : FGParams} {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.hj = σ.hj ∧ σ'.J = σ.J) ∨ (σ'.hj = σ.h ∧ σ'.J = σ.Th) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

omit hr in
/-- A block that justifies an entry whose previous height is justified finalizes that
predecessor pair `(h_j, J)` (the stock private `previousHeightJustified_justify_finalizes_block`).
-/
private theorem justify_finalizes_pair {gp : FGParams} {c : List (FGBlock gp.n)}
    {σ σ' : ChainState gp.n} {B : FGBlock gp.n} (hc : gp.chainState c = some σ)
    (h : gp.stateTransition σ B = some σ') (hb : σ.previousHeightJustified)
    (hj : σ'.hj = σ.h) : σ'.F = σ.J ∧ σ'.hF = σ.hj := by
  have hF := gp.previousHeightJustified_justify_finalizes h hb hj
  refine ⟨?_, hF⟩
  obtain ⟨-, -, -, -, -, -, hpw, hmem, hlast, -⟩ := chain_invariants gp c σ hc
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hF hj ⊢
  obtain ⟨F, hF', σ₁, rfl, hc₁, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hjh := (chain_invariants gp c σ hc).2.2.1
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] at hF hj ⊢
  · simp only [ChainState.advance] at hF ⊢
    dsimp only at hc₁
    rcases hc₁ with ⟨rfl, h2⟩ | ⟨hm, -⟩
    · exact F_eq_J_of_hF_eq_hj gp hc (h2 ▸ hF)
    · have hlt := (hmem _ hm).1
      rw [hF] at hm hlt
      have hl := hlast hlt
      have := eq_of_pairwise_fst_lt hpw hm (List.mem_of_getLast? hl) rfl
      simpa using congrArg Prod.snd this
  · simp only [ChainState.advance] at hj
    omega
  · simp only at hj
    omega

/-- Along ancestry the justification is kept, or it is at least the ancestor's height. -/
private theorem hj_anc {A W : NodeBlock P ACP} (h : st.Anc A W) :
    ((st.σ W.root).hj = (st.σ A.root).hj ∧ (st.σ W.root).J = (st.σ A.root).J) ∨
      (st.σ A.root).h ≤ (st.σ W.root).hj := by
  induction h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | @tail W' W hAW' hp ih =>
    obtain ⟨h1, h2, hpar⟩ := hp
    obtain ⟨-, -, -, hst⟩ := Healing.Store.step_σ hr h2 hpar
    have hle := Healing.h_le_of_store_anc hr hAW'
    have hjh := Healing.Store.hj_lt_h hr h1
    rcases step_hj hst with ⟨e1, e2⟩ | ⟨e1, -⟩
    · rcases ih with ⟨f1, f2⟩ | f
      · exact Or.inl ⟨e1.trans f1, e2.trans f2⟩
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)

/-- At equal height the justification is the ancestor's. -/
private theorem hj_eq_of_anc {A W : NodeBlock P ACP} (hW : W ∈ st.tree) (h : st.Anc A W)
    (hh : (st.σ W.root).h = (st.σ A.root).h) :
    (st.σ W.root).hj = (st.σ A.root).hj ∧ (st.σ W.root).J = (st.σ A.root).J := by
  have hjh := Healing.Store.hj_lt_h hr hW
  rcases hj_anc hr h with h' | h'
  · exact h'
  · omega

/-- **The proposal on a height-`h_j` block above `J` crosses.** In a shadow-reachable store,
a block `B` on a held `W` with `σ[W].h = h_j` and `J ⪯ W` that carries the store's
`proposal_attestations` for `W` enters a height above `h_j`: it counts `J`'s justification
quorum and, at an entry whose previous height is justified, the predecessor's finality
quorum, both on the chain of a held justification of `J`. -/
theorem proposal_crosses {W : NodeBlock P ACP} (hW : W ∈ st.tree)
    (hh : (st.σ W.root).h = st.hj) (hJW : st.Anc st.J W)
    {B : FGBlock P.n} (hB : B.atts = st.proposalAttestations W) {σ' : ChainState P.n}
    (hσ : P.fg.stateTransition (st.σ W.root) B = some σ') : st.hj < σ'.h := by
  classical
  have hcoh := (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.1
  have hroot : ∀ {X Y : NodeBlock P ACP}, X ∈ st.tree → Y ∈ st.tree → X.root = Y.root →
      X = Y := fun hX hY he => hcoh.1 hX hY he
  have hjh := Healing.Store.hj_lt_h hr hW
  obtain ⟨-, hJm, -, ⟨X, hX, hXJ, hXj⟩, -⟩ := cache_invariants _ _ _ _ hr
  have hJcase : (st.J = P.genesisBlock acp₀ ∧ st.hj = 0) ∨
      ((st.σ st.J.root).h = st.hj ∧ (st.σ st.J.root).Th = st.J.root) := by
    obtain ⟨E, hE, hEr, -, hcase⟩ := Goldilocks.Store.J_entry_hj _ _ hr hX
    obtain rfl : E = st.J := hroot hE hJm (hEr.trans hXJ)
    rcases hcase with ⟨he, h0⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨he, hXj ▸ h0⟩
    · exact Or.inr ⟨h1.trans hXj, h2⟩
  have hJ : (st.σ st.J.root).h = st.hj ∧ (st.σ st.J.root).Th = st.J.root := by
    rcases hJcase with ⟨-, h0⟩ | h
    · omega
    · exact h
  have hWT : (st.σ W.root).Th = st.J.root :=
    (Healing.Th_eq_of_anc hr hJW (by omega)).trans hJ.2
  have hpool := payload_mem_atts hr
  have hrowsW := rows_at hr hW
  obtain ⟨cW, hcW, -, -⟩ := Goldilocks.Store.held_chain hr hW
  obtain ⟨bf, bt, brow⟩ := Store.foldl_bits { st.σ W.root with s := B.slot } B.atts
  -- every pool attestation on `W`'s entry is counted by `B`
  have hcount : ∀ a, a ∈ st.atts → a.h = st.hj → a.T = st.J.root →
      (a.timeout = false →
        a.val ∈ (B.atts.foldl ChainState.processAtt { st.σ W.root with s := B.slot }).target) ∧
      ∀ pr, a.fin = some pr → pr ∈ (st.σ W.root).pending →
        a.val ∈ (B.atts.foldl ChainState.processAtt { st.σ W.root with s := B.slot }).fin pr.1 := by
    intro a ha hah haT
    by_cases hon : st.OnChain W a
    · obtain ⟨Z, -, hZW, haZ⟩ := hon
      obtain ⟨-, hc⟩ := hrowsW Z hZW a haZ
      rcases hc with hlt | ⟨-, -, ht, hf⟩
      · omega
      · exact ⟨fun h' => bt (ht h'), fun pr hpr hm => bf _ (hf pr hpr hm)⟩
    · have haB : a ∈ B.atts := by
        rw [hB]
        unfold Store.proposalAttestations
        refine List.mem_filter.2 ⟨ha, ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨Or.inl ⟨by omega, haT.trans hWT.symm⟩, hon⟩
      exact brow a haB (by simp only; omega) (by simp only; rw [hWT]; exact haT)
  -- the target quorum of `J`'s justification
  obtain ⟨cX, hcX, -, hattX⟩ := Goldilocks.Store.held_chain hr hX
  obtain ⟨Qt, hQt, hvt⟩ := (justification_quorum P.fg hcX).2 (by omega)
  have htq : P.fg.q ≤
      (B.atts.foldl ChainState.processAtt { st.σ W.root with s := B.slot }).target.card := by
    refine hQt.trans (Finset.card_le_card fun v hv => ?_)
    obtain ⟨a, ha, rfl, hah, haT, hto⟩ := hvt v hv
    obtain ⟨Z, hZ, -, haZ⟩ := hattX a ha
    exact (hcount a (hpool Z hZ a haZ) (hah.trans hXj) (haT.trans hXJ)).1 hto
  -- the finality quorum of the predecessor
  have hfq : (st.σ W.root).previousHeightJustified →
      ((st.σ W.root).hj, (st.σ W.root).J) ∈ (st.σ W.root).pending →
      P.fg.q ≤ ((B.atts.foldl ChainState.processAtt
        { st.σ W.root with s := B.slot }).fin (st.σ W.root).hj).card := by
    intro hb hpend
    obtain ⟨hb0, hb1⟩ := hb
    have hXh := Healing.Store.hj_lt_h hr hX
    obtain ⟨Y, hY, hYX, hYh, hYT⟩ :=
      Goldilocks.Store.entry_at_height _ _ hr hX (h := st.hj + 1) (by omega) (by omega)
    obtain ⟨pr, hpr⟩ : ∃ pr, Y.parent = some pr := by
      cases hp : Y.parent with
      | none =>
        have hg : Y = P.genesisBlock acp₀ := by
          rcases Relation.ReflTransGen.cases_tail
              ((Goldilocks.Store.accepted_tree _ _ _ _ hr).2.2.2 Y hY) with he | ⟨C, -, hCY⟩
          · exact he
          · exact (Option.some_ne_none _ (hCY.2.2.symm.trans hp)).elim
        subst hg
        have := Healing.Store.σ_genesis hr
        rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, this] at hYh
        simp [ChainState.init] at hYh
        omega
      | some pr => exact ⟨pr, rfl⟩
    obtain ⟨Yp, hYp, rfl, hstY⟩ := Healing.Store.step_σ hr hY hpr
    -- `J ⪯ Yp` and `Yp` is at `J`'s height
    obtain ⟨E, hE, hEr, hEX, -⟩ := Goldilocks.Store.J_entry_hj _ _ hr hX
    obtain rfl : E = st.J := hroot hE hJm (hEr.trans hXJ)
    have hJY : st.Anc st.J Y := by
      rcases Anc.total hcoh hEX hYX with h' | h'
      · exact h'
      · have := Healing.h_le_of_store_anc hr h'
        omega
    have hJYp : st.Anc st.J Yp := by
      rcases anc_parent hYp hpr hJY with h' | h'
      · rw [h'] at hJ
        omega
      · exact h'
    have hYph : (st.σ Yp.root).h = st.hj := by
      rcases (step_rows hstY).2 with h' | ⟨h1, h2, -⟩
      · omega
      · exfalso
        obtain ⟨⟨E', hE', hE'r, hE'Yp, -⟩, -⟩ :=
          Goldilocks.Store.entry_state_of_source _ _ _ _ hr Yp hYp
        obtain rfl : E' = Y := hroot hE' hY (hE'r.trans (h2.symm.trans hYT))
        have := (hE'Yp.slot_le hcoh).1
        have := hcoh.2 Yp hYp E' hY hpr
        omega
    have hYpT : (st.σ Yp.root).Th = st.J.root :=
      (Healing.Th_eq_of_anc hr hJYp (by omega)).trans hJ.2
    obtain ⟨hYpj, hYpJ⟩ := hj_eq_of_anc hr hYp hJYp (by omega)
    obtain ⟨hWj, hWJ⟩ := hj_eq_of_anc hr hW hJW (by omega)
    have hYj : (st.σ Y.root).hj = (st.σ Yp.root).h := by
      rcases hj_anc hr hYX with ⟨h1, -⟩ | h'
      · omega
      · omega
    have hbYp : (st.σ Yp.root).previousHeightJustified := ⟨by omega, by omega⟩
    obtain ⟨cYp, -, -, -, hcYp⟩ := Goldilocks.Store.chain_state_of_chain _ _ _ _ hr Yp hYp
    obtain ⟨hYF, hYhF⟩ := justify_finalizes_pair hcYp hstY hbYp hYj
    obtain ⟨cY, hcY, -, hattY⟩ := Goldilocks.Store.held_chain hr hY
    obtain ⟨Qf, hQf, hvf⟩ := FGParams.finalized_quorum P.fg hcY (by omega)
    refine hQf.trans (Finset.card_le_card fun v hv => ?_)
    obtain ⟨a, ha, rfl, hfa⟩ := hvf v hv
    rw [hYhF, hYF, hYpj, hYpJ, ← hWj, ← hWJ] at hfa
    obtain ⟨Z, hZ, hZY, haZ⟩ := hattY a ha
    have hrow : a.WellFormed ∧ (a.h < (st.σ Yp.root).h ∨
        (a.h = (st.σ Yp.root).h ∧ a.T = (st.σ Yp.root).Th)) := by
      rcases anc_parent hYp hpr hZY with rfl | h'
      · exact (step_rows hstY).1 a haZ
      · obtain ⟨hwf, hc⟩ := rows_at hr hYp Z h' a haZ
        exact ⟨hwf, hc.imp_right fun h => ⟨h.1, h.2.1⟩⟩
    obtain ⟨⟨-, hwf⟩, hc⟩ := hrow
    have hlt : (st.σ W.root).hj < a.h := hwf ((st.σ W.root).hj, (st.σ W.root).J) (by simp [hfa])
    rcases hc with hc | ⟨hah, haT⟩
    · omega
    · exact (hcount a (hpool Z hZ a haZ) (by omega) (haT.trans hYpT)).2 _ hfa hpend
  obtain ⟨h1, -, -⟩ := FGParams.justify_of_target_chain P.fg hcW hσ htq hfq
  have hc' : P.fg.chainState (cW.map Block.fgView ++ [B]) = some σ' := by
    have e := FGParams.chainState_append P.fg (cW.map Block.fgView) B
    rw [hcW] at e
    exact e.trans hσ
  have := (chain_invariants P.fg _ _ hc').2.2.1
  omega

omit hr in
/-- An accepted block's state is the transition of its parent's state. -/
theorem onBlock_σ {st' : Store P ACP} {B : NodeBlock P ACP} (h : st.onBlock B = some st') :
    ∃ pr, B.parent = some pr ∧ P.fg.stateTransition (st.σ pr) B.fgView = some (st'.σ B.root) := by
  obtain ⟨pr, σ', hp, -, -, -, ht, rfl⟩ := Goldilocks.Store.onBlock_eq_some h
  refine ⟨pr, hp, ?_⟩
  set st₁ : Store P ACP :=
    { st with blocks := Function.update st.blocks B.root (some B),
              σ := Function.update st.σ B.root σ' } with hst₁
  obtain ⟨-, hσu, -⟩ := Goldilocks.Store.updateFinality_spec st₁ σ'
  obtain ⟨-, hσa, -⟩ := Goldilocks.Store.addAtts_fields (Store.updateFinality st₁ σ') B.fgPayload
  rw [hσa, hσu]
  simpa [st₁] using ht

omit hr in
/-- **The proposal floor at one store.** A block on a held P-U viable `D` lies at height at least
`hmax - 1`. -/
theorem hmax_pred_le_of_isViable {D : NodeBlock P ACP} (hv : st.IsViable D)
    {B : FGBlock P.n} {σ' : ChainState P.n}
    (hσ : P.fg.stateTransition (st.σ D.root) B = some σ') : st.hmax - 1 ≤ σ'.h := by
  have hmono : (st.σ D.root).h ≤ σ'.h := by
    rcases (step_rows hσ).2 with h | ⟨h, -⟩ <;> omega
  rcases (Store.isViable_iff st D).1 hv with h | ⟨h, -⟩ <;> omega

/-- A proposal on a viable parent crosses the store's justified height. -/
theorem hj_lt_of_isViable {D : NodeBlock P ACP} (hD : D ∈ st.tree) (hv : st.IsViable D)
    {B : FGBlock P.n} (hB : B.atts = st.proposalAttestations D) {σ' : ChainState P.n}
    (hσ : P.fg.stateTransition (st.σ D.root) B = some σ') : st.hj < σ'.h := by
  have hj := Healing.Store.hj_lt_hmax_of_reachable hr
  have hmono : (st.σ D.root).h ≤ σ'.h := by
    rcases (step_rows hσ).2 with h | ⟨h, -⟩ <;> omega
  rcases (Store.isViable_iff st D).1 hv with h | ⟨h, hgap | hJD⟩
  · omega
  · omega
  · by_cases hlt : st.hj < (st.σ D.root).h
    · omega
    · exact proposal_crosses hr hD (by omega) hJD hB hσ

end Store

end Consensus.Goldilocks.Shadow.PU.Witness

end
