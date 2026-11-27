module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifiesSigned
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeCrossing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifies
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Geometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses

public section

/-! # Shadow P-U: the rows of an honest proposal

Copies over the shadow run law `Node.LocalRun'` and the shadow FG contract `FGLocalRun'`, for any
AC, of the run facts behind the stock crossing `round_cross_at_from`:

* `Healing.accept_of_proposesAt_from'`, `Healing.proposal_parent_held_from'` (stock
  `ConsumeBase`, `ProposalJustifiesSigned`);
* `Healing.processed_att_retained'` (stock `ConsumeCrossing`);
* `Healing.proposal_rows_placed_from'` (stock `ProposalJustifies`), concluding the shadow
  `FGLocalRun'` of the FG projection;
* `Healing.rows_prog'` and `Healing.cross_step'` (stock `ProposalCrosses`).

The FG-pure helpers (`processAtt_prog`, `foldl_prog`, `step_prog`, `mem_onAttestation`,
`mem_addAtts`) are copied verbatim; the store facts read the shadow store through the `_with`
lemmas of `Shadow/PU/Cache` at `finalitySpec_updateFinality'`. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

section Chain

open _root_.Consensus.Goldilocks.Store

/-- Counting an attestation only adds progress bits; one on the entry sets its bit. -/
private theorem processAtt_prog {n : Nat} (σ : FG.ChainState n) (a : FG.Att n) :
    σ.prog ⊆ (σ.processAtt a).prog ∧
      (a.h = σ.h → a.T = σ.Th → a.val ∈ (σ.processAtt a).prog) := by
  unfold FG.ChainState.processAtt
  rcases a.fin with _ | pr
  · dsimp only
    split_ifs <;> simp_all
  · dsimp only
    split_ifs <;> simp_all

/-- Counting a list of attestations only adds progress bits; each one on the entry sets its
bit. -/
private theorem foldl_prog {n : Nat} (σ : FG.ChainState n) (atts : List (FG.Att n)) :
    σ.prog ⊆ (atts.foldl FG.ChainState.processAtt σ).prog ∧
      ∀ a ∈ atts, a.h = σ.h → a.T = σ.Th →
        a.val ∈ (atts.foldl FG.ChainState.processAtt σ).prog := by
  induction atts generalizing σ with
  | nil => exact ⟨subset_rfl, by simp⟩
  | cons b l ih =>
    obtain ⟨p1, r1⟩ := processAtt_prog σ b
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [b]
    have hh : (σ.processAtt b).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt b).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    obtain ⟨p2, r2⟩ := ih (σ.processAtt b)
    refine ⟨p1.trans p2, fun a ha hah haT => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact p2 (r1 hah haT)
    · exact r2 a ha (hah.trans hh.symm) (haT.trans hT.symm)

/-- An accepted block's attestations are not above its parent's height; the block keeps the height
and entry, with the progress bits of the counting, or enters the next height. -/
private theorem step_prog {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (∀ a ∈ B.atts, a.h ≤ σ.h) ∧
      ((σ'.h = σ.h ∧ σ'.Th = σ.Th ∧
        σ'.prog = (B.atts.foldl FG.ChainState.processAtt { σ with s := B.slot }).prog) ∨
      σ'.h = σ.h + 1) := by
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
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨rfl, rfl, rfl⟩

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- The attestations on the chain of a held block are not above its height, and those on its entry
(targets and timeouts) have set their progress bits (a copy of `rows_prog`). -/
theorem rows_prog (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (m : Nat)
    {W : NodeBlock P ACP} (hW : W ∈ (tr.store y m).tree) :
    ∀ X, (tr.store y m).Anc X W → ∀ r ∈ X.fgPayload, r.h ≤ ((tr.store y m).σ W.root).h ∧
      (r.h = ((tr.store y m).σ W.root).h → r.T = ((tr.store y m).σ W.root).Th →
        r.val ∈ ((tr.store y m).σ W.root).prog) := by
  have hR := (store_reachable' hr hy m).reachableWith
  have hg := (accepted_tree_with finalitySpec_updateFinality hR).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro X hX r hrX
    rcases Relation.ReflTransGen.cases_tail hX with rfl | ⟨Z, -, -, -, hZ⟩
    · cases hrX
    · cases hZ
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨-, -, -, hst⟩ := step_σ_with finalitySpec_updateFinality hR h2 hp
    obtain ⟨hle, hcase⟩ := step_prog hst
    intro X hX r hrX
    have hX' := Store.anc_parent h1 hp hX
    have hrh : r.h ≤ ((tr.store y m).σ W'.root).h := by
      rcases hX' with rfl | hX'
      · exact hle r hrX
      · exact (ih X hX' r hrX).1
    rcases hcase with ⟨hh, hT, hpg⟩ | hh
    · refine ⟨hh ▸ hrh, fun hrh' hrT => ?_⟩
      rw [hh] at hrh'
      rw [hT] at hrT
      obtain ⟨bp, brow⟩ :=
        foldl_prog { (tr.store y m).σ W'.root with s := W.slot } W.fgView.atts
      rw [hpg]
      rcases hX' with rfl | hX'
      · exact brow r hrX hrh' hrT
      · exact bp ((ih X hX' r hrX).2 hrh' hrT)
    · exact ⟨by omega, fun h' => by omega⟩

end Chain

/-! ## The pool and the proposals of an honest node (any AC) -/

section AnyAC

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A} {proposer : Nat → Fin P.n}
  {ini : Fin P.n → A.State}

/-- `fg_on_attestation` keeps the pool and adds its attestation. -/
private theorem mem_onAttestation {ACP : Type} {st : Store P ACP} {a b : FG.Att P.n}
    (h : a ∈ st.atts ∨ a = b) : a ∈ (st.onAttestation b).atts := by
  unfold _root_.Consensus.Goldilocks.Store.onAttestation
  split_ifs with hb
  · rcases h with h | rfl
    exacts [h, hb]
  · simpa using h

/-- `addAtts` keeps the pool and adds its attestations. -/
private theorem mem_addAtts {ACP : Type} {st : Store P ACP} {a : FG.Att P.n}
    {l : List (FG.Att P.n)} (h : a ∈ st.atts ∨ a ∈ l) : a ∈ (st.addAtts l).atts := by
  induction l generalizing st with
  | nil => exact h.resolve_right (by simp)
  | cons b l ih =>
    change a ∈ ((st.onAttestation b).addAtts l).atts
    rcases h with h | h
    · exact ih (Or.inl (mem_onAttestation (Or.inl h)))
    · rcases List.mem_cons.1 h with rfl | h
      · exact ih (Or.inl (mem_onAttestation (Or.inr rfl)))
      · exact ih (Or.inr h)

/-- The fields of a shadow acceptance (a copy of `Store.onBlock_fields`). -/
theorem onBlock_fields {ACP : Type} {st st' : Store P ACP} {B : NodeBlock P ACP}
    (h : st.onBlock B = some st') :
    ∃ (pr : Nat) (σ' : FG.ChainState P.n), st.blocks B.root = none ∧ (st.blocks pr).isSome ∧
      B.parent = some pr ∧
      P.fg.stateTransition (st.σ pr) B.fgView = some σ' ∧
      st'.blocks = Function.update st.blocks B.root (some B) ∧
      st'.σ = Function.update st.σ B.root σ' ∧ ∀ a ∈ st'.atts, a ∈ st.atts ∨ a ∈ B.fgPayload := by
  rw [Store.onBlock_eq_onBlockWith] at h
  obtain ⟨pr, σ', hp, hn, hs, -, ht, rfl⟩ := Store.onBlockWith_eq_some h
  let st₁ : Store P ACP :=
    { st with blocks := Function.update st.blocks B.root (some B),
              σ := Function.update st.σ B.root σ' }
  have hspec := (Store.finalitySpec_iff _).1
    (Store.finalitySpec_updateFinality (P := P) (ACP := ACP))
  obtain ⟨hb, hσ, ha, -⟩ := hspec st₁ σ'
  obtain ⟨h1, h2, h3⟩ := Goldilocks.Store.addAtts_fields (Store.updateFinality st₁ σ') B.fgPayload
  refine ⟨pr, σ', hn, hs, hp, ht, h1.trans hb, h2.trans hσ, fun a h => ?_⟩
  rw [ha] at h3
  exact h3 a h

/-- A shadow acceptance keeps the pool and adds its payload. -/
private theorem mem_onBlock {ACP : Type} {st st' : Store P ACP} {B : NodeBlock P ACP}
    (hB : st.onBlock B = some st') {a : FG.Att P.n}
    (h : a ∈ st.atts ∨ a ∈ B.fgPayload) : a ∈ st'.atts := by
  rw [Store.onBlock_eq_onBlockWith] at hB
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := Store.onBlockWith_eq_some hB
  have hspec := (Store.finalitySpec_iff _).1
    (Store.finalitySpec_updateFinality (P := P) (ACP := ACP))
  refine mem_addAtts (h.imp_left fun h => ?_)
  rw [(hspec _ σ').2.2.1]
  exact h

/-- The pool of an honest node only grows (a copy of `atts_mono`). -/
private theorem atts_mono (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i j : Nat}
    (hij : i ≤ j) {a : FG.Att P.n} (ha : a ∈ (tr.state y i).fg.atts) :
    a ∈ (tr.state y j).fg.atts := by
  induction j, hij using Nat.le_induction with
  | base => exact ha
  | succ j _ ih =>
    have ha := ih
    rcases Coherence.fg_step h hy j with he | ⟨B, -, hB⟩ | ⟨b, -, he⟩
    · rwa [he]
    · exact mem_onBlock hB (Or.inl ha)
    · rw [he]
      exact mem_onAttestation (Or.inl ha)

/-- A processed attestation is in the pool after the cut (a copy of `mem_atts_of_process`). -/
private theorem mem_atts_of_process (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat} {a : FG.Att P.n} (hp : tr.ProcessAttAt y k a) :
    a ∈ (tr.state y (k + 1)).fg.atts := by
  rcases hp with hc | ⟨B, hc, ha⟩
  · rw [tr.state_succ_of_call hc, ((Node.cutStep_attestation _ _ _ _ _).1
      (h.cutLaw y hy k _ hc)).1]
    exact mem_onAttestation (Or.inr rfl)
  · rw [tr.state_succ_of_call hc]
    exact mem_onBlock ((Node.cutStep_block_true _ _ _ _ _).1 (h.cutLaw y hy k _ hc)).2.1
      (Or.inr ha)

end AnyAC

end Consensus.Goldilocks.Healing

end
