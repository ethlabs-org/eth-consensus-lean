module
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

open AC (ACParams Payload)

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
theorem rows_prog' (hr : FGLocalRun' acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) (m : Nat)
    {W : NodeBlock P ACP} (hW : W ∈ (tr.store y m).tree) :
    ∀ X, (tr.store y m).Anc X W → ∀ r ∈ X.fgPayload, r.h ≤ ((tr.store y m).σ W.root).h ∧
      (r.h = ((tr.store y m).σ W.root).h → r.T = ((tr.store y m).σ W.root).Th →
        r.val ∈ ((tr.store y m).σ W.root).prog) := by
  have hR := (store_reachable' hr hy m).reachableWith
  have hg := (accepted_tree_with finalitySpec_updateFinality' hR).2.2.2 W hW
  clear hW
  induction hg with
  | refl =>
    intro X hX r hrX
    rcases Relation.ReflTransGen.cases_tail hX with rfl | ⟨Z, -, -, -, hZ⟩
    · cases hrX
    · cases hZ
  | @tail W' W _ hpar ih =>
    obtain ⟨h1, h2, hp⟩ := hpar
    obtain ⟨-, -, -, hst⟩ := step_σ_with finalitySpec_updateFinality' hR h2 hp
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

/-- **The crossing at one block** (a copy of `cross_step`). -/
theorem cross_step' (hr : FGLocalRun' acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {X Pr : NodeBlock P ACP} (hX : X ∈ (tr.store y i).tree) (hPr : Pr ∈ (tr.store y i).tree)
    (hpar : X.parent = some Pr.root)
    (S : Finset (Fin P.n)) (hS : P.fg.q ≤ S.card)
    (hrow : ∀ v ∈ S, ∃ a : FG.Att P.n, a.val = v ∧ a.h = ((tr.store y i).σ Pr.root).h ∧
      a.T = ((tr.store y i).σ Pr.root).Th ∧ (a ∈ X.fgPayload ∨ (tr.store y i).OnChain Pr a))
    (hage : ((tr.store y i).σ Pr.root).ThSlot + P.fg.δt ≤ X.slot) :
    ((tr.store y i).σ X.root).h = ((tr.store y i).σ Pr.root).h + 1 ∧
      ((tr.store y i).σ X.root).Th = X.root ∧
      (((tr.store y i).σ X.root).previousHeightJustified ↔
        ((tr.store y i).σ X.root).hj = ((tr.store y i).σ Pr.root).h) ∧
      (((tr.store y i).σ X.root).hj = ((tr.store y i).σ Pr.root).h →
        ((tr.store y i).σ Pr.root).previousHeightJustified →
        ((tr.store y i).σ X.root).hF = ((tr.store y i).σ Pr.root).hj) := by
  classical
  have hR := (store_reachable' hr hy i).reachableWith
  set σ := (tr.store y i).σ Pr.root
  obtain ⟨-, -, -, hstep⟩ := step_σ_with finalitySpec_updateFinality' hR hX hpar
  obtain ⟨bp, brow⟩ := foldl_prog { σ with s := X.slot } X.fgPayload
  have hq : P.fg.q ≤
      (X.fgView.atts.foldl FG.ChainState.processAtt { σ with s := X.fgView.slot }).prog.card :=
    hS.trans (Finset.card_le_card fun v hv => by
      obtain ⟨a, rfl, hah, haT, hin | ⟨Z, -, hZ, haZ⟩⟩ := hrow v hv
      · exact brow a hin hah haT
      · exact bp ((rows_prog' hr hy i hPr Z hZ a haZ).2 hah haT))
  have hh := P.fg.cross_of_progress hstep hq hage
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain_with finalitySpec_updateFinality' hR Pr hPr
  obtain ⟨-, -, -, -, h5⟩ := FG.height_step P.fg _ _ _ _ hc hstep
  obtain ⟨hT, hiff, -⟩ := h5 hh
  exact ⟨hh, hT, hiff, fun hj hb => P.fg.previousHeightJustified_justify_finalizes hstep hb hj⟩

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
theorem onBlock'_fields {ACP : Type} {st st' : Store P ACP} {B : NodeBlock P ACP}
    (h : st.onBlock' B = some st') :
    ∃ (pr : Nat) (σ' : FG.ChainState P.n), st.blocks B.root = none ∧ (st.blocks pr).isSome ∧
      B.parent = some pr ∧
      P.fg.stateTransition (st.σ pr) B.fgView = some σ' ∧
      st'.blocks = Function.update st.blocks B.root (some B) ∧
      st'.σ = Function.update st.σ B.root σ' ∧ ∀ a ∈ st'.atts, a ∈ st.atts ∨ a ∈ B.fgPayload := by
  rw [Store.onBlock'_eq_onBlockWith] at h
  obtain ⟨pr, σ', hp, hn, hs, -, ht, rfl⟩ := Store.onBlockWith_eq_some h
  let st₁ : Store P ACP :=
    { st with blocks := Function.update st.blocks B.root (some B),
              σ := Function.update st.σ B.root σ' }
  have hspec := (Store.finalitySpec_iff _).1
    (Store.finalitySpec_updateFinality' (P := P) (ACP := ACP))
  obtain ⟨hb, hσ, ha, -⟩ := hspec st₁ σ'
  obtain ⟨h1, h2, h3⟩ := Goldilocks.Store.addAtts_fields (Store.updateFinality' st₁ σ') B.fgPayload
  refine ⟨pr, σ', hn, hs, hp, ht, h1.trans hb, h2.trans hσ, fun a h => ?_⟩
  rw [ha] at h3
  exact h3 a h

/-- A shadow acceptance keeps the pool and adds its payload. -/
private theorem mem_onBlock' {ACP : Type} {st st' : Store P ACP} {B : NodeBlock P ACP}
    (hB : st.onBlock' B = some st') {a : FG.Att P.n}
    (h : a ∈ st.atts ∨ a ∈ B.fgPayload) : a ∈ st'.atts := by
  rw [Store.onBlock'_eq_onBlockWith] at hB
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := Store.onBlockWith_eq_some hB
  have hspec := (Store.finalitySpec_iff _).1
    (Store.finalitySpec_updateFinality' (P := P) (ACP := ACP))
  refine mem_addAtts (h.imp_left fun h => ?_)
  rw [(hspec _ σ').2.2.1]
  exact h

/-- The pool of an honest node only grows (a copy of `atts_mono`). -/
private theorem atts_mono' (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i j : Nat}
    (hij : i ≤ j) {a : FG.Att P.n} (ha : a ∈ (tr.state y i).fg.atts) :
    a ∈ (tr.state y j).fg.atts := by
  induction j, hij using Nat.le_induction with
  | base => exact ha
  | succ j _ ih =>
    have ha := ih
    rcases Coherence.fg_step' h hy j with he | ⟨B, -, hB⟩ | ⟨b, -, he⟩
    · rwa [he]
    · exact mem_onBlock' hB (Or.inl ha)
    · rw [he]
      exact mem_onAttestation (Or.inl ha)

/-- A processed attestation is in the pool after the cut (a copy of `mem_atts_of_process`). -/
private theorem mem_atts_of_process' (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat} {a : FG.Att P.n} (hp : tr.ProcessAttAt y k a) :
    a ∈ (tr.state y (k + 1)).fg.atts := by
  rcases hp with hc | ⟨B, hc, ha⟩
  · rw [tr.state_succ_of_call hc, ((Node.cutStep'_attestation _ _ _ _ _).1
      (h.cutLaw y hy k _ hc)).1]
    exact mem_onAttestation (Or.inr rfl)
  · rw [tr.state_succ_of_call hc]
    exact mem_onBlock' ((Node.cutStep'_block_true _ _ _ _ _).1 (h.cutLaw y hy k _ hc)).2.1
      (Or.inr ha)

/-- **Processed attestations persist in the honest node's pool** (a copy of
`processed_att_retained`). -/
theorem processed_att_retained' (h : Node.LocalRun' proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {k j : Nat} {a : FG.Att P.n}
    (hp : tr.ProcessAttAt y k a) (hkj : k < j) : a ∈ (tr.state y j).fg.atts :=
  atts_mono' h hy (by omega) (mem_atts_of_process' h hy hp)

/-- **An honest proposal is accepted by its proposer at its cut**, for any AC from starts at which
it meets the requirements (a copy of `accept_of_proposesAt_from`). -/
theorem accept_of_proposesAt_from' (h : Node.LocalRun' proposer dg H sg tr ini)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg) (hnc : Compose.NoCollRun dg tr)
    {p : Fin P.n} (hp : p ∈ H) (hq : ({ A with initial := ini p } : NodeAC P).Requirements)
    {k : Nat} {W : A.Blk} (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hW
  rcases Coherence.blockCall_cases' h hp hc with hg |
    ⟨j, x, fgDue, rfl, hg, hpr, d, p', hdp, rfl, -, -, -, -⟩
  · rw [RunTrace.groupAt'_iff] at hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨hacc, -⟩ := own_block_accepted' h hq hroot hnc hp hg hpr hdp
  have he := hc.2.symm.trans hacc.2
  simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at he
  obtain rfl := he.2
  exact ⟨hc, Coherence.accept_mem_from' h hp hc, (tr.state_succ_of_call hc).symm⟩

/-- **The parent of an honest proposal is held at its cut** (a copy of
`proposal_parent_held_from`). -/
theorem proposal_parent_held_from' (h : Node.LocalRun' proposer dg H sg tr ini)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg) (hnc : Compose.NoCollRun dg tr)
    {p : Fin P.n} (hp : p ∈ H) (hq : ({ A with initial := ini p } : NodeAC P).Requirements)
    {kX : Nat} {X : A.Blk} (hX : tr.ProposesAt p kX X) :
    ∃ Pr : A.Blk, X.parent = some Pr.root ∧ Pr ∈ (tr.state p kX).fg.tree := by
  obtain ⟨hacc, -, -⟩ := accept_of_proposesAt_from' h hroot hnc hp hq hX
  obtain ⟨pr, _, _, hsome, hpar, _⟩ :=
    onBlock'_fields ((Node.cutStep'_block_true _ _ _ _ _).1 (h.cutLaw p hp kX _ hacc)).2.1
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 hsome
  have hR := (Node.fg_reachable_at' h hp kX).reachableWith
  have hYr : Y.root = pr := Store.blocks_root_with Store.finalitySpec_updateFinality' hR hY
  refine ⟨Y, by rw [hpar, hYr], ?_⟩
  change (tr.state p kX).fg.blocks Y.root = some Y
  rw [hYr]
  exact hY

/-- **The attestations of an honest proposal** (a copy of `proposal_rows_placed_from`; the FG
projection is the shadow `FGLocalRun'`). -/
theorem proposal_rows_placed_from' (h : Node.LocalRun' proposer dg H sg tr ini)
    (hq : ∀ y ∈ H, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hroot : (P.genesisBlock A.genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {p : Fin P.n} (hp : p ∈ H) {kX : Nat}
    {X Pr : A.Blk} (hX : tr.ProposesAt p kX X) (hpar : X.parent = some Pr.root)
    (hPr : Pr ∈ (tr.state p kX).fg.tree) :
    FGLocalRun' A.genesisPayload H (tr.HonestBlocks H) tr.projFG ∧
      X ∈ (tr.projFG.store p (kX + 1)).tree ∧ Pr ∈ (tr.projFG.store p (kX + 1)).tree ∧
      (tr.post kX).fg.σ X.root = (tr.projFG.store p (kX + 1)).σ X.root ∧
      (tr.state p kX).fg.σ Pr.root = (tr.projFG.store p (kX + 1)).σ Pr.root ∧
      ∀ att, (∃ k' < kX, tr.ProcessAttAt p k' att) →
        att.h = ((tr.state p kX).fg.σ Pr.root).h → att.T = ((tr.state p kX).fg.σ Pr.root).Th →
        att ∈ X.fgPayload ∨ (tr.projFG.store p (kX + 1)).OnChain Pr att := by
  classical
  have hU := Coherence.honest_blocks_coherent' h hnc
  obtain ⟨hacc, hXt, hpost⟩ := accept_of_proposesAt_from' h hroot hnc hp (hq p hp) hX
  have hst : tr.projFG.store p (kX + 1) = (tr.state p (kX + 1)).fg := by
    change (tr.projFG.state p (kX + 1)).1 = _
    rw [Compose.projFG_state' h hp]
  have hmono := Coherence.tree_mono' h hp (Nat.le_succ kX)
  have hPrU : Pr ∈ tr.HonestBlocks H := ⟨p, hp, kX, hPr⟩
  have hXU : X ∈ tr.HonestBlocks H := ⟨p, hp, kX + 1, hXt⟩
  rcases Coherence.blockCall_cases' h hp hacc with hg |
    ⟨j, x, fgDue, -, -, -, d, pay, -, hB, -, -, -, hfgj⟩
  · rw [RunTrace.groupAt'_iff] at hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hX.1.2
  have hpay : X.fgPayload = (tr.state p kX).fg.proposalAttestations d.head := by
    rw [hfgj, hB]; rfl
  have hdroot : d.head.root = Pr.root := by
    have : X.parent = some d.head.root := by rw [hB]; rfl
    exact Option.some.inj (this.symm.trans hpar)
  have hσPr : (tr.state p kX).fg.σ Pr.root = (tr.state p (kX + 1)).fg.σ Pr.root := by
    obtain ⟨_, _, _, _, _, _, _, hsf, _⟩ :=
      onBlock'_fields ((Node.cutStep'_block_true _ _ _ _ _).1 (h.cutLaw p hp kX _ hacc)).2.1
    have hne : Pr.root ≠ X.root := fun he => by
      obtain rfl : Pr = X := hU.1 hPrU hXU he
      exact lt_irrefl _ (hU.2 _ hPrU _ hPrU hpar)
    rw [tr.state_succ_of_call hacc, hsf, Function.update_of_ne hne]
  refine ⟨Compose.fg_projection_from' hq hroot h hnc, by rw [hst]; exact hXt,
    by rw [hst]; exact hmono hPr, by rw [hpost, hst], by rw [hst, hσPr],
    fun att ⟨k', hk', hproc⟩ hah haT => ?_⟩
  have hpool := processed_att_retained' h hp hproc hk'
  rw [hst]
  by_cases hon : (tr.state p kX).fg.OnChain d.head att
  · right
    obtain ⟨Z, hZ, hZd, haZ⟩ := hon
    have hdt := mem_of_anc_right hZd hZ
    obtain rfl : d.head = Pr := hU.1 ⟨p, hp, kX, hdt⟩ hPrU hdroot
    exact ⟨Z, hmono hZ, hZd.mono hmono, haZ⟩
  · left
    rw [hpay]
    refine List.mem_filter.2 ⟨hpool, decide_eq_true ⟨Or.inl ⟨?_, ?_⟩, hon⟩⟩
    · rw [hdroot, hah]
    · rw [hdroot, haT]

end AnyAC

end Consensus.Goldilocks.Healing

end
