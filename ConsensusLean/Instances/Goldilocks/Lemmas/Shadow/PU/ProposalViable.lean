module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FullFrameWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.HeldChains
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable

public section

/-! # Proposal heights and viability under P-U

## Store-level proposal height bounds

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
  induction hr with
  | refl =>
    intro B hB a ha
    have hB : (if B.root = P.genesisRoot then some (P.genesisBlock acp₀) else none) =
        some B := hB
    split_ifs at hB
    cases hB
    cases ha
  | @tail s s' _ hs ih =>
    rcases hs with ⟨B', hB'⟩ | ⟨b, rfl⟩
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
  obtain ⟨Qt, hQt, hvt⟩ := (Goldilocks.Store.justification_quorum P.fg hcX).2 (by omega)
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
    obtain ⟨hYF, hYhF⟩ := P.fg.previousHeightJustified_justify_finalizes_block hcYp hstY hbYp hYj
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

/-! ## Proposal viability over the P-U frame window -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {hold : Time}

/-- The viable proposal parent transfers its primed-window witness to its child. -/
theorem proposal_window_witness
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {lo hi : Time} {M u : Nat} {isTop : Prop}
    {J B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : Generic.FrameWindow tr H lo hi M isTop J)
    {z : Fin sp.n} {kB : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hB : tr.ProposesAt z kB B) (hBs : B.slot = u)
    (hlo : lo ≤ sp.ts u) (hhi : sp.ts u ≤ hi)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    M - 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h ∧
      (isTop → ((tr.state z (kB + 1)).fg.σ B.root).h = M - 1 →
        Anc (tr.HonestBlocksAt H) J B) := by
  have htime : tr.time kB = sp.ts u := by
    simpa only [sp.slotTime_eq, hBs, ACParams.ts] using hB.2.2
  have hzk : z ∈ H (tr.time kB) := htime ▸ hz
  have ht := hrun.time_nonneg kB
  have hr := hrun.upTo ht
  have hB' : (tr.upTo (tr.time kB)).ProposesAt z kB B :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hB.1⟩, hB.2.1, hB.2.2⟩
  obtain ⟨_, ip, ell, d, pay, hc, hcall, hd, hti, hpar, _⟩ :=
    Healing.honestProposalRun_of_proposesAt hr (hnc.upTo _) hzk hdes hB' hBs
  rw [← hdes] at hc hd
  have hip : tr.time ip = sp.ts u := hti
  have hzi : z ∈ H (tr.time ip) := hip ▸ hz
  have hleip : ∀ q < ip, tr.time q ≤ tr.time kB := by
    intro q hq
    exact (hrun.time_mono hq.le).trans (by rw [hip, htime])
  have hleB : ∀ q < kB + 1, tr.time q ≤ tr.time kB :=
    fun q hq => hrun.time_mono (by omega)
  have hfr := Compose.frame_of_projAC hr hzk hc
  have hfr' : ell.frame = Node.frame (tr.state z ip) := by
    rw [Trace.upTo_state tr z hleip] at hfr
    exact hfr
  obtain ⟨Q, hQ, hv, hroot⟩ := Shadow.full_frame_viable_witness_at hrun hnc hzi (hip ▸ hf)
  rw [← hfr'] at hQ hv hroot
  have hac := (Compose.goldilocks_ac_projection_from hr (hnc.upTo _)).localRun
  have hvd := Healing.proposal_head_viable hac hr.vstart hzk hc hcall
    (by rw [sp.slotTime_eq]; exact hti) hd
    ⟨(AC.frameIn_of_callAt hac hzk hc).1.fcRoot_mem, .refl, Q, hQ, hv, hroot⟩
  rw [hfr, Node.frame_eq, Store.toFrame_viableHeads] at hvd
  obtain ⟨hDm, _, hDv⟩ := hvd
  have hBm : B ∈ ((tr.upTo (tr.time kB)).state z (kB + 1)).fg.tree :=
    (Healing.accept_of_proposesAt hr (hnc.upTo _) hzk hB').2.1
  have hDhist : d.head ∈ (tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB)) :=
    ⟨z, hzk, ip, hDm⟩
  have hBhist : B ∈ (tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB)) :=
    ⟨z, hzk, kB + 1, hBm⟩
  have hDB : Anc ((tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB))) d.head B :=
    .single ⟨hDhist, hBhist, hpar⟩
  have hDBs := Compose.honest_held_anc hr (hnc.upTo _) hzk hDB hBm
  have hDpost : d.head ∈ ((tr.upTo (tr.time kB)).state z (kB + 1)).fg.tree := by
    by_cases he : d.head = B
    · exact he ▸ hBm
    · exact (Anc.mem hDBs he).1
  have hσ := Healing.Store.σ_eq_of_mem
    (Compose.fg_reachable hr.toLocalRun hzk ip)
    (Compose.fg_reachable hr.toLocalRun hzk (kB + 1))
    (Compose.honest_blocks_coherent hr.toLocalRun (hnc.upTo _)).1
    (fun _ hm => ⟨z, hzk, ip, hm⟩) (fun _ hm => ⟨z, hzk, kB + 1, hm⟩) hDm hDpost
  have hh := (Compose.honest_held_height hr (hnc.upTo _) hzk hDBs).1
  rw [← hσ] at hh
  have hM : ((tr.upTo (tr.time kB)).state z ip).fg.hmax = M := by
    rw [Trace.upTo_state tr z hleip]
    exact hwin.M_eq z ip hzi (hip ▸ hlo) (hip ▸ hhi)
  have hpred : M - 1 ≤
      (((tr.upTo (tr.time kB)).state z ip).fg.σ d.head.root).h := by
    rw [Store.isViable_iff] at hDv
    rcases hDv with hh | ⟨hh, _⟩ <;> omega
  have hheight := hpred.trans hh
  rw [Trace.upTo_state tr z hleB] at hheight
  refine ⟨hheight, ?_⟩
  intro htop heq
  have htop' : ((tr.upTo (tr.time kB)).state z ip).fg.hmax =
      ((tr.upTo (tr.time kB)).state z ip).fg.hj + 1 := by
    rw [Trace.upTo_state tr z hleip]
    exact (hwin.top_iff z ip hzi (hip ▸ hlo) (hip ▸ hhi)).2 htop
  have hJ : ((tr.upTo (tr.time kB)).state z ip).fg.J = J := by
    rw [Trace.upTo_state tr z hleip]
    exact hwin.root_eq z ip hzi (hip ▸ hlo) (hip ▸ hhi) htop
  rw [Trace.upTo_state tr z hleB, heq] at hh
  have hJD : ((tr.upTo (tr.time kB)).state z ip).fg.Anc J d.head := by
    rw [Store.isViable_iff] at hDv
    rcases hDv with hh | ⟨hh, hgap | hJD⟩
    · omega
    · omega
    · exact hJ ▸ hJD
  have hJD' : Anc ((tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB))) J d.head :=
    Anc.mono (fun _ hm => ⟨z, hzk, ip, hm⟩) hJD
  exact Anc.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono ht) (hJD'.trans hDB)

/-- Relay or early membership preserves the primed proposal witness at an honest call. -/
theorem proposal_viable_at_call_with_early_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    {g ΔF b hi : Time} {u M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts u) hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u)
    (hphi : sp.ts u + sp.Δ ≤ hi) (hib : hi ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    (hlo : sp.ts u ≤ tr.time i) (hhi : tr.time i ≤ hi)
    (hearly : tr.time i < sp.ts u + sp.Δ → P ∈ ell.frame.tree) :
    P ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) :=
    hrun.antitone (by rw [htime]; linarith [sp.toParams.hΔ]) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, ip, ellp, d, pay, hcp, hcall, hd, hti, hparent, _, _, _, ja, _, hacc, hta⟩ :=
    Healing.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hacc
  have hja : tr.time ja = sp.ts u := hta
  have hzja : z ∈ H (tr.time ja) := hja ▸ (htime ▸ hzk)
  rw [RunTrace.upTo_projAC] at hacc
  obtain ⟨ella, hca, hblock⟩ := hacc
  have hca' := ((Trace.upTo_callAt tr.projAC).mp hca).2
  have hra := hac.upTo (hrun.time_nonneg ja)
  have hca'' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hca'⟩
  have hPt := (AC.accept_new sp hra.localRun hzja ⟨ella, hca'', hblock⟩).1 ella hca''
  have hfa := Compose.Growing.frame_of_projAC_at hrun hzja hca'
  have hfi := Compose.Growing.frame_of_projAC_at hrun hy hc
  rw [hfa, Node.frame_eq, Store.toFrame_tree] at hPt
  have hPm := (Healing.accept_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
    (hnc.upTo _) hzk hP').2.1
  rw [Trace.upTo_state tr z (fun q hq => hrun.time_mono (by omega))] at hPm
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
    (fun q hq => hrun.time_mono (by omega)) hzk (hrun.time_nonneg ja)
    (fun q hq => hrun.time_mono hq.le) hzja hPm hPt.1
  have hmf (t : Time) (ht0 : 0 ≤ t) (htb : t ≤ b) :
      (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf t ht0 htb
    have hn := sp.toParams.hn
    change (H t)ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hw := proposal_window_witness hrun hnc hframe (htime ▸ hzk) hdes hP hPs le_rfl
    (by linarith [sp.toParams.hΔ])
    (hmf _ (by rw [← htime]; exact hrun.time_nonneg kP)
      (by linarith only [hphi.trans hib, sp.toParams.hΔ]))
  rw [hσ] at hw
  have hlow : sp.ts u ≤ tr.time i := by linarith [sp.toParams.hΔ]
  have hFP := Generic.FrameWindow.finalized_below_descendant_at
    hframe hrun hnc hy hzja hzja
    (hmf _ ((hrun.time_nonneg i).trans (le_max_left _ _))
      (max_le (hhi.trans hib) (by rw [hja]; linarith [sp.toParams.hΔ])))
    hlow hhi hPt.1 hw hPt.1 .refl
  have hFP' : Anc (tr.HonestBlocksAt H) ell.frame.F P := by
    rw [hfi, Node.frame_eq, Store.toFrame_F]
    exact hFP
  have hri := hac.upTo (hrun.time_nonneg i)
  have hci := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hPy : P ∈ ell.frame.tree := by
    by_cases ht : tr.time i < sp.ts u + sp.Δ
    · exact hearly ht
    obtain ⟨q, hqi, haq, _⟩ := accepted_relay_before_at hrun hsvc hnr hzja
      ⟨ella, hca', hblock⟩ (by rw [hja]; exact hgu) hy hc
      (by rw [hja]; exact not_lt.mp ht) hFP'
    have haq' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y q P := by
      obtain ⟨ellq, hcq, heq⟩ := haq
      exact ⟨ellq, (Trace.upTo_callAt _).mpr ⟨hrun.time_mono hqi, hcq⟩, heq⟩
    exact AC.mem_tree_of_acceptAtU sp hri.localRun.toU hy haq' hqi hci hFP'
  have hPyi : P ∈ (tr.state y i).fg.tree := by
    rw [hfi, Node.frame_eq, Store.toFrame_tree] at hPy
    exact hPy.1
  have hv := (windowWitness_of_frameWindow
    hrun hnc hframe hzja hPt.1 hw).held y i hy hlow hhi
      (hmf _ (hrun.time_nonneg i) (hhi.trans hib)) hPyi
  have hstore := store_anc_of_honest_anc_at hrun hnc (hrun.time_nonneg i)
    (fun q hq => hrun.time_mono hq.le) hy hFP hPyi
  refine ⟨hPy, ?_, ?_⟩
  · rw [hfi, Node.frame_eq, Store.toFrame_fcRoot]
    change Anc (tr.state y i).fg.toFrame.tree _ _
    rw [Store.toFrame_tree]
    exact Anc.restrict .refl hstore
  · rw [hfi, Node.frame_eq, Store.toFrame_viableHeads]
    exact ⟨hPyi, hstore, hv.2⟩

/-- Late calls obtain proposal membership from relay. -/
theorem proposal_viable_at_call_primed_at'
    {ini : Fin sp.n → (goldilocksNode sp).State}
    {g ΔF b hi : Time} {u M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts u) hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u)
    (hphi : sp.ts u + sp.Δ ≤ hi) (hib : hi ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y i ell)
    (hlo : sp.ts u + sp.Δ ≤ tr.time i) (hhi : tr.time i ≤ hi) :
    P ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads := by
  exact proposal_viable_at_call_with_early_at hframe hrun hnc hsvc hf hnr hgu hphi hib
    hz hdes hP hPs hy hc (by linarith [sp.toParams.hΔ]) hhi
    (fun h => absurd h (not_lt.mpr hlo))

/-- An honest cast retains the proposal in its voter-domain viable tree. -/
theorem proposal_viable_at_cast_primed_at'
    {ini : Fin sp.n → (goldilocksNode sp).State}
    {g ΔF b : Time} {s₀ p M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p) :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame p) := by
  have hri := (Compose.Growing.goldilocks_ac_projection_from hrun hnc).upTo
    (hrun.time_nonneg i)
  have hci := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hslot : e.msg.slot = sp.slot (tr.time i) := (AC.castAt_specU hri.localRun.toU hy hci).2.1
  have hslot' := hslot.symm.trans hes
  have hpT : sp.ts p ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [hslot'])
  have hhigh : tr.time i ≤ sp.ts p + sp.Δ := by
    have ht := AC.vote_time_leU hri.localRun.toU hy ⟨ell, hci⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    rwa [hslot'] at ht
  have hts : sp.ts s₀ ≤ sp.ts p := (AC.ts_le_iff sp).2 (by exact_mod_cast hsp)
  obtain ⟨hPy, hroot, hv⟩ := proposal_viable_at_call_with_early_at
    (hframe.mono hts le_rfl) hrun hnc hsvc hf hnr (hm.trans hts) le_rfl hpb
    hz hdes hP hPs hy hc.1 hpT hhigh (fun hearly => by
      obtain ⟨⟨Q, hQ, hQs, _⟩, -⟩ :=
        AC.cast_readyU hri.localRun.toU hy hci (by rw [hes]; exact hearly)
      rw [hes] at hQs
      exact proposal_frame_unique_at hrun hnc hz hdes hP hPs hp0 hy hc.1
        hhigh hQ hQs ▸ hQ)
  have hdom : P ∈ AC.voterBlockTree sp e.readPoint ell.frame p :=
    ⟨hPy, Or.inr ⟨P, hPy, hPs, .refl⟩⟩
  exact ⟨hv, hdom, hroot, P, hdom, hv, .refl⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
