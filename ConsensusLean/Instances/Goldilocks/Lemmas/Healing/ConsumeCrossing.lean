module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service

public section

/-! # Goldilocks Healing, HS.5: the pool facts of the mature crossing

Processed attestations stay in an honest node's attestation pool (`processed_att_retained`), and
an honest validator signs its own attestations (`signAt_val`). The crossing itself, part of HS.5's
consumption, is removed with HS.4 and HR.3 (retired, owner decision). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

/-! ## One block of the chain (FG traces) -/

section Chain

open _root_.Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

end Chain

/-! ## The pool of an honest node (any AC) -/

section Pool

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

/-- An accepted block keeps the pool and adds its payload. -/
private theorem mem_onBlock {ACP : Type} {st st' : Store P ACP} {B : NodeBlock P ACP}
    (hB : st.onBlock B = some st') {a : FG.Att P.n}
    (h : a ∈ st.atts ∨ a ∈ B.fgPayload) : a ∈ st'.atts := by
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := Goldilocks.Store.onBlock_eq_some hB
  refine mem_addAtts (h.imp_left fun h => ?_)
  rw [(Goldilocks.Store.updateFinality_spec _ σ').2.2.1]
  exact h

/-- **The pool of an honest node only grows.** -/
private theorem atts_mono (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {i j : Nat}
    (hij : i ≤ j) {a : FG.Att P.n} (ha : a ∈ (tr.state y i).fg.atts) :
    a ∈ (tr.state y j).fg.atts := by
  induction j, hij using Nat.le_induction with
  | base => exact ha
  | succ j _ ih =>
    have ha := ih
    rcases fg_step h hy j with he | ⟨B, -, hB⟩ | ⟨b, -, he⟩
    · rwa [he]
    · exact mem_onBlock hB (Or.inl ha)
    · rw [he]
      exact mem_onAttestation (Or.inl ha)

/-- A processed attestation is in the pool after the cut. -/
private theorem mem_atts_of_process (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H)
    {k : Nat} {a : FG.Att P.n} (hp : tr.ProcessAttAt y k a) :
    a ∈ (tr.state y (k + 1)).fg.atts := by
  rcases hp with hc | ⟨B, hc, ha⟩
  · rw [tr.state_succ_of_call hc, (h.cutLaw y hy k _ hc).1]
    exact mem_onAttestation (Or.inr rfl)
  · rw [tr.state_succ_of_call hc]
    exact mem_onBlock (h.cutLaw y hy k _ hc).2.1 (Or.inr ha)

/-- Processed attestations persist in the honest node's durable attestation pool. -/
theorem processed_att_retained (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {k j : Nat} {a : FG.Att P.n}
    (hp : tr.ProcessAttAt y k a) (hkj : k < j) : a ∈ (tr.state y j).fg.atts := by
  exact atts_mono h hy (by omega) (mem_atts_of_process h hy hp)

/-- An honest validator signs its own attestations. -/
theorem signAt_val (h : Node.LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att P.n} (hs : tr.SignAt y k att) : att.val = y := by
  obtain ⟨src, hc⟩ := hs
  have h := (h.cutLaw y hy k _ hc).1
  exact (FG.Record.createAtt_some h).1

end Pool

/-! ## The run -/

section Run

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF : Time}
  {proposer : Nat → Fin sp.n}

end Run

end Consensus.Goldilocks.Healing

end
