module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Params
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.ClientStep
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live

public section

/-! # One step of the FG state and of `create_attestation`

`Healing.stateTransition_bits` (one block of the state transition keeps the height or crosses with
a progress quorum) and `Healing.Store.createAtt_eq` (the attestation `create_attestation` makes has
its input's height and entry). They read only the FG chain and the client record, so they sit
below every store invariant that uses them (`Lemmas/FGStore/Parametric`, `Healing/Cut/Store`). -/

namespace Consensus.Goldilocks.Healing

open FG

/-! ## One block of the state transition -/

section Chain

variable {n : Nat}

/-- Counting attestations keeps the height, and every new progress or target bit is the signer
of a counted attestation at that height. -/
theorem foldl_processAtt_bits (σ : ChainState n) (atts : List (Att n)) :
    (atts.foldl ChainState.processAtt σ).h = σ.h ∧
      ∀ v ∈ (atts.foldl ChainState.processAtt σ).prog ∪
          (atts.foldl ChainState.processAtt σ).target,
        v ∈ σ.prog ∪ σ.target ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h := by
  induction atts generalizing σ with
  | nil => exact ⟨rfl, fun v hv => Or.inl hv⟩
  | cons b l ih =>
    have hb : (σ.processAtt b).h = σ.h ∧ ∀ v ∈ (σ.processAtt b).prog ∪ (σ.processAtt b).target,
        v ∈ σ.prog ∪ σ.target ∨ (b.val = v ∧ b.h = σ.h) := by
      obtain ⟨f, p, t, he⟩ := ChainState.foldl_processAtt_eq σ [b]
      refine ⟨by simpa using congrArg ChainState.h he, fun v hv => ?_⟩
      clear he ih
      unfold ChainState.processAtt at hv
      repeat' split at hv
      all_goals simp only [Finset.mem_union, Finset.mem_insert] at hv
      all_goals aesop
    obtain ⟨h1, h2⟩ := ih (σ.processAtt b)
    refine ⟨h1.trans hb.1, fun v hv => ?_⟩
    rcases h2 v hv with hv | ⟨a, ha, rfl, hah⟩
    · rcases hb.2 v hv with hv | ⟨rfl, hbh⟩
      · exact Or.inl hv
      · exact Or.inr ⟨b, List.mem_cons_self, rfl, hbh⟩
    · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, rfl, hah.trans hb.1⟩

/-- **One block, G0.2 (f).** A block keeps the height, and its state's progress and target bits
are old bits or signers of its attestations at that height; or it enters the next height, with
no bits, after a progress quorum of old bits and signers of its attestations at the old height. -/
theorem stateTransition_bits {gp : FGParams} {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.h = σ.h ∧ ∀ v ∈ σ'.prog ∪ σ'.target,
        v ∈ σ.prog ∪ σ.target ∨ ∃ a ∈ B.atts, a.val = v ∧ a.h = σ.h) ∨
      (σ'.h = σ.h + 1 ∧ σ'.prog ∪ σ'.target = ∅ ∧ ∃ S : Finset (Fin gp.n), gp.q ≤ S.card ∧
        ∀ v ∈ S, v ∈ σ.prog ∪ σ.target ∨ ∃ a ∈ B.atts, a.val = v ∧ a.h = σ.h) := by
  obtain ⟨-, rfl⟩ := (gp.stateTransition_eq_some).1 h
  obtain ⟨h1, h2⟩ := foldl_processAtt_bits { σ with s := B.slot } B.atts
  have h1' : (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).h = σ.h := h1
  obtain ⟨F, hF, σ₁, rfl, -, hc⟩ := gp.heightEvents_cases
    { B.atts.foldl ChainState.processAtt { σ with s := B.slot } with L := B.root }
  rcases hc with ⟨hj, he⟩ | ⟨-, ht, he⟩ | ⟨-, -, he⟩ <;> rw [he]
  · exact Or.inr ⟨by simp [ChainState.advance, h1'], by simp [ChainState.advance], _,
      hj.1, fun v hv => h2 v (Finset.mem_union_right _ hv)⟩
  · exact Or.inr ⟨by simp [ChainState.advance, h1'], by simp [ChainState.advance], _,
      ht.1, fun v hv => h2 v (Finset.mem_union_left _ hv)⟩
  · exact Or.inl ⟨h1, h2⟩

end Chain

namespace Store

variable {P : Params}

/-- `height_pair` names the input's height and entry. -/
theorem heightPair_eq {Λ : FG.Record} {hc Tc h T : Nat} {τ : Bool}
    (hp : Λ.heightPair hc Tc = some (h, T, τ)) : h = hc ∧ T = Tc := by
  unfold FG.Record.heightPair at hp
  split_ifs at hp <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp <;>
    exact ⟨hp.1.symm, hp.2.1.symm⟩

/-- The attestation that `create_attestation` makes has the height and entry of its input. -/
theorem createAtt_eq {Λ Λ' : FG.Record} {v : Fin P.n} {σe : ChainState P.n} {a : Att P.n}
    (h : Λ.createAtt v σe = some (a, Λ')) : a.h = σe.h ∧ a.T = σe.Th := by
  obtain ⟨-, -, hh, hT, -⟩ := FG.Record.createAtt_some h
  exact ⟨hh, hT⟩

end Store

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Store

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

/-- A block counts progress, then keeps its height and entry or crosses with a quorum. -/
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

/-- One accepted block keeps the height and entry or enters the next height by itself;
it keeps the justification or justifies the parent's entry at the parent's height. -/
theorem step_fields {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
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

end Consensus.Goldilocks.Store

end
