module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic inclusion: the record after a call whose optimistic check selects the proposal

Inside one AC call of an honest node, every record write is an `update_latest_confirmed` with a
candidate of the call (`call_writes`). When one optimistic check of the call selects `P` and every
selection of the call is an ancestor of `P` in the frame, the record after the call names a
descendant of `P` (`call_record_extends`): the write of `P` keeps a record at or below which `P`
lies or moves it to `P`, and a later candidate below `P` keeps such a record. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

section Record

variable {FGP : Type} {sp : ACParams}

/-- The record `r` names a block of `Φ` at or above `P`. -/
private def RecAbove (Φ : AC.Frm sp.n FGP) (P : AC.Blk sp.n FGP) (r : Nat) : Prop :=
  ∃ E ∈ Φ.tree, E.root = r ∧ Φ.Anc P E

/-- Writes of candidates below `P` keep a record at or above `P`. -/
private theorem Writes.recAbove {Φ : AC.Frm sp.n FGP} {New : AC.Blk sp.n FGP → Prop}
    {P : AC.Blk sp.n FGP} (hN : ∀ C, New C → C ∈ Φ.tree → Φ.Anc C P) {r r' : Nat}
    (h : Writes Φ New r r') (hr : RecAbove Φ P r) : RecAbove Φ P r' := by
  rw [writes_iff] at h
  induction h with
  | refl => exact hr
  | tail _ hs ih =>
    obtain ⟨C, hC, hn, hk | ⟨hnot, rfl⟩⟩ := hs
    · exact hk.2 ▸ ih
    · obtain ⟨E, hE, hEr, hPE⟩ := ih
      exact absurd ⟨E, hE, hEr, (hN C hn hC).trans hPE⟩ hnot

/-- An optimistic confirmation that selects `P` leaves a record at or above `P`. -/
private theorem optimisticConfirmation_recAbove {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    {t : Time} {P : AC.Blk sp.n FGP} (hsel : AC.optimisticSelect sp A Φ t = some P) :
    RecAbove Φ P (AC.optimisticConfirmation sp A Φ t).latestConfirmed := by
  have hPt := AC.optimisticSelect_mem_tree hsel
  unfold AC.optimisticConfirmation
  rw [hsel]
  dsimp only
  unfold AC.updateLatestConfirmed
  split_ifs with h
  · obtain ⟨E, hE, hEr, hPE⟩ := h
    exact ⟨E, hE, hEr, hPE⟩
  · exact ⟨P, hPt, rfl, Relation.ReflTransGen.refl⟩

end Record

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (AC.Blk sp.n FGP)} {tr : AC.GTrace sp FGP ro}

/-- **The record after a call whose optimistic check selects `P`.** At a call of an honest node,
if one optimistic check of the call selects `P` and every optimistic selection of the call is an
ancestor of `P` in the call's frame, the record after the call names a block of the frame at or
above `P`. A restart replays blocks with checks of its own and is excluded. -/
theorem call_record_extends {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)}
    (hc : tr.CallAt x i ℓ) {P : AC.Blk sp.n FGP}
    (hbelow : ∀ A B, AC.OptimisticPoint tr x i ℓ A →
      AC.optimisticSelect sp A ℓ.frame (tr.time i) = some B → ℓ.frame.Anc B P)
    {A₀ : AC.ACState sp.n} (hpt : AC.OptimisticPoint tr x i ℓ A₀)
    (hsel : AC.optimisticSelect sp A₀ ℓ.frame (tr.time i) = some P) :
    ∃ E ∈ ℓ.frame.tree, E.root = (tr.post i).latestConfirmed ∧ ℓ.frame.Anc P E := by
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  have hown : ∀ e ∈ ℓ.emits, ∀ B,
      AC.optimisticSelect sp (AC.admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame (tr.time i) =
        some B → ℓ.frame.Anc B P :=
    fun e he' B h => hbelow _ B ⟨hc, Or.inr (Or.inr ⟨e, he', rfl⟩)⟩ h
  -- a receipt check, followed by the call's `try_vote`
  have receipt : ∀ R : AC.ACState sp.n,
      (tr.post i, ℓ.emits) = AC.tryVote sp x (AC.optimisticConfirmation sp R ℓ.frame (tr.time i))
        ℓ.frame (tr.time i) →
      AC.optimisticSelect sp R ℓ.frame (tr.time i) = some P →
      RecAbove ℓ.frame P (tr.post i).latestConfirmed := by
    intro R hR hRs
    have h1 : tr.post i = (AC.tryVote sp x (AC.optimisticConfirmation sp R ℓ.frame (tr.time i))
      ℓ.frame (tr.time i)).1 := congrArg Prod.fst hR
    have h2 : ℓ.emits = (AC.tryVote sp x (AC.optimisticConfirmation sp R ℓ.frame (tr.time i))
      ℓ.frame (tr.time i)).2 := congrArg Prod.snd hR
    rw [h1]
    refine (writes_tryVote x _ ℓ.frame (tr.time i)).recAbove ?_
      (optimisticConfirmation_recAbove hRs)
    rintro C ⟨e, he', hC⟩ -
    exact hown e (h2 ▸ he') C hC
  obtain ⟨-, ⟨m, hm, rfl⟩ | ⟨B, hB, rfl⟩ | ⟨e, he', rfl⟩⟩ := hpt
  · rw [hm] at hpost hemits
    exact receipt _ (Prod.ext hpost.symm hemits.symm) hsel
  · rw [hB] at hpost hemits
    exact receipt _ (Prod.ext hpost.symm hemits.symm) hsel
  · change RecAbove ℓ.frame P _
    rw [AC.post_of_castAt hr hx ⟨hc, he'⟩]
    exact optimisticConfirmation_recAbove hsel

/-- **The last optimistic point of a call.** A non-restart call of an honest node with an
optimistic point has a point whose pools hold those of every point of the call and of the state
before the call, with the state's restart time: the own vote's check when the call votes, else
its receipt check. -/
theorem point_top {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro)}
    (hnr : ℓ.call ≠ .restart) {A₀ : AC.ACState sp.n} (h₀ : AC.OptimisticPoint tr x i ℓ A₀) :
    ∃ A, AC.OptimisticPoint tr x i ℓ A ∧
      (∀ A', AC.OptimisticPoint tr x i ℓ A' → ∀ σ, A'.pool σ ⊆ A.pool σ) ∧
      (∀ σ, (tr.state x i).pool σ ⊆ A.pool σ) ∧ A.restartTime = (tr.state x i).restartTime := by
  have hc := h₀.1
  by_cases hne : ∃ e, e ∈ ℓ.emits
  · -- the own vote's check: the call leaves its pools and restart time
    obtain ⟨e, he'⟩ := hne
    have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
    rw [hc.1] at he
    have hpost := congrArg Prod.fst he
    simp only at hpost
    have hP := AC.post_of_castAt hr hx ⟨hc, he'⟩
    have hpool := AC.optimistic_pool (AC.admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame
      (tr.time i)
    have hrt := (AC.optimistic_keeps (AC.admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame
      (tr.time i)).2
    refine ⟨_, ⟨hc, Or.inr (Or.inr ⟨e, he', rfl⟩)⟩, fun A' hA' σ v hv => ?_, fun σ v hv => ?_, ?_⟩
    · have h := AC.optimisticPoint_pool_post hr hx hA' σ hv
      rwa [AC.state_succ_of_call hc, hP, hpool] at h
    · have h := AC.step_pool_subset (ro := ro) x _ ℓ.frame (tr.time i) ℓ.call hnr σ hv
      rwa [hpost, hP, hpool] at h
    · rw [← hrt, ← hP, ← hpost]
      exact AC.step_restartTime x _ ℓ.frame (tr.time i) ℓ.call hnr
  · -- no own vote: the receipt check is the only one
    have hcall : ∀ A', AC.OptimisticPoint tr x i ℓ A' → A' = A₀ := by
      intro A' ⟨_, h'⟩
      obtain ⟨_, h⟩ := h₀
      rcases h' with ⟨m', hm', rfl⟩ | ⟨B', hB', rfl⟩ | ⟨e, he, -⟩
      · rcases h with ⟨m, hm, rfl⟩ | ⟨B, hB, -⟩ | ⟨e, he, -⟩
        · rw [hm] at hm'; cases hm'; rfl
        · rw [hB] at hm'; cases hm'
        · exact absurd ⟨e, he⟩ hne
      · rcases h with ⟨m, hm, -⟩ | ⟨B, hB, rfl⟩ | ⟨e, he, -⟩
        · rw [hm] at hB'; cases hB'
        · rw [hB] at hB'; cases hB'; rfl
        · exact absurd ⟨e, he⟩ hne
      · exact absurd ⟨e, he⟩ hne
    refine ⟨A₀, h₀, fun A' hA' σ v hv => hcall A' hA' ▸ hv, ?_⟩
    obtain ⟨_, ⟨m, -, rfl⟩ | ⟨B, -, rfl⟩ | ⟨e, he, -⟩⟩ := h₀
    · exact ⟨fun σ v hv => AC.mem_admitVote_pool hv, AC.admitVote_restartTime _ _ _⟩
    · exact ⟨fun σ v hv => hv, AC.blockReceipt_restartTime _ _ _⟩
    · exact absurd ⟨e, he⟩ hne

end Consensus.Goldilocks.Compose

end
