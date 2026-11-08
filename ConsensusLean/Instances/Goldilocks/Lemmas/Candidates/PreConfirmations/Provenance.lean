module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.PreConfirmations.Handlers

public section

/-! # ½ pre-confirmations: key provenance

On a run of the PC SA (`ACLocalRun`) with ack authenticity (`HonestObjectsPC`) and fewer than `μ`
faulty validators, a key in an honest node's `pcs` was decided by an honest acker
(`keyProvenance`):

* a key in `pcs` has its quorum in the same store (`pcsQuorum`, a stable predicate of the store:
  `onAck` adds a key only with its quorum, the ackers only grow, and a restart empties both);
* the quorum of the first ack committee holds `μ` ackers, so an honest one;
* its ack, held by an honest node, was emitted by its node (`HonestObjectsPC.held_ack`), and an
  emitted ack is the sender's decision at the call's pre-state (`step_ack_emission`);
* a decision held at a state was made at an earlier tick cut after the update of its slot, with
  `μ` clean early supporters of the target there (`myAcks_decided`, by `step_myAcks`).

Nothing here transports activity, bounds D21 support, or settles a base. -/

namespace Consensus.Goldilocks.PreConfirmations

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type} {σ : Type} {E : UnlockStage sp wlockStore σ} {c : σ}
  {m : WriteMode} {ro : ReplayOrder sp FGP}

variable (sp) in
/-- Every key in `pcs` has its quorum in the same store. -/
def PcsQuorum (P : PCStore sp.n) : Prop := ∀ s X, (s, X) ∈ P.pcs → quorum sp P s X

theorem pcsQuorum_iff (P : PCStore sp.n) :
    PcsQuorum sp P ↔ ∀ s X, (s, X) ∈ P.pcs → quorum sp P s X := Iff.rfl

theorem quorum_mono {P P' : PCStore sp.n} {s X : Nat}
    (hsub : ∀ j, P.acks s X j ⊆ P'.acks s X j) (h : quorum sp P s X) : quorum sp P' s X :=
  fun j hj => (h j hj).trans (Set.ncard_le_ncard (hsub j) (Set.toFinite _))

theorem pcsQuorum_of {P P' : PCStore sp.n} (hacks : P'.acks = P.acks) (hpcs : P'.pcs ⊆ P.pcs)
    (h : PcsQuorum sp P) : PcsQuorum sp P' := by
  intro s X hk
  have := h s X (hpcs hk)
  unfold quorum at this ⊢
  rw [hacks]
  exact this

/-- **The quorum of the keys is a stable predicate of the store.** -/
theorem pcsQuorum_stable : StoreStable (FGP := FGP) (PcsQuorum sp) where
  empty_ok _ _ h := absurd h (Set.notMem_empty _)
  refresh_ok P Φ t h :=
    pcsQuorum_of (P := P) (P' := refresh sp P Φ t) rfl (fun _ hk => (mem_refresh_pcs.1 hk).1) h
  record_ok P t v h := by
    obtain ⟨h₁, h₂, -⟩ := (keepsButVotes_iff _ _).1 (recordVote_keeps P t v)
    exact pcsQuorum_of (P := P) h₁ (le_of_eq h₂) h
  onAck_ok P t a h := by
    unfold onAck
    dsimp only
    split_ifs with h₁ h₂
    · exact h
    · intro s X hk
      rcases (Set.mem_insert_iff.1 hk) with he | hk
      · cases he
        exact h₂
      · refine quorum_mono (fun j => ?_) (h s X hk)
        intro v hv
        dsimp only
        split_ifs
        · exact Set.mem_insert_of_mem _ hv
        · exact hv
    · intro s X hk
      refine quorum_mono (fun j => ?_) (h s X hk)
      intro v hv
      dsimp only
      split_ifs
      · exact Set.mem_insert_of_mem _ hv
      · exact hv
  decide_ok P A Φ t u h := by
    have hr : PcsQuorum sp (refresh sp P Φ t) :=
      pcsQuorum_of (P := P) (P' := refresh sp P Φ t) rfl (fun _ hk => (mem_refresh_pcs.1 hk).1) h
    unfold decideAck
    split
    · exact h
    · split_ifs
      · exact h
      · split
        · exact h
        · dsimp only
          split_ifs
          · exact hr
          · exact hr

/-- On a run, a stable predicate of the store holds at every honest state. -/
theorem honest_storeStable {Q : PCStore sp.n → Prop} (hQ : StoreStable (FGP := FGP) Q)
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : ACTrace (preConfSAM sp E c m FGP ro)}
    (hr : ACLocalRun (preConfSAM sp E c m FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i, Q (tr.state y i).store := by
  intro i
  induction i with
  | zero =>
    change Q (tr.init y).store
    rw [hr.init y hy]
    exact hQ.empty_ok
  | succ i ih =>
    simp only [Trace.state]
    split_ifs with hc
    · obtain ⟨hn, hl⟩ := hc
      obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hl
      have hex := hr.exec i ℓ hℓ (hn ▸ hy)
      rw [hn] at hex
      have := step_storeStable hQ y (tr.state y i) ℓ.frame (tr.time i) ℓ.call ih
      rw [hex] at this
      exact this
    · exact ih

/-- **A decision held at a state was made earlier**: an honest node's decision of slot `s` on `x`
at cut `i` was made at an earlier tick cut. -/
theorem myAcks_decided {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    {tr : ACTrace (preConfSAM sp E c m FGP ro)}
    (hr : ACLocalRun (preConfSAM sp E c m FGP ro) H U tr) {v : Fin sp.n} (hv : v ∈ H)
    {s x : Nat} : ∀ i, (tr.state v i).store.myAcks s = some x →
      ∃ i' < i, AckDecidedAt sp FGP E c m ro tr v i' s x := by
  intro i
  induction i with
  | zero =>
    intro h
    change (tr.init v).store.myAcks s = some x at h
    rw [hr.init v hv] at h
    cases h
  | succ i ih =>
    intro h
    simp only [Trace.state] at h
    split_ifs at h with hc
    · obtain ⟨hn, hl⟩ := hc
      obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hl
      have hex := hr.exec i ℓ hℓ (hn ▸ hv)
      rw [hn] at hex
      have hpost : ((preConfSAM sp E c m FGP ro).step v (tr.state v i) ℓ.frame (tr.time i)
          ℓ.call).1 = tr.post i := congrArg Prod.fst hex
      rw [← hpost] at h
      rcases step_myAcks v (tr.state v i) ℓ.frame (tr.time i) ℓ.call h with
        h' | ⟨hk, h₁, h₂⟩
      · obtain ⟨i', hi', hd⟩ := ih h'
        exact ⟨i', by omega, hd⟩
      · refine ⟨i, by omega, ℓ, ⟨hn, hℓ⟩, hk, h₁, ?_, ?_⟩
        · rw [← hpost]
          exact h
        · rw [← hpost]
          exact h₂
    · obtain ⟨i', hi', hd⟩ := ih h
      exact ⟨i', by omega, hd⟩

/-- **Key provenance.** -/
theorem keyProvenance : KeyProvenance sp FGP E c m ro := by
  intro sel H U tr hr hobj hf y hy i s X hk
  -- the quorum of the first ack committee has an honest acker
  have hq := honest_storeStable pcsQuorum_stable hr hy i s X hk 2 (Or.inl rfl)
  obtain ⟨v, hvA, hvH⟩ : ∃ v ∈ (tr.state y i).store.acks s X 2, v ∈ H := by
    by_contra hno
    have hsub : (tr.state y i).store.acks s X 2 ⊆ Hᶜ := fun v hv hvH => hno ⟨v, hv, hvH⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  -- its ack was emitted by its node, at a decision of its pre-state
  obtain ⟨k, hki, ℓ, hc, e, he, hem⟩ :=
    hobj.held_ack y hy i ⟨v, s, X, 2⟩ hvA hvH
  have hex := hr.exec k ℓ hc.2 (hc.1 ▸ hvH)
  rw [hc.1] at hex
  have he' : e ∈ ((preConfSAM sp E c m FGP ro).step v (tr.state v k) ℓ.frame (tr.time k)
      ℓ.call).2 := by
    rw [hex]
    exact he
  obtain ⟨-, hmy⟩ := step_ack_emission v (tr.state v k) ℓ.frame (tr.time k) ℓ.call he' hem
  obtain ⟨i', hi', hd⟩ := myAcks_decided hr hvH k hmy
  exact ⟨v, hvH, i', by omega, hd⟩

end Consensus.Goldilocks.PreConfirmations

end
