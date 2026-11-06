module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.State
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.FinalityPair

public section

/-! # Goldilocks FG: the validator client (G0.5, G0.10)

Client safety (G0.5) from a record invariant over the attestations sent so far: each target
is the recorded target at its height, each timeout's root is in the recorded timeout set at
its height, and each finality pair is the lock at its height and stays permitted. The
invariant holds for the empty record and `createAtt` keeps it when the entry state's pairs
are below its height; at the end it rules out E1 (the permitted pair meets every attestation at its
height) and E2 (one recorded target per height). Aggregation (G0.10) unfolds `createAtt`. -/

namespace Consensus.Goldilocks.FG

namespace Record

variable {n : Nat}

/-- The record invariant of a client run over the attestations `atts` sent so far. -/
private def Tracks (Λ : Record) (atts : List (Att n)) : Prop :=
  ∀ a ∈ atts, (a.timeout = true → a.T ∈ Λ.timeout a.h) ∧
    (a.timeout = false → Λ.target a.h = some a.T) ∧
    ∀ p ∈ a.fin.toList, Λ.lock p.1 = some p.2 ∧ Λ.permits p.1 p.2

private theorem tracks_empty : Tracks empty ([] : List (Att n)) := by
  simp [Tracks]

/-- The fold of `finalityPair` returns its start or an element of the list. -/
private theorem foldl_newest_mem {l : List (Nat × Nat)} {o : Option (Nat × Nat)} {p : Nat × Nat}
    (h : l.foldl (fun acc p => match acc with
      | none => some p
      | some r => if r.1 < p.1 then some p else some r) o = some p) : o = some p ∨ p ∈ l := by
  exact Consensus.Goldilocks.FG.Record.foldl_newest_mem_or_initial h

/-- The finality pair of an entry state is permitted and below its height. -/
private theorem finalityPair_spec {Λ : Record} {σe : ChainState n}
    (hσ : σe.hj < σe.h ∧ ∀ p ∈ σe.pending, p.1 < σe.h) {p : Nat × Nat}
    (hp : Λ.finalityPair σe = some p) : Λ.permits p.1 p.2 ∧ p.1 < σe.h := by
  unfold finalityPair at hp
  split_ifs at hp with hb hper
  · cases hp
    exact ⟨hper, hσ.1⟩
  · rcases foldl_newest_mem hp with h | h
    · cases h
    · rw [List.mem_filter, decide_eq_true_iff] at h
      exact ⟨h.2, hσ.2 p h.1⟩

/-- A height pair names the entry, its lock is free or equal, and a target finds its
target free or equal. -/
private theorem heightPair_spec {Λ : Record} {h T hc Tc : Nat} {τ : Bool}
    (hp : Λ.heightPair h T = some (hc, Tc, τ)) :
    hc = h ∧ Tc = T ∧ (Λ.lock h = none ∨ Λ.lock h = some T) ∧
      (τ = false → Λ.target h = none ∨ Λ.target h = some T) := by
  unfold heightPair at hp
  split_ifs at hp with h1 h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp <;>
    obtain ⟨rfl, rfl, rfl⟩ := hp <;> simp_all <;> tauto

/-- Recording an attestation keeps the timeout roots. -/
private theorem timeout_subset_recordAtt (Λ : Record) (a : Att n) (j : Nat) :
    Λ.timeout j ⊆ (Λ.recordAtt a).timeout j := by
  simp only [recordAtt]
  split_ifs
  · rw [Function.update_apply]
    split_ifs with he
    · exact he ▸ Finset.subset_insert _ _
    · exact subset_rfl
  · exact subset_rfl

/-- Recording an attestation keeps a recorded target. -/
private theorem target_recordAtt {Λ : Record} (a : Att n) {j T : Nat} (h : Λ.target j = some T) :
    (Λ.recordAtt a).target j = some T := by
  simp only [recordAtt]
  split_ifs with hc
  · rw [Function.update_of_ne (by rintro rfl; simp [h] at hc), h]
  · exact h

/-- Recording an attestation keeps a lock that its finality pair agrees with. -/
private theorem lock_recordAtt {Λ : Record} {a : Att n} {j T : Nat} (h : Λ.lock j = some T)
    (hf : ∀ p ∈ a.fin.toList, p.1 = j → p.2 = T) : (Λ.recordAtt a).lock j = some T := by
  rcases ha : a.fin with _ | p
  · simpa [recordAtt, ha] using h
  · simp only [recordAtt, ha, Function.update_apply]
    split_ifs with he
    · rw [hf p (by simp [ha]) he.symm]
    · exact h

/-- Recording an attestation keeps a permitted pair that it agrees with. -/
private theorem permits_recordAtt {Λ : Record} {a : Att n} {j T : Nat} (hp : Λ.permits j T)
    (hh : a.h = j → a.T = T) (hf : ∀ p ∈ a.fin.toList, p.1 = j → p.2 = T) :
    (Λ.recordAtt a).permits j T := by
  obtain ⟨ht, hto, hl⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · simp only [recordAtt]
    split_ifs
    · rw [Function.update_apply]
      split_ifs with he
      · exact Or.inr (by rw [hh he.symm])
      · exact ht
    · exact ht
  · simp only [recordAtt]
    split_ifs
    · rw [Function.update_apply]
      split_ifs with he
      · subst he
        rw [hh rfl]
        exact Finset.insert_subset (by simp) hto
      · exact hto
    · exact hto
  · rcases hl with hl | hl
    · rcases ha : a.fin with _ | p
      · simpa [recordAtt, ha] using Or.inl hl
      · simp only [recordAtt, ha, Function.update_apply]
        split_ifs with he
        · rw [hf p (by simp [ha]) he.symm]
          exact Or.inr rfl
        · exact Or.inl hl
    · exact Or.inr (lock_recordAtt hl hf)

/-- `createAtt` keeps the invariant when the entry state's pairs are below its height. -/
private theorem tracks_createAtt {Λ Λ' : Record} {atts : List (Att n)} {v : Fin n}
    {σe : ChainState n} {a : Att n} (hΛ : Tracks Λ atts)
    (hσ : σe.hj < σe.h ∧ ∀ p ∈ σe.pending, p.1 < σe.h)
    (h : Λ.createAtt v σe = some (a, Λ')) : Tracks Λ' (a :: atts) := by
  unfold createAtt at h
  split at h
  · cases h
  rename_i hc Tc τ hhp
  split_ifs at h
  cases h
  obtain ⟨rfl, rfl, hlock, htgt⟩ := heightPair_spec hhp
  have hfin := fun p (hp : p ∈ (Λ.finalityPair σe).toList) =>
    finalityPair_spec hσ (Option.mem_toList.1 hp)
  generalize Λ.finalityPair σe = fp at *
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · refine ⟨fun (ht : τ = true) => ?_, fun (ht : τ = false) => ?_, fun q hq => ?_⟩
    · simp [recordAtt, ht]
    · rcases htgt ht with h0 | h0 <;> simp [recordAtt, ht, h0]
    · obtain ⟨hp, hlt⟩ := hfin q hq
      obtain rfl : fp = some q := Option.mem_toList.1 hq
      refine ⟨by simp [recordAtt], permits_recordAtt hp (fun he => absurd he hlt.ne') ?_⟩
      intro p hp' _
      obtain rfl : p = q := by simpa using hp'
      rfl
  · obtain ⟨h1, h2, h3⟩ := hΛ x hx
    refine ⟨fun ht => timeout_subset_recordAtt _ _ _ (h1 ht), fun ht => target_recordAtt _ (h2 ht),
      fun q hq => ?_⟩
    obtain ⟨hl, hp⟩ := h3 q hq
    have hpc : ∀ p ∈ fp.toList, p.1 = q.1 → p.2 = q.2 := fun p hp he => by
      have := (hfin p hp).1.2.2
      rw [he, hl] at this
      simpa [eq_comm] using this
    refine ⟨lock_recordAtt hl hpc, permits_recordAtt hp (fun (he : σe.h = q.1) => ?_) hpc⟩
    rw [he, hl] at hlock
    simpa [eq_comm] using hlock

/-- A tracked set of attestations has no slashable pair. -/
private theorem not_slashable_of_tracks {Λ : Record} {atts : List (Att n)} (hΛ : Tracks Λ atts)
    {a b : Att n} (ha : a ∈ atts) (hb : b ∈ atts) : ¬ slashable a b := by
  have he1 : ∀ a ∈ atts, ∀ b ∈ atts, ¬ e1 a b := by
    rintro a ha b hb ⟨p, hp, hbh, hbT⟩
    obtain ⟨-, ⟨ht, hto, -⟩⟩ := (hΛ a ha).2.2 p hp
    rw [← hbh] at ht hto
    cases hτ : b.timeout
    · have := (hΛ b hb).2.1 hτ
      rcases ht with ht | ht <;> rw [ht] at this
      · cases this
      · exact hbT (Option.some.inj this).symm
    · exact hbT (Finset.mem_singleton.1 (hto ((hΛ b hb).1 hτ)))
  rintro ⟨-, h | h | ⟨heq, hta, htb, hne⟩⟩
  · exact he1 a ha b hb h
  · exact he1 b hb a ha h
  · have := (hΛ a ha).2.1 hta
    rw [heq, (hΛ b hb).2.1 htb] at this
    exact hne (Option.some.inj this).symm

/-- A client run keeps the invariant over the attestations it sends. -/
private theorem tracks_run (v : Fin n) : ∀ (ins : List (ChainState n)) (Λ : Record)
    (L : List (Att n)), Tracks Λ L → (∀ σe ∈ ins, σe.hj < σe.h ∧ ∀ p ∈ σe.pending, p.1 < σe.h) →
    Tracks (run v Λ ins).1 ((run v Λ ins).2 ++ L)
  | [], _, _, hΛ, _ => hΛ
  | σe :: rest, Λ, L, hΛ, hin => by
    have hrest := fun σ (h : σ ∈ rest) => hin σ (List.mem_cons_of_mem _ h)
    unfold run
    split
    · exact tracks_run v rest Λ L hΛ hrest
    · rename_i a Λ' hc
      have := tracks_run v rest Λ' (a :: L) (tracks_createAtt hΛ (hin σe List.mem_cons_self) hc)
        hrest
      intro x hx
      exact this x (by simp only [List.cons_append, List.mem_append, List.mem_cons] at hx ⊢; tauto)

end Record

/-- **G0.10.** -/
theorem aggregation (gp : FGParams) : Aggregation gp := by
  intro σe Λ v hb hlock hto htgt hsent
  have hhp : Λ.heightPair σe.h σe.Th = some (σe.h, σe.Th, false) := by
    rcases hlock with h | h <;> simp [Record.heightPair, h, hto, htgt]
  have hany : ¬ ∃ b ∈ Λ.sent, b.1 = σe.h := fun ⟨b, hb, he⟩ => hsent b hb he
  let a : Att gp.n := ⟨v, σe.h, σe.Th, false, Λ.finalityPair σe⟩
  refine ⟨a, Λ.recordAtt a, by simp [Record.createAtt, hhp, hany, a], ?_⟩
  simp [a, Att.content, Record.finalityPair, hb]

/-- **G0.5.** -/
theorem client_safety (gp : FGParams) : ClientSafety gp := by
  intro v ins hin a ha b hb
  have := Record.tracks_run v ins Record.empty [] Record.tracks_empty (fun σe h => (hin σe h).2)
  rw [List.append_nil] at this
  exact Record.not_slashable_of_tracks this ha hb

end Consensus.Goldilocks.FG

end
