module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.RecordsCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups

/-! # Erasing the validator client's sent history

The previous rule is expressed here only to compare input/output traces. Its record consists
of the three retained fields and the list of sent contents. -/

namespace Consensus.Goldilocks.FG.Record

public section

/-- A timeout at a height follows a target and names a different entry. -/
def TimeoutAfterTarget (Λ : Record) : Prop :=
  ∀ h, Λ.timeout h ≠ ∅ → ∃ T, Λ.target h = some T ∧ T ∉ Λ.timeout h

theorem timeoutAfterTarget_iff {Λ : Record} : TimeoutAfterTarget Λ ↔
    ∀ h, Λ.timeout h ≠ ∅ → ∃ T, Λ.target h = some T ∧ T ∉ Λ.timeout h := by rfl

theorem timeoutAfterTarget_empty : TimeoutAfterTarget empty :=
  timeoutAfterTarget_iff.2 (by simp [empty])

theorem timeoutAfterTarget_createAtt {n : Nat} {Λ Λ' : Record} {v : Fin n} {σ : ChainState n}
    {a : Att n} (hinv : Λ.TimeoutAfterTarget) (ha : Λ.createAtt v σ = some (a, Λ')) :
    Λ'.TimeoutAfterTarget := by
  obtain ⟨-, rfl, -, -, -, -, hne, -, ht⟩ := createAtt_some ha
  apply timeoutAfterTarget_iff.2
  intro h
  by_cases hh : h = a.h
  · subst h
    cases hτ : a.timeout
    · have hnone := ht.mp hτ
      have he : Λ.timeout a.h = ∅ := by
        by_contra h
        obtain ⟨T, hT, -⟩ := timeoutAfterTarget_iff.1 hinv _ h
        simp [hnone] at hT
      simp [recordAtt, hτ, he]
    · have hn : Λ.target a.h ≠ none := by
        intro h
        simp [hτ] at ht
        exact ht h
      obtain ⟨T, hT⟩ := Option.ne_none_iff_exists'.1 hn
      have hTa : T ≠ a.T := fun e => hne (e ▸ hT)
      have hm : T ∉ Λ.timeout a.h := by
        intro h
        obtain ⟨R, hR, hnR⟩ := timeoutAfterTarget_iff.1 hinv _ (Finset.ne_empty_of_mem h)
        exact hnR (Option.some.inj (hT.symm.trans hR) ▸ h)
      simp [recordAtt, hτ, hT, hTa, hm]
  · simpa only [recordAtt, ite_apply, Function.update_of_ne hh, ite_self] using
      timeoutAfterTarget_iff.1 hinv h

end

end Consensus.Goldilocks.FG.Record

namespace Consensus.Goldilocks.FG.LegacyClient

public section

/-- The old finality permission, before replacing the subset test with emptiness. -/
def permits (Λ : Record) (j T : Nat) : Prop :=
  (Λ.target j = none ∨ Λ.target j = some T) ∧ Λ.timeout j ⊆ {T} ∧
    (Λ.lock j = none ∨ Λ.lock j = some T)

instance (Λ : Record) (j T : Nat) : Decidable (permits Λ j T) :=
  inferInstanceAs (Decidable ((Λ.target j = none ∨ Λ.target j = some T) ∧
    Λ.timeout j ⊆ {T} ∧ (Λ.lock j = none ∨ Λ.lock j = some T)))

private def finalityPair {n : Nat} (Λ : Record) (σ : ChainState n) : Option (Nat × Nat) :=
  if σ.previousHeightJustified then
    if permits Λ σ.hj σ.J then some (σ.hj, σ.J) else none
  else
    (σ.pending.filter (fun p => decide (permits Λ p.1 p.2))).foldl (fun acc p =>
      match acc with
      | none => some p
      | some r => if r.1 < p.1 then some p else some r) none

private def heightPair (Λ : Record) (h T : Nat) : Option (Nat × Nat × Bool) :=
  if Λ.lock h ≠ none ∧ Λ.lock h ≠ some T then none
  else if Λ.timeout h ≠ ∅ then some (h, T, true)
  else if Λ.target h = none ∨ Λ.target h = some T then some (h, T, false)
  else some (h, T, true)

/-- The previous signing rule, including its scan and append of sent contents. -/
def createAtt {n : Nat} (Λ : Record) (sent : List Content) (v : Fin n) (σ : ChainState n) :
    Option (Att n × (Record × List Content)) :=
  match heightPair Λ σ.h σ.Th with
  | none => none
  | some (h, T, τ) =>
    if sent.any (fun b => b.1 = h ∧ (!τ ∨ b.2.1 = T)) then none
    else
      let a : Att n := ⟨v, h, T, τ, finalityPair Λ σ⟩
      some (a, (Λ.recordAtt a, sent ++ [a.content]))

/-- Certificates for an old record reached from the empty record. -/
inductive Reachable : Record → List Content → Prop where
  | empty : Reachable Record.empty []
  | sign {n : Nat} {Λ Λ' : Record} {sent sent' : List Content} {v : Fin n}
      {σ : ChainState n} {a : Att n} : Reachable Λ sent →
      createAtt Λ sent v σ = some (a, (Λ', sent')) → Reachable Λ' sent'

private theorem permits_iff {Λ : Record} (hi : Λ.TimeoutAfterTarget) (j T : Nat) :
    permits Λ j T ↔ Λ.permits j T := by
  constructor
  · rintro ⟨ht, hs, hl⟩
    refine ⟨ht, ?_, hl⟩
    by_contra hn
    obtain ⟨R, hR, hm⟩ := Record.timeoutAfterTarget_iff.1 hi j hn
    rcases ht with ht | ht
    · simp [ht] at hR
    · obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.2 hn
      have he := Finset.mem_singleton.1 (hs hr)
      exact hm (Option.some.inj (ht.symm.trans hR) ▸ he ▸ hr)
  · rintro ⟨ht, he, hl⟩
    exact ⟨ht, he ▸ Finset.empty_subset _, hl⟩

private theorem finalityPair_eq {n : Nat} {Λ : Record} (hi : Λ.TimeoutAfterTarget)
    (σ : ChainState n) : finalityPair Λ σ = Λ.finalityPair σ := by
  unfold finalityPair Record.finalityPair
  simp only [permits_iff hi]
  rfl

private def Tracks (Λ : Record) (sent : List Content) : Prop :=
  ∀ h T, (∃ b ∈ sent, b.1 = h ∧ b.2.1 = T) ↔ Λ.target h = some T ∨ T ∈ Λ.timeout h

private theorem step_eq {n : Nat} {Λ : Record} {sent : List Content}
    (hi : Λ.TimeoutAfterTarget) (hs : Tracks Λ sent) (v : Fin n) (σ : ChainState n) :
    createAtt Λ sent v σ = (Λ.createAtt v σ).map (fun (a, Λ') =>
      (a, (Λ', sent ++ [a.content]))) := by
  let h := σ.h
  let T := σ.Th
  have hd : sent.any (fun b => b.1 = h ∧ (!true ∨ b.2.1 = T)) =
      decide (Λ.target h = some T ∨ T ∈ Λ.timeout h) := by
    apply Bool.eq_iff_iff.2
    simpa only [List.any_eq_true, decide_eq_true_eq, Bool.not_true, Bool.false_eq_true,
      false_or] using hs h T
  have hfresh : Λ.target h = none → Λ.timeout h = ∅ := by
    intro ht
    by_contra hn
    obtain ⟨R, hR, -⟩ := Record.timeoutAfterTarget_iff.1 hi h hn
    simp [ht] at hR
  have hfree (ht : Λ.target h = none) : sent.any (fun b => b.1 = h ∧
      (!false ∨ b.2.1 = T)) = false := by
    apply List.any_eq_false.2
    intro b hb
    have hn : b.1 ≠ h := fun he => by
      have hm := (hs h b.2.1).1 ⟨b, hb, he, rfl⟩
      simp [ht, hfresh ht] at hm
    simp [hn]
  have hrepeat (ht : Λ.target h = some T) : sent.any (fun b => b.1 = h ∧
      (!false ∨ b.2.1 = T)) = true := by
    obtain ⟨b, hb, he, _⟩ := (hs h T).2 (Or.inl ht)
    exact List.any_eq_true.2 ⟨b, hb, by simp [he]⟩
  unfold createAtt heightPair Record.createAtt Record.heightPair
  simp only [h, T] at hd hfresh hfree hrepeat
  by_cases hl : Λ.lock σ.h ≠ none ∧ Λ.lock σ.h ≠ some σ.Th
  · simp [hl]
  by_cases he : Λ.timeout σ.h = ∅
  · have hn : ¬ Λ.timeout σ.h ≠ ∅ := not_not_intro he
    by_cases ht : Λ.target σ.h = none
    · simp only [hl, ite_eq_right hn, ht, ↓reduceIte, true_or, reduceCtorEq]
      simp only [he, Finset.notMem_empty, or_self]
      rw [hfree ht, finalityPair_eq hi]
      rfl
    · by_cases hT : Λ.target σ.h = some σ.Th
      · simp only [hl, ite_eq_right hn, hT, ↓reduceIte, or_true, true_or]
        rw [hrepeat hT]
        rfl
      · simp only [hl, ite_eq_right hn, ht, hT, ↓reduceIte, false_or]
        rw [hd]
        simp [he, hT, finalityPair_eq hi]
  · have ht : Λ.target σ.h ≠ none := fun ht => he (hfresh ht)
    simp only [hl, ite_eq_left he, ht, ↓reduceIte]
    rw [hd]
    simp only [decide_eq_true_eq, finalityPair_eq hi]
    split_ifs <;> rfl

private theorem reachable_invariants {Λ : Record} {sent : List Content} (hr : Reachable Λ sent) :
    Λ.TimeoutAfterTarget ∧ Tracks Λ sent := by
  induction hr with
  | empty => exact ⟨Record.timeoutAfterTarget_empty, fun h T => by simp [Record.empty]⟩
  | @sign n Λ Λ' sent sent' v σ a _ ha ih =>
    rw [step_eq ih.1 ih.2] at ha
    rcases hc : Λ.createAtt v σ with _ | ⟨a₀, Λ₀⟩ <;> rw [hc] at ha
    · cases ha
    cases ha
    refine ⟨Record.timeoutAfterTarget_createAtt ih.1 hc, ?_⟩
    obtain ⟨-, rfl, -, -, -, -, -, -, ht⟩ := Record.createAtt_some hc
    intro h T
    rw [Record.recordAtt_entry_iff ht.mp, ← ih.2]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨b, hb | rfl, hh, hT⟩
      · exact Or.inl ⟨b, hb, hh, hT⟩
      · exact Or.inr ⟨hh, hT⟩
    · rintro (⟨b, hb, hh, hT⟩ | ⟨hh, hT⟩)
      · exact ⟨b, Or.inl hb, hh, hT⟩
      · exact ⟨_, Or.inr rfl, hh, hT⟩

/-- The old freshness premise means exactly an empty target and timeout entry on a reachable
record. -/
theorem fresh_target_iff {Λ : Record} {sent : List Content} (hr : Reachable Λ sent) (h : Nat) :
    (∀ b ∈ sent, b.1 ≠ h) ↔ Λ.target h = none ∧ Λ.timeout h = ∅ := by
  have hs := (reachable_invariants hr).2
  constructor
  · intro hf
    have hn (T : Nat) : ¬ (Λ.target h = some T ∨ T ∈ Λ.timeout h) := by
      intro hm
      obtain ⟨b, hb, he, _⟩ := (hs h T).2 hm
      exact hf b hb he
    refine ⟨?_, Finset.eq_empty_iff_forall_notMem.2 fun T hm => hn T (Or.inr hm)⟩
    cases ht : Λ.target h with
    | none => rfl
    | some T => exact (hn T (Or.inl ht)).elim
  · rintro ⟨ht, he⟩ b hb hh
    have hm := (hs h b.2.1).1 ⟨b, hb, hh, rfl⟩
    simp [ht, he] at hm

/-- Both implementations abstain on the same inputs at every reachable old record. -/
theorem createAtt_none_iff {n : Nat} {Λ : Record} {sent : List Content}
    (hr : Reachable Λ sent) (v : Fin n) (σ : ChainState n) :
    createAtt Λ sent v σ = none ↔ Λ.createAtt v σ = none := by
  obtain ⟨hi, hs⟩ := reachable_invariants hr
  rw [step_eq hi hs]
  cases Λ.createAtt v σ <;> simp

/-- In both directions, a signing emits the very same attestation and next retained record.
The only extra output from the old rule is its appended history. -/
theorem createAtt_some_iff {n : Nat} {Λ Λ' : Record} {sent sent' : List Content}
    (hr : Reachable Λ sent) (v : Fin n) (σ : ChainState n) (a : Att n) :
    createAtt Λ sent v σ = some (a, (Λ', sent')) ↔
      Λ.createAtt v σ = some (a, Λ') ∧ sent' = sent ++ [a.content] := by
  obtain ⟨hi, hs⟩ := reachable_invariants hr
  rw [step_eq hi hs]
  rcases Λ.createAtt v σ with _ | ⟨b, M⟩
  · simp
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, h⟩
      exact ⟨⟨rfl, rfl⟩, h.symm⟩
    · rintro ⟨⟨rfl, rfl⟩, h⟩
      exact ⟨rfl, rfl, h.symm⟩

/-- On any list of inputs, the old and compact clients emit identical traces, including
abstentions, and have the same final retained record. -/
theorem trace_eq {n : Nat} {Λ : Record} {sent : List Content} (hr : Reachable Λ sent)
    (v : Fin n) (inputs : List (ChainState n)) (out : List (Option (Att n)) := []) :
    let run (R : Type) (step : R → ChainState n → Option (Att n × R)) :=
      fun (r : R) => inputs.foldl (fun (s, out) σ => match step s σ with
        | none => (s, out ++ [none]) | some (a, s') => (s', out ++ [some a]))
        (r, out)
    let old := run _ (fun (r, log) σ => createAtt r log v σ) (Λ, sent)
    ((old.1).1, old.2) = run _ (fun r σ => r.createAtt v σ) Λ := by
  dsimp only
  induction inputs generalizing Λ sent out with
  | nil => rfl
  | cons σ rest ih =>
    simp only [List.foldl_cons]
    rcases hc : Λ.createAtt v σ with _ | ⟨a, Λ'⟩
    · rw [(createAtt_none_iff hr v σ).2 hc]
      exact ih hr _
    · have ha := (createAtt_some_iff (sent' := sent ++ [a.content]) hr v σ a).2 ⟨hc, rfl⟩
      rw [ha]
      exact ih (hr.sign ha) _

end

end Consensus.Goldilocks.FG.LegacyClient

namespace Consensus.Goldilocks.Healing

public section

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {proposer : Nat → Fin P.n} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
  {tr : RunTrace A} {ini : Fin P.n → A.State} {y : Fin P.n}

/-- The compact client record at every honest cut is the projection of a reachable old record. -/
theorem client_record_legacy_reachable (hrun : LocalRun proposer dg H sg tr ini) (hy : y ∈ H) :
    ∀ i, ∃ sent, FG.LegacyClient.Reachable (tr.state y i).record sent
  | 0 => by
    rw [Trace.state, hrun.init y hy]
    exact ⟨[], FG.LegacyClient.Reachable.empty⟩
  | i + 1 => by
    obtain ⟨sent, hr⟩ := client_record_legacy_reachable hrun hy i
    rcases record_step_from hrun hy i with he | ⟨a, ⟨src, hc⟩, _⟩
    · exact ⟨sent, he ▸ hr⟩
    · have hs := (hrun.cutLaw y hy i _ hc).1
      rw [← tr.state_succ_of_call hc] at hs
      change (tr.state y i).record.createAtt y ((tr.state y i).fg.σ
        ((tr.state y i).fg.σ src.root).Th) = some (a, (tr.state y (i + 1)).record) at hs
      exact ⟨sent ++ [a.content], hr.sign ((FG.LegacyClient.createAtt_some_iff hr y _ a).2
        ⟨hs, rfl⟩)⟩

end

end Consensus.Goldilocks.Healing
