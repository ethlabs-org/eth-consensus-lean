module
public import AvailableChainKitFG.ClientOnce
public import AvailableChainKitFG.ClientSafety

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-! Safety of the released rows. The proof uses the actual record writes,
including finality suppression, rather than the old client's output list. -/

/-- Full signed content identifies the signer and both pairs. -/
theorem onceSignedContent_eq_iff {V S L : Type} (seatOf : V ≃ S) (label : L)
    (a b : Row V) :
    a.onceSignedContent seatOf label = b.onceSignedContent seatOf label ↔ a = b := by
  cases a
  cases b
  dsimp only [Row.onceSignedContent, Row.onceKey]
  simp [seatOf.injective.eq_iff]

/-- For one record owner, full-key equality is exactly full signed-content
 equality. The fixed bijection preserves the authentication identity. -/
theorem onceKey_eq_iff_signedContent_eq {V S L : Type} (seatOf : V ≃ S) (label : L)
    {a b : Row V} (owner : a.signer = b.signer) :
    a.onceKey = b.onceKey ↔
      a.onceSignedContent seatOf label = b.onceSignedContent seatOf label := by
  dsimp only [Row.onceSignedContent]
  simp [owner]

/-- A row with the original height pair and a suppressed finality pair
keeps the invariant, extends the record, and is covered by its write. -/
theorem record_row_without_finality {V : Type} {Λ : Record} (hΛ : RecordInv Λ)
    (i : V) (fields : Option (Height × BlockId)) (hd : HeadFields) :
    let a : Row V := ⟨i, height_pair Λ fields (finality_pair Λ hd), none⟩
    RecordInv (record_row Λ a) ∧ RecordExtends Λ (record_row Λ a) ∧
      Covers (record_row Λ a) a := by
  dsimp only
  have hl (g : Height) :
      (record_row Λ (⟨i, height_pair Λ fields (finality_pair Λ hd), none⟩ : Row V)).lock g =
        Λ.lock g := by rw [record_row_lock]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro g X hg
    rw [hl] at hg
    have hc := hΛ g X hg
    have hol := own_lock_eq_of_lock hg hd
    refine ⟨record_row_timeout_false_of_ne _ _ hc.1 ?_,
      record_row_target_compatible_of _ _ hc.2 ?_⟩
    · intro T hp
      exact Bool.noConfusion (height_pair_of_own_lock hc.1 hol hp).1
    · intro T hp
      exact (height_pair_of_own_lock hc.1 hol hp).2
  · exact ⟨fun _ _ ht => record_row_target_mono _ _ ht,
      fun _ ht => record_row_timeout_mono _ _ ht, fun g _ ht => (hl g).trans ht⟩
  · refine ⟨fun _ _ hp => record_row_target_of_vote _ _ hp
        (height_pair_target_compat hΛ hp),
      fun _ _ hp => record_row_timeout_of_vote _ _ hp, ?_⟩
    intro p hp
    cases hp

/-- Keeping or removing the computed finality pair preserves record safety. -/
theorem record_row_optional_finality {V : Type} {Λ : Record} (hΛ : RecordInv Λ)
    (i : V) (fields : Option (Height × BlockId)) (hd : HeadFields) (fp : Option FinalityPair)
    (hf : fp = none ∨ fp = finality_pair Λ hd) :
    let a : Row V := ⟨i, height_pair Λ fields (finality_pair Λ hd), fp⟩
    RecordInv (record_row Λ a) ∧ RecordExtends Λ (record_row Λ a) ∧
      Covers (record_row Λ a) a := by
  rcases hf with rfl | rfl
  · exact record_row_without_finality hΛ i fields hd
  · exact ⟨recordInv_clientRow hΛ i fields hd,
      recordExtends_clientRow Λ i fields hd, covers_clientRow hΛ i fields hd⟩

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- An emitted row has the guarded form, and the returned record is its
write. The finality pair is the filtered current action pair. -/
theorem createRowOnce_released (E : Electorate V) (cfg : FGConfig) (Λ : RecordOnce)
    (i : V) (src : Option (FGBlock V)) (hd : HeadFields) {a : Row V}
    (ha : (createRowOnce E cfg Λ i src hd).1 = some a) :
    ∃ h T timeout,
      height_pair Λ.toRecord
        (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root))
        (finality_pair Λ.toRecord hd) = .vote h T timeout ∧
      a = ⟨i, .vote h T timeout,
        (finality_pair Λ.toRecord hd).filter (fun p => decide (p.height < h))⟩ ∧
      sameHeightOnce Λ h T timeout = false ∧ a.onceKey ∉ Λ.sent ∧
      (createRowOnce E cfg Λ i src hd).2 = record_row_once Λ a := by
  rw [createRowOnce_def] at ha ⊢
  dsimp only at ha ⊢
  generalize hp : height_pair Λ.toRecord
    (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root))
    (finality_pair Λ.toRecord hd) = pair at ha ⊢
  cases pair with
  | empty => cases ha
  | vote h T timeout =>
    dsimp only at ha ⊢
    split at ha
    · cases ha
    · rename_i hs
      split at ha
      · cases ha
      · rename_i hn
        cases ha
        exact ⟨h, T, timeout, rfl, rfl, Bool.eq_false_iff.mpr hs, hn,
          by simp [hs, hn]⟩

/-- No release means no record write, including no provisional lock write. -/
theorem createRowOnce_none (E : Electorate V) (cfg : FGConfig) (Λ : RecordOnce)
    (i : V) (src : Option (FGBlock V)) (hd : HeadFields)
    (ha : (createRowOnce E cfg Λ i src hd).1 = none) :
    (createRowOnce E cfg Λ i src hd).2 = Λ := by
  rw [createRowOnce_def] at ha ⊢
  dsimp only at ha ⊢
  generalize hp : height_pair Λ.toRecord
    (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root))
    (finality_pair Λ.toRecord hd) = pair at ha ⊢
  cases pair with
  | empty => rfl
  | vote h T timeout =>
    dsimp only at ha ⊢
    split <;> simp_all only
    split <;> simp_all only
    cases ha

/-- The actual released write keeps all three record safety facts. -/
theorem createRowOnce_safe (E : Electorate V) (cfg : FGConfig) {Λ : RecordOnce}
    (hΛ : RecordInv Λ.toRecord) (i : V) (src : Option (FGBlock V)) (hd : HeadFields) :
    RecordInv (createRowOnce E cfg Λ i src hd).2.toRecord ∧
    RecordExtends Λ.toRecord (createRowOnce E cfg Λ i src hd).2.toRecord ∧
    ∀ a, (createRowOnce E cfg Λ i src hd).1 = some a →
      Covers (createRowOnce E cfg Λ i src hd).2.toRecord a := by
  cases ha : (createRowOnce E cfg Λ i src hd).1 with
  | none =>
      rw [createRowOnce_none E cfg Λ i src hd ha]
      exact ⟨hΛ, RecordExtends.refl _, by intro a he; cases he⟩
  | some a =>
      obtain ⟨h, T, timeout, hp, rfl, _, _, hw⟩ :=
        createRowOnce_released E cfg Λ i src hd ha
      rw [hw]
      dsimp only [record_row_once]
      rw [← hp]
      have hf : (finality_pair Λ.toRecord hd).filter (fun p => decide (p.height < h)) = none ∨
          (finality_pair Λ.toRecord hd).filter (fun p => decide (p.height < h)) =
            finality_pair Λ.toRecord hd := by
        cases finality_pair Λ.toRecord hd <;> simp [Option.filter]
        simp only [Height]
        omega
      have safe := record_row_optional_finality hΛ i
        (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) hd _ hf
      refine ⟨safe.1, safe.2.1, ?_⟩
      intro b hb
      cases hb
      exact safe.2.2

/-- Every released row has a height pair and finality strictly below it. -/
theorem createRowOnce_valid (E : Electorate V) (cfg : FGConfig) (Λ : RecordOnce)
    (i : V) (src : Option (FGBlock V)) (hd : HeadFields) {a : Row V}
    (ha : (createRowOnce E cfg Λ i src hd).1 = some a) :
    ∃ h T timeout, a.height_pair = .vote h T timeout ∧
      ∀ p, a.finality_pair = some p → p.height < h := by
  obtain ⟨h, T, timeout, _, rfl, _, _, _⟩ := createRowOnce_released E cfg Λ i src hd ha
  refine ⟨h, T, timeout, rfl, ?_⟩
  intro p hp
  exact of_decide_eq_true (Option.filter_eq_some_iff.mp hp).2

/-- The step retains all sent content and records each new release. -/
theorem createRowOnce_sent (E : Electorate V) (cfg : FGConfig) (Λ : RecordOnce)
    (i : V) (src : Option (FGBlock V)) (hd : HeadFields) :
    Λ.sent ⊆ (createRowOnce E cfg Λ i src hd).2.sent ∧
      ∀ a, (createRowOnce E cfg Λ i src hd).1 = some a →
        a.onceKey ∉ Λ.sent ∧
        (createRowOnce E cfg Λ i src hd).2.sent = a.onceKey :: Λ.sent := by
  cases ha : (createRowOnce E cfg Λ i src hd).1 with
  | none =>
      rw [createRowOnce_none E cfg Λ i src hd ha]
      exact ⟨fun _ hm => hm, by intro a he; cases he⟩
  | some a =>
      obtain ⟨_, _, _, _, _, _, hn, hw⟩ := createRowOnce_released E cfg Λ i src hd ha
      rw [hw]
      refine ⟨fun _ hm => List.mem_cons_of_mem _ hm, ?_⟩
      intro b hb
      cases hb
      exact ⟨hn, rfl⟩

/-- Only a timeout for an entry absent at that height can repeat. -/
theorem createRowOnce_sameHeight (E : Electorate V) (cfg : FGConfig) (Λ : RecordOnce)
    (i : V) (src : Option (FGBlock V)) (hd : HeadFields) {a : Row V}
    (ha : (createRowOnce E cfg Λ i src hd).1 = some a)
    {h : Height} {T U : BlockId} {timeout oldTimeout : Bool} {fp : Option FinalityPair}
    (hp : a.height_pair = .vote h T timeout)
    (hm : (NamedHeightPair.vote h U oldTimeout, fp) ∈ Λ.sent) :
    timeout = true ∧ U ≠ T := by
  obtain ⟨g, X, t, _, rfl, hs, _, _⟩ := createRowOnce_released E cfg Λ i src hd ha
  cases hp
  have guard := List.any_eq_false.mp hs _ hm
  change ¬ (decide (h = h) && (!timeout || decide (U = T))) = true at guard
  simpa using guard

/-- The complete run keeps the invariant, extends its starting record, and
covers every released row in its final durable record. -/
theorem clientRunOnce_covers (E : Electorate V) (cfg : FGConfig) (i : V)
    (inputs : List (Option (FGBlock V) × HeadFields)) :
    ∀ Λ, RecordInv Λ.toRecord →
      RecordInv (clientRecordOnce E cfg i Λ inputs).toRecord ∧
      RecordExtends Λ.toRecord (clientRecordOnce E cfg i Λ inputs).toRecord ∧
      ∀ a ∈ clientRunOnce E cfg i Λ inputs,
        Covers (clientRecordOnce E cfg i Λ inputs).toRecord a := by
  induction inputs with
  | nil => exact fun Λ hΛ => ⟨hΛ, RecordExtends.refl _, by dsimp only [clientRunOnce]; simp⟩
  | cons x rest ih =>
      intro Λ hΛ
      obtain ⟨src, hd⟩ := x
      have hs := createRowOnce_safe E cfg hΛ i src hd
      obtain ⟨hi, he, hc⟩ := ih _ hs.1
      refine ⟨hi, hs.2.1.trans he, ?_⟩
      intro a ha
      dsimp only [clientRunOnce] at ha
      cases ho : (createRowOnce E cfg Λ i src hd).1 with
      | none => rw [ho] at ha; exact hc a ha
      | some b =>
          rw [ho] at ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact (hs.2.2 a ho).mono he
          · exact hc a ha

/-- Released rows have no E1 or E2 pair, also when the two rows are equal. -/
theorem clientRunOnce_noSlash (E : Electorate V) (cfg : FGConfig) (i : V)
    (inputs : List (Option (FGBlock V) × HeadFields)) :
    ∀ a ∈ clientRunOnce E cfg i RecordOnce.initial inputs,
      ∀ b ∈ clientRunOnce E cfg i RecordOnce.initial inputs, ¬ Slashable a b := by
  obtain ⟨hi, _, hc⟩ := clientRunOnce_covers E cfg i inputs RecordOnce.initial recordInv_initial
  exact fun a ha b hb => not_slashable_of_covers hi (hc a ha) (hc b hb)

/-- No released key was in the starting record. This applies after restart. -/
theorem clientRunOnce_fresh (E : Electorate V) (cfg : FGConfig) (i : V)
    (inputs : List (Option (FGBlock V) × HeadFields)) :
    ∀ Λ, ∀ a ∈ clientRunOnce E cfg i Λ inputs, a.onceKey ∉ Λ.sent := by
  induction inputs with
  | nil => dsimp only [clientRunOnce]; simp
  | cons x rest ih =>
      intro Λ a ha
      obtain ⟨src, hd⟩ := x
      have hs := createRowOnce_sent E cfg Λ i src hd
      dsimp only [clientRunOnce] at ha
      cases ho : (createRowOnce E cfg Λ i src hd).1 with
      | none =>
          rw [ho] at ha
          exact fun hm => ih _ a ha (hs.1 hm)
      | some b =>
          rw [ho] at ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact (hs.2 a ho).1
          · exact fun hm => ih _ a ha (hs.1 hm)

/-- Full two-pair content is released at most once in every run. -/
theorem clientRunOnce_keys_nodup (E : Electorate V) (cfg : FGConfig) (i : V)
    (inputs : List (Option (FGBlock V) × HeadFields)) :
    ∀ Λ, ((clientRunOnce E cfg i Λ inputs).map Row.onceKey).Nodup := by
  induction inputs with
  | nil => dsimp only [clientRunOnce]; simp
  | cons x rest ih =>
      intro Λ
      obtain ⟨src, hd⟩ := x
      dsimp only [clientRunOnce]
      cases ho : (createRowOnce E cfg Λ i src hd).1 with
      | none => exact ih _
      | some a =>
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih _⟩
          intro hm
          obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
          have hn := clientRunOnce_fresh E cfg i rest _ b hb
          rw [(createRowOnce_sent E cfg Λ i src hd).2 a ho |>.2] at hn
          exact hn (by simp [he])

/-- The final sent history is the old history plus exactly the new releases.
The most recent release is first in the durable list. -/
theorem clientRecordOnce_sent (E : Electorate V) (cfg : FGConfig) (i : V)
    (inputs : List (Option (FGBlock V) × HeadFields)) :
    ∀ Λ, (clientRecordOnce E cfg i Λ inputs).sent =
      ((clientRunOnce E cfg i Λ inputs).map Row.onceKey).reverse ++ Λ.sent := by
  induction inputs with
  | nil => dsimp only [clientRecordOnce, clientRunOnce]; simp
  | cons x rest ih =>
      intro Λ
      obtain ⟨src, hd⟩ := x
      dsimp only [clientRecordOnce, clientRunOnce]
      rw [ih]
      cases ho : (createRowOnce E cfg Λ i src hd).1 with
      | none =>
          rw [createRowOnce_none E cfg Λ i src hd ho]
      | some a =>
          rw [(createRowOnce_sent E cfg Λ i src hd).2 a ho |>.2]
          simp

/-- Splitting the actions at restart preserves the durable final record. -/
theorem clientRecordOnce_append (E : Electorate V) (cfg : FGConfig) (i : V)
    (xs ys : List (Option (FGBlock V) × HeadFields)) (Λ : RecordOnce) :
    clientRecordOnce E cfg i Λ (xs ++ ys) =
      clientRecordOnce E cfg i (clientRecordOnce E cfg i Λ xs) ys := by
  induction xs generalizing Λ with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- Resume with the same record: the combined release list is unchanged. -/
theorem clientRunOnce_append (E : Electorate V) (cfg : FGConfig) (i : V)
    (xs ys : List (Option (FGBlock V) × HeadFields)) (Λ : RecordOnce) :
    clientRunOnce E cfg i Λ (xs ++ ys) = clientRunOnce E cfg i Λ xs ++
      clientRunOnce E cfg i (clientRecordOnce E cfg i Λ xs) ys := by
  induction xs generalizing Λ with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨src, hd⟩ := x
      simp only [List.cons_append]
      dsimp only [clientRunOnce, clientRecordOnce]
      cases ho : (createRowOnce E cfg Λ i src hd).1 <;> simp [ih]

omit [DecidableEq V] [Fintype V] [RowCodec V] in
/-- Record writes depend on both pairs, not on the supplied signer value. -/
theorem record_row_once_signer_irrel (Λ : RecordOnce) (i j : V)
    (hp : NamedHeightPair) (fp : Option FinalityPair) :
    record_row_once Λ (⟨i, hp, fp⟩ : Row V) = record_row_once Λ (⟨j, hp, fp⟩ : Row V) := by
  rfl

/-- The body computation and durable write are independent of the signer
argument. A caller can compute the body with its fixed placeholder seat. -/
theorem createRowOnce_signer_irrel (E : Electorate V) (cfg : FGConfig) (Λ : RecordOnce)
    (i j : V) (src : Option (FGBlock V)) (hd : HeadFields) :
    (createRowOnce E cfg Λ i src hd).1.map Row.onceKey =
      (createRowOnce E cfg Λ j src hd).1.map Row.onceKey ∧
    (createRowOnce E cfg Λ i src hd).2 = (createRowOnce E cfg Λ j src hd).2 := by
  have key (hp : NamedHeightPair) (fp : Option FinalityPair) :
      (⟨j, hp, fp⟩ : Row V).onceKey = (⟨i, hp, fp⟩ : Row V).onceKey := rfl
  simp only [createRowOnce_def]
  generalize hp : height_pair Λ.toRecord
    (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root))
    (finality_pair Λ.toRecord hd) = pair
  cases pair <;> dsimp only
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · rw [key]
      split
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩

/-- The fixed authentication label and seat map give unique full signed
content for all releases. No FGSA adapter is needed for this pure fact. -/
theorem clientRunOnce_signedContent_nodup {S L : Type} (seatOf : V ≃ S) (label : L)
    (E : Electorate V) (cfg : FGConfig) (i : V) (Λ : RecordOnce)
    (inputs : List (Option (FGBlock V) × HeadFields)) :
    ((clientRunOnce E cfg i Λ inputs).map (Row.onceSignedContent seatOf label)).Nodup := by
  apply List.Nodup.of_map (f := Prod.snd)
  simp only [List.map_map, Function.comp_def]
  dsimp only [Row.onceSignedContent]
  exact clientRunOnce_keys_nodup E cfg i inputs Λ

/-- One action keeps the pair-history invariant. -/
theorem recordInv_createRowOnce (E : Electorate V) (cfg : FGConfig) {Λ : RecordOnce}
    (hΛ : RecordInv Λ.toRecord) (i : V) (src : Option (FGBlock V)) (hd : HeadFields) :
    RecordInv (createRowOnce E cfg Λ i src hd).2.toRecord :=
  (createRowOnce_safe E cfg hΛ i src hd).1

/-- One action keeps every previous pair-history entry. -/
theorem recordExtends_createRowOnce (E : Electorate V) (cfg : FGConfig) {Λ : RecordOnce}
    (hΛ : RecordInv Λ.toRecord) (i : V) (src : Option (FGBlock V)) (hd : HeadFields) :
    RecordExtends Λ.toRecord (createRowOnce E cfg Λ i src hd).2.toRecord :=
  (createRowOnce_safe E cfg hΛ i src hd).2.1

/-- Every released row is covered before it leaves the client. -/
theorem covers_createRowOnce (E : Electorate V) (cfg : FGConfig) {Λ : RecordOnce}
    (hΛ : RecordInv Λ.toRecord) (i : V) (src : Option (FGBlock V)) (hd : HeadFields)
    {a : Row V} (ha : (createRowOnce E cfg Λ i src hd).1 = some a) :
    Covers (createRowOnce E cfg Λ i src hd).2.toRecord a :=
  (createRowOnce_safe E cfg hΛ i src hd).2.2 a ha

/-- One released row cannot be E1 or E2 evidence against itself. -/
theorem createRowOnce_noSelfSlash (E : Electorate V) (cfg : FGConfig) {Λ : RecordOnce}
    (hΛ : RecordInv Λ.toRecord) (i : V) (src : Option (FGBlock V)) (hd : HeadFields)
    {a : Row V} (ha : (createRowOnce E cfg Λ i src hd).1 = some a) : ¬ Slashable a a := by
  have hs := createRowOnce_safe E cfg hΛ i src hd
  exact not_slashable_of_covers hs.1 (hs.2.2 a ha) (hs.2.2 a ha)

end AvailableChain.KitFG
end
