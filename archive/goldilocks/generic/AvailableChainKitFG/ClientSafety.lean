module
public import AvailableChainSimplexFG.Client
public import AvailableChainSimplexFG.Evidence

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-! # Client record safety

One honest client that starts from `Record.initial` and makes every row with
`createRow` signs no E1 or E2 pair (Astra G01). The proof keeps two facts
about the record: `RecordInv`, and `Covers` (the record holds every row that
the client emitted). The record only grows (`RecordExtends`). -/

-- port: DC/DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Records.lean:86-88
/-- [helper] The record invariant (port: DC `LockCompatible`,
Goldfish/Records.lean:86): a lock rules out a timeout and agrees with an empty
or matching target. -/
def RecordInv (Λ : Record) : Prop :=
  ∀ h T, Λ.lock h = some T → Λ.timeout h = false ∧ (Λ.target h = none ∨ Λ.target h = some T)

-- port: DC/DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Records.lean:91-93
/-- [helper] The initial record has no lock, so it satisfies `RecordInv`. -/
theorem recordInv_initial : RecordInv Record.initial := by
  intro h T hl
  simp [Record.initial] at hl

/-- [helper] The record `Λ'` keeps every entry of `Λ`: a set target, a set
timeout and a set lock stay. -/
def RecordExtends (Λ Λ' : Record) : Prop :=
  (∀ h T, Λ.target h = some T → Λ'.target h = some T) ∧
  (∀ h, Λ.timeout h = true → Λ'.timeout h = true) ∧
  (∀ h T, Λ.lock h = some T → Λ'.lock h = some T)

/-- [helper] Every record extends itself. -/
theorem RecordExtends.refl (Λ : Record) : RecordExtends Λ Λ :=
  ⟨fun _ _ h => h, fun _ h => h, fun _ _ h => h⟩

/-- [helper] Extension is transitive. -/
theorem RecordExtends.trans {Λ₁ Λ₂ Λ₃ : Record} (h₁ : RecordExtends Λ₁ Λ₂)
    (h₂ : RecordExtends Λ₂ Λ₃) : RecordExtends Λ₁ Λ₃ :=
  ⟨fun h T hs => h₂.1 h T (h₁.1 h T hs), fun h hs => h₂.2.1 h (h₁.2.1 h hs),
    fun h T hs => h₂.2.2 h T (h₁.2.2 h T hs)⟩

/-! ## The pair rules -/

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:75-89
-- (finality_pair_record_conditions)
/-- [helper] A nonempty finality pair is `(h_j, J)` of the head fields, and
all three record guards hold at its height. -/
theorem finality_pair_record_conditions {Λ : Record} {hd : HeadFields} {p : FinalityPair}
    (h : finality_pair Λ hd = some p) :
    p = ⟨hd.h_j, hd.J⟩ ∧ Λ.timeout p.height = false ∧
      (Λ.target p.height = none ∨ Λ.target p.height = some p.target) ∧
      (Λ.lock p.height = none ∨ Λ.lock p.height = some p.target) := by
  unfold finality_pair at h
  split at h
  · rename_i hg
    cases h
    exact ⟨rfl, hg.2.2.1, hg.2.1, hg.2.2.2⟩
  · cases h

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/Divergence.lean:40-60
-- (height_pair_target_height)
/-- [helper] Every nonempty height pair names the height and the entry of its
fields, also on the timeout branches. -/
theorem height_pair_vote_fields {Λ : Record} {fields : Option (Height × BlockId)}
    {fp : Option FinalityPair} {h : Height} {T : BlockId} {t : Bool}
    (hp : height_pair Λ fields fp = .vote h T t) : fields = some (h, T) := by
  unfold height_pair at hp
  split at hp
  · cases hp
  · rename_i h_c T_c
    split at hp
    · cases hp; rfl
    · split at hp
      · split at hp
        · cases hp; rfl
        · cases hp
      · split at hp
        · split at hp <;> (cases hp; rfl)
        · cases hp; rfl

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:138-165
-- (height_pair_ne_timeout_of_own_lock, height_pair_target_eq_of_own_lock)
/-- [helper] At a height with no recorded timeout and an effective lock `X`,
`height_pair` emits no timeout, and every target it emits is `X`. -/
theorem height_pair_of_own_lock {Λ : Record} {fields : Option (Height × BlockId)}
    {fp : Option FinalityPair} {h : Height} {X : BlockId} (htimeout : Λ.timeout h = false)
    (hlock : own_lock Λ h fp = some X) {T : BlockId} {t : Bool}
    (hp : height_pair Λ fields fp = .vote h T t) : t = false ∧ T = X := by
  have hf := height_pair_vote_fields hp
  subst hf
  simp only [height_pair, htimeout, Bool.false_eq_true, ↓reduceIte, hlock] at hp
  split at hp
  · rename_i heq
    cases hp
    exact ⟨rfl, heq.symm⟩
  · cases hp

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/RecordCore.lean:45-62
-- (own_lock_compatible)
/-- [helper] The lock that `height_pair` reads has an empty or matching
target record. -/
theorem own_lock_compatible {Λ : Record} (hΛ : RecordInv Λ) {hd : HeadFields} {h : Height}
    {X : BlockId} (hol : own_lock Λ h (finality_pair Λ hd) = some X) :
    Λ.timeout h = false ∧ (Λ.target h = none ∨ Λ.target h = some X) := by
  cases hfp : finality_pair Λ hd with
  | none =>
      rw [hfp] at hol
      exact hΛ h X hol
  | some p =>
      rw [hfp] at hol
      simp only [own_lock] at hol
      split at hol
      · rename_i hph
        cases hol
        have hc := finality_pair_record_conditions hfp
        rw [hph] at hc
        exact ⟨hc.2.1, hc.2.2.1⟩
      · exact hΛ h X hol

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/RecordCore.lean:74-107
-- (height_pair_target_compat)
/-- [helper] A target that `height_pair` emits agrees with an empty or
matching recorded target. -/
theorem height_pair_target_compat {Λ : Record} (hΛ : RecordInv Λ)
    {fields : Option (Height × BlockId)} {hd : HeadFields} {h : Height} {T : BlockId}
    (hp : height_pair Λ fields (finality_pair Λ hd) = .vote h T false) :
    Λ.target h = none ∨ Λ.target h = some T := by
  have hf := height_pair_vote_fields hp
  subst hf
  cases hol : own_lock Λ h (finality_pair Λ hd) with
  | some X =>
      have hc := own_lock_compatible hΛ hol
      have hT := (height_pair_of_own_lock hc.1 hol hp).2
      subst hT
      exact hc.2
  | none =>
      cases hs : Λ.target h with
      | none => exact Or.inl rfl
      | some s =>
          simp only [height_pair, hol, hs] at hp
          split at hp
          · cases hp
          · split at hp
            · rename_i heq
              exact Or.inr (by rw [heq])
            · cases hp

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:280-295
-- (own_lock_eq_of_lock)
/-- [helper] A set lock is the lock that the next `height_pair` reads, also
when the same row emits a finality pair. -/
theorem own_lock_eq_of_lock {Λ : Record} {h : Height} {T : BlockId}
    (hlock : Λ.lock h = some T) (hd : HeadFields) :
    own_lock Λ h (finality_pair Λ hd) = some T := by
  cases hfp : finality_pair Λ hd with
  | none => simpa [own_lock] using hlock
  | some p =>
      by_cases hph : p.height = h
      · have hguard := (finality_pair_record_conditions hfp).2.2.2
        rw [hph, hlock] at hguard
        rcases hguard with hnone | hsame
        · cases hnone
        · simp [own_lock, hph, Option.some_inj.mp hsame]
      · simp [own_lock, hph, hlock]

/-! ## The record writer -/

section RecordRow

variable {V : Type}

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:93-133
-- (record_attestation_lock_eq, record_attestation_lock_eq_own_lock)
/-- [helper] The lock that `record_row` stores is the lock that the same
row's `height_pair` reads. -/
theorem record_row_lock (Λ : Record) (a : Row V) (g : Height) :
    (record_row Λ a).lock g = own_lock Λ g a.finality_pair := by
  rcases a with ⟨s, hp, fp⟩
  cases fp with
  | none =>
      cases hp with
      | empty => rfl
      | vote h T t => cases t <;> simp only [record_row, own_lock] <;> (try split) <;> rfl
  | some p =>
      have key : (Λ.with_lock p.height p.target).lock g = own_lock Λ g (some p) := by
        by_cases hpg : p.height = g
        · subst hpg; simp [own_lock, Record.with_lock]
        · simp [own_lock, Record.with_lock, hpg, Ne.symm hpg]
      rw [← key]
      cases hp with
      | empty => rfl
      | vote h T t => cases t <;> simp only [record_row] <;> (try split) <;> rfl

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:27-56
-- (record_attestation_target_mono)
/-- [helper] `record_row` keeps a set target. -/
theorem record_row_target_mono (Λ : Record) (a : Row V) {h : Height} {T : BlockId}
    (hs : Λ.target h = some T) : (record_row Λ a).target h = some T := by
  rcases a with ⟨s, hp, fp⟩
  cases hp with
  | empty => cases fp <;> simpa [record_row, Record.with_lock] using hs
  | vote g X t =>
      cases t with
      | true => cases fp <;> simpa [record_row, Record.with_lock, Record.with_timeout] using hs
      | false =>
          by_cases hgh : h = g
          · subst hgh
            cases fp <;> simp [record_row, Record.with_lock, hs]
          · cases fp <;> simp only [record_row] <;> split <;>
              simpa [Record.with_lock, Record.with_target, hgh] using hs

/-- [helper] `record_row` keeps a set timeout. -/
theorem record_row_timeout_mono (Λ : Record) (a : Row V) {h : Height}
    (hs : Λ.timeout h = true) : (record_row Λ a).timeout h = true := by
  rcases a with ⟨s, hp, fp⟩
  cases hp with
  | empty => cases fp <;> simpa [record_row, Record.with_lock] using hs
  | vote g X t =>
      cases t with
      | true => cases fp <;> simp [record_row, Record.with_lock, Record.with_timeout, hs]
      | false =>
          cases fp <;> simp only [record_row] <;> split <;>
            simpa [Record.with_lock, Record.with_target] using hs

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/RecordCore.lean:28-34
-- (record_attestation_target_recorded)
/-- [helper] A released target is recorded, when the height was empty or held
the same target. -/
theorem record_row_target_of_vote (Λ : Record) (a : Row V) {h : Height} {T : BlockId}
    (hhp : a.height_pair = .vote h T false) (hpre : Λ.target h = none ∨ Λ.target h = some T) :
    (record_row Λ a).target h = some T := by
  rcases a with ⟨s, hp, fp⟩
  cases hhp
  rcases hpre with hpre | hpre <;> cases fp <;>
    simp_all [record_row, Record.with_lock, Record.with_target]

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/SlashableBound.lean:194-198
-- (record_attestation_timeout_true)
/-- [helper] Recording a timeout sets the timeout bit. -/
theorem record_row_timeout_of_vote (Λ : Record) (a : Row V) {h : Height} {T : BlockId}
    (hhp : a.height_pair = .vote h T true) : (record_row Λ a).timeout h = true := by
  rcases a with ⟨s, hp, fp⟩
  cases hhp
  cases fp <;> simp [record_row, Record.with_lock, Record.with_timeout]

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:206-227
-- (record_attestation_timeout_false_of_ne)
/-- [helper] `record_row` keeps a clear timeout bit unless the row is a
timeout at that height. -/
theorem record_row_timeout_false_of_ne (Λ : Record) (a : Row V) {h : Height}
    (hpre : Λ.timeout h = false) (hne : ∀ T, a.height_pair ≠ .vote h T true) :
    (record_row Λ a).timeout h = false := by
  rcases a with ⟨s, hp, fp⟩
  cases hp with
  | empty => cases fp <;> simpa [record_row, Record.with_lock] using hpre
  | vote g X t =>
      cases t with
      | true =>
          have hgh : h ≠ g := fun heq => hne X (by subst heq; rfl)
          cases fp <;> simpa [record_row, Record.with_lock, Record.with_timeout, hgh] using hpre
      | false =>
          cases fp <;> simp only [record_row] <;> split <;>
            simpa [Record.with_lock, Record.with_target] using hpre

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:170-201
-- (record_attestation_target_compatible_of)
/-- [helper] `record_row` keeps an empty or matching target at `h` when every
target of the row at `h` is `T`. -/
theorem record_row_target_compatible_of (Λ : Record) (a : Row V) {h : Height} {T : BlockId}
    (hpre : Λ.target h = none ∨ Λ.target h = some T)
    (hrow : ∀ U, a.height_pair = .vote h U false → U = T) :
    (record_row Λ a).target h = none ∨ (record_row Λ a).target h = some T := by
  rcases hpre with hnone | hsome
  · rcases a with ⟨s, hp, fp⟩
    cases hp with
    | empty => cases fp <;> exact Or.inl (by simpa [record_row, Record.with_lock] using hnone)
    | vote g U t =>
        cases t with
        | true =>
            cases fp <;> exact Or.inl (by
              simpa [record_row, Record.with_lock, Record.with_timeout] using hnone)
        | false =>
            by_cases hgh : g = h
            · subst hgh
              have hUT : U = T := hrow U rfl
              subst hUT
              exact Or.inr (record_row_target_of_vote Λ _ rfl (Or.inl hnone))
            · have hhg : h ≠ g := Ne.symm hgh
              cases fp <;> exact Or.inl (by
                simp only [record_row]
                split <;> simpa [Record.with_lock, Record.with_target, hhg] using hnone)
  · exact Or.inr (record_row_target_mono Λ a hsome)

end RecordRow

/-! ## One client step -/

section Step

variable {V : Type}

/-- [helper] The row that the client makes from the height fields `fields`
and the head fields `hd` (the body of `createRow`). -/
def clientRow (Λ : Record) (i : V) (fields : Option (Height × BlockId)) (hd : HeadFields) :
    Row V :=
  ⟨i, height_pair Λ fields (finality_pair Λ hd), finality_pair Λ hd⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:231-274
-- (lockCompatible_create_attestation)
/-- [helper] One client step keeps `RecordInv`. -/
theorem recordInv_clientRow {Λ : Record} (hΛ : RecordInv Λ) (i : V)
    (fields : Option (Height × BlockId)) (hd : HeadFields) :
    RecordInv (record_row Λ (clientRow Λ i fields hd)) := by
  intro g X hlock
  rw [record_row_lock] at hlock
  have hpre := own_lock_compatible hΛ hlock
  refine ⟨?_, ?_⟩
  · apply record_row_timeout_false_of_ne _ _ hpre.1
    intro T hp
    exact Bool.noConfusion (height_pair_of_own_lock hpre.1 hlock hp).1
  · apply record_row_target_compatible_of _ _ hpre.2
    intro U hp
    exact (height_pair_of_own_lock hpre.1 hlock hp).2

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:300-309
-- (create_attestation_lock_mono)
/-- [helper] One client step keeps every entry of the record. -/
theorem recordExtends_clientRow (Λ : Record) (i : V) (fields : Option (Height × BlockId))
    (hd : HeadFields) : RecordExtends Λ (record_row Λ (clientRow Λ i fields hd)) := by
  refine ⟨fun h T hs => record_row_target_mono Λ _ hs,
    fun h hs => record_row_timeout_mono Λ _ hs, fun h T hs => ?_⟩
  rw [record_row_lock]
  exact own_lock_eq_of_lock hs hd

/-- [helper] The record `Λ` covers the row `a`: it holds each target, timeout
and finality pair of `a`. -/
def Covers (Λ : Record) (a : Row V) : Prop :=
  (∀ h T, a.height_pair = .vote h T false → Λ.target h = some T) ∧
  (∀ h T, a.height_pair = .vote h T true → Λ.timeout h = true) ∧
  (∀ p, a.finality_pair = some p → Λ.lock p.height = some p.target)

/-- [helper] A larger record covers the same rows. -/
theorem Covers.mono {Λ Λ' : Record} {a : Row V} (hc : Covers Λ a) (he : RecordExtends Λ Λ') :
    Covers Λ' a :=
  ⟨fun h T hp => he.1 h T (hc.1 h T hp), fun h T hp => he.2.1 h (hc.2.1 h T hp),
    fun p hp => he.2.2 _ _ (hc.2.2 p hp)⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/RecordCore.lean:118-126
-- (create_attestation_saves) and SlashableBound.lean:149-166
-- (create_attestation_finalitySafeAt)
/-- [helper] "Record, then release": the record after one step covers the
row of the step. -/
theorem covers_clientRow {Λ : Record} (hΛ : RecordInv Λ) (i : V)
    (fields : Option (Height × BlockId)) (hd : HeadFields) :
    Covers (record_row Λ (clientRow Λ i fields hd)) (clientRow Λ i fields hd) := by
  refine ⟨fun h T hp => ?_, fun h T hp => record_row_timeout_of_vote Λ _ hp, fun p hp => ?_⟩
  · exact record_row_target_of_vote Λ _ hp (height_pair_target_compat hΛ hp)
  · rw [record_row_lock, hp]
    simp [own_lock]

end Step

/-! ## No slashable pair -/

section NoSlash

variable {V : Type} [DecidableEq V]

/-- [helper] Under `RecordInv`, two rows of one signer that the record covers
form no E1 or E2 pair. This is also the case `a = b`. -/
theorem not_slashable_of_covers {Λ : Record} (hΛ : RecordInv Λ) {a b : Row V}
    (ha : Covers Λ a) (hb : Covers Λ b) : ¬ Slashable a b := by
  have e1 : ∀ x y : Row V, Covers Λ x → Covers Λ y →
      x.finality_pair.elim false (conflictsWithFinality y.height_pair) = true → False := by
    intro x y hx hy hc
    cases hfp : x.finality_pair with
    | none => simp [hfp] at hc
    | some p =>
        rw [hfp] at hc
        have hinv := hΛ _ _ (hx.2.2 p hfp)
        cases hyp : y.height_pair with
        | empty => simp [hyp, conflictsWithFinality] at hc
        | vote g T t =>
            cases t with
            | true =>
                have hg : g = p.height := by
                  simpa [hyp, conflictsWithFinality] using hc
                have ht := hy.2.1 g T hyp
                rw [hg, hinv.1] at ht
                cases ht
            | false =>
                have hg : g = p.height ∧ ¬ T = p.target := by
                  simpa [hyp, conflictsWithFinality] using hc
                have ht := hy.1 g T hyp
                rw [hg.1] at ht
                rcases hinv.2 with hn | hs
                · rw [hn] at ht; cases ht
                · rw [hs] at ht; exact hg.2 (Option.some_inj.mp ht).symm
  intro hs
  simp only [Slashable, slashable, Bool.or_eq_true, e1Slashable, e2Slashable,
    Bool.and_eq_true, e1Fields] at hs
  rcases hs with ⟨-, h1 | h1⟩ | ⟨-, h2⟩
  · exact e1 a b ha hb h1
  · exact e1 b a hb ha h1
  · unfold e2Fields at h2
    split at h2
    · rename_i lh lT rh rT hl hr
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not] at h2
      have t1 := ha.1 _ _ hl
      have t2 := hb.1 _ _ hr
      rw [h2.1, t2] at t1
      exact h2.2 (Option.some_inj.mp t1).symm
    · cases h2

end NoSlash

/-! ## The pinned statements -/

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- [helper] `createRow` is one client step on the source fields. -/
theorem createRow_eq (E : Electorate V) (cfg : FGConfig) (Λ : Record) (i : V)
    (src : Option (FGBlock V)) (hd : HeadFields) :
    createRow E cfg Λ i src hd =
      (clientRow Λ i (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) hd,
        record_row Λ
          (clientRow Λ i (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) hd)) :=
  rfl

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/FinalityPairCore.lean:231-274
-- (lockCompatible_create_attestation)
/-- [helper] `createRow` keeps the invariant (port: DC
`lockCompatible_create_attestation`, FinalityPairCore.lean:231). -/
theorem recordInv_createRow (E : Electorate V) (cfg : FGConfig) {Λ : Record} (hΛ : RecordInv Λ)
    (i : V) (src : Option (FGBlock V)) (hd : HeadFields) :
    RecordInv (createRow E cfg Λ i src hd).2 := by
  rw [createRow_eq]
  exact recordInv_clientRow hΛ i _ hd

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/Divergence.lean:70-102
-- (height_pair_no_self_E1, create_attestation_no_self_E1) and SlashableBound.lean:36-77
-- (create_attestation_no_self_timeout)
/-- [helper] One row never forms E1 evidence against itself (port: DC
`create_attestation_no_self_E1`, Divergence.lean:92). -/
theorem createRow_noSelfSlash (E : Electorate V) (cfg : FGConfig) (Λ : Record) (hΛ : RecordInv Λ)
    (i : V) (src : Option (FGBlock V)) (hd : HeadFields) :
    ¬ Slashable (createRow E cfg Λ i src hd).1 (createRow E cfg Λ i src hd).1 := by
  rw [createRow_eq]
  have hc := covers_clientRow hΛ i
    (src.map fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) hd
  exact not_slashable_of_covers (recordInv_clientRow hΛ i _ hd) hc hc

/-- [helper] The run invariant: from a record with `RecordInv`, a client run
ends in a record that extends it, keeps `RecordInv`, and covers every emitted
row. -/
theorem clientRun_covers (E : Electorate V) (cfg : FGConfig) (i : V)
    (inputs : List (Option (FGBlock V) × HeadFields)) :
    ∀ Λ, RecordInv Λ → ∃ Λf, RecordInv Λf ∧ RecordExtends Λ Λf ∧
      ∀ a ∈ clientRun E cfg i Λ inputs, Covers Λf a := by
  induction inputs with
  | nil => exact fun Λ hΛ => ⟨Λ, hΛ, RecordExtends.refl Λ, by simp [clientRun]⟩
  | cons x rest ih =>
      intro Λ hΛ
      obtain ⟨src, hd⟩ := x
      have h1 := recordInv_createRow E cfg hΛ i src hd
      obtain ⟨Λf, hf, hext, hcov⟩ := ih _ h1
      have hstep : RecordExtends Λ (createRow E cfg Λ i src hd).2 := by
        rw [createRow_eq]; exact recordExtends_clientRow Λ i _ hd
      refine ⟨Λf, hf, hstep.trans hext, ?_⟩
      intro a ha
      simp only [clientRun, List.mem_cons] at ha
      rcases ha with rfl | ha
      · have hc : Covers (createRow E cfg Λ i src hd).2 (createRow E cfg Λ i src hd).1 := by
          rw [createRow_eq]; exact covers_clientRow hΛ i _ hd
        exact hc.mono hext
      · exact hcov a ha

/-- [helper] Client record safety (Astra G01): the rows of one honest client
run from the initial record contain no E1 or E2 pair, for ANY sources and head
fields. -/
theorem clientRun_noSlash (E : Electorate V) (cfg : FGConfig) (i : V)
    (inputs : List (Option (FGBlock V) × HeadFields)) :
    ∀ a ∈ clientRun E cfg i Record.initial inputs,
      ∀ b ∈ clientRun E cfg i Record.initial inputs, ¬ Slashable a b := by
  obtain ⟨Λf, hf, -, hcov⟩ := clientRun_covers E cfg i inputs _ recordInv_initial
  exact fun a ha b hb => not_slashable_of_covers hf (hcov a ha) (hcov b hb)

end AvailableChain.KitFG
end
