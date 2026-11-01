module
public import AvailableChainGeneric.Statements.V2.Signatures

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

-- G12: duties fix the time; no duplicate events fixes the tick and its input.
theorem emitted_unique_per_label_statement : EmittedUniquePerLabelStatement := by
  rw [EmittedUniquePerLabelStatement_def]
  intro V _ In P E rho hnodup v ℓ i j₁ j₂ t₁ t₂ o₁ o₂ he₁ he₂ ho₁ ho₂ ha₁ ha₂
  have action : ∀ j t (o : P.Object), rho.events[j]? = some (.tick v t) →
      o ∈ Run.emitsAt E rho j → o.auth = .seat ℓ i →
      t = P.actTime ℓ ∧
        P.act (P.clock (Run.stateBefore E rho j v) t) ℓ (rho.input v t) =
          some o.payload := by
    intro j t o he ho ha
    rw [(Run.step_tick_eq E rho he).2] at ho
    simp only [tick] at ho
    split at ho
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨label, hl, ho⟩ := List.mem_flatMap.mp ho
        obtain ⟨seat, _, ho⟩ := List.mem_filterMap.mp ho
        obtain ⟨payload, hp, heq⟩ := Option.map_eq_some_iff.mp ho
        have hauth := (congrArg Signed.auth heq).trans ha
        have hlabel : label = ℓ := (Auth.seat.inj hauth).1
        subst label
        exact ⟨((P.duties_spec ℓ t).mp hl).symm,
          hp.trans (congrArg some (congrArg Signed.payload heq))⟩
      · obtain ⟨payload, _, heq⟩ := List.mem_map.mp ho
        have hauth := (congrArg Signed.auth heq).trans ha
        cases hauth
    · simp at ho
  obtain ⟨ht₁, hp₁⟩ := action j₁ t₁ o₁ he₁ ho₁ ha₁
  obtain ⟨ht₂, hp₂⟩ := action j₂ t₂ o₂ he₂ ho₂ ha₂
  subst t₁
  subst t₂
  have hj : j₁ = j₂ :=
    (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp he₁).1 hnodup).mp
      (he₁.trans he₂.symm)
  subst j₂
  refine ⟨rfl, ?_⟩
  have hp : o₁.payload = o₂.payload := Option.some.inj (hp₁.symm.trans hp₂)
  cases o₁
  cases o₂
  cases ha₁.trans ha₂.symm
  cases hp
  rfl

-- G12 LINK; binder names agree with the closed Statement.
set_option linter.unusedVariables false in
theorem emitted_unique_per_label :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P) (hnodup : rho.events.Nodup)
    (v : V) (ℓ : P.Label) (i : Fin (P.seats ℓ))
    (j₁ j₂ : Nat) (t₁ t₂ : Time) (o₁ o₂ : P.Object)
    (he₁ : rho.events[j₁]? = some (.tick v t₁))
    (he₂ : rho.events[j₂]? = some (.tick v t₂))
    (ho₁ : o₁ ∈ Run.emitsAt E rho j₁)
    (ho₂ : o₂ ∈ Run.emitsAt E rho j₂)
    (ha₁ : o₁.auth = .seat ℓ i) (ha₂ : o₂.auth = .seat ℓ i),
    j₁ = j₂ ∧ o₁ = o₂ :=
  @emitted_unique_per_label_statement

-- G12: direct and carried signatures both give an emission by the holder.
theorem honest_unique_per_label_statement : HonestUniquePerLabelStatement := by
  rw [HonestUniquePerLabelStatement_def]
  intro V _ In P E rho hnodup hU hhandles ℓ i hh o₁ o₂ ha₁ ha₂ h₁ h₂
  have origin : ∀ o : P.Object, o.auth = .seat ℓ i →
      ((∃ t, Run.emits E rho (rho.seatOf ℓ i) o t) ∨
        ∃ j v t, Run.handlesAt E rho j v o t) →
      ∃ t, Run.emits E rho (rho.seatOf ℓ i) o t := by
    intro o ha ho
    rcases ho with ho | ⟨j, v, t, envelope, he, hc⟩
    · exact ho
    · have hholder : Run.holder rho o.auth = some (rho.seatOf ℓ i) := by
        rw [ha]
        rfl
      rcases hhandles _ _ _ hc with rfl | hc
      · obtain ⟨t', _, hem⟩ := hU.unforgeable v envelope t ⟨j, he⟩ _ hh hholder
        exact ⟨t', hem⟩
      · obtain ⟨t', _, hem⟩ := hU.carried v envelope t ⟨j, he⟩ o hc _ hh hholder
        exact ⟨t', hem⟩
  obtain ⟨t₁, j₁, he₁, ho₁⟩ := origin o₁ ha₁ h₁
  obtain ⟨t₂, j₂, he₂, ho₂⟩ := origin o₂ ha₂ h₂
  exact (emitted_unique_per_label E rho hnodup (rho.seatOf ℓ i) ℓ i
    j₁ j₂ t₁ t₂ o₁ o₂ he₁ he₂ ho₁ ho₂ ha₁ ha₂).2

-- G12 LINK; binder names agree with the closed Statement.
set_option linter.unusedVariables false in
theorem honest_unique_per_label :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P) (hnodup : rho.events.Nodup)
    (hU : UnforgeableSignatures E rho)
    (hhandles : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o')
    (ℓ : P.Label) (i : Fin (P.seats ℓ))
    (hh : rho.seatOf ℓ i ∈ rho.honest) (o₁ o₂ : P.Object)
    (ha₁ : o₁.auth = .seat ℓ i) (ha₂ : o₂.auth = .seat ℓ i)
    (h₁ : (∃ t, Run.emits E rho (rho.seatOf ℓ i) o₁ t) ∨
      ∃ j v t, Run.handlesAt E rho j v o₁ t)
    (h₂ : (∃ t, Run.emits E rho (rho.seatOf ℓ i) o₂ t) ∨
      ∃ j v t, Run.handlesAt E rho j v o₂ t),
    o₁ = o₂ :=
  @honest_unique_per_label_statement

end AvailableChain.Gen.V2
