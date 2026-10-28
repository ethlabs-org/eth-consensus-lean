module
public import ConsensusModel.System

@[expose] public section

/-! # Engine candidates

What the engine signs for a node: every candidate of node `v` is unsigned, or
signed with `v`'s own key in a role that selects that key. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run
variable (rho : Run F E)

omit [DecidableEq V] in
/-- Every candidate of `v` is unsigned, or signed with `v`'s own key in a role
whose selection contains that key. -/
theorem candidates_auth (st : (protoOf F E).State) (v : V) (t : Time)
    {o : (protoOf F E).Object} (ho : o ∈ rho.candidates st v t) :
    o.auth = .none ∨ ∃ r, o.auth = .signed (rho.ownKey v) r ∧ rho.ownKey v ∈ rho.sel r := by
  unfold candidates at ho
  rcases List.mem_append.mp ho with hs | hg
  · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hs
    cases ha : (protoOf F E).act st d with
    | none => simp [ha] at hd
    | some mc =>
      obtain ⟨m, cs⟩ := mc
      rw [ha] at hd
      dsimp only at hd
      by_cases hk : rho.ownKey v ∈ rho.sel ((protoOf F E).role d)
      · simp only [hk, ↓reduceIte] at hd
        rcases List.mem_singleton.mp hd with rfl
        exact Or.inr ⟨_, rfl, hk⟩
      · simp only [hk, ↓reduceIte] at hd
        cases hd
  · obtain ⟨mc, _, rfl⟩ := List.mem_map.mp hg
    exact Or.inl rfl

omit [DecidableEq V] in
/-- Every engine candidate of `v` is unsigned or signed by `v`'s own key. -/
theorem candidates_signer (st : (protoOf F E).State) (v : V) (t : Time)
    {o : (protoOf F E).Object} (ho : o ∈ rho.candidates st v t) :
    o.signer? = none ∨ o.signer? = some (rho.ownKey v) := by
  rcases rho.candidates_auth st v t ho with h | ⟨r, h, _⟩
  · exact Or.inl (by simp [Obj.signer?, h])
  · exact Or.inr (by simp [Obj.signer?, h])

omit [DecidableEq V] in
/-- Every signed candidate is signed by a key selected for its role. -/
theorem candidates_selected (st : (protoOf F E).State) (v : V) (t : Time)
    {o : (protoOf F E).Object} (ho : o ∈ rho.candidates st v t) {k r}
    (ha : o.auth = .signed k r) : k ∈ rho.sel r := by
  rcases rho.candidates_auth st v t ho with h | ⟨r', h, hk⟩
  · rw [h] at ha; cases ha
  · rw [h] at ha; cases ha; exact hk

omit [DecidableEq V] in
/-- Through the PKI, every signed candidate of `v` is signed by `v`. -/
theorem candidates_signerOf (st : (protoOf F E).State) (v : V) (t : Time)
    {o : (protoOf F E).Object} (ho : o ∈ rho.candidates st v t) :
    rho.signerOf o = none ∨ rho.signerOf o = some v := by
  rcases rho.candidates_auth st v t ho with h | ⟨r, h, _⟩
  · exact Or.inl (by simp [signerOf, Obj.signer?, h])
  · exact Or.inr (by simp [signerOf, Obj.signer?, ownKey, h])

omit [DecidableEq V] in
/-- A signed candidate comes from a due duty of its role, whose message and
carried objects it is. -/
theorem candidates_duty (st : (protoOf F E).State) (v : V) (t : Time)
    {a : Model.Auth (Fintype.card V) (protoOf F E).Role} {m cs}
    (ho : Obj.mk a m cs ∈ rho.candidates st v t) {k r} (ha : a = .signed k r) :
    ∃ d ∈ (protoOf F E).duties t, (protoOf F E).role d = r ∧
      (protoOf F E).act st d = some (m, cs) := by
  subst ha
  unfold candidates at ho
  rcases List.mem_append.mp ho with hs | hg
  · obtain ⟨d, hd, hm⟩ := List.mem_flatMap.mp hs
    cases hact : (protoOf F E).act st d with
    | none => simp [hact] at hm
    | some mc =>
      obtain ⟨m', cs'⟩ := mc
      rw [hact] at hm
      dsimp only at hm
      split at hm
      · rcases List.mem_singleton.mp hm with he
        injection he with h₁ h₂ h₃
        injection h₁ with _ hr
        cases h₂
        cases h₃
        exact ⟨d, hd, hr.symm, hact⟩
      · cases hm
  · obtain ⟨mc, _, he⟩ := List.mem_map.mp hg
    injection he with h₁
    cases h₁

end Run
end Consensus.Model
end
