module
public import AvailableChainPCSA.Model.Objects
public import Mathlib.Data.List.Basic

public section

/-! [PC-SA M1; review minor 8] The digest embedding `DigestInput.toFGSA` is
injective, so `digestOf p` is injective whenever `p.digest` is: no signature
confusion through the embedding. -/

namespace AvailableChain.PCSA

theorem Label.toFGSA_injective : Function.Injective Label.toFGSA := by
  intro a b h
  rcases a with s | _ | s <;> rcases b with s' | _ | s'
  all_goals delta Label.toFGSA at h
  all_goals dsimp only at h
  all_goals first | rfl | (cases h) | skip
  all_goals injection h with h
  -- `Slot` is an abbreviation of `Nat`; `omega` needs the `Nat`-typed forms.
  all_goals (have h' : (_ : Nat) = _ := h; clear h)
  · have : @Eq Nat s s' := by omega
    exact this ▸ rfl
  · exact absurd h' (by omega)
  · exact absurd h' (by omega)
  · have : @Eq Nat s s' := by omega
    exact this ▸ rfl

theorem authToFGSA_injective {n : Nat} : Function.Injective (authToFGSA (n := n)) := by
  intro a b h
  cases a <;> cases b <;> delta authToFGSA at h
  all_goals simp only [Auth.seat.injEq, Auth.proposer.injEq, reduceCtorEq] at h ⊢
  · exact ⟨Label.toFGSA_injective h.1, h.2⟩
  · exact h

theorem HeadWire.toFGSA_injective {n : Nat} : Function.Injective (HeadWire.toFGSA (n := n)) := by
  intro a b h
  cases a; cases b
  delta HeadWire.toFGSA at h
  simp only [Signed.mk.injEq] at h ⊢
  exact ⟨authToFGSA_injective h.1, h.2⟩

theorem RowBody.toFGSA_injective : Function.Injective RowBody.toFGSA := by
  intro a b h
  cases a; cases b
  delta RowBody.toFGSA at h
  simp only [FGSA.RowBody.mk.injEq, RowBody.mk.injEq] at h ⊢
  exact h

theorem RowPayload.toFGSA_injective : Function.Injective RowPayload.toFGSA := by
  intro a b h
  cases a; cases b
  delta RowPayload.toFGSA at h
  simp only [FGSA.RowPayload.vote.injEq, RowPayload.vote.injEq] at h ⊢
  exact RowBody.toFGSA_injective h

theorem RowWire.toFGSA_injective {n : Nat} : Function.Injective (RowWire.toFGSA (n := n)) := by
  intro a b h
  cases a; cases b
  delta RowWire.toFGSA at h
  simp only [Signed.mk.injEq] at h ⊢
  exact ⟨authToFGSA_injective h.1, RowPayload.toFGSA_injective h.2⟩

theorem encLabel_injective : Function.Injective encLabel := by
  intro a b h
  cases a <;> cases b
  all_goals
    first
    | rfl
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h); omega)
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h); rw [h'.2])

theorem encAuth_injective {n : Nat} : Function.Injective (encAuth (n := n)) := by
  intro a b h
  cases a <;> cases b
  all_goals
    first
    | rfl
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h); omega)
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h)
       have h'' := epair_inj h'.2
       rw [encLabel_injective h''.1, Fin.ext h''.2])
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h); rw [h'.2])

theorem encBlock_injective : Function.Injective encBlock := by
  intro a
  induction a with
  | genesis =>
      intro b h
      cases b with
      | genesis => rfl
      | node P s r x => have h' := epair_inj (show epair _ _ = epair _ _ from h); omega
  | node P s r x ih =>
      intro b h
      cases b with
      | genesis => have h' := epair_inj (show epair _ _ = epair _ _ from h); omega
      | node P' s' r' x' =>
          have h1 := epair_inj (show epair _ _ = epair _ _ from h)
          have h2 := epair_inj h1.2
          have h3 := epair_inj h2.2
          have h4 := epair_inj h3.2
          cases r; cases r'
          simp only at h4
          rw [ih h2.1, h3.1, h4.1, h4.2]

theorem encAckWire_injective {n : Nat} : Function.Injective (encAckWire (n := n)) := by
  intro a b h
  cases a; cases b
  have h' := epair_inj (show epair _ _ = epair _ _ from h)
  simp only [Signed.mk.injEq]
  refine ⟨encAuth_injective h'.1, ?_⟩
  rename_i r _ r'
  cases r; cases r'
  simp only at h'
  rw [h'.2]

theorem encPC_injective {n : Nat} : Function.Injective (encPC (n := n)) := by
  intro a b h
  cases a; cases b
  have h1 := epair_inj (show epair _ _ = epair _ _ from h)
  have h2 := epair_inj h1.2
  simp only [PC.mk.injEq]
  exact ⟨h1.1, encBlock_injective h2.1, encList_inj encAckWire_injective h2.2⟩

theorem DigestInput.toFGSA_injective {n : Nat} :
    Function.Injective (DigestInput.toFGSA (n := n)) := by
  intro a b h
  cases a; cases b
  delta DigestInput.toFGSA at h
  simp only [FGSA.DigestInput.mk.injEq] at h
  obtain ⟨hp, hs, ha, hrows, hraw, hsup⟩ := h
  have ha' := epair_inj ha
  simp only [DigestInput.mk.injEq]
  exact ⟨hp, hs, ha'.1, List.map_injective_iff.mpr RowWire.toFGSA_injective hrows,
    List.map_injective_iff.mpr HeadWire.toFGSA_injective hraw,
    List.map_injective_iff.mpr HeadWire.toFGSA_injective hsup,
    encOption_inj encPC_injective ha'.2⟩

/-- The digest of the PC-SA input is injective whenever the FG-SA digest is. -/
theorem digestOf_injective_of (p : Params) (hd : Function.Injective p.digest) :
    Function.Injective (digestOf p) :=
  fun _ _ h => DigestInput.toFGSA_injective (hd h)

end AvailableChain.PCSA
end
