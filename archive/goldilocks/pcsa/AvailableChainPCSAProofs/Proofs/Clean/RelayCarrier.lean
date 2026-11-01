module
public import AvailableChainPCSAProofs.Proofs.Clean.RelayStore

public section

/-! C6 RelayCarrier: concrete receipt and count support. -/
namespace AvailableChain.PCSA.CleanPCRelay
open AvailableChain.PCSA.Run AvailableChain.SimplexFG
variable {p : Params}

/-- A decoded ack wire is the ack object of its auth and root. -/
theorem pcsa_relay_decoded_ack (o : Obj p) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : (toWire p o).decode = some (.ack s i r)) : ofAck p ⟨(toWire p o).auth, r⟩ = o := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
  | seat l j =>
    cases l with
    | prop k => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
    | base l =>
      cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl

/-- A decoded PC wire carries that PC as its payload. -/
theorem pcsa_relay_decoded_pc (o : Obj p) (d : PC p.n)
    (h : (toWire p o).decode = some (.pc d)) : o.payload = .pc d := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none =>
    cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
    subst h
    rfl
  | seat l j =>
    cases l with
    | prop k => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
    | base l => cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h

/-- A decoded proposal wire carries that proposal as its payload. -/
theorem pcsa_relay_decoded_proposal (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) : o.payload = .proposal N := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
  | seat l j =>
    cases l with
    | prop k =>
      cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | base l => cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h

/-- A handled PC object either installs its key or pools its acks. -/
theorem pcsa_handles_pc_store (st : State p.n) (o : Obj p) (C : PC p.n)
    (hwf : C.wellFormed = true) (h : handlesS p st o (⟨.none, .pc C⟩ : Obj p)) :
    KeyHeld (process p st (toWire p o)) C.slot C.target ∨
      ∀ a ∈ C.acks, a ∈ (process p st (toWire p o)).ackPool := by
  rcases h with rfl | h | ⟨-, C', hC', hm, -⟩
  · right
    exact pcsa_admitPC_pool st C hwf
  · exfalso
    revert h
    cases (toWire p o).decode with
    | none => exact id
    | some msg =>
      cases msg with
      | block s N =>
        intro h
        obtain ⟨-, hm | hm | hm⟩ := (h : _ ∧ _)
        all_goals
          obtain ⟨x, -, hx⟩ := List.mem_map.mp hm
          cases congrArg (fun x : Obj p => x.payload) hx
      | pc d =>
        intro h
        obtain ⟨x, -, hx⟩ := List.mem_map.mp (h : (⟨.none, .pc C⟩ : Obj p) ∈ d.acks.map (ofAck p))
        cases congrArg (fun x : Obj p => x.payload) hx
      | vote => exact id
      | row => exact id
      | ack => exact id
  · have he := congrArg (fun x : Obj p => x.payload) hC'
    cases he
    left
    rw [KeyHeld_def]
    exact ⟨C, hm, rfl, rfl⟩

/-- [pcsa34-r4.3 §5.2.3] Stage 1: the call that installs a key that a closed
store does not hold carries the installed PC: an ack call (the completing ack
is in the PC), a PC call (its slot and root) or a proposal call (the slot and
root of its block or of its PC). -/
theorem pcsa_install_carries (st : State p.n) (o : Obj p)
    (hwfo : PCSA.wellFormed p (toWire p o) = true) (hcl : CollectClosed st)
    (hF : st.fg.F = .genesis) (C : PC p.n) (hC : C ∈ (process p st (toWire p o)).pcs)
    (hk : ¬ KeyHeld st C.slot C.target) :
    carriesS p o (⟨.none, .pc C⟩ : Obj p) := by
  have hheld : C ∉ st.pcs := fun hm => hk ((KeyHeld_def _ _ _).mpr ⟨C, hm, rfl, rfl⟩)
  delta carriesS
  right
  refine ⟨C, rfl, ?_⟩
  revert hwfo hC
  delta process PCSA.wellFormed
  cases hd : (toWire p o).decode with
  | none => intro _ hC; exact absurd hC hheld
  | some msg => cases msg with
    | vote s i r => intro _ hC; exact absurd hC hheld
    | row i body =>
      dsimp only
      intro _ hC
      rw [(pcsa_admitRow_frame p st _).1] at hC
      exact absurd hC hheld
    | ack s i r =>
      dsimp only
      intro _ hC
      have ha := pcsa_ack_new_key p st _ hcl hF C hC hk
      rw [← pcsa_relay_decoded_ack o s i r hd]
      exact List.mem_map.mpr ⟨_, ha, rfl⟩
    | pc d =>
      dsimp only
      intro hw hC
      rw [show (admitPC st d) = collectPCs (d.acks.foldl poolAckRaw st) by
        delta admitPC
        simp only [hw, ↓reduceIte]] at hC
      · rcases pcsa_collect_new_key st st d.acks .genesis (List.Subset.refl _) rfl
            (fun x hx => Or.inl hx) hcl hF C hC hk with ⟨hb, hn, -⟩ | ⟨a, ha, i, hi⟩
        · exact absurd hb hn
        · rw [pcsa_relay_decoded_pc o d hd]
          obtain ⟨j, hj⟩ := (pcsa_pc_wellFormed_parts d hw).2.2.2.2.2 a ha
          rw [hi] at hj
          have he := Option.some.inj hj
          simp only [Prod.mk.injEq] at he
          exact ⟨he.1.symm, he.2.2.symm⟩
    | block s N =>
      dsimp only
      intro hw hC
      have hG := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
      revert hC
      delta admitBlock
      split
      · intro hC; exact absurd hC hheld
      · cases hP : parentFG st N.erase with
        | none => intro hC; exact absurd hC hheld
        | some P =>
          dsimp only
          split
          · intro hC
            refine (fun hres => ?_) (pcsa_admitBlock_new_key p st _ _ N.rows N.pcAcks N.erase
              ?_ ?_ ?_ hcl hF C hC hk)
            · rw [pcsa_relay_decoded_proposal o s N hd]
              rcases hres with ⟨-, hB, hs⟩ | ⟨a, ha, i, hi⟩
              · exact Or.inl ⟨hs, by rw [hB]⟩
              · right
                revert ha hG
                change (N.pc.map PC.wellFormed).getD true = true →
                  a ∈ (N.pc.map PC.acks).getD [] → _
                cases N.pc with
                | none => intro _ ha; exact absurd ha List.not_mem_nil
                | some d =>
                  intro hdw ha
                  obtain ⟨j, hj⟩ := (pcsa_pc_wellFormed_parts d hdw).2.2.2.2.2 a ha
                  rw [hi] at hj
                  have he := Option.some.inj hj
                  simp only [Prod.mk.injEq] at he
                  exact ⟨d, rfl, he.1.symm, he.2.2.symm⟩
            · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
                (try simp only [deleteConflictingLeases_def])
              all_goals exact List.Subset.refl _
            · cases N.pc
              · rfl
              · dsimp only
                split_ifs <;> rfl
            · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
                (try simp only [deleteConflictingLeases_def])
              all_goals exact fun x hx => pcsa_admitProposal_blocks _ _ _ _ _ x hx
          · intro hC; exact absurd hC hheld

end AvailableChain.PCSA.CleanPCRelay

end
