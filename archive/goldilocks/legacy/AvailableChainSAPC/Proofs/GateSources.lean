module
public import AvailableChainSAPC.Proofs.Projection
public import AvailableChainGridCO.Proofs.RowOrigins

@[expose] public section
namespace AvailableChain.SAPC

private theorem fold_field {α β γ : Type} (f : α → γ) (step : α → β → α)
    (h : ∀ st x, f (step st x) = f st) (xs : List β) (st : α) :
    f (xs.foldl step st) = f st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact (ih _).trans (h st x)

/-- Saving raw history is independent of both guards. -/
theorem gateWithPC_genuine (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (c : Option (PC n)) :
    (gateWithPC p st r c).genuine =
      @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st r (SA.confirmation p st r) := by
  cases c with
  | none => exact @GridCO.gate_genuine GridCO.slowLeasePolicy p.engine n st r
  | some cert =>
      cases hc : SA.confirmation p st r with
      | none => simp [gateWithPC, hc]
      | some h =>
          simp only [gateWithPC, hc]
          split
          · rfl
          · have hf (base : GridCO.State n .block) (prefixes : List Block)
                (levels : Block → List Nat) :
                (prefixes.foldl (fun acc b => (levels b).foldl (fun acc g =>
                  GridCO.writeObligation acc b g (gateTime p r + lifetime p)) acc) base).genuine =
                    base.genuine := by
                apply fold_field GridCO.State.genuine
                intro acc b
                exact fold_field GridCO.State.genuine _ (by intros; rfl) _ _
            rw [hf]
            split <;> rfl

theorem gate_genuine (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).base.genuine =
      @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st.base r
        (SA.confirmation p st.base r) :=
  gateWithPC_genuine p st.base r _

/-- PC-vetoed raw tips do not write S, even when their prefix loop writes leases. -/
theorem gateWithPC_stable_of_veto (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (cert : PC n) (h : Block)
    (hc : SA.confirmation p st r = some h) (hv : pcOK (some cert) h = false) :
    (gateWithPC p st r (some cert)).stableRecord = st.stableRecord := by
  simp only [gateWithPC, hc]
  split
  · rfl
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    apply fold_field GridCO.State.stableRecord
    intro acc b
    exact fold_field GridCO.State.stableRecord _ (by intros; rfl) _ _

/-- Whole-tip finite veto still blocks all finite writes. -/
theorem gateWithPC_finite_veto (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (c : Option (PC n)) (h : Block)
    (hc : SA.confirmation p st r = some h)
    (hg : st.obligations.any (fun (b, _, _) => !Block.compatible b h) = true) :
    (gateWithPC p st r c).obligations = st.obligations := by
  cases c <;> simp [gateWithPC, SA.gate, GridCO.gate, hc, hg]

/-- Every new row has a raw genuine source, its own SA admission test,
its own PC guard, and the exact public deadline. No S premise is used. -/
theorem gateWithPC_row_origin (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (c : Option (PC n)) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (gateWithPC p st r c).obligations) :
    (B, g, d) ∈ st.obligations ∨ ∃ X,
      SA.confirmation p st r = some X ∧ Block.Preceq B X ∧
      g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .block st r B ∧
      pcOK c B = true ∧ d = gateTime p r + lifetime p := by
  cases c with
  | none =>
      rcases @GridCO.gate_row_admitted_origin GridCO.slowLeasePolicy p.engine n
        st r B g d hm with hold | ⟨X, hc, hp, ha, hd⟩
      · exact Or.inl hold
      · exact Or.inr ⟨X, hc, hp, ha, rfl, hd⟩
  | some cert =>
      cases hc : SA.confirmation p st r with
      | none => exact Or.inl (by simpa [gateWithPC, hc] using hm)
      | some X =>
          simp only [gateWithPC, hc] at hm
          split at hm
          · exact Or.inl hm
          · let base := { st with
                goldfishRecord := GridCO.advance st.goldfishRecord X
                genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st r (some X)
                stableRecord := if pcOK (some cert) X then
                  GridCO.advance st.stableRecord X else st.stableRecord }
            let prefixes := st.blocks.filter (fun b =>
              b != .genesis && Block.preceq b X && pcOK (some cert) b)
            let levels :=
              @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .block st r
            have hbase : (if pcOK (some cert) X then
                { st with goldfishRecord := GridCO.advance st.goldfishRecord X
                          genuine :=
                            @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st r (some X)
                          stableRecord := GridCO.advance st.stableRecord X }
                else { st with
                  goldfishRecord := GridCO.advance st.goldfishRecord X
                  genuine :=
                    @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st r (some X) }) =
                  base := by dsimp [base]; split <;> rfl
            rw [hbase] at hm
            have hw : (B, g, d) ∈ (GridCO.writeKeys base
                (prefixes.flatMap (fun b => (levels b).map (fun level => (b, level))))
                (gateTime p r + lifetime p)).obligations := by
              simpa only [GridCO.writeKeys, List.foldl_flatMap, List.foldl_map] using hm
            rcases GridCO.writeKeys_row_origin _ _ B g d _ hw with hold | ⟨hkey, hd⟩
            · exact Or.inl hold
            · obtain ⟨b, hb, hmap⟩ := List.mem_flatMap.mp hkey
              obtain ⟨level, hlevel, he⟩ := List.mem_map.mp hmap
              rcases Prod.mk.inj he with ⟨rfl, rfl⟩
              have hprefix := List.mem_filter.mp hb
              have hf := Bool.and_eq_true_iff.mp hprefix.2
              exact Or.inr ⟨X, rfl, (Bool.and_eq_true_iff.mp hf.1).2, hlevel, hf.2, hd⟩

/-- This source statement remains valid when the raw tip is vetoed for S. -/
theorem gate_new_row_source (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (gate p st r).base.obligations)
    (hnew : (B, g, d) ∉ st.base.obligations) :
    ∃ X, SA.confirmation p st.base r = some X ∧ Block.Preceq B X ∧
      g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .block st.base r B ∧
      pcOK (if capBroken p st then none else st.bestPC) B = true ∧
      st.base.obligations.any (fun (K, _, _) => !Block.compatible K X) = false ∧
      d = gateTime p r + lifetime p := by
  rcases gateWithPC_row_origin p st.base r _ B g d hm with hold | ⟨X, hc, hp, ha, hpc, hd⟩
  · exact False.elim (hnew hold)
  · refine ⟨X, hc, hp, ha, hpc, ?_, hd⟩
    cases hg : st.base.obligations.any (fun (K, _, _) => !Block.compatible K X) with
    | false => rfl
    | true =>
        have he := gateWithPC_finite_veto p st.base r
          (if capBroken p st then none else st.bestPC) X hc hg
        exact False.elim (hnew (he ▸ hm))

end AvailableChain.SAPC
end
