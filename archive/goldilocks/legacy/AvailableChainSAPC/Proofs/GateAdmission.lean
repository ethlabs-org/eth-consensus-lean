module
public import AvailableChainSAPC.Proofs.GateSources
public import AvailableChainGridCO.Proofs.Protection

@[expose] public section
namespace AvailableChain.SAPC

/-- The prefix loop writes every admitted compatible prefix. Its PC
condition concerns B only; the raw descendant C may fail that condition.
The deadline bound is the shared map premise for an exact new deadline. -/
theorem gateWithPC_writes_admitted_prefix (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (cert : Option (PC n)) (B C : Block) (g : Nat)
    (raw : SA.confirmation p st r = some C)
    (finite : st.obligations.any (fun (a, _, _) => !Block.compatible a C) = false)
    (stored : B ∈ st.blocks) (nonzero : B ≠ .genesis) (below : Block.Preceq B C)
    (admitted : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .block st r B)
    (compatible : pcOK cert B = true)
    (bound : GridCO.DeadlinesAtMost st (gateTime p r + lifetime p)) :
    (B, g, gateTime p r + lifetime p) ∈ (gateWithPC p st r cert).obligations := by
  cases cert with
  | none =>
    change (B, g, gateTime p r + lifetime p) ∈ (SA.gate p st r).obligations
    unfold SA.gate
    rw [@GridCO.gate_eq_writeKeys GridCO.slowLeasePolicy p.engine n st r C raw finite]
    apply GridCO.writeKeys_mem_of_key
      { st with stableRecord := GridCO.advance st.stableRecord C
                goldfishRecord := GridCO.advance st.goldfishRecord C
                genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st r (some C) }
      _ B g _ bound
    apply List.mem_flatMap.mpr
    refine ⟨B, List.mem_filter.mpr ⟨stored, ?_⟩, List.mem_map.mpr ⟨g, admitted, rfl⟩⟩
    simpa only [bne_iff_ne, Bool.and_eq_true] using! And.intro nonzero below
  | some cert =>
    let base := { st with
      goldfishRecord := GridCO.advance st.goldfishRecord C
      genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st r (some C)
      stableRecord := if pcOK (some cert) C then
        GridCO.advance st.stableRecord C else st.stableRecord }
    let prefixes := st.blocks.filter (fun b =>
      b != .genesis && Block.preceq b C && pcOK (some cert) b)
    let levels := @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .block st r
    have form : gateWithPC p st r (some cert) = GridCO.writeKeys base
        (prefixes.flatMap (fun b => (levels b).map (fun level => (b, level))))
        (gateTime p r + lifetime p) := by
      simp only [gateWithPC, raw, finite, Bool.false_eq_true, ↓reduceIte]
      simp only [base, prefixes, levels, GridCO.writeKeys, List.foldl_flatMap, List.foldl_map]
      split <;> rfl
    rw [form]
    apply GridCO.writeKeys_mem_of_key base _ B g _ bound
    apply List.mem_flatMap.mpr
    refine ⟨B, List.mem_filter.mpr ⟨stored, ?_⟩, List.mem_map.mpr ⟨g, admitted, rfl⟩⟩
    simpa only [bne_iff_ne, Bool.and_eq_true] using! And.intro (And.intro nonzero below) compatible

/-- A vetoed descendant can create the first lease for its protection
prefix. S remains fixed. No earlier lease for B is required. -/
theorem gateWithPC_arms_vetoed_prefix (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (cert : PC n) (B C : Block) (g : Nat)
    (raw : SA.confirmation p st r = some C)
    (finite : st.obligations.any (fun (a, _, _) => !Block.compatible a C) = false)
    (stored : B ∈ st.blocks) (nonzero : B ≠ .genesis) (below : Block.Preceq B C)
    (admitted : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .block st r B)
    (compatible : pcOK (some cert) B = true) (veto : pcOK (some cert) C = false)
    (bound : GridCO.DeadlinesAtMost st (gateTime p r + lifetime p)) :
    (gateWithPC p st r (some cert)).stableRecord = st.stableRecord ∧
      (B, g, gateTime p r + lifetime p) ∈ (gateWithPC p st r (some cert)).obligations :=
  ⟨gateWithPC_stable_of_veto p st r cert C raw veto,
    gateWithPC_writes_admitted_prefix p st r (some cert) B C g raw finite stored nonzero
      below admitted compatible bound⟩

/-- An existing finite row protects an already stored prefix through any
gate. A PC veto can retain S, but cannot defeat the whole-tip finite guard. -/
theorem gateWithPC_preserves_protected_prefix (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (cert : Option (PC n)) (B : Block) (g : Nat) (d : Time)
    (protection : GridCO.ProtectsUntil st B g d) (old : Block.Preceq B st.stableRecord) :
    Block.Preceq B (gateWithPC p st r cert).stableRecord := by
  cases cert with
  | none =>
    exact @GridCO.gate_preserves_protected_prefix GridCO.slowLeasePolicy
      p.engine n st r B g d protection old
  | some cert =>
    obtain ⟨deadline, _, row⟩ := protection
    cases raw : SA.confirmation p st r with
    | none => simpa only [gateWithPC, raw] using old
    | some C =>
      have writes (base : GridCO.State n .block) (prefixes : List Block)
          (levels : Block → List Nat) :
          (prefixes.foldl (fun acc b => (levels b).foldl (fun acc g =>
            GridCO.writeObligation acc b g (gateTime p r + lifetime p)) acc) base).stableRecord =
              base.stableRecord := by
        simpa only [GridCO.writeKeys, List.foldl_flatMap, List.foldl_map] using
          GridCO.writeKeys_stable base
            (prefixes.flatMap (fun b => (levels b).map (fun g => (b, g))))
            (gateTime p r + lifetime p)
      simp only [gateWithPC, raw]
      split
      · exact old
      · rename_i finite
        rw [writes]
        split
        · apply GridCO.advance_preserves_prefix B st.stableRecord C old
          apply Bool.eq_true_of_not_eq_false
          intro conflict
          have veto : st.obligations.any (fun (a, _, _) => !Block.compatible a C) = true :=
            List.any_eq_true.mpr ⟨(B, g, deadline), row, by simp [conflict]⟩
          exact finite veto
        · exact old

end AvailableChain.SAPC
end
