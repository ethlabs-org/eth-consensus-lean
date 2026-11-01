module
public import AvailableChainFGSA.Proofs.NamedProposal
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.Fields
public import AvailableChainFGSA.Statements.Invariants

-- Find matcher bodies in the two definitions; do not depend on generated names.
local elab "hygieneEq% " lhs:term:max rhs:term:max : term => do
  let left ← Lean.Elab.Term.elabTerm lhs none
  let right ← Lean.Elab.Term.elabTerm rhs none
  let a ← Lean.getConstInfo left.getAppFn.constName!
  let b ← Lean.getConstInfo right.getAppFn.constName!
  for x in a.value!.getUsedConstants do
    unless (← Lean.Meta.getMatcherInfo? x).isSome do continue
    let ex ← Lean.Meta.mkConstWithFreshMVarLevels x
    for y in b.value!.getUsedConstants do
      unless (← Lean.Meta.getMatcherInfo? y).isSome do continue
      let ey ← Lean.Meta.mkConstWithFreshMVarLevels y
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType ex) (← Lean.Meta.inferType ey) then
        if ← Lean.Meta.isDefEq ex ey then
          return ← Lean.Meta.mkEq ex ey
  throwError "No equal matcher bodies in the supplied definitions"

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_namedByErase {n : Nat} (st : State n) (H : Block) : Option (NamedProposal n) :=
  match (st.namedBodies.filter (fun N => N.erase == H)).eraseDups with
  | [N] => some N
  | _ => none

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_namedByErase_match_1_eq :
    hygieneEq% (@namedByErase?) (@hygiene_namedByErase) := rfl

end AvailableChain.FGSA

attribute [local simp]
  AvailableChain.FGSA.hygiene_namedByErase_match_1_eq

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.FGSA.hygiene_namedByErase_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.FGSA.hygiene_namedByErase_match_1_eq] at *;
    all_goals split at $h:ident))

public section

namespace AvailableChain.FGSA
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] Decode retains the exact signed proposal. -/
theorem proposal?_eq_some {n : Nat} (o : Wire n) (N : NamedProposal n) :
    o.proposal? = some N ↔ ∃ s, o = ⟨.proposer s, .proposal N⟩ := by
  rcases o with ⟨a, m⟩
  cases a with
  | seat l i => cases l <;> cases m <;> simp [Wire.proposal?, Wire.decode]
  | proposer s => cases m <;> simp [Wire.proposal?, Wire.decode]
  | none => cases m <;> simp [Wire.proposal?, Wire.decode]

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] Named membership has a literal wire origin. -/
theorem mem_namedBodies {n : Nat} (st : State n) (N : NamedProposal n) :
    N ∈ st.namedBodies ↔ N = .genesis ∨
      ∃ s, (⟨.proposer s, .proposal N⟩ : Wire n) ∈ st.proposals := by
  simp only [State.namedBodies, List.mem_cons, List.mem_filterMap, proposal?_eq_some]
  constructor
  · rintro (h | ⟨o, ho, s, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, ho⟩
  · rintro (h | ⟨s, hs⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, hs, s, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] Metadata gives local named parent closure. -/
theorem namedBodies_parent (p : Params) (st : State p.n) (m : MetaInv p st)
    {N : NamedProposal p.n} (hN : N ∈ st.namedBodies) : N.parent ∈ st.namedBodies := by
  rcases (mem_namedBodies st N).mp hN with rfl | ⟨s, hs⟩
  · exact (mem_namedBodies st .genesis).mpr (Or.inl rfl)
  · obtain ⟨s', N', he, _, hp, _⟩ := m.wireTree _ hs
    have h := (Msg.proposal.inj (congrArg Signed.payload he))
    simpa only [h] using hp

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] Exact wire uniqueness gives local erasure identity. -/
theorem namedBodies_erase_injective (p : Params) (st : State p.n) (m : MetaInv p st)
    {N M : NamedProposal p.n} (hN : N ∈ st.namedBodies) (hM : M ∈ st.namedBodies)
    (he : N.erase = M.erase) : N = M := by
  rcases (mem_namedBodies st N).mp hN with rfl | ⟨s, hs⟩
  · exact ((named_erase_eq_genesis M).mp he.symm).symm
  rcases (mem_namedBodies st M).mp hM with rfl | ⟨t, ht⟩
  · exact (named_erase_eq_genesis N).mp he
  obtain ⟨s', N', ho, _, _, _, B, hB, hb, _⟩ := m.wireTree _ hs
  have hNN : N = N' := Msg.proposal.inj (congrArg Signed.payload ho)
  subst N'
  have hBg : B ≠ .genesis := by
    intro h
    apply m.noGenesisWire _ hs
    simp only [Wire.block?, Wire.decode]
    rw [← hb, h]
    rfl
  obtain ⟨o, _, hu⟩ := m.treeWire B hB hBg
  have hsB : Wire.block? (⟨.proposer s, .proposal N⟩ : Wire p.n) = some (eraseFG B) := by
    simpa [Wire.block?, Wire.decode] using congrArg some hb.symm
  have htB : Wire.block? (⟨.proposer t, .proposal M⟩ : Wire p.n) = some (eraseFG B) := by
    simpa [Wire.block?, Wire.decode] using congrArg some (he.symm.trans hb.symm)
  exact Msg.proposal.inj (congrArg Signed.payload
    ((hu _ ⟨hs, hsB⟩).trans (hu _ ⟨ht, htB⟩).symm))

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] Named erasures and the base tree have one domain. -/
theorem namedBodies_erase_domain (p : Params) (st : State p.n) (h : CStoreInv p st)
    (m : MetaInv p st) (b : Block) :
    b ∈ st.base.blocks ↔ ∃ N ∈ st.namedBodies, N.erase = b := by
  constructor
  · intro hb
    obtain ⟨B, hB, rfl⟩ := (h.baseTree b).mp hb
    by_cases hg : B = .genesis
    · subst B
      exact ⟨.genesis, (mem_namedBodies st _).mpr (Or.inl rfl), rfl⟩
    obtain ⟨o, ⟨ho, he⟩, _⟩ := m.treeWire B hB hg
    obtain ⟨s, N, rfl, _, _, _, _, _, _, _⟩ := m.wireTree o ho
    exact ⟨N, (mem_namedBodies st _).mpr (Or.inr ⟨s, ho⟩), Option.some.inj he⟩
  · rintro ⟨N, hN, rfl⟩
    apply (h.baseTree _).mpr
    rcases (mem_namedBodies st N).mp hN with rfl | ⟨s, hs⟩
    · exact ⟨.genesis, h.fg.gen, rfl⟩
    obtain ⟨s', N', he, _, _, _, B, hB, hb, _⟩ := m.wireTree _ hs
    have hNN := Msg.proposal.inj (congrArg Signed.payload he)
    exact ⟨B, hB, hb.trans (congrArg NamedProposal.erase hNN.symm)⟩

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] Local admitted root identity needs no run premise. -/
theorem namedBodies_root_injective (p : Params) (st : State p.n) (h : CStoreInv p st)
    (m : MetaInv p st) {N M : NamedProposal p.n}
    (hN : N ∈ st.namedBodies) (hM : M ∈ st.namedBodies) (he : N.root = M.root) : N = M := by
  have hn := (namedBodies_erase_domain p st h m N.erase).mpr ⟨N, hN, rfl⟩
  have hm := (namedBodies_erase_domain p st h m M.erase).mpr ⟨M, hM, rfl⟩
  obtain ⟨B, hB, hb⟩ := (h.baseTree _).mp hn
  obtain ⟨C, hC, hc⟩ := (h.baseTree _).mp hm
  have eqBC := h.rootInj B hB C hC (by
    rw [← eraseFG_root, ← eraseFG_root, hb, hc, named_erase_root, named_erase_root, he])
  exact namedBodies_erase_injective p st m hN hM
    (hb.symm.trans ((congrArg eraseFG eqBC).trans hc))

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Active filtering retains the resolution domain. -/
theorem actView_resolutionTree {n : Nat} (st : State n) :
    GridCO.resolutionTree (actView st) = GridCO.resolutionTree st.base := rfl

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] A successful parent lookup returns a held full value. -/
theorem namedByErase?_sound {n : Nat} (st : State n) (H : Block) (N : NamedProposal n)
    (h : namedByErase? st H = some N) : N ∈ st.namedBodies ∧ N.erase = H := by
  unfold namedByErase? at h
  hygiene_split at h
  · rename_i P he
    cases h
    have hm : N ∈ (st.namedBodies.filter (fun M => M.erase == H)).eraseDups := by
      simp [he]
    simpa using hm
  · contradiction

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Unique named matches give one lookup result. -/
theorem namedByErase?_complete {n : Nat} (st : State n) (H : Block) (N : NamedProposal n)
    (hN : N ∈ st.namedBodies) (he : N.erase = H)
    (hu : ∀ M ∈ st.namedBodies, M.erase = H → M = N) : namedByErase? st H = some N := by
  have singleton {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (a : α)
      (ha : a ∈ xs) (hall : ∀ b ∈ xs, b = a) : xs.eraseDups = [a] := by
    cases xs with
    | nil => simp at ha
    | cons b bs =>
        have hb := hall b (by simp)
        subst b
        rw [List.eraseDups_cons]
        have hf : bs.filter (fun b => !b == a) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b h
          simp [hall b (by simp [h])]
        simp [hf]
  have hxs : (st.namedBodies.filter (fun M => M.erase == H)).eraseDups = [N] := by
    apply singleton
    · simp [hN, he]
    · intro M hM
      obtain ⟨hm, he⟩ := List.mem_filter.mp hM
      exact hu M hm (beq_iff_eq.mp he)
  simp [namedByErase?, hxs]

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Every stored geometric head has a unique named parent. -/
theorem namedByErase?_stored (p : Params) (st : State p.n) (h : CStoreInv p st)
    (m : MetaInv p st) (H : Block) (hH : H ∈ st.base.blocks) :
    ∃ N, namedByErase? st H = some N ∧ N ∈ st.namedBodies ∧ N.erase = H := by
  obtain ⟨N, hn, he⟩ := (namedBodies_erase_domain p st h m H).mp hH
  refine ⟨N, namedByErase?_complete st H N hn he ?_, hn, he⟩
  intro M hm hem
  exact namedBodies_erase_injective p st m hm hn (hem.trans he.symm)

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] A clock does not change named proposal storage. -/
theorem clock_namedBodies (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).namedBodies = st.namedBodies := by
  simp only [State.namedBodies, clock_proposals]

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] The geometric API follows full agreement. -/
theorem contentAgree_projection {n : Nat} {st st' : State n} (hc : ContentAgree st st')
    {s s' : Slot} {N N' : NamedProposal n}
    (hN : (⟨.proposer s, .proposal N⟩ : Wire n) ∈ st.proposals)
    (hN' : (⟨.proposer s', .proposal N'⟩ : Wire n) ∈ st'.proposals)
    (he : N.root = N'.root) : N.erase = N'.erase ∧ N.rows = N'.rows := by
  have h := hc s N hN s' N' hN' he
  exact ⟨h.2.1, h.2.2.2.2⟩

end AvailableChain.FGSA
end
