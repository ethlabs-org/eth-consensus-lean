module
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalReceipt

public section

/-! C6 concrete frozen and carried voter input lists. -/
namespace AvailableChain.PCSA
variable {n : Nat}
/-- A vote-list row comes from a decoded stored proposal of the requested slot. -/
theorem pcsa_proposalsAt_mem (st : State n) (s : Slot)
    (raw sup : List (HeadWire n)) (hm : (raw, sup) ∈ proposalsAt st s) :
    ∃ w ∈ st.proposals, ∃ t N, w.decode = some (.block t N) ∧
      N.slot = s ∧ N.raw = raw ∧ N.support = sup := by
  obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp hm
  cases hd : w.decode with
  | none => rw [hd] at he; cases he
  | some msg => cases msg with
    | vote t i r => rw [hd] at he; cases he
    | row i body => rw [hd] at he; cases he
    | ack t i r => rw [hd] at he; cases he
    | pc C => rw [hd] at he; cases he
    | block t N =>
      rw [hd] at he
      change (if N.slot = s then some (N.raw, N.support) else none) = some (raw, sup) at he
      split at he
      · rename_i hs
        have hh := Option.some.inj he
        exact ⟨w, hw, t, N, hd, hs, congrArg Prod.fst hh, congrArg Prod.snd hh⟩
      · cases he
/-- A raw voter input is either a frozen pool HEAD or a carried raw HEAD. -/
theorem pcsa_headVotes_mem (p : Params) (st : State p.n) (s : Slot)
    (o : GridCO.Wire p.n .root) (hm : o ∈ headVotes p st s) :
    (o ∈ GridCO.votesAt st.base (s - 1) ∧
      GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)) ∨
    (∃ w ∈ st.proposals, ∃ t N a, w.decode = some (.block t N) ∧
      N.slot = s ∧ a ∈ N.raw ∧ baseVote a = o ∧ GridCO.headLabel? o = some (s - 1)) := by
  delta headVotes at hm
  rcases List.mem_append.mp (List.mem_eraseDups.mp hm) with hf | hc
  · obtain ⟨hm, hs⟩ := List.mem_filter.mp hf
    exact Or.inl ⟨hm, of_decide_eq_true hs⟩
  · obtain ⟨hc, hl⟩ := List.mem_filter.mp hc
    obtain ⟨row, hr, ha⟩ := List.mem_flatMap.mp hc
    obtain ⟨a, ha, he⟩ := List.mem_map.mp ha
    obtain ⟨w, hw, t, N, hd, hs, hraw, _⟩ := pcsa_proposalsAt_mem st s row.1 row.2 hr
    exact Or.inr ⟨w, hw, t, N, a, hd, hs, hraw ▸ ha, he, beq_iff_eq.mp hl⟩
/-- Support voter inputs use the frozen resolution check or declared carried support. -/
theorem pcsa_headSupport_mem (p : Params) (st : State p.n) (s : Slot)
    (o : GridCO.Wire p.n .root) (hm : o ∈ headSupport p st s) :
    (o ∈ GridCO.votesAt st.base (s - 1) ∧
      GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)) = true) ∨
    (∃ w ∈ st.proposals, ∃ t N a B, w.decode = some (.block t N) ∧
      N.slot = s ∧ a ∈ N.support ∧ baseVote a = o ∧
      GridCO.headLabel? o = some (s - 1) ∧ GridCO.resolvedHead? st.base o = some B ∧
      B.slot ≤ s - 1) := by
  delta headSupport at hm
  rcases List.mem_append.mp (List.mem_eraseDups.mp hm) with hf | hc
  · exact Or.inl (List.mem_filter.mp hf)
  · obtain ⟨hc, hl⟩ := List.mem_filter.mp hc
    obtain ⟨hl, hb⟩ := Bool.and_eq_true_iff.mp hl
    obtain ⟨row, hr, ha⟩ := List.mem_flatMap.mp hc
    obtain ⟨a, ha, he⟩ := List.mem_map.mp ha
    obtain ⟨w, hw, t, N, hd, hs, _, hsup⟩ := pcsa_proposalsAt_mem st s row.1 row.2 hr
    cases hB : GridCO.resolvedHead? st.base o with
    | none => rw [hB] at hb; cases hb
    | some B =>
      rw [hB] at hb
      exact Or.inr ⟨w, hw, t, N, a, B, hd, hs, hsup ▸ ha, he,
        beq_iff_eq.mp hl, rfl, of_decide_eq_true hb⟩

/-- Frozen raw inputs belong to the voter raw list. -/
theorem pcsa_headVotes_of_frozen (p : Params) (st : State p.n) (s : Slot)
    (o : GridCO.Wire p.n .root) (hm : o ∈ GridCO.votesAt st.base (s - 1))
    (ht : GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)) :
    o ∈ headVotes p st s := by
  delta headVotes
  apply List.mem_eraseDups.mpr
  exact List.mem_append_left _ (List.mem_filter.mpr ⟨hm, decide_eq_true ht⟩)
/-- A carried raw HEAD of the preceding label belongs to the voter raw list. -/
theorem pcsa_headVotes_of_carried (p : Params) (st : State p.n) (s : Slot)
    (w : Wire p.n) (hw : w ∈ st.proposals) (t : Slot) (N : NamedProposal p.n)
    (hd : w.decode = some (.block t N)) (hs : N.slot = s)
    (a : HeadWire p.n) (ha : a ∈ N.raw)
    (hl : GridCO.headLabel? (baseVote a) = some (s - 1)) :
    baseVote a ∈ headVotes p st s := by
  have hr : (N.raw, N.support) ∈ proposalsAt st s := by
    apply List.mem_filterMap.mpr
    refine ⟨w, hw, ?_⟩
    rw [hd]
    exact ite_eq_left hs
  delta headVotes
  apply List.mem_eraseDups.mpr
  apply List.mem_append_right
  apply List.mem_filter.mpr
  exact ⟨List.mem_flatMap.mpr ⟨(N.raw, N.support), hr,
    List.mem_map.mpr ⟨a, ha, rfl⟩⟩, beq_iff_eq.mpr hl⟩
/-- The frozen support check supplies both first-stamp bounds and exact resolution. -/
theorem pcsa_frozen_support_data (p : Params) (st : State p.n) (s : Slot)
    (o : GridCO.Wire p.n .root) (hm : o ∈ GridCO.votesAt st.base (s - 1))
    (hr : GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)) = true) :
    ∃ B, GridCO.resolvedHead? (actView st) o = some B ∧ B.slot ≤ s - 1 ∧
      GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1) ∧
      GridCO.stampBlock st.base B < SA.freezeTime p.toParams (s - 1) := by
  have hl : GridCO.headLabel? o = some (s - 1) :=
    beq_iff_eq.mp (List.mem_filter.mp hm).2
  delta GridCO.resolvedBefore at hr
  cases hd : GridCO.resolvedHead? (actView st) o with
  | none => rw [hd] at hr; cases hr
  | some B =>
    rw [hd, hl] at hr
    obtain ⟨⟨hb, hv⟩, ht⟩ := Bool.and_eq_true_iff.mp hr |>.imp_left Bool.and_eq_true_iff.mp
    exact ⟨B, rfl, of_decide_eq_true hb, of_decide_eq_true hv, of_decide_eq_true ht⟩

/-- Valid carried support and frozen support are both in the concrete raw list. -/
theorem pcsa_headSupport_subset_headVotes (p : Params) (st : State p.n) (s : Slot)
    (hwf : ∀ w ∈ st.proposals, wellFormed p w = true) :
    headSupport p st s ⊆ headVotes p st s := by
  intro o ho
  rcases pcsa_headSupport_mem p st s o ho with hf | hc
  · obtain ⟨_, _, _, ht, _⟩ := pcsa_frozen_support_data p st s o hf.1 hf.2
    exact pcsa_headVotes_of_frozen p st s o hf.1 ht
  · obtain ⟨w, hw, t, N, a, B, hd, hs, ha, he, hl, _⟩ := hc
    have h : wellFormed p w = true := hwf w hw
    delta wellFormed at h
    rw [hd] at h
    change (_ && _ && _ && _ &&
      N.support.all (fun v => decide (v ∈ N.raw)) && _ && _ && _) = true at h
    have h8 := (Bool.and_eq_true_iff.mp h).1
    have h7 := (Bool.and_eq_true_iff.mp h8).1
    have h6 := (Bool.and_eq_true_iff.mp h7).1
    have hraw : a ∈ N.raw :=
      of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h6).2 a ha)
    subst o
    exact pcsa_headVotes_of_carried p st s w hw t N hd hs a hraw hl
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- The raw/support subset law holds at every indexed post-clock read. -/
theorem pcsa_headSupport_subset_at_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.DeliveryWellFormed E rho)
    (k : Nat) (x : V) (u : Time) (s : Slot) :
    headSupport p (clock p (V2.D.Run.stateBefore E rho k x).st u) s ⊆
      headVotes p (clock p (V2.D.Run.stateBefore E rho k x).st u) s := by
  apply pcsa_headSupport_subset_headVotes
  intro w hw
  rw [pcsa_clock_proposals] at hw
  exact pcsa_proposal_pool_wellFormed E rho hv k x w hw
end AvailableChain.PCSA.Run

end
