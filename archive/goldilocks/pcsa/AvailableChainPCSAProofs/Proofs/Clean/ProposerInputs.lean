module
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalReceipt
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures

public section

/-! C6 ProposerInputs: concrete receipt and count support. -/
namespace AvailableChain.PCSA
private theorem proposer_named_geometry (p : Params) (st : State p.n) (H : Block)
    (N : NamedProposal p.n) (h : namedByErase? st H = some N) : N.erase = H := by
  delta namedByErase? at h
  cases hl : (st.namedBodies.filter (fun N => N.erase == H)).eraseDups with
  | nil => rw [hl] at h; cases h
  | cons A rest =>
    cases rest with
    | nil =>
      rw [hl] at h
      obtain rfl := Option.some.inj h
      have hm : A ∈ (st.namedBodies.filter (fun N => N.erase == H)).eraseDups := by
        rw [hl]
        exact List.mem_singleton_self _
      exact beq_iff_eq.mp (List.mem_filter.mp (List.mem_eraseDups.mp hm)).2
    | cons B rest => rw [hl] at h; cases h
/-- Lifting a labelled root HEAD and projecting it back keeps its exact signed wire. -/
theorem pcsa_liftHead_baseVote {n : Nat} (o : GridCO.Wire n .root) (s : Slot)
    (hl : GridCO.headLabel? o = some s) : (liftHead? o).map baseVote = some o := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> (delta GridCO.headLabel? at hl; cases hl)
  rfl
private theorem proposer_lift_list {n : Nat} (xs : List (GridCO.Wire n .root)) (s : Slot)
    (hl : ∀ o ∈ xs, GridCO.headLabel? o = some s) :
    (xs.filterMap liftHead?).map baseVote = xs := by
  rw [List.map_filterMap]
  have he : xs.filterMap (fun o => (liftHead? o).map baseVote) = xs.filterMap some :=
    List.filterMap_congr (fun o ho => pcsa_liftHead_baseVote o s (hl o ho))
  simpa only [List.filterMap_some] using he
/-- Proposal construction keeps the exact source vote lists, PC view, and selected parent. -/
theorem pcsa_generated_proposal_inputs (p : Params) (st : State p.n)
    (s app : Nat) (N : NamedProposal p.n)
    (he : (propose p st s).map (Run.withApp p app) = some (.proposal N)) :
    0 < s ∧ N.slot = s ∧ N.raw.map baseVote = proposerVotes st s ∧
      N.support.map baseVote = proposerSupport st s ∧ N.pc = proposerPC p st ∧
      N.parent.erase = getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st s)
        := by
  obtain ⟨M, hM, hN⟩ := Option.map_eq_some_iff.mp he
  delta propose at hM
  split at hM
  · cases hM
  · rename_i hs
    obtain ⟨A, hA, hMsg⟩ := Option.map_eq_some_iff.mp hM
    subst M
    change Msg.proposal (namedProposal p A s app _ _ _ _) = Msg.proposal N at hN
    obtain rfl := Msg.proposal.inj hN
    refine ⟨Nat.pos_of_ne_zero hs, rfl, ?_, ?_, rfl, ?_⟩
    · apply proposer_lift_list _ (s - 1)
      intro o ho
      exact beq_iff_eq.mp (List.mem_filter.mp ho).2
    · apply proposer_lift_list _ (s - 1)
      intro o ho
      exact beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
    · exact proposer_named_geometry p st _ A hA
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Only the proposal duty uses a slot's proposer signing label. -/
theorem pcsa_prop_single_duty (p : Params) {In : Type} (c : AppCodec In) (m : FGMode)
    (s : Slot) : Gen.V2.Duty.SingleDuty (pcsaWith m p c) (.prop s) := by
  refine ⟨.propAction s, rfl, ?_⟩
  intro d hd
  change d.signLabel = .prop s at hd
  cases d <;> cases hd
  rfl
/-- An emitted proposal exposes the exact inputs of its indexed proposer read. -/
theorem pcsa_emitted_proposal_inputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (N : NamedProposal p.n)
    (he : V2.D.Run.emits E rho x (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p)
      (SA.proposalTime p.toParams s)) :
    ∃ k, rho.events[k]? = some (.tick x (SA.proposalTime p.toParams s)) ∧
      let st := clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams s)
      0 < s ∧ N.slot = s ∧ N.raw.map baseVote = proposerVotes st s ∧
        N.support.map baseVote = proposerSupport st s ∧ N.pc = proposerPC p st ∧
        N.parent.erase = getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st
          s) := by
  obtain ⟨k, hk, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, _, hact⟩ := (Gen.V2.Duty.mem_tick_singleDuty_iff E rho _ x _
    (.prop s) (pcsa_prop_single_duty p c m s) (.propAction s) rfl (0 : Fin 1) (.proposal N)).mp ho
  refine ⟨k, hk, ?_⟩
  cases m <;> apply pcsa_generated_proposal_inputs p _ s (c.app (rho.input x _)) N
  all_goals exact hact
end AvailableChain.PCSA.Run

end
