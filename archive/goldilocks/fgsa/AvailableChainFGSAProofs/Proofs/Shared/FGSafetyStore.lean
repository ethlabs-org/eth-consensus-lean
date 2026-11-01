module
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

/-- The FG-SA store laws: the reachable store, its invariant, and the one new block of a
delivery. -/
theorem fgsaSafetyStoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyStoreLaws (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (heightView p) (finalityView p) (fun nd => Reachable p nd.st) := by
  rw [fgsaCoreReads_def, fgsaSafetyReads_def]
  refine
    { initial_good := Reachable.init
      clock_good := fun _ t h => Reachable.tick t h
      process_good := fun _ o h => Reachable.deliver (toWire p o) h
      own_good := fun _ _ h => h
      restart_good := fun nd t h => reachable_acRestart p nd.st t h
      invariant := fun nd h => (storeBundle_of_reachable p nd.st h).cstore.fg
      initial_tf := fun _ hB => Finset.mem_singleton.mp hB
      restart_tf := fun nd t B _ hB => by
        change B ∈ (acRestart p nd.st t).fg.TF at hB
        rw [acRestart_fg] at hB
        exact hB
      process_new := fun nd o B _ hB hn => ?_ }
  change B ∈ (FGSA.process p nd.st (toWire p o)).fg.TF at hB
  obtain ⟨s, N, P, hw, hP, hacc, rfl⟩ := process_TF_new p nd.st (toWire p o) B hB hn
  have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
    apply toWire_injective
    rw [toWire_ofWire, hw]
  subst ho
  obtain ⟨hg, -⟩ := blockAccepted_facts hacc
  have he : eraseFG (fgBlock P N.erase N.rows) = N.erase :=
    eraseFG_fgBlock hg ((parentFG_spec nd.st N.erase P).1 hP).2 N.rows (blockAccepted_rowsOk hacc)
  constructor
  · change safetyProposalErase p (ofWire p ⟨.proposer s, .proposal N⟩) =
      some (eraseFG (fgBlock P N.erase N.rows))
    rw [he, fgsa_safetyProposalErase_def]
    rfl
  · change (fgBlock P N.erase N.rows).rows =
      (safetyProposalRows p (ofWire p ⟨.proposer s, .proposal N⟩)).filterMap RowWire.toRow?
    rw [fgsa_safetyProposalRows_def]
    rfl

/-- Restore keeps F, J, and both height fields through the kept FG store. -/
theorem fgsaSafetyRestartLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyRestartLaws (fgsaCoreReads p c) := by
  rw [fgsaCoreReads_def]
  refine ⟨?_⟩
  intro nd t
  exact congrArg (fun st => st.F) (acRestart_fg p nd.st t)

/-- Restore keeps all four durable FG finality fields. -/
theorem fgsa_restore_finality_fields (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (t : Time) :
    ((fgsa p c).restore ((fgsa p c).durable nd) t).st.fg.F = nd.st.fg.F ∧
    ((fgsa p c).restore ((fgsa p c).durable nd) t).st.fg.J = nd.st.fg.J ∧
    ((fgsa p c).restore ((fgsa p c).durable nd) t).st.fg.h_j = nd.st.fg.h_j ∧
    ((fgsa p c).restore ((fgsa p c).durable nd) t).st.fg.h_max = nd.st.fg.h_max := by
  change (acRestart p nd.st t).fg.F = nd.st.fg.F ∧
    (acRestart p nd.st t).fg.J = nd.st.fg.J ∧
    (acRestart p nd.st t).fg.h_j = nd.st.fg.h_j ∧
    (acRestart p nd.st t).fg.h_max = nd.st.fg.h_max
  rw [acRestart_fg]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The FG-SA order laws: F moves forward and the output is the erased F. -/
theorem fgsaSafetyOrderLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (fgsaCoreReads p c) (fgsaSafetyReads p c) := by
  rw [fgsaCoreReads_def, fgsaSafetyReads_def]
  exact
    { process_F := fun nd o => process_F_mono p nd.st (toWire p o)
      erase_prefix := fun _ _ h => eraseFG_preceq h
      output_eq := fun _ => rfl }

/-- P0c3 partial projection. FG-SA has no retained missing-parent queue. -/
private theorem p0c3_accepted_leaf_fragment (p : Params) {In : Type} (c : AppCodec In) :
    FGCoreLaws (fgsaCoreReads p c) ∧
    FGSafetyStoreLaws (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (heightView p) (finalityView p) (fun nd => Reachable p nd.st) :=
  ⟨fgsaCoreLaws p c, fgsaSafetyStoreLaws p c⟩

private theorem p0c3_missing_parent_noop (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (missing : namedParentHeld st N = false) :
    admitBlock p st s N = st := by
  delta admitBlock
  simp [missing]

private theorem p0c3_refused_leaf_noop (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (parent : FGBlock (Fin p.n))
    (held : parentFG st N.erase = some parent)
    (refused : blockAccepted p st s N parent = false) : admitBlock p st s N = st := by
  delta admitBlock
  simp [held, refused]

#print axioms p0c3_accepted_leaf_fragment
#print axioms p0c3_missing_parent_noop
#print axioms p0c3_refused_leaf_noop

end AvailableChain.FGSA.Run
end
