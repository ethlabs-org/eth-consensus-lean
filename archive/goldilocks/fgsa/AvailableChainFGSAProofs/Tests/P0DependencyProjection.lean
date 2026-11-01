module
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyStore

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0DependencyProjection
open AvailableChain.SimplexFG AvailableChain.FGCompose

/-- Actual FG-SA accepted-tree retention and original one-object row provenance. -/
private theorem p0c3_real_leaf (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (o : (fgsa p c).Object) (good : Reachable p nd.st) :
    ((fgsaCoreReads p c).core nd).fg.TF ⊆
      ((fgsaCoreReads p c).core ((fgsa p c).process nd o)).fg.TF ∧
    (∀ B ∈ ((fgsaCoreReads p c).core ((fgsa p c).process nd o)).fg.TF,
      B ∉ ((fgsaCoreReads p c).core nd).fg.TF →
      (fgsaSafetyReads p c).proposalErase o = some ((fgsaCoreReads p c).erase B) ∧
      B.rows = ((fgsaSafetyReads p c).proposalRows o).filterMap (fgsaSafetyReads p c).decode) :=
  ⟨(fgsaCoreLaws p c).process_tf nd o,
    fun B mem fresh => (fgsaSafetyStoreLaws p c).process_new nd o B good mem fresh⟩

private theorem p0c3_real_restore (p : Params) (st : State p.n) (t : Time) :
    (acRestart p st t).fg = st.fg ∧ (acRestart p st t).namedBodies = st.namedBodies := by
  exact ⟨acRestart_fg p st t, by simp only [State.namedBodies, acRestart_proposals]⟩

/-- This no-op is why the partial projection is not a full dependency instance. -/
private theorem p0c3_real_missing_parent (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (missing : namedParentHeld st N = false) :
    admitBlock p st s N = st := by
  simp [admitBlock, missing]

private theorem p0c3_real_missing_fg_parent (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (missing : parentFG st N.erase = none) :
    admitBlock p st s N = st := by
  simp [admitBlock, missing]

private theorem p0c3_real_leaf_refusal (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (parent : FGBlock (Fin p.n))
    (held : parentFG st N.erase = some parent)
    (refused : blockAccepted p st s N parent = false) : admitBlock p st s N = st := by
  simp [admitBlock, held, refused]

private theorem p0c3_real_missing_parent_example (p : Params) :
    let parent : NamedProposal p.n := .node .genesis 1 ⟨1⟩ 7 [] [] []
    let child : NamedProposal p.n := .node parent 2 ⟨2⟩ 9 [] [] []
    namedParentHeld (initial p.n) child = false ∧
      admitBlock p (initial p.n) 2 child = initial p.n := by
  refine ⟨rfl, ?_⟩
  exact p0c3_real_missing_parent p _ _ _ rfl

#print axioms p0c3_real_missing_parent_example
#print axioms p0c3_real_leaf
#print axioms p0c3_real_restore
#print axioms p0c3_real_missing_parent
#print axioms p0c3_real_missing_fg_parent
#print axioms p0c3_real_leaf_refusal

end AvailableChain.FGSA.Run.Tests.P0DependencyProjection
end
