module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadBody

public section

/-! C6 ProposalPaths: concrete receipt and count support. -/
namespace AvailableChain.PCSA
private theorem proposal_prefix_parent (C B : Block) (hc : Block.Preceq C B) (hn : C ≠ B) :
    Block.Preceq C B.parent := by
  cases B with
  | genesis => exact hc
  | node P s r app =>
    change (decide (C = .node P s r app) || Block.preceq C P) = true at hc
    exact (Bool.or_eq_true_iff.mp hc).resolve_left
      (fun he => hn (of_decide_eq_true he))
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An honest stage-one proposer walk returns a held body. -/
theorem pcsa_getHead_body_at_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (k : Nat) (x : V) (hx : x ∈ rho.honest) (t : Time)
    (view : Option (PC p.n)) (raw sup : List (GridCO.Wire p.n .root)) :
    getHead p (clock p (V2.D.Run.stateBefore E rho k x).st t) view raw sup ∈
      (clock p (V2.D.Run.stateBefore E rho k x).st t).base.blocks := by
  let st := clock p (V2.D.Run.stateBefore E rho k x).st t
  have hreach : Reachable p st := Reachable.tick t (pcsa_reachable_stateBefore E rho k x)
  have hz : (controls p st).Z = .genesis := by
    change (KitFG.storeControlsView (FGSA.heightView p) (clock p _ t).fg).Z = .genesis
    rw [pcsa_body_clock_fg]
    exact (hF x hx k).2.1
  have hg : Block.genesis ∈ st.base.blocks := by
    change Block.genesis ∈ (clock p _ t).base.blocks
    rw [pcsa_clock_blocks]
    exact (pcsa_genesis_body_stamp E rho h.noRestart k x).1
  rcases pcsa_headInTree_mem_or_root p st view (erasedList st (fullTree p st)) raw sup with
    hr | hm
  · change headInTree p st view (erasedList st (fullTree p st)) raw sup ∈ st.base.blocks
    rw [hr]
    exact pcsa_liveRoot_body_mem p st view (pcsa_tree_correspondence p st hreach) hz hg
  · exact (List.mem_filter.mp hm).1
/-- Every proper proposal prefix is in the full proposer tree selected by its parent read. -/
theorem pcsa_proposal_proper_prefix_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (k : Nat) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (N : NamedProposal p.n)
    (hp : N.parent.erase = getHead p
      (clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams s))
      (proposerPC p (clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams s)))
      (proposerVotes (clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams s)) s)
      (proposerSupport (clock p (V2.D.Run.stateBefore E rho k x).st
        (SA.proposalTime p.toParams s)) s))
    (C : Block) (hc : Block.Preceq C N.erase) (hn : C ≠ N.erase) :
    C ∈ erasedList (clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams s))
      (fullTree p (clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams s))) :=
        by
  have hparent : N.parent.erase ∈
      (clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams s)).base.blocks := by
    rw [hp]
    exact pcsa_getHead_body_at_read E rho h hF k x hx _ _ _ _
  have he : N.erase.parent = N.parent.erase := by cases N <;> rfl
  have hcp := proposal_prefix_parent C N.erase hc hn
  rw [he] at hcp
  exact pcsa_full_read_prefix_mem E rho hF k x hx _ N.parent.erase C hparent hcp
end AvailableChain.PCSA.Run

end
