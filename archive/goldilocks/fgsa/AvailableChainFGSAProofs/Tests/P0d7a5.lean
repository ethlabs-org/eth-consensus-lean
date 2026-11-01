module
public import AvailableChainFGSAProofs.Proofs.Finality.Accept -- shake: keep (axiom audit)
public import AvailableChainFGSAProofs.Proofs.Finality.Receipt -- shake: keep (axiom audit)
public import AvailableChainFGSAProofs.Proofs.Finality.ReceiptSuppliers -- shake: keep (axiom audit)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0d7a5
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def d7a5t_proposalFG := (fgsaCoreReads p c).proposalFG

private theorem d7a5t_reads_eq :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a5t_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a5t_proposalFG p c })
    (fgsaCoreReads_def p c)

-- The durable-finality leaf is the actual clock/process monotonicity and restart equation.
private theorem d7a5t_durable : FGCompose.FGFinalityDurableLaws (fgsaCoreReads p c) := by
  rw [d7a5t_reads_eq]
  refine ⟨fun X => fgsa_monoAlong_preceq_F p c X, fun nd t => ?_⟩
  change (acRestart p nd.st t).fg.F = nd.st.fg.F
  rw [acRestart_fg]

-- The store invariant read by the receipt guards is the reachable FG-SA invariant.
private theorem d7a5t_inv (i : Nat) (x : V) :
    KitFG.FGStoreInvariant (heightView p) (finalityView p)
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg := by
  rw [d7a5t_reads_eq]
  exact (cstoreInv_stateBefore E rho i x).fg

-- The root-scope leaf of the generic J-path is produced from the frozen collision premise,
-- for a held certificate and an honest action source; no new root premise is added.
private theorem d7a5t_rootScope (hroots : NamedRootCollisionFree p c E rho) {i : Nat} {x u : V}
    {r : Nat} (hx : x ∈ rho.honest) (hu : u ∈ rho.honest) (C B : FGBlock (Fin p.n))
    (hC : C ∈ (storeAt p c E rho i x).fg.TF)
    (hsrc : actionSourceFG p c E rho u r = some (some B))
    (hroot : (heightView p C).J.root = (heightView p B).T_h.root) :
    (heightView p C).J = (heightView p B).T_h :=
  rootScope_eq hroots (rootScope_justified (rootScope_store hx hC))
    (rootScope_entry (rootScope_source hu hsrc)) hroot

-- The selected receipt of FG-SA is the actual handler: a ready event is a delivery of the
-- exact named proposal whose decoded FG block is the carrier.
private theorem d7a5t_ready_delivery (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (t : Time) (h : Ready_W p c E rho i x W t) :
    ∃ o s N, rho.events[i]? = some (.deliver x o t) ∧ N.erase = eraseFG W ∧
      (toWire p o).decode = some (.block s N) := by
  obtain ⟨o, s, N, P, he, heN, hd, _⟩ := (Ready_W_def p c E rho i x W t).mp h
  exact ⟨o, s, N, he, heN, hd⟩

#print axioms d7a5t_durable
#print axioms d7a5t_inv
#print axioms d7a5t_rootScope
#print axioms d7a5t_ready_delivery
#print axioms AvailableChain.FGSA.Run.finality_restore_preceq_F
#print axioms AvailableChain.FGSA.Run.finality_acceptsFinalBefore_of_idx
#print axioms AvailableChain.FGSA.Run.finality_acceptsFinalBefore_mono_deadline
#print axioms AvailableChain.FGSA.Run.finality_acceptsFinalBefore_mono_ancestor
#print axioms AvailableChain.FGSA.Run.finality_heldBefore_at_proposal
#print axioms AvailableChain.FGSA.Run.receipt_kernel_fields
#print axioms AvailableChain.FGSA.Run.receipt_finalized_of_carriage
#print axioms AvailableChain.FGSA.Run.receipt_finCmp_of_block
#print axioms AvailableChain.FGSA.Run.receipt_finCmp
#print axioms AvailableChain.FGSA.Run.receipt_cap
#print axioms AvailableChain.FGSA.Run.receipt_receiver_finalityLag
#print axioms AvailableChain.FGSA.Run.receipt_jPath_of_cached_anchor
#print axioms AvailableChain.FGSA.Run.receipt_jPath
#print axioms AvailableChain.FGSA.Run.receipt_acceptPrem_W
#print axioms AvailableChain.FGSA.Run.fgsa_acceptBefore_W
#print axioms AvailableChain.FGSA.Run.fgsa_finalizePending_W
#print axioms AvailableChain.FGSA.Run.finality_target_service_of_held
#print axioms AvailableChain.FGSA.Run.finality_action_receipts

end AvailableChain.FGSA.Run.Tests.P0d7a5
end
