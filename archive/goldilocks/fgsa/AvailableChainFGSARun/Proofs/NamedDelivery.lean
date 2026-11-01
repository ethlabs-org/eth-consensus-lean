module
public import AvailableChainFGSARun.Proofs.NamedOrigins -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.NamedHistory
public import AvailableChainFGSARun.Proofs.Reachable

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]

/-- [P23-A] A proposal trigger supplies receipt scope from emission or source acceptance. -/
theorem proposal_trigger_in_receipt_scope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (s : Slot) (N : NamedProposal p.n) (t : Time)
    (hT : Gen.V2.Duty.Trigger E rho (ofWire p ⟨.proposer s, .proposal N⟩) t) :
    NamedProposalReceiptScope p c E rho N := by
  rcases hT with ⟨v, hv, hem⟩ | ⟨v, _, i, ha⟩
  · exact namedReceiptScope_emitted E rho hv hem rfl (named_preceq_refl N)
  · exact Or.inl (proposal_handle_in_scope E rho _ s N rfl i v t ha.1)

/-- [P23-A] A processed root has an exact old-scoped named body.
Receipt collision freedom identifies it with the required receipt-scoped body. -/
theorem proposal_processed_in_scope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hRoots : NamedReceiptRootCollisionFree p c E rho)
    {w : V} (hw : w ∈ rho.honest) (k : Nat) (s : Slot) (N : NamedProposal p.n)
    (hN : NamedProposalReceiptScope p c E rho N)
    (hp : (fgsa p c).processed (V2.D.Run.stateBefore E rho k w)
      (ofWire p ⟨.proposer s, .proposal N⟩) = true) :
    NamedProposalInRun p c E rho N := by
  change decide (∃ Y ∈ (V2.D.Run.stateBefore E rho k w).st.fg.TF,
    Y.root = N.root) = true at hp
  obtain ⟨Y, hY, hroot⟩ := of_decide_eq_true hp
  by_cases hg : Y = .genesis
  · subst Y
    have hgen : NamedProposalInRun p c E rho .genesis :=
      namedScope_held E rho hw 0 ((mem_namedBodies _ _).mpr (Or.inl rfl))
    have he := hRoots .genesis N (Or.inl hgen) hN hroot
    exact he ▸ hgen
  obtain ⟨wire, ⟨hwire, hblock⟩, _⟩ := (metaInv_stateBefore E rho k w).treeWire Y hY hg
  obtain ⟨r, M, hw', _, _, _, _⟩ := (metaInv_stateBefore E rho k w).wireTree wire hwire
  have hM : NamedProposalInRun p c E rho M :=
    namedScope_stored_proposal E rho k w (by rw [← hw']; exact hwire)
  have herase : M.erase = eraseFG Y := by
    rw [hw'] at hblock
    exact Option.some.inj hblock
  have he : M = N := by
    apply hRoots M N (Or.inl hM) hN
    have hr := congrArg Block.root herase
    rw [named_erase_root, eraseFG_root] at hr
    exact hr.trans hroot
  exact he ▸ hM

/-- [P23-A] Historical processing of an honest emitted proposal supplies old scope.
The witness can precede a restart; this scope concerns the whole run. -/
theorem emitted_proposal_history_in_scope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hRoots : NamedReceiptRootCollisionFree p c E rho)
    {v w : V} {t a : Time} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (s : Slot) (N : NamedProposal p.n)
    (hem : V2.D.Run.emits E rho v (ofWire p ⟨.proposer s, .proposal N⟩) t)
    (hp : V2.D.ProcessedByActionCut E rho w (ofWire p ⟨.proposer s, .proposal N⟩) a) :
    NamedProposalInRun p c E rho N := by
  obtain ⟨k, _, hp⟩ := hp
  exact proposal_processed_in_scope E rho hRoots hw k s N
    (namedReceiptScope_emitted E rho hv hem rfl (named_preceq_refl N)) hp

/-- [P23-A] Delivery service scopes an emitted proposal; a relay uses source acceptance. -/
theorem proposal_trigger_service_in_scope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hRoots : NamedReceiptRootCollisionFree p c E rho)
    (s : Slot) (N : NamedProposal p.n) (t a d : Time) (w : V) (hw : w ∈ rho.honest)
    (hT : Gen.V2.Duty.Trigger E rho (ofWire p ⟨.proposer s, .proposal N⟩) t)
    (hService : V2.D.DeliveryService E rho w (ofWire p ⟨.proposer s, .proposal N⟩) a d) :
    NamedProposalInRun p c E rho N := by
  rcases hT with ⟨v, hv, hem⟩ | ⟨v, _, i, ha⟩
  · rcases hService with hp | ⟨t', _, _, j, hh⟩
    · exact emitted_proposal_history_in_scope E rho hRoots hv hw s N hem hp
    · exact proposal_handle_in_scope E rho _ s N rfl j w t' hh
  · exact proposal_handle_in_scope E rho _ s N rfl i v t ha.1

-- W3 integration: these delivery-bound consumers retain their original contracts.
/-- [ROOT-DIGEST-2 W1; DC NamedReceiptCalls] Broadcast or source acceptance scopes a trigger.
This proof uses no root idealization or processed-to-body inference. -/
theorem proposal_trigger_in_scope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (ho : o = ofWire p ⟨.proposer s, .proposal N⟩)
    (dl : Time → Time) (cut t : Time) (w : V)
    (_hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t) (_hw : w ∈ rho.honest)
    (_hcut : dl t ≤ cut)
    (_hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false)
    (hService : V2.D.DeliveryService E rho w o t (dl t))
    (hHistory : V2.D.ProcessedByActionCut E rho w o t → NamedProposalInRun p c E rho N) :
    NamedProposalInRun p c E rho N := by
  rcases hT with ⟨_, _, _⟩ | ⟨v, _, i, haccept⟩
  · rcases hService with hh | ⟨t', _, _, j, hh⟩
    · exact hHistory hh
    · exact proposal_handle_in_scope E rho o s N ho j w t' hh
  · exact proposal_handle_in_scope E rho o s N ho i v t haccept.1

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Trigger scope retains the Block projection. -/
theorem proposal_trigger_in_root_scope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (ho : o = ofWire p ⟨.proposer s, .proposal N⟩)
    (dl : Time → Time) (cut t : Time) (w : V)
    (_hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t) (_hw : w ∈ rho.honest)
    (_hcut : dl t ≤ cut)
    (_hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false)
    (hService : V2.D.DeliveryService E rho w o t (dl t))
    (hHistory : V2.D.ProcessedByActionCut E rho w o t → NamedProposalInRun p c E rho N) :
    RootBlockInRun p c E rho N.erase :=
  ⟨N, proposal_trigger_in_scope E rho o s N ho dl cut t w _hD hT _hw _hcut _hNX
    hService hHistory, rfl⟩


end AvailableChain.FGSA.Run
end
