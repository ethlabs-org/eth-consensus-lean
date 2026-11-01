module
public import AvailableChainGridCO.Proofs.ProposalTransport
public import AvailableChainGridCO.Proofs.Coverage

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The ordinary proposal walk from genesis, with the actual source views.
This is a proof expression; honest code still starts at its live root. -/
def ordinaryProposalHead {n : Nat} (st : State n) (s : Slot) : Block :=
  ghost .genesis st.blocks (goldfishScore st.blocks (proposerView st s) (proposerSupportView st s))
    (goldfishEligible st.blocks (proposerView st s) (proposerSupportView st s) s)

private theorem freeze_to_proposal (p : Params) (r : Slot) :
    freezeTime p r ≤ proposalTime p (r + 1) := by
  dsimp [freezeTime, proposalTime]
  nlinarith [p.deltaPos]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Early resolved support is present in the next proposer's ordinary
view before it acts. Raw HEAD and target-path relay are both included. -/
theorem early_support_at_proposal {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source : V) (hs : source ∈ rho.honest)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest) (o : Wire p.n)
    (ho : o ∈ cleanSupport p (gateInput p rho r source) r) :
    o ∈ proposerSupportView (proposalState p rho (r + 1)) (r + 1) ∧
      ∃ target, headTarget? o = some target ∧ target ∈ (proposalState p rho (r + 1)).blocks := by
  have hearly := (List.mem_filter.mp ho).1
  have hraw := (List.mem_filter.mp hearly).1
  have hres := (List.mem_filter.mp hearly).2
  have hl : headLabel? o = some r := by simpa using (List.mem_filter.mp hraw).2
  cases ht : headTarget? o with
  | none => simp [resolvedBefore_block, ht] at hres
  | some target =>
      have hvote := (synchronous_early_head_at_freeze p E rho hΔ r hsync source
        (rho.proposerOf (r + 1)) hs hprop o ho).1
      have hblock := (synchronous_early_target_at_freeze p E rho hΔ r hsync source
        (rho.proposerOf (r + 1)) hs hprop o target ht hearly).1
      have hpre := time_input_receiptPrefix p E rho hsync.1.toScheduleWellFormed
        (freezeTime p r) (proposalTime p (r + 1)) (freeze_to_proposal p r)
        (rho.proposerOf (r + 1))
      have hv := congrArg (fun x => x.2.2.1) (proposalState_receiptData p rho (r + 1))
      have hb := congrArg Prod.fst (proposalState_receiptData p rho (r + 1))
      change (proposalState p rho (r + 1)).votes = _ at hv
      change (proposalState p rho (r + 1)).blocks = _ at hb
      have hvote' : o ∈ proposerView (proposalState p rho (r + 1)) (r + 1) := by
        apply List.mem_filter.mpr
        exact ⟨by rw [hv]; exact hpre.votes.subset (List.mem_filter.mp hvote).1,
          by simp [hl]⟩
      have hblock' : target ∈ (proposalState p rho (r + 1)).blocks := by
        rw [hb]; exact hpre.blocks.subset hblock
      simp only [resolvedBefore_block, ht, hl, Option.getD_some, Bool.and_eq_true,
        decide_eq_true_eq] at hres
      exact ⟨List.mem_filter.mpr ⟨hvote', by
        simp [resolvedHead?, ht, resolveTarget, resolutionTree, hblock', hres.1.1.2]⟩,
        target, rfl, hblock'⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every proposer raw HEAD settles in the preceding confirmer's late pool
as exact membership or equivocation evidence. -/
theorem proposal_raw_in_previous_late {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source : V) (hs : source ∈ rho.honest)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest) (o : Wire p.n)
    (ho : o ∈ proposerView (proposalState p rho (r + 1)) (r + 1)) :
    ∀ i, headSeat? o = some i →
      o ∈ lateVotes p (gateInput p rho r source) r ∨
      equivocates (lateVotes p (gateInput p rho r source) r) i = true := by
  apply synchronous_release_vote_late p E rho hΔ r hsync
    (rho.proposerOf (r + 1)) source hprop hs o
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa using hl⟩
  have hv := congrArg (fun x => x.2.2.1) (proposalState_receiptData p rho (r + 1))
  change (proposalState p rho (r + 1)).votes = _ at hv
  rw [hv] at hm
  exact (time_input_receiptPrefix p E rho hsync.1.toScheduleWellFormed
    (proposalTime p (r + 1)) (releaseTime p r)
    (by dsimp [proposalTime, releaseTime]; nlinarith [p.deltaPos]) _).votes.subset hm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The genuine-result transfer receipt conditions hold for the next
proposer as well as for the next ordinary HEAD. -/
theorem proposalTransferReceipts_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source : V) (hs : source ∈ rho.honest)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest) (B : Block) :
    TransferReceipts p (gateInput p rho r source) r (proposalState p rho (r + 1)).blocks
      (proposerView (proposalState p rho (r + 1)) (r + 1))
      (proposerSupportView (proposalState p rho (r + 1)) (r + 1)) B := by
  refine ⟨?_, ?_, ?_⟩
  · intro o ho _
    exact early_support_at_proposal p E rho hΔ r hsync source hs hprop o ho
  · intro o ho i hi
    exact proposal_raw_in_previous_late p E rho hΔ r hsync source hs hprop o ho i hi
  · intro o ho; exact (List.mem_filter.mp ho).1

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every genuine prefix of a synchronous label is on the next ordinary
proposer walk from genesis. No live-root assumption is required. -/
theorem genuine_prefix_at_ordinary_proposal {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source : V) (hs : source ∈ rho.honest)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest) (B C : Block)
    (hc : confirmation p (gateInput p rho r source) r = some C) (hp : Block.Preceq B C) :
    Block.Preceq B (ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1)) := by
  let st := proposalState p rho (r + 1)
  let free := { st with obligations := [] }
  have hreceipts := proposalTransferReceipts_from_engine p E rho hΔ r hsync source hs hprop B
  have hpos : 0 < (prefixSupportSeats p (gateInput p rho r source) r B).card := by
    have hm := confirmation_majority p _ r C hc
    have hp' := prefixSupport_mono p (gateInput p rho r source) r B C hp
    rw [prefixSupport_eq_card p _ r B] at hp'
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨o, ho, _, target, ht, hBT⟩ := prefixSupportSeats_witness p _ r B i hi
  obtain ⟨_, target', ht', hstored⟩ := early_support_at_proposal p E rho hΔ r hsync source hs hprop
    o ho
  have he : target' = target := Option.some.inj (ht'.symm.trans ht)
  subst target'
  have hclosed : StoredPrefixClosed st := clock_stored_prefix_closed p _ _
    (run_time_stored_prefix_closed p rho _ _)
  have hwalk := forkChoice_covers_of_transfer p (gateInput p rho r source) free r (r + 1)
    st.blocks (proposerView st (r + 1)) (proposerSupportView st (r + 1)) B C hc hp hreceipts
    (by
      change Block.Compatible .genesis B
      exact Bool.or_eq_true_iff.mpr (Or.inl (genesis_prefix B)))
    (fun A hn hAB => hclosed target hstored A hn (prefix_trans A B target hAB hBT))
  simpa [ordinaryProposalHead, forkChoice, free, liveRoot, st] using hwalk

end AvailableChain.GridCO
end
