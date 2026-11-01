module
public import AvailableChainGridCO.Proofs.ProposalHeads

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- If every row target is below B, the live root is below B. -/
theorem liveRoot_below_of_rows {n : Nat} (st : State n) (B : Block)
    (h : ∀ K g d, (K, g, d) ∈ st.obligations → Block.Preceq K B) :
    Block.Preceq (liveRoot st) B := by
  rcases (liveRoot_is_deepest st).1 with hg | hm
  · rw [hg]; exact genesis_prefix B
  · obtain ⟨⟨K, g, d⟩, hr, he⟩ := List.mem_filterMap.mp hm
    dsimp only at he
    split at he
    · have hK : K = liveRoot st := Option.some.inj he
      simpa [hK] using h K g d hr
    · contradiction

/-- Targets in the actual proposal state come from strictly older gates.
The label immediately before the proposal has not yet gated. -/
theorem proposalState_target_genuine_origin {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (proposalState p rho (r + 1)).obligations) :
    ∃ s C, s < r ∧ confirmation p (gateInput p rho s (rho.proposerOf (r + 1))) s = some C ∧
      Block.Preceq B C := by
  have hcut : proposalTime p (r + 1) < gateTime p r := by
    dsimp [proposalTime, gateTime]; nlinarith [p.deltaPos]
  rcases clock_target_origin p _ (proposalTime p (r + 1))
      (run_time_receiptStamped p rho _ _) B g d hm with ⟨k, deadline, hold⟩ | ⟨s, C, ht, hc, hp⟩
  · obtain ⟨s, C, ht, hc, hp⟩ := time_input_target_genuine_origin p E rho hs
      (proposalTime p (r + 1)) (rho.proposerOf (r + 1)) B k deadline hold
    refine ⟨s, C, ?_, hc, hp⟩
    by_contra hn
    have hb := (gateTime_le_iff p r s).mpr (Nat.le_of_not_gt hn)
    exact (not_lt.mpr hb) (ht.trans hcut)
  · refine ⟨s, C, ?_, ?_, hp⟩
    · by_contra hn
      have hb := (gateTime_le_iff p r s).mpr (Nat.le_of_not_gt hn)
      rw [← ht] at hb
      exact (not_lt.mpr hb) hcut
    · change confirmation p (Run.stateBeforeTime (gridCO p) rho (gateTime p s) _) s = some C
      rwa [← ht]

/-- All earlier clean genuine results lie on the ordinary proposer walk.
This combines clean history with the proposer form of genuine transfer. -/
theorem clean_history_at_ordinary_proposal {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest)
    (s : Slot) (hsr : s < r) (source : V) (hs : source ∈ rho.honest) (B : Block)
    (hc : confirmation p (gateInput p rho s source) s = some B) :
    Block.Preceq B (ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1)) := by
  obtain ⟨C, hC, hBC⟩ := (clean_genuine_history p E rho hΔ r hclean).1
    s hsr source hs B hc source hs
  exact genuine_prefix_at_ordinary_proposal p E rho hΔ r (hclean r (le_refl _))
    source hs hprop B C hC hBC

/-- Both the source root at proposal and every reader root after release
lie below the same ordinary proposer result in a clean history. -/
theorem clean_roots_at_ordinary_proposal {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest) :
    Block.Preceq (liveRoot (proposalState p rho (r + 1)))
      (ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1)) ∧
      ∀ reader ∈ rho.honest, Block.Preceq (liveRoot (nextHeadState p rho r reader))
        (ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1)) := by
  have hs := (hclean r (le_refl _)).1.toScheduleWellFormed
  constructor
  · apply liveRoot_below_of_rows
    intro K g d hm
    obtain ⟨s, C, hsr, hc, hKC⟩ := proposalState_target_genuine_origin p E rho hs r K g d hm
    exact prefix_trans K C _ hKC (clean_history_at_ordinary_proposal p E rho hΔ r hclean
      hprop s hsr (rho.proposerOf (r + 1)) hprop C hc)
  · intro reader hr
    apply liveRoot_below_of_rows
    intro K g d hm
    obtain ⟨s, C, hsr, hc, hKC⟩ := nextHeadState_target_genuine_origin p E rho hs r reader K g d hm
    exact prefix_trans K C _ hKC
      (clean_history_at_ordinary_proposal p E rho hΔ r hclean hprop s hsr reader hr C hc)

/-- The honest clean proposal uses the same parent as its ordinary walk
from genesis. Thus release cannot remove the only route to that parent. -/
theorem clean_proposal_parent_ordinary {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (hroot : RootInjective E (gridInterface p) rho) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B) :
    B.parent = ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1) := by
  have hs := (hclean r (le_refl _)).1.toScheduleWellFormed
  let st := proposalState p rho (r + 1)
  have hclosed : StoredPrefixClosed st := clock_stored_prefix_closed p _ _
    (run_time_stored_prefix_closed p rho _ _)
  have hg : Block.genesis ∈ st.blocks := by
    have he := congrArg Prod.fst (proposalState_receiptData p rho (r + 1))
    change st.blocks = _ at he
    rw [he]
    exact (genesis_stored_at_time p E rho hs _ _).1
  have hordinary : ordinaryProposalHead st (r + 1) ∈ st.blocks := by
    unfold ordinaryProposalHead ghost
    rcases ghostWalk_mem st.blocks.eraseDups _ _ st.blocks.eraseDups.length .genesis with he | hm
    · rw [he]; exact hg
    · exact List.mem_eraseDups.mp hm
  have hanchor := (clean_roots_at_ordinary_proposal p E rho hΔ r hclean hB.1).1
  have hwalk := ghost_reanchor st.blocks
    (goldfishScore st.blocks (proposerView st (r + 1)) (proposerSupportView st (r + 1)))
    (goldfishEligible st.blocks (proposerView st (r + 1)) (proposerSupportView st (r + 1)) (r + 1))
    .genesis (liveRoot st) (ordinaryProposalHead st (r + 1))
    (proposalState_rootInjectiveBelow p E rho hs hroot (r + 1)) hclosed rfl
    ⟨genesis_prefix _, hanchor⟩
    (fun C hn hC => hclosed _ hordinary C hn hC)
  obtain ⟨_, hnode, _⟩ := honest_proposal_views p E rho hs (r + 1) B hB
  rw [hnode]
  exact hwalk

/-- Every clean honest would-be HEAD adopts the honest proposal, including
sleeping readers. Delivery, view merge, score transport, and the root
condition after release all follow from the engine and clean history. -/
theorem clean_honest_proposal_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho (r + 1))
    (hroot : RootInjective E (gridInterface p) rho)
    (hready : ProposalRelayReady p E rho (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B) :
    ∀ reader ∈ rho.honest, Block.Preceq B (nextHead p (nextHeadState p rho r reader) r) := by
  have hprev : CleanThroughLabel p E rho r := fun s hs => hclean s (hs.trans (Nat.le_succ r))
  have hparent := clean_proposal_parent_ordinary p E rho hΔ r hprev hroot B hB
  have hroots := (clean_roots_at_ordinary_proposal p E rho hΔ r hprev hB.1).2
  exact honest_proposal_heads_of_ordinary_parent p E rho hΔ r (hclean (r + 1) (le_refl _))
    hroot hready B hB hparent (by intro reader hr; rw [hparent]; exact hroots reader hr)

/-- A clean honest proposal replaces every record at its 6Δ gate. -/
theorem clean_honest_proposal_repair {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho (r + 1))
    (hroot : RootInjective E (gridInterface p) rho)
    (hready : ProposalRelayReady p E rho (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B) :
    ∀ reader ∈ rho.honest,
      stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader) = B := by
  have hsync := hclean (r + 1) (le_refl _)
  have hheads := clean_honest_proposal_heads p E rho hΔ r hclean hroot hready B hB
  have hslot := (honest_proposal_contains_source_root p E rho hsync.1.toScheduleWellFormed
    (r + 1) B hB).1
  intro reader hr
  obtain ⟨C, hc, hBC, _⟩ := preserve_from_engine p E rho hΔ r hsync
    hsync.2.1 B hheads reader hr
  have he : B = C := prefix_eq_of_slot_ge B C
    (by
      have hmem := confirmation_mem p (gateInput p rho (r + 1) reader) (r + 1) C hc
      rcases hmem with hg | hm
      · rw [hg]; trivial
      · exact (run_time_recordSlotOrdered p rho _ reader).1 C hm)
    hBC ((confirmation_slot_le p _ (r + 1) C
      (run_time_recordSlotOrdered p rho _ reader).1 hc).trans_eq hslot.symm)
  subst C
  exact read_gate_repairs_heads p E rho hΔ r (.of_synchronous hsync) hsync.2.1 hsync.2.2.1
    B hslot hheads reader hr (clean_gate_guard p E rho hΔ (r + 1) hclean reader hr B hc)

/-- The full Draft 4.2 clean 6Δ inclusion claim. -/
theorem included_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hsleep : SleepyRegime (gridCO p) E (gridInterface p) rho t₀) :
    IncludedFrom (gridCO p) E (gridInterface p) rho (gridInterface p).stable t₀ (6 * p.Δ) := by
  intro s hs hawake hh
  have hpos : 0 < s := by
    by_contra hn
    have hz := Nat.eq_zero_of_not_pos hn
    simp [gridCO, proposalTime, hsleep.start_zero, hz] at hs
  have htime : proposalTime p s ≤ rho.horizon := by
    change proposalTime p s + 6 * p.Δ ≤ rho.horizon at hh
    linarith [p.deltaPos]
  obtain ⟨B, hB⟩ := honest_proposal_exists hsleep.execution hΔ s hpos hawake htime
  refine ⟨B, hB, ?_⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hclean := cleanThroughLabel_of_sleepy t₀ hsleep (r + 1) hh
  have hrepair := clean_honest_proposal_repair p E rho hΔ r hclean hsleep.rootInjective
    (proposalRelayReady_of_sleepy hΔ t₀ hsleep (r + 1) (Nat.succ_pos r)) B hB
  intro reader hr
  change Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader))
  rw [hrepair reader hr]
  exact block_preceq_self B

end AvailableChain.GridCO
end
