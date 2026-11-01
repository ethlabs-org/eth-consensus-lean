module
public import AvailableChainGridCO.Proofs.RecoveryStages
public import AvailableChainGridCO.Proofs.CleanInclusion

@[expose] public section

namespace AvailableChain.GridCO

set_option linter.unusedSectionVars false
variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Every admitted source whose deadline passes the boundary has permanent
support from its own next HEAD. This applies before and after row deletion. -/
def AdmittedSourcesSupported {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (boundary : Slot) : Prop :=
  ∀ s, gateTime p s ≤ rho.horizon → ∀ source ∈ rho.honest, ∀ B C g,
    voteTime p boundary < gateTime p s + lifetime p →
    confirmation p (gateInput p rho s source) s = some C → Block.Preceq B C →
    g ∈ admissionLevels p (gateInput p rho s source) s B →
    ∀ t, s ≤ t → gateTime p t ≤ rho.horizon →
      ReleasedRowsCompatible p rho t B ∧ HeadCovers p rho t B

/-- An honest strict input after a public tick has processed that tick. -/
theorem time_input_now_ge_public {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (reader : V) (hr : reader ∈ rho.honest) (u cut : Time)
    (hpub : PublicTime E u) (hz : 0 ≤ u) (hh : u ≤ rho.horizon) (hlt : u < cut) :
    u ≤ (Run.stateBeforeTime (gridCO p) rho cut reader).now := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hs.tick_total reader hr u hpub hz hh)
  rw [time_input_eq_event_prefix p E rho hs]
  have hindex := (index_lt_read_length_iff hs (cut - 1) hi).mpr (Int.le_sub_one_iff.mpr hlt)
  have hmono := stateBefore_now_mono p E rho hs (Nat.succ_le_of_lt hindex) reader
  rw [stateBefore_succ_event hi] at hmono
  simpa [World.step, gridCO, clock_now] using hmono

/-- Exact row sources also apply after a virtual clock. A current gate is
included; all other sources are strictly before the clock time. -/
theorem clock_input_row_admitted_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈
      (clock p (Run.stateBeforeTime (gridCO p) rho cut reader) cut).obligations) :
    ∃ s C, gateTime p s ≤ cut ∧ confirmation p (gateInput p rho s reader) s = some C ∧
      Block.Preceq B C ∧ g ∈ admissionLevels p (gateInput p rho s reader) s B ∧
      d = gateTime p s + lifetime p := by
  rcases clock_row_admitted_origin p _ cut (run_time_receiptStamped p rho cut reader) B g d hm
      with hold | ⟨s, C, ht, hc, hp, hadmit, hd⟩
  · obtain ⟨s, C, ht, rest⟩ :=
      time_input_row_genuine_admitted_origin p E rho hs cut reader B g d hold
    exact ⟨s, C, le_of_lt ht, rest⟩
  · subst cut
    exact ⟨s, C, le_refl _, hc, hp, hadmit, hd⟩

/-- A live clock row after the last stage has its target in every later
complete honest batch, starting at its own source's next HEAD. -/
theorem stage_clock_row_support {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (boundary : Slot) (hsources : AdmittedSourcesSupported p rho boundary)
    (cut : Time) (hz : 0 < cut) (hb : voteTime p boundary ≤ cut)
    (reader : V) (hr : reader ∈ rho.honest) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈
      (clock p (Run.stateBeforeTime (gridCO p) rho cut reader) cut).obligations) :
    ∃ s, gateTime p s ≤ cut ∧ ∀ t, s ≤ t → gateTime p t ≤ rho.horizon → HeadCovers p rho t B := by
  set_option backward.isDefEq.respectTransparency false in
  have hmap := run_time_map_reachable p E rho hs cut reader
  have hclock := clock_map_reachable p _ cut hmap
    (le_of_lt (time_input_now_lt p E rho hs cut hz reader))
  have hd : cut < d := by simpa [LiveRows, clock_now] using! hclock.liveRows (B, g, d) hm
  obtain ⟨s, C, ht, hc, hp, hadmit, hdeadline⟩ :=
    clock_input_row_admitted_origin p E rho hs cut reader B g d hm
  refine ⟨s, ht, ?_⟩
  intro t hst hh
  exact (hsources s (((gateTime_le_iff p s t).mpr hst).trans hh) reader hr B C g
    (hdeadline ▸ hb.trans_lt hd) hc hp hadmit t hst hh).2

/-- The source root at the honest proposal and every reader root after
release lie on the same ordinary proposer walk after the stages. -/
theorem stage_roots_at_ordinary_proposal {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (boundary r : Slot) (hsources : AdmittedSourcesSupported p rho boundary)
    (hsync : SynchronousLabel p E rho r)
    (hb : voteTime p boundary ≤ proposalTime p (r + 1))
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest) :
    Block.Preceq (liveRoot (proposalState p rho (r + 1)))
      (ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1)) ∧
    ∀ reader ∈ rho.honest, Block.Preceq (liveRoot (nextHeadState p rho r reader))
      (ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1)) := by
  have hs := hsync.1.toScheduleWellFormed
  have hroot (cut : Time) (hz : 0 < cut) (hbc : voteTime p boundary ≤ cut)
      (hcut : cut < gateTime p r) (reader : V) (hr : reader ∈ rho.honest) :
      Block.Preceq (liveRoot (clock p (Run.stateBeforeTime (gridCO p) rho cut reader) cut))
        (ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1)) := by
    apply liveRoot_below_of_rows
    intro K g d hm
    obtain ⟨s, ht, hcover⟩ := stage_clock_row_support p E rho hs boundary hsources
      cut hz hbc reader hr K g d hm
    have hsr : s < r := by
      by_contra hn
      have hle := (gateTime_le_iff p r s).mpr (Nat.le_of_not_gt hn)
      exact (not_lt.mpr hle) (ht.trans_lt hcut)
    have hrpos : 0 < r := Nat.zero_le s |>.trans_lt hsr
    have he : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
    have hpres := preserve_from_engine p E rho hΔ (r - 1)
    rw [he] at hpres
    obtain ⟨C, hc, hp, _⟩ := hpres hsync hsync.2.1 K
      (hcover (r - 1) (Nat.le_sub_one_of_lt hsr)
        (((gateTime_le_iff p (r - 1) r).mpr (Nat.sub_le r 1)).trans hsync.2.2.1)) reader hr
    exact genuine_prefix_at_ordinary_proposal p E rho hΔ r hsync reader hr hprop K C hc hp
  have hz : 0 < proposalTime p (r + 1) := by
    dsimp [proposalTime]; nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hpq : proposalTime p (r + 1) ≤ releaseTime p r := by
    dsimp [proposalTime, releaseTime]; nlinarith [p.deltaPos]
  constructor
  · exact hroot _ hz hb (by dsimp [proposalTime, gateTime]; nlinarith [p.deltaPos]) _ hprop
  · intro reader hr
    exact hroot _ (hz.trans_le hpq) (hb.trans hpq)
      (by dsimp [releaseTime, gateTime]; linarith [p.deltaPos]) reader hr

/-- Re-anchoring an ordinary proposer path proves the actual parent
equality. This local proof is shared by recovery and later suffix proposals. -/
theorem proposal_parent_ordinary_of_root {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (hroot : RootInjective E (gridInterface p) rho) (s : Slot) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho s B)
    (hanchor : Block.Preceq (liveRoot (proposalState p rho s))
      (ordinaryProposalHead (proposalState p rho s) s)) :
    B.parent = ordinaryProposalHead (proposalState p rho s) s := by
  let st := proposalState p rho s
  have hclosed : StoredPrefixClosed st := clock_stored_prefix_closed p _ _
    (run_time_stored_prefix_closed p rho _ _)
  have hg : Block.genesis ∈ st.blocks := by
    have he := congrArg Prod.fst (proposalState_receiptData p rho s)
    change st.blocks = _ at he
    rw [he]; exact (genesis_stored_at_time p E rho hs _ _).1
  have hordinary : ordinaryProposalHead st s ∈ st.blocks := by
    unfold ordinaryProposalHead ghost
    rcases ghostWalk_mem st.blocks.eraseDups _ _ st.blocks.eraseDups.length .genesis with he | hm
    · rw [he]; exact hg
    · exact List.mem_eraseDups.mp hm
  have hwalk := ghost_reanchor st.blocks
    (goldfishScore st.blocks (proposerView st s) (proposerSupportView st s))
    (goldfishEligible st.blocks (proposerView st s) (proposerSupportView st s) s)
    .genesis (liveRoot st) (ordinaryProposalHead st s)
    (proposalState_rootInjectiveBelow p E rho hs hroot s) hclosed rfl
    ⟨genesis_prefix _, hanchor⟩ (fun C hn hC => hclosed _ hordinary C hn hC)
  obtain ⟨_, hnode, _⟩ := honest_proposal_views p E rho hs s B hB
  rw [hnode]; exact hwalk

/-- At a gate after the stages, every row target is covered by the
current genuine result. In particular, the gate guard permits repair. -/
theorem stage_gate_guard {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (boundary r : Slot) (hsources : AdmittedSourcesSupported p rho boundary)
    (hsync : SynchronousLabel p E rho r) (hb : voteTime p boundary ≤ releaseTime p r)
    (reader : V) (hr : reader ∈ rho.honest) (C : Block)
    (hc : confirmation p (gateInput p rho r reader) r = some C) :
    (gateInput p rho r reader).obligations.any
      (fun (target, _, _) => !Block.compatible target C) = false := by
  have hs := hsync.1.toScheduleWellFormed
  have hpub : PublicTime E (releaseTime p r) := by
    refine ⟨4 * r + 5, ?_⟩
    simp only [releaseTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]; ring
  have hz : 0 ≤ releaseTime p r := by
    dsimp [releaseTime, proposalTime]; nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hlt : releaseTime p r < gateTime p r := by
    dsimp [releaseTime, gateTime]; linarith [p.deltaPos]
  have hnow := time_input_now_ge_public p E rho hs reader hr _ _ hpub hz
    (hlt.le.trans hsync.2.2.1) hlt
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨⟨B, g, d⟩, hm, hconflict⟩ := List.any_eq_true.mp hany
  have hd := (run_time_map_reachable p E rho hs (gateTime p r) reader).liveRows (B, g, d) hm
  obtain ⟨s, D, ht, hD, hp, hadmit, hdeadline⟩ :=
    time_input_row_genuine_admitted_origin p E rho hs (gateTime p r) reader B g d hm
  have hsr : s < r := by
    by_contra hn
    exact (not_lt.mpr ((gateTime_le_iff p r s).mpr (Nat.le_of_not_gt hn))) ht
  have hheads := (hsources s (ht.le.trans hsync.2.2.1) reader hr B D g
    (hdeadline ▸ hb.trans_lt (hnow.trans_lt hd)) hD hp hadmit
    (r - 1) (Nat.le_sub_one_of_lt hsr)
    (((gateTime_le_iff p (r - 1) r).mpr (Nat.sub_le r 1)).trans hsync.2.2.1)).2
  have he : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.zero_le s |>.trans_lt hsr)
  have hpres := preserve_from_engine p E rho hΔ (r - 1)
  rw [he] at hpres
  obtain ⟨C', hC', hBC, _⟩ := hpres hsync hsync.2.1 B hheads reader hr
  have heq : C' = C := Option.some.inj (hC'.symm.trans hc)
  subst C'
  have hcompat : Block.compatible B C = true := Bool.or_eq_true_iff.mpr (Or.inl hBC)
  simp [hcompat] at hconflict

/-- An honest proposal after the source-support boundary repairs every
record at its 6Δ gate, including sleeping readers and stale old records. -/
theorem stage_honest_proposal_repair {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (boundary r : Slot) (hsources : AdmittedSourcesSupported p rho boundary)
    (hprev : SynchronousLabel p E rho r) (hsync : SynchronousLabel p E rho (r + 1))
    (hroot : RootInjective E (gridInterface p) rho)
    (hready : ProposalRelayReady p E rho (r + 1))
    (hb : voteTime p boundary ≤ proposalTime p (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B) :
    (∀ reader ∈ rho.honest,
      stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader) = B) ∧
    (∀ reader ∈ rho.honest,
      confirmation p (gateInput p rho (r + 1) reader) (r + 1) = some B) := by
  have hroots := stage_roots_at_ordinary_proposal p E rho hΔ boundary r hsources hprev hb hB.1
  have hparent := proposal_parent_ordinary_of_root p E rho hsync.1.toScheduleWellFormed
    hroot (r + 1) B hB hroots.1
  have hheads := honest_proposal_heads_of_ordinary_parent p E rho hΔ r hsync hroot hready
    B hB hparent (by intro reader hr; rw [hparent]; exact hroots.2 reader hr)
  have hslot := (honest_proposal_contains_source_root p E rho hsync.1.toScheduleWellFormed
    (r + 1) B hB).1
  have hconf : ∀ reader ∈ rho.honest,
      confirmation p (gateInput p rho (r + 1) reader) (r + 1) = some B := by
    intro reader hr
    obtain ⟨C, hc, hp, _⟩ := preserve_from_engine p E rho hΔ r hsync
      hsync.2.1 B hheads reader hr
    have he : B = C := prefix_eq_of_slot_ge B C
      (by
        rcases confirmation_mem p (gateInput p rho (r + 1) reader) (r + 1) C hc with hg | hm
        · rw [hg]; trivial
        · exact (run_time_recordSlotOrdered p rho _ reader).1 C hm)
      hp ((confirmation_slot_le p _ (r + 1) C
        (run_time_recordSlotOrdered p rho _ reader).1 hc).trans_eq hslot.symm)
    simpa only [← he] using hc
  refine ⟨?_, hconf⟩
  intro reader hr
  exact read_gate_repairs_heads p E rho hΔ r (.of_synchronous hsync) hsync.2.1 hsync.2.2.1
    B hslot hheads reader hr (stage_gate_guard p E rho hΔ boundary (r + 1) hsources hsync
      (hb.trans (by dsimp [releaseTime]; linarith [p.deltaPos])) reader hr B (hconf reader hr))

end AvailableChain.GridCO
end
