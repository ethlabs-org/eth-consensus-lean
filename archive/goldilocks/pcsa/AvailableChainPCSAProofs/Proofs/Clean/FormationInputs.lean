module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCompose
public import AvailableChainPCSAProofs.Proofs.Clean.FormationOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.FormationHeads
public import AvailableChainPCSAProofs.Proofs.Clean.FormationEarlyHeads
public import AvailableChainPCSAProofs.Proofs.Clean.AckAdmit
public import AvailableChainPCSAProofs.Proofs.Shared.HonestProposal
public import AvailableChainPCSAProofs.Proofs.Shared.StoreRoots

public section

/-! Formation input producers from the named stage-2 receipt contracts.
Shared body relay closes the old frozen-target receipt (hFrozenBody).
Shared honest-proposal receipt closes the vote-read metadata and early
presence. No body-admission or body-relay proof is copied here. The retained
path, support receipts, timely HEAD witnesses and ack handler pool stay
named. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA
variable {p : Params}
/-- Stored metadata carries each source raw HEAD into the voter merge. -/
theorem pcsa_formation_raw_keep_of_metadata (src dst : State p.n) (s : Slot)
    (N : NamedProposal p.n) (hslot : N.slot = s)
    (hRaw : N.raw = (proposerVotes src s).filterMap liftHead?)
    (hMetadata : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ dst.proposals) :
    proposerVotes src s ⊆ headVotes p dst s := by
  have hPair : (N.raw, N.support) ∈ proposalsAt dst s := by
    delta proposalsAt
    exact List.mem_filterMap.mpr ⟨_, hMetadata, by
      change (if N.slot = s then some (N.raw, N.support) else none) = _
      rw [ite_eq_left hslot]⟩
  intro o ho
  have hl : GridCO.headLabel? o == some (s - 1) := by
    change o ∈ src.base.votes.filter _ at ho
    exact (List.mem_filter.mp ho).2
  have hx : ∃ a, liftHead? o = some a ∧ baseVote a = o := by
    obtain ⟨auth, msg⟩ := o
    cases auth with
    | none => cases msg <;> cases hl
    | proposer r => cases msg <;> cases hl
    | seat r i =>
      cases msg with
      | head b => exact ⟨⟨.seat (.head r) i, b⟩, rfl, rfl⟩
      | proposal B raw sup => cases hl
  obtain ⟨a, ha, he⟩ := hx
  have hc : o ∈ N.raw.map baseVote := by
    rw [hRaw]
    exact List.mem_map.mpr ⟨a, List.mem_filterMap.mpr ⟨o, ho, ha⟩, he⟩
  delta headVotes
  apply List.mem_eraseDups.mpr
  apply List.mem_append.mpr
  right
  exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_, hPair, hc⟩, hl⟩
/-- A stored current-slot body remains in the actual stage-1 voter tree. -/
theorem pcsa_formation_current_body_in_voter_tree (p : Params) (st : State p.n)
    (s : Slot) (P : Block) (hReach : Reachable p st) (hFrame : Run.FrameVacuous p st)
    (hBody : P ∈ st.base.blocks) (hSlot : P.slot = s) :
    P ∈ erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)) := by
  obtain ⟨B, hB, he⟩ := (pcsa_tree_correspondence p st hReach P).mp hBody
  have hBs : B.slot = s := by
    have hs : (eraseFG B).slot = B.slot := by cases B <;> rfl
    exact hs.symm.trans (he ▸ hSlot)
  have hV : B ∈ voterBlocks p st s := by
    delta voterBlocks
    apply Finset.mem_filter.mpr
    refine ⟨hB, Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true ?_))⟩
    exact ⟨B, hB, hBs, KitFG.preceq_refl B⟩
  have hFiltered : B ∈ KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s) := by
    change B ∈ KitFG.filteredFromView (FGSA.heightView p) (controls p st) (voterBlocks p st s)
    apply (KitFG.mem_filteredFromView (FGSA.heightView p) (controls p st) _ B).mpr
    have hF : (controls p st).F = FGBlock.genesis := hFrame.1
    rw [hF, hFrame.2.1, hFrame.2.2]
    exact ⟨hV, KitFG.genesis_preceq B, KitFG.genesis_preceq B,
      B, hV, KitFG.preceq_refl B, Nat.zero_le _⟩
  rw [erasedList_def]
  exact List.mem_filter.mpr ⟨hBody, decide_eq_true ⟨B, hFiltered, he⟩⟩

private theorem formation_support_resolved {n : Nat} (st : State n) (s : Slot)
    (hd : st.base.headDomain = none) (o : GridCO.Wire n .root)
    (ho : o ∈ proposerSupport st s) :
    ∃ r H, GridCO.headTarget? o = some r ∧ Block.findByRoot? st.base.blocks r = some H ∧
      H.slot ≤ s - 1 := by
  have hf := (List.mem_filter.mp ho).2
  cases hres : GridCO.resolvedHead? (actView st) o with
  | none => rw [hres] at hf; cases hf
  | some H =>
    rw [hres] at hf
    obtain ⟨r, ht, hr⟩ := pcsa_actView_resolved st hd o H hres
    exact ⟨r, H, ht, hr, of_decide_eq_true hf⟩

/-- Proposer support resolves to the same bodies in a larger root-unique store. -/
theorem pcsa_formation_resolution_of_blocks {n : Nat} (src dst : State n) (s : Slot)
    (hd : src.base.headDomain = none) (hsub : src.base.blocks ⊆ dst.base.blocks)
    (hu : ∀ C ∈ dst.base.blocks, ∀ D ∈ dst.base.blocks, C.root = D.root → C = D) :
    ∀ o ∈ proposerSupport src s, ∀ B,
      Gen.AC.Root.voteSupports src.base.blocks B o =
        Gen.AC.Root.voteSupports dst.base.blocks B o := by
  intro o ho B
  obtain ⟨r, H, ht, hf, _⟩ := formation_support_resolved src s hd o ho
  have hf' := pcsa_findByRoot_mono hsub hu hf
  have e1 : Gen.AC.Root.resolvedTarget? src.base.blocks o = some H := by
    delta Gen.AC.Root.resolvedTarget?
    rw [ht]
    exact hf
  have e2 : Gen.AC.Root.resolvedTarget? dst.base.blocks o = some H := by
    delta Gen.AC.Root.resolvedTarget?
    rw [ht]
    exact hf'
  rw [Gen.AC.Root.voteSupports_def, Gen.AC.Root.voteSupports_def, e1, e2]
  dsimp only
  rw [decide_eq_true (Block.findByRoot?_mem hf), decide_eq_true (Block.findByRoot?_mem hf')]

/-- Stored metadata carries proposer support into the voter support merge. -/
theorem pcsa_formation_support_keep_of_metadata (src dst : State p.n) (s : Slot)
    (N : NamedProposal p.n) (hslot : N.slot = s)
    (hSupport : N.support = (proposerSupport src s).filterMap liftHead?)
    (hMetadata : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ dst.proposals)
    (hdSrc : src.base.headDomain = none) (hdDst : dst.base.headDomain = none)
    (hsub : src.base.blocks ⊆ dst.base.blocks)
    (hu : ∀ C ∈ dst.base.blocks, ∀ D ∈ dst.base.blocks, C.root = D.root → C = D) :
    proposerSupport src s ⊆ headSupport p dst s := by
  have hPair : (N.raw, N.support) ∈ proposalsAt dst s := by
    delta proposalsAt
    exact List.mem_filterMap.mpr ⟨_, hMetadata, by
      change (if N.slot = s then some (N.raw, N.support) else none) = _
      rw [ite_eq_left hslot]⟩
  intro o ho
  have hl : GridCO.headLabel? o == some (s - 1) := by
    have hv := (List.mem_filter.mp ho).1
    change o ∈ src.base.votes.filter _ at hv
    exact (List.mem_filter.mp hv).2
  obtain ⟨r, H, ht, hf, hH⟩ := formation_support_resolved src s hdSrc o ho
  have hres := pcsa_base_resolved dst hdDst o r H ht
    (pcsa_findByRoot_mono hsub hu hf)
  have hx : ∃ a, liftHead? o = some a ∧ baseVote a = o := by
    obtain ⟨auth, msg⟩ := o
    cases auth with
    | none => cases msg <;> cases hl
    | proposer r => cases msg <;> cases hl
    | seat r i =>
      cases msg with
      | head b => exact ⟨⟨.seat (.head r) i, b⟩, rfl, rfl⟩
      | proposal B raw sup => cases hl
  obtain ⟨a, ha, he⟩ := hx
  have hc : o ∈ N.support.map baseVote := by
    rw [hSupport]
    exact List.mem_map.mpr ⟨a, List.mem_filterMap.mpr ⟨o, ho, ha⟩, he⟩
  delta headSupport
  apply List.mem_eraseDups.mpr
  apply List.mem_append.mpr
  right
  refine List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_, hPair, hc⟩, ?_⟩
  rw [hl, hres]
  exact decide_eq_true hH

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-- A strict old-PC handler and its stored target give a held key before t_s. -/
theorem pcsa_formation_key_before_proposal_of_handler (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (hy : y ∈ rho.honest)
    (C : PC p.n) (hw : C.wellFormed = true) (j : Nat) (t : Time)
    (ht : t < SA.proposalTime p.toParams s)
    (hh : V2.D.Run.handlesAt E rho j y (⟨.none, .pc C⟩ : Obj p) t)
    (hTarget : C.target ∈ (V2.D.Run.stateBeforeTime E rho
      (SA.proposalTime p.toParams s) y).st.base.blocks) :
    KeyHeld (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s) y).st
      C.slot C.target := by
  obtain ⟨o, he, hhandle⟩ := hh
  have hj : j < V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed he _).mpr ht
  have hp := pcsa_handles_pc_store (V2.D.Run.stateBefore E rho j y).st o C hw hhandle
  rw [← pcsa_deliver_succ E rho he] at hp
  rcases hp with hk | hpool
  · rw [KeyHeld_def] at hk ⊢
    obtain ⟨A, hA, hs, hb⟩ := hk
    have hm := pcsa_run_pcs_mono E rho h.frame h.base.noRestart y hy (j + 1)
      (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s)) (Nat.succ_le_of_lt hj) hA
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.base.valid.toScheduleWellFormed] at hm
    exact ⟨A, hm, hs, hb⟩
  · have hpool' : ∀ a ∈ C.acks, a ∈ (V2.D.Run.stateBeforeTime E rho
        (SA.proposalTime p.toParams s) y).st.ackPool := by
      intro a ha
      have hm := pcsa_formation_run_ackPool_mono E rho h.base.noRestart y (j + 1)
        (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s)) (Nat.succ_le_of_lt hj) (hpool a ha)
      rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.base.valid.toScheduleWellFormed] at hm
      exact hm
    have hc := pcsa_collectClosed_stateBefore E rho h.base y hy
      (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s))
    have hf := (h.frame y hy (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s))).1
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ h.base.valid.toScheduleWellFormed] at hc hf
    have ha : activeCompatible (V2.D.Run.stateBeforeTime E rho
        (SA.proposalTime p.toParams s) y).st C.target = true := by
      change Block.compatible C.target (eraseFG _) = true
      rw [hf]
      exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq _))
    obtain ⟨D, hd⟩ := pcsa_assemblePC_of_pool _ C hw hpool' hTarget ha
    exact (CollectClosed_def _).mp hc C.slot C.target D hTarget hd

omit [Fintype V] in
/-- A held key in the strict time reader remains held at the post-clock read. -/
theorem pcsa_formation_key_at_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (y : V) (hy : y ∈ rho.honest)
    (t : Time) (nd : Node p) (s : Slot) (B : Block)
    (hr : pcsa_postClock E rho y t = some nd)
    (hk : KeyHeld (V2.D.Run.stateBeforeTime E rho t y).st s B) : KeyHeld nd.st s B := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, hidx, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  have htick := V2.D.Run.tickIdx?_spec hidx
  have hle : V2.D.Run.idxBefore rho t ≤ k := by
    by_contra hn
    exact (lt_irrefl t) ((Gen.V2.Duty.index_lt_idxBefore_iff
      hBase.valid.toScheduleWellFormed htick t).mp (by omega))
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho t hBase.valid.toScheduleWellFormed,
    KeyHeld_def] at hk
  obtain ⟨C, hC, hs, hb⟩ := hk
  rw [KeyHeld_def]
  refine ⟨C, ?_, hs, hb⟩
  change C ∈ (clock p (V2.D.Run.stateBefore E rho k y).st t).pcs
  rw [pcsa_clock_pcs]
  exact pcsa_run_pcs_mono E rho hFrame hBase.noRestart y hy _ k hle hC

/-- Stage-2 target receipt closes the stronger frozen-PC identity input. -/
theorem pcsa_formation_frozen_pc_receipt_of_body (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hFrozenBody : ∀ x ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho x (SA.earlyTime p.toParams s) = some nd →
      ∀ C ∈ pcSnapshotAt nd.st (s - 1),
        C.target ∈ (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s)
          (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)).st.base.blocks) :
    ∀ y ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
      ∀ src, pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      ∀ C ∈ pcSnapshotAt nd.st (s - 1), frameActive p nd.st C = true →
        ∃ A ∈ src.st.pcs.filter (frameActive p src.st), A.slot = C.slot ∧ A.target = C.target := by
  intro y hy nd hr src hsrc C hC _
  let x := V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s
  have hx : x ∈ rho.honest := h.proposal.1
  have hne : SA.earlyTime p.toParams s ≠ SA.freezeTime p.toParams (s - 1) := by
    have hs : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
      have hi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
        exact_mod_cast Nat.sub_add_cancel h.slotPos
      omega
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≠ 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
    rw [hs]
    nlinarith
  obtain ⟨j, t, D, ht, hDs, hDt, hw, ha⟩ := pcsa_frozen_pc_origin_read_valid
    E rho h.base h.frame y hy (s - 1) _ nd C hr hne hC
  have hb := hFrozenBody y hy nd hr C hC
  have hk : KeyHeld (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s) x).st
      D.slot D.target := by
    rcases pcsa_formation_pc_receipt_before_proposal E rho s N ΔF h j y x t D hy hx ht ha
        with hHeld | ⟨u, _, hu, k, hh⟩
    · exact (KeyHeld_def _ _ _).mpr hHeld
    · exact pcsa_formation_key_before_proposal_of_handler E rho s N ΔF h x hx D hw k u hu hh
        (hDt.symm ▸ hb)
  have hread := pcsa_formation_key_at_read E rho h.base h.frame x hx _ src D.slot D.target hsrc hk
  obtain ⟨A, hA, has, hab⟩ := (KeyHeld_def _ _ _).mp hread
  have hReach : Reachable p src.st := by
    rw [pcsa_postClock_def] at hsrc
    obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hsrc
    rw [pcsa_preTick_def] at hp
    obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
    subst pre
    subst src
    exact Reachable.tick _ (pcsa_reachable_stateBefore E rho k x)
  have hf := pcsa_formation_frame_read E rho h.frame x _ src hx hsrc
  have hactive := pcsa_formation_frame_active_of_target p src.st A hReach hf
    (pcsa_pc_targets_held p src.st hReach A hA)
  exact ⟨A, List.mem_filter.mpr ⟨hA, hactive⟩, has.trans hDs, hab.trans hDt⟩

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}
theorem pcsa_formation_carried_presence_of_metadata (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (nd : Node p)
    (hy : y ∈ rho.honest)
    (hr : pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd)
    (hMetadata : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals)
    (hPCValid : ∀ D, N.pc = some D → pcValid nd.st D = true) :
    ∀ D, N.pc = some D →
      D ∈ (pcSnapshotAt nd.st (s - 1) ++ carriedPCs nd.st s).filter (frameActive p nd.st) := by
  obtain ⟨_, _, hslot, _⟩ := pcsa_formation_base_below_parent E rho s N ΔF h
  intro D hd
  have hm : D ∈ carriedPCs nd.st s := by
    delta carriedPCs
    apply List.mem_filter.mpr
    refine ⟨List.mem_filterMap.mpr ⟨_, hMetadata, ?_⟩, hPCValid D hd⟩
    change (if N.slot = s then N.pc else none) = some D
    have hs : N.slot = s := by
      have he : N.erase.slot = N.slot := by cases N <;> rfl
      exact he.symm.trans hslot
    rw [ite_eq_left hs, hd]
  have hb : D.target ∈ nd.st.base.blocks := by
    have hv := hPCValid D hd
    change (_ && _ && _) = true at hv
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2
  have hReach : Reachable p nd.st := by
    have hr' := hr
    rw [pcsa_postClock_def] at hr'
    obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr'
    rw [pcsa_preTick_def] at hp
    obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
    subst pre
    subst nd
    exact Reachable.tick _ (pcsa_reachable_stateBefore E rho k y)
  have ha := pcsa_formation_frame_active_of_target p nd.st D
    hReach
    (pcsa_formation_frame_read E rho h.frame y _ nd hy hr) hb
  exact List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inr hm), ha⟩

omit [DecidableEq V] [Fintype V] in
/-- The Formation delivery deadline is monotone. -/
private theorem formation_dl_mono (E : Generic.Env V) (s : Slot) :
    Monotone (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) := by
  intro a b hab
  dsimp only
  exact Int.add_le_add_right (max_le_max hab (le_refl _)) E.Δ

omit [DecidableEq V] [Fintype V] in
/-- The Formation delivery deadline is after its send time. -/
private theorem formation_dl_lt (E : Generic.Env V) (s : Slot) (t : Time) :
    t < max t (SA.freezeTime p.toParams (s - 1)) + E.Δ :=
  lt_of_le_of_lt (le_max_left t _) (lt_add_of_pos_right _ E.Δ_pos)

omit [DecidableEq V] [Fintype V] in
/-- Every event before index `k + 1` is no later than the time of event `k`. -/
private theorem formation_times_before (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (k : Nat) (e : V2.Event V (Obj p)) (hk : rho.events[k]? = some e) (T : Time)
    (hT : e.time ≤ T) :
    ∀ k' < k + 1, ∀ e', rho.events[k']? = some e' → e'.time ≤ T := by
  intro k' hk' e' he'
  have h1 := (Gen.V2.Duty.index_lt_idxBefore_iff hS hk (T + 1)).mpr
    (lt_of_le_of_lt hT (lt_add_one _))
  have h2 := (Gen.V2.Duty.index_lt_idxBefore_iff hS he' (T + 1)).mp
    (lt_of_le_of_lt (Nat.lt_succ_iff.mp hk') h1)
  exact Int.lt_add_one_iff.mp h2

/-- F1 stores each old frozen target at the proposer strictly before t_s. -/
theorem pcsa_formation_frozen_body (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) :
    ∀ x ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho x (SA.earlyTime p.toParams s) = some nd →
      ∀ C ∈ pcSnapshotAt nd.st (s - 1),
        C.target ∈ (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s)
          (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)).st.base.blocks := by
  intro x hx nd hr C hC
  have hne : SA.earlyTime p.toParams s ≠ SA.freezeTime p.toParams (s - 1) := by
    have hs : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
      have hi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
        exact_mod_cast Nat.sub_add_cancel h.slotPos
      omega
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≠ 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
    rw [hs]
    nlinarith
  obtain ⟨j, u, D, hu, _, hDt, _, ha⟩ := pcsa_frozen_pc_origin_read_valid
    E rho h.base h.frame x hx (s - 1) _ nd C hr hne hC
  obtain ⟨o, hj, _⟩ := ha.1
  have hp : (V2.D.Run.stateBefore E rho (j + 1) x).st.pcs.any
      (fun d => d.slot == D.slot && d.target == D.target) = true := ha.2.2
  obtain ⟨A, hA, hAD⟩ := List.any_eq_true.mp hp
  have hAt : A.target = D.target := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hAD).2
  have hT := pcsa_pc_targets_held p _ (pcsa_reachable_stateBefore E rho (j + 1) x) A hA
  rw [hAt, hDt] at hT
  have hdl : max (SA.freezeTime p.toParams (s - 1)) (SA.freezeTime p.toParams (s - 1)) + E.Δ =
      SA.proposalTime p.toParams s := by
    have hs : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
      have hi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
        exact_mod_cast Nat.sub_add_cancel h.slotPos
      omega
    rw [max_self, h.base.delta]
    change (4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ) + p.Δ = 4 * p.Δ * (s : Int)
    rw [hs]
    ring
  have hR := pcsa_indexed_body_within_on E rho h.base h.frame h.delivery
    (fun o r M hdec => pcsa_block_isNonRow o r M hdec) (formation_dl_mono E s)
    (formation_dl_lt E s) x _ hx h.proposal.1 (j + 1) (SA.freezeTime p.toParams (s - 1))
    (formation_times_before E rho h.base.valid.toScheduleWellFormed j _ hj _ hu)
    (by
      rw [hdl]
      have hd : (0 : Int) < p.Δ := p.deltaPos
      change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
      linarith)
    C.target hT
  rwa [hdl] at hR

omit [Fintype V] in
/-- Proposal metadata at the vote read also gives its stored body. -/
theorem pcsa_formation_vote_presence_of_metadata (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n)
    (hVoteMetadata : ∀ y ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
      (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals) :
    ∀ y ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
      N.erase ∈ nd.st.base.blocks ∧ (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals := by
  intro y hy nd hr
  have hm := hVoteMetadata y hy nd hr
  have hReach : Reachable p nd.st := by
    have hr' := hr
    rw [pcsa_postClock_def] at hr'
    obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr'
    rw [pcsa_preTick_def] at hp
    obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
    subst pre
    subst nd
    exact Reachable.tick _ (pcsa_reachable_stateBefore E rho k y)
  exact ⟨pcsa_formation_metadata_body p nd.st hReach s N hm, hm⟩

/-- The retained inputs for the actual proposer and voter reads. -/
structure FormationRetainedHeadRest (p : Params) (src dst : Node p)
    (s : Slot) (N : NamedProposal p.n) : Prop where
  hRawBack : ∀ o ∈ headVotes p dst.st s, ∀ i, GridCO.headSeat? o = some i →
    o ∈ proposerVotes src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true
  hSupportKeep : proposerSupport src.st s ⊆ headSupport p dst.st s
  hSupportBack : ∀ o ∈ headSupport p dst.st s, ∀ i, GridCO.headSeat? o = some i →
    o ∈ proposerSupport src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true
  hResolution : ∀ o ∈ proposerSupport src.st s, ∀ B,
    Gen.AC.Root.voteSupports src.st.base.blocks B o =
      Gen.AC.Root.voteSupports dst.st.base.blocks B o
  hKeep : Gen.Pure.SuffixPersists (walkBase p src.st (proposerPC p src.st)) N.erase.parent
    (erasedList src.st (fullTree p src.st))
    (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
      (voterBlocks p dst.st s)))
    (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s))
  hReflect : Gen.Pure.SuffixReflects (walkBase p src.st (proposerPC p src.st)) N.erase.parent
    (erasedList src.st (fullTree p src.st))
    (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
      (voterBlocks p dst.st s)))
    (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s))
  hUnique : ∀ B ∈ erasedList dst.st
    (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)),
    B.parent? = some N.erase.parent →
    eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s) B = true →
    B = N.erase

/-- Run inputs after the identity, carried-PC, raw-HEAD and child consumers. -/
structure FormationRunInputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) : Prop where
  hRetained : ∀ src dst y,
    pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
    y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
    pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
    FormationRetainedHeadRest p src dst s N
  hEarlyHeads : ∀ y ∈ rho.honest, ∀ nd,
    pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
    ∀ i : Fin p.n, rho.seatOf (.base (.head s)) i ∈ awakeHonestLabel p c E rho s →
      ∃ o ∈ GridCO.earlyVotes p.toParams.engine (actView nd.st) s,
        GridCO.headSeat? o = some i ∧ GridCO.resolvedHead? (actView nd.st) o = some N.erase

  hFrozenBody : ∀ x ∈ rho.honest, ∀ nd,
    pcsa_postClock E rho x (SA.earlyTime p.toParams s) = some nd →
    ∀ C ∈ pcSnapshotAt nd.st (s - 1),
      C.target ∈ (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s)
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)).st.base.blocks
  hVotePresence : ∀ y ∈ rho.honest, ∀ nd,
    pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
    N.erase ∈ nd.st.base.blocks ∧ (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals
  hEarlyPresence : ∀ y ∈ rho.honest, ∀ nd,
    pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
    (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals ∧
      ∀ D, N.pc = some D → pcValid nd.st D = true
  hAckAdmit : ∀ y ∈ rho.honest, ∀ (i : Fin p.n) j t,
    rho.seatOf (.base (.ack s)) i ∈ rho.honest →
    SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
    V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t →
    (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool


/-- The retained rest and the vote-read presence give the retained HEAD
inputs of the pre-freeze theorem. -/
theorem pcsa_formation_retained_inputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hRetained : ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
      FormationRetainedHeadRest p src dst s N)
    (hVotePresence : ∀ y ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
      N.erase ∈ nd.st.base.blocks ∧ (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals) :
    ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
      FormationRetainedHeadInputs p src dst s N := by
    intro src dst y hs hy haw hd
    have hi := hRetained src dst y hs hy haw hd
    have hPresence := hVotePresence y hy dst hd
    have hSrc := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hs
    have hslot : N.slot = s := by
      have he : N.erase.slot = N.slot := by cases N <;> rfl
      exact he.symm.trans hSrc.1
    have hRaw := pcsa_formation_raw_keep_of_metadata src.st dst.st s N hslot
      hSrc.2.2.2.1 hPresence.2
    have hReach : Reachable p dst.st := by
      have hd' := hd
      rw [pcsa_postClock_def] at hd'
      obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hd'
      rw [pcsa_preTick_def] at hp
      obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
      subst pre
      subst dst
      exact Reachable.tick _ (pcsa_reachable_stateBefore E rho k y)
    have hChild := pcsa_formation_current_body_in_voter_tree p dst.st s N.erase hReach
      (pcsa_formation_frame_read E rho h.frame y _ dst hy hd) hPresence.1 hSrc.1
    exact ⟨hRaw, hi.hRawBack, hi.hSupportKeep, hi.hSupportBack, hi.hResolution,
      hi.hKeep, hi.hReflect, hChild, hi.hUnique⟩

/-- The remaining run inputs supply all input fields of the pre-freeze theorem. -/
theorem pcsa_formation_inputs_of_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hRun : FormationRunInputs E rho s N) : FormationPreFreezeInputs E rho s N := by
  refine ⟨pcsa_formation_retained_inputs E rho s N ΔF h hRun.hRetained hRun.hVotePresence, ?_,
    pcsa_formation_frozen_pc_receipt_of_body E rho s N ΔF h hRun.hFrozenBody,
    ?_, hRun.hAckAdmit⟩
  · intro y hy nd hr i hi
    obtain ⟨o, ho, hs, hb⟩ := hRun.hEarlyHeads y hy nd hr i hi
    have hhon : rho.seatOf (.base (.head s)) i ∈ rho.honest := by
      rw [pcsa_awakeHonestLabel_def] at hi
      have hm := (Finset.mem_inter.mp hi).1
      rw [Gen.V2.Duty.awakeHonest_def] at hm
      exact (Finset.mem_filter.mp hm).1
    exact ⟨o, pcsa_formation_timely_head_of_early E rho h.base y hy _ nd hr s i hhon o ho hs,
      hs, hb⟩
  · intro y hy nd hr
    have hi := hRun.hEarlyPresence y hy nd hr
    exact pcsa_formation_carried_presence_of_metadata E rho s N ΔF h y nd hy hr hi.1 hi.2

/-- The pre-freeze conclusion now uses the exact stage-2 body and ack contracts. -/
theorem pcsa_formation_preFreeze_of_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hRun : FormationRunInputs E rho s N) :
    (∀ y H, HonestHeadAt p c E rho y s H → H = N.erase) ∧
    (∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
      holdsN p (actView nd.st) s N.erase = true) ∧
    (∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
      HonestAckAt p c E rho y s N.erase) ∧
    (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) := by
  exact pcsa_formation_preFreeze E rho s N ΔF h
    (pcsa_formation_inputs_of_run E rho s N ΔF h hRun)

/-- F1 carries every body of the proposer read to each honest vote read. -/
theorem pcsa_formation_proposer_blocks_at_vote (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hy : y ∈ rho.honest)
    (hs : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hd : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst) :
    src.st.base.blocks ⊆ dst.st.base.blocks := by
  have hS := h.base.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
    have hi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
      exact_mod_cast Nat.sub_add_cancel h.slotPos
    omega
  have hdl : max (SA.proposalTime p.toParams s) (SA.freezeTime p.toParams (s - 1)) + E.Δ =
      SA.voteTime p.toParams s := by
    rw [max_eq_left, h.base.delta]
    · rfl
    · change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int)
      rw [hs1]
      linarith
  intro B hB
  rw [pcsa_postClock_def] at hs
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hs
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, hidx, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst src
  have htick := V2.D.Run.tickIdx?_spec hidx
  have hB0 := pcsa_clock_body_scope p
    (· ∈ (V2.D.Run.stateBefore E rho k
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)).st.base.blocks)
    _ _ (fun b hb => hb) B hB
  have hR := pcsa_indexed_body_within_on E rho h.base h.frame h.delivery
    (fun o r M hdec => pcsa_block_isNonRow o r M hdec) (formation_dl_mono E s)
    (formation_dl_lt E s) _ y h.proposal.1 hy k (SA.proposalTime p.toParams s)
    (fun k' hk' => formation_times_before E rho hS k _ htick _ le_rfl k'
      (Nat.lt_succ_of_lt hk'))
    (by
      rw [hdl]
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
      linarith)
    B hB0
  rw [hdl] at hR
  rw [pcsa_postClock_def] at hd
  obtain ⟨pre, hp', hc'⟩ := Option.map_eq_some_iff.mp hd
  rw [pcsa_preTick_def] at hp'
  obtain ⟨k', hidx', he'⟩ := Option.map_eq_some_iff.mp hp'
  subst pre
  subst dst
  have htick' := V2.D.Run.tickIdx?_spec hidx'
  have hle : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ k' := by
    by_contra hn
    exact (lt_irrefl (SA.voteTime p.toParams s)) ((Gen.V2.Duty.index_lt_idxBefore_iff
      hS htick' _).mp (by omega))
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hR
  exact pcsa_body_clock_keep p _ _ (pcsa_reachable_stateBefore E rho k' y)
    (pcsa_body_stateBefore_mono E rho h.base.noRestart y hle hR)

/-- Shared honest-proposal receipt gives the proposal metadata at the vote read. -/
theorem pcsa_formation_vote_metadata (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) :
    ∀ y ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
      (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals := by
  intro y hy nd hr
  have hd : (0 : Int) < p.Δ := p.deltaPos
  exact (pcsa_honest_proposal_from_vote E rho h.base h.frame s h.slotPos N h.proposal
    h.delivery _ le_rfl (by
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
      linarith) y hy nd hr).1

/-- Shared honest-proposal receipt gives exact metadata and PC validity at `e_s`. -/
theorem pcsa_formation_early_presence (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) :
    ∀ y ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
      (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals ∧
        ∀ D, N.pc = some D → pcValid nd.st D = true := by
  have hd : (0 : Int) < p.Δ := p.deltaPos
  exact pcsa_honest_proposal_early E rho h.base h.frame s h.slotPos N h.proposal h.delivery
    (by
      change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
      linarith)

/-- The retained inputs that remain open at the actual proposer and voter reads. -/
structure FormationRetainedHeadOpen (p : Params) (src dst : Node p)
    (s : Slot) (N : NamedProposal p.n) : Prop where
  hRawBack : ∀ o ∈ headVotes p dst.st s, ∀ i, GridCO.headSeat? o = some i →
    o ∈ proposerVotes src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true
  hSupportBack : ∀ o ∈ headSupport p dst.st s, ∀ i, GridCO.headSeat? o = some i →
    o ∈ proposerSupport src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true
  hKeep : Gen.Pure.SuffixPersists (walkBase p src.st (proposerPC p src.st)) N.erase.parent
    (erasedList src.st (fullTree p src.st))
    (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
      (voterBlocks p dst.st s)))
    (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s))
  hReflect : Gen.Pure.SuffixReflects (walkBase p src.st (proposerPC p src.st)) N.erase.parent
    (erasedList src.st (fullTree p src.st))
    (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
      (voterBlocks p dst.st s)))
    (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
    (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s))
  hUnique : ∀ B ∈ erasedList dst.st
    (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)),
    B.parent? = some N.erase.parent →
    eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s) B = true →
    B = N.erase

/-- Body relay and stored metadata close support retention and resolution. -/
theorem pcsa_formation_retained_rest_of_open (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hs : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest)
    (hd : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst)
    (hOpen : FormationRetainedHeadOpen p src dst s N) :
    FormationRetainedHeadRest p src dst s N := by
  have hSrc := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hs
  have hslot : N.slot = s := by
    have he : N.erase.slot = N.slot := by cases N <;> rfl
    exact he.symm.trans hSrc.1
  have hdSrc := pcsa_reachable_headDomain_none p src.st
    (pcsa_read_reachable E rho _ _ src hs)
  have hdDst := pcsa_reachable_headDomain_none p dst.st
    (pcsa_read_reachable E rho y _ dst hd)
  have hsub := pcsa_formation_proposer_blocks_at_vote E rho s N ΔF h src dst y hy hs hd
  have hu := pcsa_read_root_unique E rho h.base y hy _ dst hd
  exact ⟨hOpen.hRawBack,
    pcsa_formation_support_keep_of_metadata src.st dst.st s N hslot hSrc.2.2.2.2
      (pcsa_formation_vote_metadata E rho s N ΔF h y hy dst hd) hdSrc hdDst hsub hu,
    hOpen.hSupportBack,
    pcsa_formation_resolution_of_blocks src.st dst.st s hdSrc hsub hu,
    hOpen.hKeep, hOpen.hReflect, hOpen.hUnique⟩

/-- Clean ack admission gives the honest ack handler pool of the pre-freeze
theorem. -/
theorem pcsa_formation_preFreeze_ack_admit (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) :
    ∀ y ∈ rho.honest, ∀ (i : Fin p.n) j t,
      rho.seatOf (.base (.ack s)) i ∈ rho.honest →
      SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t →
      (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool := by
  intro y hy i j t hi het _htz hh
  exact pcsa_honest_ack_admitted E rho h.base y hy s i N.erase.root j t hi het hh

/-- The pre-freeze premise supplies every field of `FormationPreFreezeInputs`
from three named producers. Shared body relay closes the old frozen targets
and, with stored metadata, support retention and resolution. Shared
honest-proposal receipt gives the metadata at `v_s` and `e_s`. The retained
facts make the honest HEADs exact; Formation delivery then gives early HEAD
receipt, and Clean ack admission gives the ack handler pool. The binders
are the five retained HEAD facts. -/
theorem pcsa_formation_preFreeze_inputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hRetained : ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
      FormationRetainedHeadOpen p src dst s N) :
    FormationPreFreezeInputs E rho s N := by
  have hRest := fun src dst y hs hy haw hd => pcsa_formation_retained_rest_of_open E rho s N
    ΔF h src dst y hs hy hd (hRetained src dst y hs hy haw hd)
  have hPresence := pcsa_formation_vote_presence_of_metadata E rho s N
    (pcsa_formation_vote_metadata E rho s N ΔF h)
  have hExact := pcsa_formation_head_exact_of_retained E rho s N ΔF h
    (pcsa_formation_retained_inputs E rho s N ΔF h hRest hPresence)
  exact pcsa_formation_inputs_of_run E rho s N ΔF h
    ⟨hRest, pcsa_formation_early_heads_of_exact E rho s N ΔF h hExact,
      pcsa_formation_frozen_body E rho s N ΔF h, hPresence,
      pcsa_formation_early_presence E rho s N ΔF h,
      pcsa_formation_preFreeze_ack_admit E rho s N ΔF h⟩

/-- Formation parts 1–4 from the pre-freeze premise and the three named producers. -/
theorem pcsa_formation_preFreeze_of_prem (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hRetained : ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
      FormationRetainedHeadOpen p src dst s N) :
    (∀ y H, HonestHeadAt p c E rho y s H → H = N.erase) ∧
    (∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
      holdsN p (actView nd.st) s N.erase = true) ∧
    (∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
      HonestAckAt p c E rho y s N.erase) ∧
    (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) :=
  pcsa_formation_preFreeze E rho s N ΔF h
    (pcsa_formation_preFreeze_inputs E rho s N ΔF h hRetained)

end AvailableChain.PCSA.Run
end
