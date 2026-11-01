module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationInputs
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths
public import AvailableChainPCSAProofs.Proofs.Clean.CommonTree
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalPaths
public import AvailableChainPCSAProofs.Proofs.Clean.BodyRelayTime
public import AvailableChainPCSAProofs.Proofs.Shared.BodyRelay

public section

/-! The retained HEAD walk facts from the two back receipts. Equal
eligibility comes from root-mode receipt. hKeep then needs only the proposal
path. Formation body relay puts each frozen voter-tree body in the proposer
tree, and the other voter-tree bodies are prefixes of the proposal. With
equal eligibility, this gives hReflect and hUnique. The two back receipts
stay open (`FormationRetainedBackOpen`). -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

private theorem retained_parent_prefix (A C : Block) (h : C.parent? = some A) :
    Block.Preceq A C := by
  cases C with
  | genesis => cases h
  | node P s root body =>
    change some P = some A at h
    cases Option.some.inj h
    change (decide (_ = _) || Block.preceq _ _) = true
    exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_refl _))

private theorem retained_erase_parent (N : NamedProposal p.n) (hs : N.erase.slot ≠ 0) :
    N.erase.parent? = some N.erase.parent := by
  cases N with
  | genesis => exact (hs rfl).elim
  | node P slot root body raw support rows pc => rfl

/-- Root-mode receipt makes stage-1 eligibility equal at the proposer and
voter reads. -/
theorem pcsa_formation_retained_eligible_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst)
    (hRawBack : ∀ o ∈ headVotes p dst.st s, ∀ i, GridCO.headSeat? o = some i →
      o ∈ proposerVotes src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true)
    (hSupportBack : ∀ o ∈ headSupport p dst.st s, ∀ i, GridCO.headSeat? o = some i →
      o ∈ proposerSupport src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true) :
    eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s) =
      eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s) := by
  have hInputs := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hSrc
  have hslot : N.slot = s := by
    have he : N.erase.slot = N.slot := by cases N <;> rfl
    exact he.symm.trans hInputs.1
  have hMeta := pcsa_formation_vote_metadata E rho s N ΔF h y hy dst hDst
  have hdSrc := pcsa_reachable_headDomain_none p src.st
    (pcsa_read_reachable E rho _ _ src hSrc)
  have hdDst := pcsa_reachable_headDomain_none p dst.st
    (pcsa_read_reachable E rho y _ dst hDst)
  have hsub := pcsa_formation_proposer_blocks_at_vote E rho s N ΔF h src dst y hy hSrc hDst
  have hu := pcsa_read_root_unique E rho h.base y hy _ dst hDst
  have hCounts := pcsa_formation_root_merge_counts p src.st dst.st
    (proposerVotes src.st s) (proposerSupport src.st s) (headVotes p dst.st s)
    (headSupport p dst.st s)
    (pcsa_formation_raw_keep_of_metadata src.st dst.st s N hslot hInputs.2.2.2.1 hMeta)
    hRawBack
    (pcsa_formation_support_keep_of_metadata src.st dst.st s N hslot hInputs.2.2.2.2 hMeta
      hdSrc hdDst hsub hu)
    hSupportBack (pcsa_formation_resolution_of_blocks src.st dst.st s hdSrc hsub hu)
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hsSlot : src.st.slot p = s := pcsa_formation_read_slot E rho _ _ s 0 src hSrc
    (by rw [add_zero]; rfl) le_rfl (by omega)
  have hdSlot : dst.st.slot p = s := pcsa_formation_read_slot E rho y _ s p.Δ dst hDst
    rfl (le_of_lt hΔ) (by omega)
  exact pcsa_formation_eligible_eq_of_scores p src.st dst.st _ _ _ _
    (pcsa_formation_frame_read E rho h.frame _ _ src h.proposal.1 hSrc)
    (pcsa_formation_frame_read E rho h.frame y _ dst hy hDst)
    (hsSlot.trans hdSlot.symm) hCounts.1 hCounts.2

/-- Equal eligibility and the proposal path give hKeep. -/
theorem pcsa_formation_retained_keep (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst)
    (hEq : eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s) =
      eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)) :
    Gen.Pure.SuffixPersists (walkBase p src.st (proposerPC p src.st)) N.erase.parent
      (erasedList src.st (fullTree p src.st))
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s)
        (proposerSupport src.st s))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)) := by
  have hInputs := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hSrc
  have hPN := retained_parent_prefix _ _
    (retained_erase_parent N (hInputs.1.trans_ne (Nat.ne_of_gt h.slotPos)))
  have hm := (pcsa_formation_vote_presence_of_metadata E rho s N
    (pcsa_formation_vote_metadata E rho s N ΔF h) y hy dst hDst).1
  rw [Gen.Pure.SuffixPersists_def]
  intro X C _ _ hstep hC
  obtain ⟨_, _, he⟩ := GridCO.ghostStep_child _ _ _ X C hstep
  refine ⟨?_, by rw [← hEq]; exact he⟩
  rw [pcsa_postClock_def] at hDst
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hDst
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, _, he'⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst dst
  exact pcsa_proposal_prefix_voter_mem E rho h.frame k y hy _ s N.erase C hm hInputs.1
    (Gen.Pure.block_preceq_trans hC hPN)

/-- Equal eligibility and tree inclusion give hReflect and hUnique. The
source walk ends at the proposal parent, so no source child of it is
eligible. -/
theorem pcsa_formation_retained_reflect_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hEq : eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s) =
      eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s))
    (hTree : ∀ C ∈ erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)),
      C = N.erase ∨ C ∈ erasedList src.st (fullTree p src.st)) :
    Gen.Pure.SuffixReflects (walkBase p src.st (proposerPC p src.st)) N.erase.parent
      (erasedList src.st (fullTree p src.st))
      (erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s))
      (eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s)) ∧
    ∀ B ∈ erasedList dst.st
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st s)),
      B.parent? = some N.erase.parent →
      eligible p dst.st (headVotes p dst.st s) (headSupport p dst.st s) B = true →
      B = N.erase := by
  have hInputs := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hSrc
  have hParent := retained_erase_parent N (hInputs.1.trans_ne (Nat.ne_of_gt h.slotPos))
  have hb : walkBase p src.st (proposerPC p src.st) =
      ((proposerPC p src.st).map PC.target).getD (eraseFG (controls p src.st).Z) := by
    cases hv : proposerPC p src.st with
    | none => rfl
    | some C =>
      have hm : C ∈ src.st.pcs.filter (frameActive p src.st) := bestPC_mem _ C hv
      change (if frameActive p src.st C then C.target else _) = C.target
      rw [ite_eq_left (List.mem_filter.mp hm).2]
  have hGhost : GridCO.ghost (walkBase p src.st (proposerPC p src.st))
      (erasedList src.st (fullTree p src.st))
      (GridCO.goldfishScore src.st.base.blocks (proposerVotes src.st s)
        (proposerSupport src.st s))
      (eligible p src.st (proposerVotes src.st s) (proposerSupport src.st s)) =
      N.erase.parent := by
    rw [hb, hInputs.2.1]
    exact pcsa_formation_proposer_base_walk E rho s N ΔF h src hSrc
  have hroot := pcsa_formation_read_root_injective E rho h.base _ _ src h.proposal.1 hSrc
    (fullTree p src.st)
  have hclosed : Gen.Pure.AnchorClosed (walkBase p src.st (proposerPC p src.st))
      (erasedList src.st (fullTree p src.st)) := by
    rw [Gen.Pure.AnchorClosed_def]
    intro B hB _ A _ hAB
    rw [pcsa_postClock_def] at hSrc
    obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hSrc
    rw [pcsa_preTick_def] at hp
    obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
    subst pre
    subst src
    exact pcsa_full_read_prefix_mem E rho h.frame k _ h.proposal.1 _ B A
      (List.mem_filter.mp hB).1 hAB
  constructor
  · rw [Gen.Pure.SuffixReflects_def]
    intro X C _ hXp hC hpar hel
    rcases hTree C hC with rfl | hc
    · rw [hParent] at hpar
      cases Option.some.inj hpar
      change (!decide (_ = _) && Block.preceq _ _) = true at hXp
      simp at hXp
    · exact ⟨hc, by rw [hEq]; exact hel⟩
  · intro B hB hpar hel
    rcases hTree B hB with hb' | hc
    · exact hb'
    · rw [← hGhost] at hpar
      have hn := Gen.Pure.walk_noEligibleChild_of_anchorClosed _ _ _ _ hroot hclosed B hc hpar
      rw [← hEq, hn] at hel
      cases hel

/-- Formation body relay: a body stamped before `z_{s-1}` at an honest read is
held at the actual proposer tick. -/
theorem pcsa_formation_frozen_body_in_proposer (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (a k : Nat) (y : V) (hy : y ∈ rho.honest)
    (v : Time)
    (hk : rho.events[k]? = some (.tick
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s)))
    (C : Block) (hm : C ∈ (clock p (V2.D.Run.stateBefore E rho a y).st v).base.blocks)
    (hs : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a y).st v).base C <
      SA.freezeTime p.toParams (s - 1)) :
    C ∈ (V2.D.Run.stateBefore E rho k
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)).st.base.blocks := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
    have hi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by
      exact_mod_cast Nat.sub_add_cancel h.slotPos
    omega
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams (s - 1)) := by
    refine ⟨4 * (s - 1) + 3, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ = ((4 * (s - 1) + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hzero : 0 ≤ SA.freezeTime p.toParams (s - 1) := by
    change 0 ≤ 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
    positivity
  have hdl : SA.freezeTime p.toParams (s - 1) + E.Δ = SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ + p.Δ = 4 * p.Δ * (s : Int)
    rw [hs1]
    ring
  have hcut : SA.proposalTime p.toParams s ≤ SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith
  rw [pcsa_clock_blocks] at hm
  by_cases hg : C = .genesis
  · rw [hg]
    exact (pcsa_genesis_body_stamp E rho h.base.noRestart k _).1
  have hs' : GridCO.stampBlock (V2.D.Run.stateBefore E rho a y).st.base C <
      SA.freezeTime p.toParams (s - 1) := by
    have hse : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a y).st v).base C =
        GridCO.stampBlock (V2.D.Run.stateBefore E rho a y).st.base C := by
      obtain ⟨row, hr⟩ := pcsa_body_stamp_lookup E rho a y C hm
      delta GridCO.stampBlock
      rw [pcsa_clock_bodyStamps, hr]
      rfl
    rwa [hse] at hs
  obtain ⟨j, _, t, o, s', N', P, hev, htz, hd, hNB, hP, hacc, hAcc⟩ :=
    pcsa_body_accepted_before E rho h.base a y C _ hpub hzero hg hm hs'
  have hmax : max t (SA.freezeTime p.toParams (s - 1)) + E.Δ =
      SA.proposalTime p.toParams s := by
    rw [max_eq_right (le_of_lt htz), hdl]
  have hR := pcsa_body_relay_within_on E rho h.base h.frame h.delivery j y _ hy
    h.proposal.1 t o s' N' P hev hd hP hacc hAcc (pcsa_block_isNonRow o s' N' hd)
    (lt_of_le_of_lt (le_max_left t _) (lt_add_of_pos_right _ E.Δ_pos))
    (by
      rw [hmax]
      exact hcut)
  change N'.erase ∈ (V2.D.Run.stateBeforeTime E rho
    (max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) _).st.base.blocks at hR
  rw [hmax, hNB, ← Gen.V2.Duty.stateBefore_idxBefore E rho _
    h.base.valid.toScheduleWellFormed] at hR
  have hle : V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hn
    exact lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff
      h.base.valid.toScheduleWellFormed hk _).mp hn)
  exact pcsa_body_stateBefore_mono E rho h.base.noRestart _ hle hR

/-- Each voter-tree body at `v_s` is the proposal or a proposer-tree body.
Formation body relay carries the frozen bodies to the proposer by `t_s`. The
other bodies are prefixes of the unique slot-`s` body. -/
theorem pcsa_formation_retained_tree (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst) :
    ∀ C ∈ erasedList dst.st (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg
        (voterBlocks p dst.st s)),
      C = N.erase ∨ C ∈ erasedList src.st (fullTree p src.st) := by
  have hInputs := pcsa_formation_proposer_read_inputs E rho s N ΔF h src hSrc
  have hp : N.parent.erase = getHead p src.st (proposerPC p src.st)
      (proposerVotes src.st s) (proposerSupport src.st s) := by
    have he : N.erase.parent = N.parent.erase := by cases N <;> rfl
    rw [← he]
    exact hInputs.2.1
  rw [pcsa_postClock_def] at hSrc hDst
  obtain ⟨pre, hpre, hc⟩ := Option.map_eq_some_iff.mp hSrc
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, hidx, he⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst src
  obtain ⟨pre', hpre', hc'⟩ := Option.map_eq_some_iff.mp hDst
  rw [pcsa_preTick_def] at hpre'
  obtain ⟨a, _, he'⟩ := Option.map_eq_some_iff.mp hpre'
  subst pre'
  subst dst
  have htick := V2.D.Run.tickIdx?_spec hidx
  have hReach := Reachable.tick (SA.voteTime p.toParams s) (pcsa_reachable_stateBefore E rho a y)
  intro C hC
  obtain ⟨hm, hnamed⟩ := List.mem_filter.mp hC
  obtain ⟨D, hDmem, hDC⟩ := of_decide_eq_true hnamed
  have hDv := ((KitFG.mem_filteredFromView (FGSA.heightView p) _ _ D).mp hDmem).1
  rcases Bool.or_eq_true_iff.mp (Finset.mem_filter.mp hDv).2 with hfreeze | hancestor
  · right
    have hs : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a y).st
        (SA.voteTime p.toParams s)).base C < SA.freezeTime p.toParams (s - 1) := by
      rw [← hDC]
      exact of_decide_eq_true hfreeze
    have hb := pcsa_formation_frozen_body_in_proposer E rho s N ΔF h a k y hy _ htick C hm hs
    exact pcsa_full_read_prefix_mem E rho h.frame k _ h.proposal.1 _ C C
      (pcsa_body_clock_keep p _ _ (pcsa_reachable_stateBefore E rho k _) hb)
      (Gen.Pure.block_preceq_refl _)
  · obtain ⟨P, hP, hslot, hDP⟩ := of_decide_eq_true hancestor
    have hbody : eraseFG P ∈ (V2.D.Run.stateBefore E rho a y).st.base.blocks := by
      have hb := (pcsa_tree_correspondence p _ hReach (eraseFG P)).mpr ⟨P, hP, rfl⟩
      rwa [pcsa_clock_blocks] at hb
    have hslot' : (eraseFG P).slot = s := by
      have he : (eraseFG P).slot = P.slot := by cases P <;> rfl
      exact he.trans hslot
    have hPN := pcsa_honest_slot_body_unique E rho h.base a y s h.slotPos N h.proposal.1
      h.proposal.2 (eraseFG P) hbody hslot'
    have hCN : Block.Preceq C N.erase := by
      rw [← hPN, ← hDC]
      simpa only [pcsa_eraseFG_eq] using (FGSA.eraseFG_preceq_iff.mpr hDP)
    by_cases hn : C = N.erase
    · exact Or.inl hn
    · exact Or.inr (pcsa_proposal_proper_prefix_source E rho h.base h.frame k _ h.proposal.1
        s N hp C hCN hn)

/-- The two retained HEAD inputs that stay open: the voter raw and support
HEADs are proposer HEADs, or their seat is capped at the proposer. -/
structure FormationRetainedBackOpen (p : Params) (src dst : Node p)
    (s : Slot) (N : NamedProposal p.n) : Prop where
  hRawBack : ∀ o ∈ headVotes p dst.st s, ∀ i, GridCO.headSeat? o = some i →
    o ∈ proposerVotes src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true
  hSupportBack : ∀ o ∈ headSupport p dst.st s, ∀ i, GridCO.headSeat? o = some i →
    o ∈ proposerSupport src.st s ∨ GridCO.equivocates (proposerVotes src.st s) i = true

/-- The two back receipts give the retained HEAD facts. -/
theorem pcsa_formation_retained_open_of_back (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (src dst : Node p) (y : V)
    (hSrc : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src)
    (hy : y ∈ rho.honest)
    (hDst : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst)
    (hBack : FormationRetainedBackOpen p src dst s N) :
    FormationRetainedHeadOpen p src dst s N := by
  have hEq := pcsa_formation_retained_eligible_eq E rho s N ΔF h src dst y hSrc hy hDst
    hBack.hRawBack hBack.hSupportBack
  have hRU := pcsa_formation_retained_reflect_unique E rho s N ΔF h src dst hSrc hEq
    (pcsa_formation_retained_tree E rho s N ΔF h src dst y hSrc hy hDst)
  exact ⟨hBack.hRawBack, hBack.hSupportBack,
    pcsa_formation_retained_keep E rho s N ΔF h src dst y hSrc hy hDst hEq, hRU.1, hRU.2⟩

/-- The pre-freeze inputs from the premise and the two back receipts. -/
theorem pcsa_formation_preFreeze_inputs_of_back (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hBack : ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
      FormationRetainedBackOpen p src dst s N) :
    FormationPreFreezeInputs E rho s N :=
  pcsa_formation_preFreeze_inputs E rho s N ΔF h (fun src dst y hs hy haw hd =>
    pcsa_formation_retained_open_of_back E rho s N ΔF h src dst y hs hy hd
      (hBack src dst y hs hy haw hd))

end AvailableChain.PCSA.Run
end
