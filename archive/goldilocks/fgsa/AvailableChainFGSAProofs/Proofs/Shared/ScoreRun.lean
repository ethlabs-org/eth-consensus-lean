module
public import AvailableChainFGSA.Proofs.Head.Score
public import AvailableChainFGSA.Proofs.Port.Tree
public import AvailableChainFGSA.Proofs.Head.Walk -- shake: keep (prefix lift)
public import AvailableChainFGSARun.Proofs.RootResolution
public import AvailableChainFGSARun.Proofs.ReadFacts

public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G25; blueprint 03:293–295.
DC: Goldfish/ProposalSnapshotBridge.lean:139–155, candidate transport.
INTENTIONAL: FG-SA has two active floors. The consumer supplies their
bounds at the proposal and HEAD reads; no ordering between them is required. -/
structure ScoreRunGeometry {n : Nat} (src dst : State n) (D : Block) : Prop where
  source_floor : Block.Preceq (eraseFG src.fg.F) D
  target_floor : Block.Preceq (eraseFG dst.fg.F) D

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G11; blueprint 03:249–253,350–359,367–373.
DC: Goldfish/ProposalWalkTransportCore.lean:172–180, anchors and path.
INTENTIONAL: the two FG-SA walks can have different roots and floors.
The comparison prefixes are consumer geometry over the canonical frames;
the suffix domains follow from the Z and height bounds with internal witnesses. -/
structure WalkRunGeometry (p : Params) (src dst : State p.n)
    (s : Slot) (D : FGBlock (Fin p.n)) : Prop
    extends ScoreRunGeometry src dst (eraseFG D) where
  source_Z : FGBlock.Preceq (controls p src).Z D
  target_Z : FGBlock.Preceq (controls p dst).Z D
  source_lo : (controls p src).lo ≤ hOf p.E p.cfg D
  target_lo : (controls p dst).lo ≤ hOf p.E p.cfg D
  source_anchor : Block.Preceq (liveRoot p src) (eraseFG D)
  target_anchor : Block.Preceq (liveRoot p dst) (eraseFG D)
  source_prefix : Gen.Pure.DominatedSuffix (liveRoot p src) (eraseFG D)
    (erasedList src (fullTree p src))
    (GridCO.goldfishScore src.base.blocks (proposerVotes src s) (proposerSupport src s))
    (eligible p src (proposerVotes src s) (proposerSupport src s))
  target_prefix : Gen.Pure.DominatedSuffix (liveRoot p dst) (eraseFG D)
    (erasedList dst (filteredFrom p.E p.cfg (controls p dst) (voterBlocks p dst s)))
    (GridCO.goldfishScore dst.base.blocks (headVotes p dst s) (headSupport p dst s))
    (eligible p dst (headVotes p dst s) (headSupport p dst s))

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem scoreRun_lift_raw {n : Nat} (xs : List (GridCO.Wire n .root)) (s : Slot)
    (hl : ∀ o ∈ xs, GridCO.headLabel? o = some s) :
    (xs.filterMap liftHead?).map baseVote = xs := by
  induction xs with
  | nil => rfl
  | cons o xs ih =>
    have ho := hl o (List.mem_cons_self ..)
    have ht := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
    rcases o with ⟨auth, payload⟩
    cases auth <;> cases payload <;> try contradiction
    change some _ = some s at ho
    cases ho
    change _ :: (xs.filterMap liftHead?).map baseVote = _ :: xs
    rw [ht]
    rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b G25; blueprint 03:279–283.
DC: Goldfish/ProposalSnapshotBridge.lean:29,42,55, proposal snapshot identities.
INTENTIONAL: the wire encoding preserves the actual FG-SA proposal pools.
The proposal's row list is kept opaque; only its vote fields are projected. -/
theorem fgsa_scoreRun_proposal_pools (p : Params) (st : State p.n) (s : Slot)
    (a : Nat) (N : NamedProposal p.n)
    (he : (propose p st s).map (withApp p a) = some (.proposal N)) :
    N.erase.slot = s ∧ N.raw.map baseVote = proposerVotes st s ∧
      N.support.map baseVote = proposerSupport st s := by
  have hl : ∀ o ∈ proposerVotes st s, GridCO.headLabel? o = some (s - 1) := by
    intro o ho
    exact beq_iff_eq.mp (List.mem_filter.mp ho).2
  have hls : ∀ o ∈ proposerSupport st s, GridCO.headLabel? o = some (s - 1) := by
    intro o ho
    exact hl o (List.mem_filter.mp ho).1
  unfold propose at he
  split at he
  · cases he
  · simp only [Option.map_map] at he
    obtain ⟨P, _, he⟩ := Option.map_eq_some_iff.mp he
    cases Msg.proposal.inj he
    exact ⟨rfl, scoreRun_lift_raw _ _ hl, scoreRun_lift_raw _ _ hls⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G25; blueprint 03:279–283.
DC: Goldfish/ProposalSnapshotBridge.lean:144, `raw_subset`.
INTENTIONAL: authenticate the complete stored FG-SA proposal before using
its carried metadata. The row list is passed as an opaque value. -/
theorem fgsa_scoreRun_stored_proposal_eq
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot)
    (N : NamedProposal p.n)
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho i x).st.proposals)
    (hh : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ ∈ rho.honest)
    (o : Obj p) (ha : o.auth = .seat (.prop s) ⟨0, Nat.one_pos⟩)
    (he : ∃ t, V2.D.Run.emits E rho (rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩) o t) :
    (⟨.proposer s, .proposal N⟩ : Wire p.n) = toWire p o := by
  obtain ⟨j, u, t, -, hd, hu, -, -⟩ := stored_proposal_delivered E rho i x _ hw
  have hua : u.auth = .seat (.prop s) ⟨0, Nat.one_pos⟩ := by
    have hu' : u = ofWire p ⟨.proposer s, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire, hu]
    rw [hu']
    rfl
  have heq := Gen.V2.Duty.honest_unique_singleDuty_statement E rho hE.nodup
    hE.toUnforgeableSignatures (fgsaHooks p c).handles_carries
    (.prop s) (fgsa_prop_singleDuty s) ⟨0, Nat.one_pos⟩ hh u o hua ha
    (Or.inr ⟨j, x, t, u, hd, Or.inl rfl⟩) (Or.inl he)
  exact hu.symm.trans (congrArg (toWire p) heq)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G25; blueprint 03:279–283.
DC: Goldfish/ProposalSnapshotBridge.lean:144, `raw_subset`.
INTENTIONAL: the admitted proposal metadata persists to the actual
post-clock HEAD read, even if an individual carried vote was refused. -/
theorem fgsa_scoreRun_metadata_retained_restart
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i j : Nat} (hij : i ≤ j) (x : V)
    (w : Wire p.n) (hw : w ∈ (V2.D.Run.stateBefore E rho i x).st.proposals)
    (s : Slot) :
    w ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho j x).st
      (SA.voteTime p.toParams s)).proposals := by
  rw [clock_proposals]
  exact (fgsa_store_durable p c E rho hij x).2.2.1.subset hw

theorem fgsa_scoreRun_metadata_retained
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) (x : V)
    (w : Wire p.n) (hw : w ∈ (V2.D.Run.stateBefore E rho i x).st.proposals)
    (s : Slot) :
    w ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho j x).st
      (SA.voteTime p.toParams s)).proposals := by
  rw [clock_proposals]
  exact (fgsa_store_cumulative p c E rho hN hij x).2.2.2.2.1.subset hw

private theorem scoreRun_retained_tree (p : Params) (st : State p.n)
    (h : CStoreInv p st) (B : Block) (hb : B ∈ st.base.blocks)
    (hF : Block.Preceq (eraseFG st.fg.F) B) :
    ∃ A ∈ Next.tree p st, eraseFG A = B := by
  obtain ⟨A, hA, rfl⟩ := (h.baseTree B).mp hb
  exact ⟨A, (Next.mem_tree p st A).mpr ⟨hA, eraseFG_preceq_iff.mp hF⟩, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G25; blueprint 03:279–283.
DC: Goldfish/ProposalSnapshotBridge.lean:144, `raw_subset`.
INTENTIONAL: literal inclusion comes from stored proposal metadata, not
from successful admission of each carried vote. Rows remain opaque. -/
theorem fgsa_scoreRun_carried_raw_subset (p : Params) (st : State p.n)
    (s : Slot) (N : NamedProposal p.n)
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ st.proposals)
    (hs : N.erase.slot = s)
    (hret : ∃ B ∈ Next.tree p st, eraseFG B = N.erase)
    (hl : ∀ o ∈ N.raw.map baseVote, GridCO.headLabel? o = some (s - 1)) :
    N.raw.map baseVote ⊆ headVotes p st s := by
  intro o ho
  change o ∈ List.eraseDups (_ ++ _)
  rw [List.mem_eraseDups, List.mem_append]
  apply Or.inr
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨(N.raw, N.support), ?_, ho⟩, ?_⟩
  · apply List.mem_filterMap.mpr
    refine ⟨⟨.proposer s, .proposal N⟩, hw, ?_⟩
    change (if N.slot = s ∧ ∃ B ∈ Next.tree p st, eraseFG B = N.erase then
      some (N.raw, N.support) else none) = some (N.raw, N.support)
    rw [ite_eq_left ⟨by simpa only [named_erase_slot] using hs, hret⟩]
  · simpa only [beq_iff_eq] using hl o ho

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G25; blueprint 03:279–283.
DC: Goldfish/ProposalSnapshotBridge.lean:144, `raw_subset`.
INTENTIONAL: authenticate an admitted slot-s proposal against the actual
proposal tick, retain its metadata, and project its original N.raw pool.
All proposal row lists are opaque. No delivery premise is needed for this arm. -/
theorem fgsa_scoreRun_raw_subset_restart
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot) {ip ia ih : Nat} {x y : V}
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hx : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (hh : x ∈ rho.honest) (horder : ia ≤ ih)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (M : NamedProposal p.n)
    (hadm : (⟨.proposer s, .proposal M⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho ia y).st.proposals)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase) :
    proposerVotes (FGSA.clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams s)) s ⊆
    headVotes p (FGSA.clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)) s := by
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2
  have heq := fgsa_scoreRun_stored_proposal_eq E rho hE ia y s M
    hadm (hx ▸ hh) _ rfl ⟨_, by rw [hx]; exact ⟨ip, hip, hem⟩⟩
  have hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho ia y).st.proposals := by
    rw [heq] at hadm
    exact hadm
  have hkeep := fgsa_scoreRun_metadata_retained_restart E rho horder y _ hw s
  rw [← pools.2.1]
  have hInv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y)
    (SA.voteTime p.toParams s)
  have hMeta := metaInv_clock p _ (metaInv_stateBefore E rho ih y)
    (SA.voteTime p.toParams s)
  have hheld := wire_block_mem p _ hInv hMeta hkeep (block?_proposal s N)
  apply fgsa_scoreRun_carried_raw_subset p _ s N hkeep pools.1
    (scoreRun_retained_tree p _ hInv _ hheld hFN)
  intro o ho
  rw [pools.2.1] at ho
  exact beq_iff_eq.mp (List.mem_filter.mp ho).2

theorem fgsa_scoreRun_raw_subset
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (s : Slot) {ip ia ih : Nat} {x y : V}
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hx : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (hh : x ∈ rho.honest) (horder : ia ≤ ih)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (M : NamedProposal p.n)
    (hadm : (⟨.proposer s, .proposal M⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho ia y).st.proposals)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase) :
    proposerVotes (FGSA.clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams s)) s ⊆
    headVotes p (FGSA.clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)) s := by
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2
  have heq := fgsa_scoreRun_stored_proposal_eq E rho hE ia y s M
    hadm (hx ▸ hh) _ rfl ⟨_, by rw [hx]; exact ⟨ip, hip, hem⟩⟩
  have hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho ia y).st.proposals := by
    rw [heq] at hadm
    exact hadm
  have hkeep := fgsa_scoreRun_metadata_retained E rho hN horder y _ hw s
  rw [← pools.2.1]
  have hInv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y)
    (SA.voteTime p.toParams s)
  have hMeta := metaInv_clock p _ (metaInv_stateBefore E rho ih y)
    (SA.voteTime p.toParams s)
  have hheld := wire_block_mem p _ hInv hMeta hkeep (block?_proposal s N)
  apply fgsa_scoreRun_carried_raw_subset p _ s N hkeep pools.1
    (scoreRun_retained_tree p _ hInv _ hheld hFN)
  intro o ho
  rw [pools.2.1] at ho
  exact beq_iff_eq.mp (List.mem_filter.mp ho).2

private theorem scoreRun_stored_label (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot)
    (N : NamedProposal p.n)
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho i x).st.proposals) : s = N.erase.slot := by
  obtain ⟨j, u, t, -, hd, hu, -, -⟩ := stored_proposal_delivered E rho i x _ hw
  have hf := hE.wire j x u t hd
  change FGSA.wellFormed p (toWire p u) = true at hf
  rw [hu] at hf
  exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).1).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G25; blueprint 03:279–283.
DC: Goldfish/ProposalSnapshotBridge.lean:115–124, `carried_raw_subset_voter_view`.
INTENTIONAL: authentication identifies every admitted slot-s metadata pair
with the actual signed proposal. The opaque row lists are never inspected. -/
theorem fgsa_scoreRun_proposalsAt_eq
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot)
    (N : NamedProposal p.n)
    (hh : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ ∈ rho.honest)
    (he : ∃ t, V2.D.Run.emits E rho (rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩)
      ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ t) :
    ∀ q ∈ proposalsAt (V2.D.Run.stateBefore E rho i x).st s, q = (N.raw, N.support) := by
  intro q hq
  obtain ⟨w, hw, hd⟩ := List.mem_filterMap.mp hq
  obtain ⟨r, M, rfl, -⟩ := (metaInv_stateBefore E rho i x).wireTree w hw
  change (if M.slot = s ∧
      ∃ B ∈ Next.tree p (V2.D.Run.stateBefore E rho i x).st, eraseFG B = M.erase then
    some (M.raw, M.support) else none) = some q at hd
  split at hd
  · rename_i hs
    have hr := scoreRun_stored_label E rho hE i x r M hw
    have hrs : r = s := (by simpa only [named_erase_slot] using hr : r = M.slot).trans hs.1
    rw [hrs] at hw
    have heq := fgsa_scoreRun_stored_proposal_eq E rho hE i x s M hw hh _ rfl he
    have hp := congrArg Signed.payload heq
    change Msg.proposal M = Msg.proposal N at hp
    cases Msg.proposal.inj hp
    exact (Option.some.inj hd).symm
  · cases hd

private theorem scoreRun_votes_mono (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) (x : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i x).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho j x).st.base.votes :=
  fgsa_votes_cumulative_on p c E rho hij x (hN.restartFree x i j)

private theorem scoreRun_proposal_window (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams s)))
    (d : Time) (hd : d ≤ SA.proposalTime p.toParams s) :
    (V2.D.Run.stateBeforeTime E rho d x).st.slot p ≤ s := by
  have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hN
    (fgsa_idxBefore_mono rho hd) x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho d) x),
    fgsa_clock_now p c (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s)) x)] at hm
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho d hS,
    Gen.V2.Duty.stateBefore_idxBefore E rho _ hS,
    ← fgsa_preTick_eq_timeRead E rho hS hN hi] at hm
  have hb := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c)
    E rho hS hi x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x)] at hb
  have hs := Internal.slotOf_mono (p := p) (hm.trans hb)
  have he : p.slotOf (SA.proposalTime p.toParams s) = s :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_proposal_slot (c := c) _ s)
  exact hs.trans_eq he

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G25 N1; blueprint 03:285–291.
DC: Handlers/GoldfishVotePool.lean:755,791 and
Goldfish/ProposalSnapshotBridge.lean:145, `raw_extra_equiv`.
INTENTIONAL: relay a frozen FG-SA raw vote into the actual proposal pool,
with the N1 pair (t_s - Δ, v_s). A deadline equal to t_s is sufficient:
the receipt is in the strict-before state. No strict local deadline is assumed.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_scoreRun_frozen_vote_relay
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.voteTime p.toParams (s + 1)))
    {ip : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (k : Nat) (seat : Fin p.n) (B : BlockId)
    (hm : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k y).st.base.votes)
    (ht : GridCO.stampVote (V2.D.Run.stateBefore E rho k y).st.base
      ⟨.seat s seat, .head B⟩ < SA.freezeTime p.toParams s) :
    let U := proposerVotes (FGSA.clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams (s + 1))) (s + 1)
    (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n .root) ∈ U ∨ GridCO.equivocates U seat = true := by
  intro U
  have hz : SA.freezeTime p.toParams s = SA.proposalTime p.toParams (s + 1) - p.Δ := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) - p.Δ
    push_cast
    ring
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = _
    push_cast
    ring
  have hzero : 0 ≤ SA.freezeTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    positivity
  obtain ⟨j, -, t, ha, htz⟩ := fgsa_vote_accepted_before E rho hE
    hN k y s seat B _ hpub hzero hm ht
  obtain ⟨dl, cut, hD, -, hlt, hb, -, hcut, -⟩ := hSync
  have hd : dl t ≤ SA.proposalTime p.toParams (s + 1) := by
    have hb := hb t
    rw [← hz, max_eq_right (le_of_lt htz), hDelta, hz] at hb
    linarith
  have hpv : SA.proposalTime p.toParams (s + 1) ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    linarith [p.deltaPos]
  have hT : Gen.V2.Duty.Trigger E rho
      (ofHead p ⟨.seat (.head s) seat, B⟩) t :=
    Or.inr ⟨y, hy, j, ha⟩
  have hr := fgsa_head_receipt E rho hDelta hE hN dl cut s seat B t x hD
    hT hx (hd.trans (hpv.trans hcut)) (hlt t)
    (scoreRun_proposal_window E rho hE.toScheduleWellFormed hN hip (dl t) hd)
    (hd.trans (hE.in_horizon _ (List.mem_of_getElem? hip)).2)
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hip hx
      (fgsa_trigger_nonneg E rho hE.toScheduleWellFormed hT) hd)
  have hkeep : (V2.D.Run.stateBeforeTime E rho (dl t) x).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho ip x).st.base.votes := by
    rw [fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hip,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed]
    exact scoreRun_votes_mono E rho hN x (fgsa_idxBefore_mono rho hd)
  have hin (o : GridCO.Wire p.n .root)
      (ho : o ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.base.votes)
      (hl : GridCO.headLabel? o = some s) : o ∈ U := by
    apply List.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [(clock_vn _ _).1]
      exact hkeep ho
    · simpa only [Nat.add_sub_cancel, beq_iff_eq] using hl
  rcases hr with hr | ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, -, -⟩
  · exact Or.inl (hin _ hr.1 rfl)
  · exact Or.inr ((Gen.AC.Root.cap_pair U seat).mpr
      ⟨u, hin u hu hlu, v, hin v hv hlv, hne, hku, hkv⟩)

private theorem scoreRun_vote_shape (o : GridCO.Wire p.n .root) (s : Slot) (i : Fin p.n)
    (hl : GridCO.headLabel? o = some s) (hi : GridCO.headSeat? o = some i) :
    ∃ B, o = ⟨.seat s i, .head B⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> try contradiction
  rename_i r j B
  have hr : r = s := Option.some.inj hl
  have hj : j = i := Option.some.inj hi
  subst r; subst j
  exact ⟨B, rfl⟩

private theorem scoreRun_clock_vote_stamp
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (k : Nat) (y : V)
    (t : Time) (o : GridCO.Wire p.n .root)
    (hm : o ∈ (V2.D.Run.stateBefore E rho k y).st.base.votes) :
    GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho k y).st t).base o =
      GridCO.stampVote (V2.D.Run.stateBefore E rho k y).st.base o := by
  rw [← fgsa_vote_stamp_keys E rho k y] at hm
  obtain ⟨⟨v, u⟩, hv, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst v
  unfold GridCO.stampVote
  rw [(clock_cumulative p _ _).2.2.2.1]
  cases hf : (V2.D.Run.stateBefore E rho k y).st.base.voteStamp.find?
      (fun row => row.1 == o) with
  | none =>
    have hn := List.find?_eq_none.mp hf (o, u) hv
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G25 N1; blueprint 03:279–291.
DC: Goldfish/ProposalSnapshotBridge.lean:145–146, `raw_extra_equiv`.
INTENTIONAL: every extra HEAD-merge signature is frozen; the original
proposal arm is identified by authentication. Receipt gives a vote or
cap evidence in the actual proposal pool, at the N1 time pair.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_scoreRun_raw_extra
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.voteTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))
    ∀ o ∈ headVotes p dst (s + 1), ∀ seat, GridCO.headSeat? o = some seat →
      o ∉ proposerVotes src (s + 1) →
      GridCO.equivocates (proposerVotes src (s + 1)) seat = true := by
  intro src dst o ho seat hk hn
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ (s + 1) _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ (s + 1) _ N hp.2.2.2.2
  have hpairs : ∀ q ∈ proposalsAt dst (s + 1), q = (N.raw, N.support) := by
    have h := fgsa_scoreRun_proposalsAt_eq E rho hE ih y (s + 1) N
      (hseat ▸ hx) ⟨_, by rw [hseat]; exact ⟨ip, hip, hem⟩⟩
    dsimp only [proposalsAt, dst] at h ⊢
    rw [clock_proposals, clock_fg]
    exact h
  change o ∈ List.eraseDups (_ ++ _) at ho
  rw [List.mem_eraseDups, List.mem_append] at ho
  rcases ho with ho | ho
  · obtain ⟨hm, ht⟩ := List.mem_filter.mp ho
    obtain ⟨hm, hl⟩ := List.mem_filter.mp hm
    have hl' : GridCO.headLabel? o = some s := by
      simpa only [Nat.add_sub_cancel, beq_iff_eq] using hl
    have hm' : o ∈ (V2.D.Run.stateBefore E rho ih y).st.base.votes := by
      change o ∈ (clock p _ _).base.votes at hm
      rwa [(clock_vn _ _).1] at hm
    have ht' : GridCO.stampVote (V2.D.Run.stateBefore E rho ih y).st.base o <
        SA.freezeTime p.toParams s := by
      have ht' := of_decide_eq_true ht
      change GridCO.stampVote (clock p _ _).base o < _ at ht'
      rwa [scoreRun_clock_vote_stamp E rho ih y _ o hm', Nat.add_sub_cancel] at ht'
    obtain ⟨B, rfl⟩ := scoreRun_vote_shape o s seat hl' hk
    exact (fgsa_scoreRun_frozen_vote_relay E rho hE hN hDelta s hSync hx hy hip
      ih seat B hm' ht').resolve_left hn
  · obtain ⟨hm, -⟩ := List.mem_filter.mp ho
    obtain ⟨q, hq, hraw⟩ := List.mem_flatMap.mp hm
    rw [hpairs q hq] at hraw
    exact (hn (pools.2.1 ▸ hraw)).elim

private theorem scoreRun_block_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ s N, o = ofWire p ⟨.proposer s, .proposal N⟩ ∧ N.erase = b := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i s N
    refine ⟨s, N, ?_, h⟩
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd

private theorem scoreRun_block_receipt_to_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut : Time) (hD : Gen.V2.Duty.DeliveryWithinOn E rho
      (fun o => ¬ isRowObject o) dl cut)
    (t : Time) (o : Obj p) (B : Block) (ho : blockOf? p o = some B)
    (hT : Gen.V2.Duty.Trigger E rho o t) (hlt : t < dl t) (hc : dl t ≤ cut)
    {ih : Nat} {y : V} {u : Time} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y u)) (hd : dl t ≤ u)
    (hF : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st u).fg.F) B)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    B ∈ (clock p (V2.D.Run.stateBefore E rho ih y).st u).base.blocks := by
  let a := V2.D.Run.idxBefore rho (dl t)
  let z := V2.D.Run.idxBefore rho u
  have haz : a ≤ z := fgsa_idxBefore_mono rho hd
  have hFmono : FGBlock.Preceq (V2.D.Run.stateBefore E rho a y).st.fg.F
      (V2.D.Run.stateBefore E rho z y).st.fg.F := by
    have h := fgsa_monoAlong_preceq_F p c (V2.D.Run.stateBefore E rho a y).st.fg.F
    rw [Gen.V2.Duty.MonoAlong_def] at h
    exact V2.D.Engine.stateBefore_stable _ h.1 h.2.1 h.2.2 E rho haz y
      (hN.restartFree y a z) (KitFG.preceq_refl _)
  have hF' := hF
  rw [clock_F_eq, fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hih,
    ← Gen.V2.Duty.stateBefore_idxBefore E rho u hE.toScheduleWellFormed] at hF'
  have hcompat : Block.Compatible B
      (eraseFG (V2.D.Run.stateBeforeTime E rho (dl t) y).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl B)
      (Gen.Pure.block_preceq_trans (eraseFG_preceq hFmono) hF')
  obtain ⟨s, N, rfl, heN⟩ := scoreRun_block_decode ho
  obtain ⟨Y, hY, he⟩ := fgsa_proposal_receipt (hRoots := hroots) E rho hDelta hE hN dl cut
    s N t y hD hT hy hc hlt (by simpa only [heN] using hcompat)
    (hd.trans (hE.in_horizon _ (List.mem_of_getElem? hih)).2)
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hih hy
      (fgsa_trigger_nonneg E rho hE.toScheduleWellFormed hT) hd)
  have hkeep := (fgsa_store_cumulative p c E rho hN haz y).1
  change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (dl t)) y).st.fg.TF ⊆
    (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho u) y).st.fg.TF at hkeep
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed,
    Gen.V2.Duty.stateBefore_idxBefore E rho u hE.toScheduleWellFormed,
    ← fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hih] at hkeep
  rw [clock_base_blocks]
  exact ((cstoreInv_stateBefore E rho ih y).baseTree B).mpr ⟨Y, hkeep hY, he.trans heN⟩

private theorem scoreRun_block_before_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {u : Time} (hi : rho.events[i]? = some (.tick x u))
    (B : Block) (hgen : B ≠ .genesis)
    (hm : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) :
    ∃ j t o, blockOf? p o = some B ∧ V2.D.Run.acceptsAt E rho j x o t ∧ t < u := by
  rw [fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hi,
    ← Gen.V2.Duty.stateBefore_idxBefore E rho u hE.toScheduleWellFormed] at hm
  rw [← (metaInv_stateBefore E rho (V2.D.Run.idxBefore rho u) x).stampKeys] at hm
  obtain ⟨⟨b, stamp⟩, hm, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst b
  rcases fgsa_block_stamp_source E rho hN _ x B stamp hm with hg | ⟨j, hj, t, o, ho, ha, -⟩
  · exact (hgen hg.1).elim
  · obtain ⟨parent, hd, -⟩ := ha.1
    exact ⟨j, t, o, ho, ha,
      (Gen.V2.Duty.index_lt_idxBefore_iff hE.toScheduleWellFormed hd u).mp hj⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b G25 N1; blueprint 03:293–304.
DC: Goldfish/ProposalSnapshotBridge.lean:147–151, forward target membership.
INTENTIONAL: the receiving endpoint floor bounds earlier receipt floors.
A stored proposal-support head above D is retained at the HEAD read.
The accepted proposal's raw, support and row lists are bound by
`scoreRun_block_decode`; the row list is passed unchanged to the receipt.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_scoreRun_block_forward
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (D B : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hDB : Block.Preceq D B)
    (hm : B ∈ (clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams s)).base.blocks)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    B ∈ (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).base.blocks := by
  rw [clock_base_blocks] at hm
  by_cases hg : B = .genesis
  · subst B
    rw [clock_base_blocks]
    have hi := cstoreInv_stateBefore E rho ih y
    exact (hi.baseTree _).mpr ⟨.genesis, hi.fg.gen, rfl⟩
  obtain ⟨j, t, o, ho, ha, ht⟩ := scoreRun_block_before_tick E rho hE hN hip B hg hm
  obtain ⟨dl, cut, hD, -, hlt, hb, -, hc, -⟩ := hSync
  have hd : dl t ≤ SA.voteTime p.toParams s := by
    have hb := hb t
    rw [hDelta] at hb
    have hmax : max t (SA.proposalTime p.toParams s - p.Δ) < SA.proposalTime p.toParams s :=
      max_lt ht (sub_lt_self _ p.deltaPos)
    change dl t ≤ SA.proposalTime p.toParams s + p.Δ
    linarith
  exact scoreRun_block_receipt_to_tick (hroots := hroots) E rho hE hN hDelta dl cut hD t o B ho
    (Or.inr ⟨x, hx, j, ha⟩) (hlt t) (hd.trans hc) hy hih hd
    (Gen.Pure.block_preceq_trans hgeom.target_floor hDB)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b G25 N1; blueprint 03:305–312.
DC: Goldfish/ProposalSnapshotBridge.lean:152–155, backward target membership.
INTENTIONAL: a frozen resolved head above D is active at the proposal read.
The source endpoint floor supplies compatibility at the earlier receipt.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_scoreRun_block_backward
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.voteTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (D B : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))) D)
    (hDB : Block.Preceq D B)
    (hm : B ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (ht : GridCO.stampBlock (V2.D.Run.stateBefore E rho ih y).st.base B <
      SA.freezeTime p.toParams s)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    B ∈ (actView (clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams (s + 1)))).blocks := by
  have hFB := Gen.Pure.block_preceq_trans hgeom.source_floor hDB
  apply (actView_blocks _ B).mpr
  refine ⟨?_, Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl B) hFB⟩
  by_cases hg : B = .genesis
  · subst B
    rw [clock_base_blocks]
    have hi := cstoreInv_stateBefore E rho ip x
    exact (hi.baseTree _).mpr ⟨.genesis, hi.fg.gen, rfl⟩
  have hz : SA.freezeTime p.toParams s = SA.proposalTime p.toParams (s + 1) - p.Δ := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) - p.Δ
    push_cast
    ring
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = _
    push_cast
    ring
  have hzero : 0 ≤ SA.freezeTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    positivity
  obtain ⟨j, -, t, o, ho, ha, htz⟩ := fgsa_block_accepted_before E rho hE
    ih y B _ hg hpub hzero hm ht
  obtain ⟨dl, cut, hD, -, hlt, hb, -, hc, -⟩ := hSync
  have hd : dl t ≤ SA.proposalTime p.toParams (s + 1) := by
    have hb := hb t
    rw [← hz, max_eq_right (le_of_lt htz), hDelta, hz] at hb
    linarith
  have hpv : SA.proposalTime p.toParams (s + 1) ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    linarith [p.deltaPos]
  exact scoreRun_block_receipt_to_tick (hroots := hroots) E rho hE hN hDelta dl cut hD t o B ho
    (Or.inr ⟨y, hy, j, ha⟩) (hlt t) (hd.trans (hpv.trans hc)) hx hip hd hFB

private theorem scoreRun_carried_support (p : Params) (st : State p.n)
    (s : Slot) (N : NamedProposal p.n)
    (hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ st.proposals)
    (hs : N.erase.slot = s)
    (hret : ∃ B ∈ Next.tree p st, eraseFG B = N.erase)
    (o : GridCO.Wire p.n .root) (ho : o ∈ N.support.map baseVote)
    (hl : GridCO.headLabel? o = some (s - 1)) (K : Block)
    (hk : GridCO.resolvedHead? st.base o = some K)
    (hK : ∃ B ∈ Next.tree p st, eraseFG B = K) (hv : K.slot ≤ s - 1) :
    o ∈ headSupport p st s := by
  change o ∈ List.eraseDups (_ ++ _)
  rw [List.mem_eraseDups, List.mem_append]
  apply Or.inr
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨(N.raw, N.support), ?_, ho⟩, ?_⟩
  · apply List.mem_filterMap.mpr
    refine ⟨⟨.proposer s, .proposal N⟩, hw, ?_⟩
    change (if N.slot = s ∧ ∃ B ∈ Next.tree p st, eraseFG B = N.erase then
      some (N.raw, N.support) else none) = some (N.raw, N.support)
    rw [ite_eq_left ⟨by simpa only [named_erase_slot] using hs, hret⟩]
  · simp only [hl, beq_self_eq_true, Bool.true_and, hk, hK, hv, decide_true]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b G25 N1; blueprint 03:298–304.
DC: Goldfish/ProposalSnapshotBridge.lean:147–151, `forward`.
INTENTIONAL: the original declared support is carried literally and its
head is relayed using the target endpoint floor. This gives incidence above D.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_scoreRun_support_forward
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho ih y).st.proposals)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    ∀ X, Block.Preceq D X → ∀ i,
      Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src s) i X = true →
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst s) i X = true := by
  intro src dst X hDX i hs
  obtain ⟨o, ho, hi, hv⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mp hs
  obtain ⟨hraw, hresolved⟩ := List.mem_filter.mp ho
  have hl : GridCO.headLabel? o = some (s - 1) := beq_iff_eq.mp (List.mem_filter.mp hraw).2
  obtain ⟨K, hk, hm, hslot, hXK⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hv
  have ht := resolvedTarget_root _ o hk
  have hslot' : K.slot ≤ s - 1 := by simpa only [hl, Option.getD_some] using hslot
  have hKdst := fgsa_scoreRun_block_forward (hroots := hroots)
    E rho hE hN hDelta s hSync hx hy hip hih
    D K hgeom (Gen.Pure.block_preceq_trans hDX hXK) hm
  have hInv : CStoreInv p dst :=
    cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hdomain : dst.base.headDomain = none :=
    base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ih y))
  have hres := base_resolve_target p dst hInv hdomain o hKdst ht
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2
  have hadm' := fgsa_scoreRun_metadata_retained E rho hN (Nat.le_refl ih) y _ hadm s
  have hMeta := metaInv_clock p _ (metaInv_stateBefore E rho ih y)
    (SA.voteTime p.toParams s)
  have hheld := wire_block_mem p dst hInv hMeta hadm' (block?_proposal s N)
  have hcar := scoreRun_carried_support p dst s N hadm' pools.1
    (scoreRun_retained_tree p dst hInv _ hheld hFN) o
    (pools.2.2.symm ▸ ho) hl K hres
    (scoreRun_retained_tree p dst hInv K hKdst
      (Gen.Pure.block_preceq_trans hgeom.target_floor
        (Gen.Pure.block_preceq_trans hDX hXK))) hslot'
  apply (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mpr
  refine ⟨o, hcar, hi, ?_⟩
  exact (Gen.AC.Root.vote_support_body _ _ _).mpr
    ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst hInv) o hKdst ht, hKdst, hslot, hXK⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b G25 N1; blueprint 03:305–312.
DC: Goldfish/ProposalSnapshotBridge.lean:152–155, `backward`.
INTENTIONAL: an original declaration is already source support; a frozen
support relays both its signature and head. A clean source seat rules out
the receipt's cap alternative. The source endpoint floor makes the head active.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_scoreRun_support_backward
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.voteTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))) D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))
    ∀ X, Block.Preceq D X → ∀ i, GridCO.equivocates (proposerVotes src (s + 1)) i = false →
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X = true →
      Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X = true := by
  intro src dst X hDX i hclean hs
  obtain ⟨o, ho, hi, hv⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mp hs
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ (s + 1) _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ (s + 1) _ N hp.2.2.2.2
  have hpairs : ∀ q ∈ proposalsAt dst (s + 1), q = (N.raw, N.support) := by
    have h := fgsa_scoreRun_proposalsAt_eq E rho hE ih y (s + 1) N
      (hseat ▸ hx) ⟨_, by rw [hseat]; exact ⟨ip, hip, hem⟩⟩
    dsimp only [proposalsAt, dst] at h ⊢
    rw [clock_proposals, clock_fg]
    exact h
  obtain ⟨K, hk, hKdst, hslotK, hXK⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hv
  have ht := resolvedTarget_root _ o hk
  have hDK := Gen.Pure.block_preceq_trans hDX hXK
  have hSrc : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hDst : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hdomain : src.base.headDomain = none :=
    base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ip x))
  have finish (hsource : o ∈ proposerSupport src (s + 1)) :
      Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X = true := by
    have hr := (List.mem_filter.mp hsource).2
    change (match GridCO.resolvedHead? (actView src) o with
      | some C => Block.preceq (eraseFG src.fg.F) C && decide (C.slot ≤ s + 1 - 1)
      | none => false) = true at hr
    cases hc : GridCO.resolvedHead? (actView src) o with
    | none => simp only [hc, Bool.false_eq_true] at hr
    | some C =>
      have hm := (List.mem_filter.mp (resolvedHead_mem _ o hc)).1
      have he : C = K := clock_stored_block_eq E rho
        (hroots.toNamedRootCollisionFree E rho) ip ih x y _ _ hm hKdst
        (Option.some.inj ((resolvedHead_root _ o hc).symm.trans ht))
      subst C
      apply (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mpr
      refine ⟨o, hsource, hi, ?_⟩
      exact (Gen.AC.Root.vote_support_body _ _ _).mpr
        ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p src hSrc) o hm ht, hm, hslotK, hXK⟩
  change o ∈ List.eraseDups (_ ++ _) at ho
  rw [List.mem_eraseDups, List.mem_append] at ho
  rcases ho with ho | ho
  · obtain ⟨hm, hr⟩ := List.mem_filter.mp ho
    obtain ⟨hm, hl⟩ := List.mem_filter.mp hm
    have hl' : GridCO.headLabel? o = some s := by
      simpa only [Nat.add_sub_cancel, beq_iff_eq] using hl
    have hm' : o ∈ (V2.D.Run.stateBefore E rho ih y).st.base.votes := by
      change o ∈ (clock p _ _).base.votes at hm
      rwa [(clock_vn _ _).1] at hm
    change GridCO.resolvedBefore (actView dst) o _ = true at hr
    unfold GridCO.resolvedBefore at hr
    have hres : GridCO.resolvedHead? (actView dst) o = some K := by
      cases hc : GridCO.resolvedHead? (actView dst) o with
      | none => simp only [hc, Bool.false_eq_true] at hr
      | some C =>
        have hmC := (List.mem_filter.mp (resolvedHead_mem _ o hc)).1
        have he := baseBlocks_rootInj p dst hDst C hmC K hKdst
          (Option.some.inj ((resolvedHead_root _ o hc).symm.trans ht))
        exact congrArg some he
    have hactive := resolvedHead_mem _ o hres
    rw [hres, hl'] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.getD_some, Nat.add_sub_cancel] at hr
    obtain ⟨⟨hslot, hvstamp⟩, hbstamp⟩ := hr
    have hKpre : K ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks := by
      have hm := (List.mem_filter.mp hactive).1
      change K ∈ (clock p _ _).base.blocks at hm
      rwa [clock_base_blocks] at hm
    change GridCO.stampBlock (clock p _ _).base K < _ at hbstamp
    rw [fgsa_clock_block_stamp E rho ih y _ K hKpre] at hbstamp
    have hKsrc := fgsa_scoreRun_block_backward (hroots := hroots)
      E rho hE hN hDelta s hSync hx hy hip D K hgeom hDK hKpre hbstamp
    change GridCO.stampVote (clock p _ _).base o < _ at hvstamp
    rw [scoreRun_clock_vote_stamp E rho ih y _ o hm'] at hvstamp
    obtain ⟨K', he⟩ := scoreRun_vote_shape o s i hl' hi
    have hraw : o ∈ proposerVotes src (s + 1) := by
      have hr := fgsa_scoreRun_frozen_vote_relay E rho hE hN hDelta s hSync hx hy hip
        ih i K' (he ▸ hm') (he ▸ hvstamp)
      rw [← he] at hr
      exact hr.resolve_right (by rw [hclean]; exact Bool.noConfusion)
    apply finish
    apply List.mem_filter.mpr
    refine ⟨hraw, ?_⟩
    change (match GridCO.resolvedHead? (actView src) o with
      | some C => Block.preceq (eraseFG src.fg.F) C && decide (C.slot ≤ s + 1 - 1)
      | none => false) = true
    rw [actView_resolve_target p src hSrc hdomain o hKsrc ht]
    exact Bool.and_eq_true_iff.mpr
      ⟨Gen.Pure.block_preceq_trans hgeom.source_floor hDK,
        decide_eq_true (by simpa only [Nat.add_sub_cancel] using hslot)⟩
  · obtain ⟨hm, _⟩ := List.mem_filter.mp ho
    obtain ⟨q, hq, hsup⟩ := List.mem_flatMap.mp hm
    rw [hpairs q hq] at hsup
    exact finish (pools.2.2 ▸ hsup)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b G25, N1 C9/C11–C13/C19; blueprint 03:256–317.
DC: Goldfish/ProposalSnapshotBridge.lean:139–155,210,225.
INTENTIONAL: FG-SA compares the actual proposal and HEAD pools only above
D. The two endpoint floor bounds replace any ordering of active floors.
The admitted honest proposal supplies its original signed metadata;
LabelSync is used at exactly (t_s - Δ, v_s), with no Batch or LabelFacts.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_score_eq_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  intro src dst U U'
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2
  cases s with
  | zero =>
    have he := hp.2.2.2.2
    change (none : Option (Msg p.n)) = some (.proposal N) at he
    cases he
  | succ s =>
    have hg : N.erase ≠ .genesis := by
      intro hg
      have hs := pools.1
      rw [hg] at hs
      change 0 = s + 1 at hs
      omega
    obtain ⟨w, hw, hb, -⟩ := fgsa_stored_block_origin E rho ih y N.erase hadm hg
    obtain ⟨r, M, rfl, -⟩ := (metaInv_stateBefore E rho ih y).wireTree w hw
    have hB : M.erase = N.erase := Option.some.inj hb
    have hr := scoreRun_stored_label E rho hE ih y r M hw
    have hrs : r = s + 1 := hr.trans (hB ▸ pools.1)
    rw [hrs] at hw
    have heq := fgsa_scoreRun_stored_proposal_eq E rho hE ih y (s + 1) M hw
      (hseat ▸ hx) _ rfl ⟨_, by rw [hseat]; exact ⟨ip, hip, hem⟩⟩
    rw [heq] at hw
    have hadm' : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
        (V2.D.Run.stateBefore E rho ih y).st.proposals := hw
    apply fgsa_score_eq_on_retained_suffix p src dst D U (proposerSupport src (s + 1))
      U' (headSupport p dst (s + 1))
    · exact fgsa_scoreRun_raw_subset E rho hE hN (s + 1) hip hseat hx
        (Nat.le_refl ih) N hem N hadm' hFN
    · exact fgsa_scoreRun_raw_extra E rho hE hN hDelta s hSync hx hy hip hseat N hem
    · intro X hDX i hclean
      apply Bool.eq_iff_iff.mpr
      exact ⟨fgsa_scoreRun_support_forward (hroots := hroots)
        E rho hE hN hDelta (s + 1) hSync hx hy hip hih
          N hem hadm' hFN D hgeom X hDX i,
        fgsa_scoreRun_support_backward (hroots := hroots) E rho hE hN hDelta s hSync hx hy hip hseat
          N hem D hgeom X hDX i hclean⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b N1 C14; blueprint 03:367–373.
DC: Goldfish/ProposalWalkTransportCore.lean:183–187, reflected membership.
INTENTIONAL: relay an FG-SA frozen block at exactly (t_s - Δ, t_s).
The endpoint floor gives receipt compatibility. The existing private
receipt helper binds the proposal row list and passes it unchanged.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_walkRun_frozen_block
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (D B : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))) D)
    (hDB : Block.Preceq D B)
    (hm : B ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (ht : GridCO.stampBlock (V2.D.Run.stateBefore E rho ih y).st.base B <
      SA.freezeTime p.toParams s)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    B ∈ (actView (clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams (s + 1)))).blocks := by
  have hFB := Gen.Pure.block_preceq_trans hgeom.source_floor hDB
  apply (actView_blocks _ B).mpr
  refine ⟨?_, Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl B) hFB⟩
  by_cases hg : B = .genesis
  · subst B
    rw [clock_base_blocks]
    have hi := cstoreInv_stateBefore E rho ip x
    exact (hi.baseTree _).mpr ⟨.genesis, hi.fg.gen, rfl⟩
  have hz : SA.freezeTime p.toParams s = SA.proposalTime p.toParams (s + 1) - p.Δ := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) - p.Δ
    push_cast
    ring
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = _
    push_cast
    ring
  have hzero : 0 ≤ SA.freezeTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    positivity
  obtain ⟨j, -, t, o, ho, ha, htz⟩ := fgsa_block_accepted_before E rho hE
    ih y B _ hg hpub hzero hm ht
  obtain ⟨dl, cut, hD, -, hlt, hb, -, hc, -⟩ := hSync
  have hd : dl t ≤ SA.proposalTime p.toParams (s + 1) := by
    have hb := hb t
    rw [← hz, max_eq_right (le_of_lt htz), hDelta, hz] at hb
    linarith
  exact scoreRun_block_receipt_to_tick (hroots := hroots) E rho hE hN hDelta dl cut hD t o B ho
    (Or.inr ⟨y, hy, j, ha⟩) (hlt t) (hd.trans hc) hx hip hd hFB

private theorem walkRun_lift_prefix {n : Nat} {A B : FGBlock (Fin n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B := by
  exact eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G11; blueprint 03:371–373.
DC: Goldfish/ProposalWalkTransportCore.lean:183–187, reflected membership.
INTENTIONAL: a stored FG-SA suffix child supplies its own witness in the
full filtered domain. The Z and floor bounds are separate geometry. -/
theorem fgsa_walkRun_full_domain (p : Params) (st : State p.n)
    (h : CStoreInv p st) (D : FGBlock (Fin p.n)) (C : Block)
    (hF : Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hZ : FGBlock.Preceq (controls p st).Z D)
    (hlo : (controls p st).lo ≤ hOf p.E p.cfg D)
    (hC : C ∈ st.base.blocks) (hDC : Block.Preceq (eraseFG D) C) :
    C ∈ erasedList st (fullTree p st) := by
  obtain ⟨B, hB, rfl⟩ := (h.baseTree C).mp hC
  have hDB := walkRun_lift_prefix hDC
  have hFB := walkRun_lift_prefix (Gen.Pure.block_preceq_trans hF hDC)
  have hZB := KitFG.preceq_trans hZ hDB
  have hheight : (controls p st).lo ≤ hOf p.E p.cfg B :=
    hlo.trans (KitFG.h_mono p.E p.cfg hDB)
  rw [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hheight
  have hm : B ∈ fullTree p st :=
    (KitFG.mem_filteredFromView (heightView p) _ _ B).mpr
      ⟨hB, hFB, hZB, B, hB, KitFG.preceq_refl B, hheight⟩
  exact List.mem_filter.mpr ⟨(h.baseTree _).mpr ⟨B, hB, rfl⟩,
    decide_eq_true ⟨B, hm, rfl⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G11; blueprint 03:350–354,364–366.
DC: Goldfish/ProposalWalkTransportCore.lean:174–176, target path membership.
INTENTIONAL: the admitted proposal is the height witness inside the
receiving voter view itself, before applying its live controls. -/
theorem fgsa_walkRun_path_domain_filtered (p : Params) (st : State p.n)
    (h : CStoreInv p st) (s : Slot) (D : FGBlock (Fin p.n)) (C P : Block)
    (hF : Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hZ : FGBlock.Preceq (controls p st).Z D)
    (hlo : (controls p st).lo ≤ hOf p.E p.cfg D)
    (hP : P ∈ st.base.blocks) (hs : P.slot = s)
    (hDC : Block.Preceq (eraseFG D) C) (hCP : Block.Preceq C P) :
    C ∈ erasedList st (filteredFrom p.E p.cfg (controls p st) (voterBlocks p st s)) := by
  obtain ⟨B, hB, heB⟩ := (h.baseTree P).mp hP
  obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem h.fg.closed hB (heB ▸ hCP)
  have hAB : FGBlock.Preceq A B := walkRun_lift_prefix (heA ▸ heB ▸ hCP)
  have hDA : FGBlock.Preceq D A := walkRun_lift_prefix (heA ▸ hDC)
  have hslot : B.slot = s := by rw [← eraseFG_slot, heB, hs]
  have hFA : FGBlock.Preceq st.fg.F A :=
    walkRun_lift_prefix (Gen.Pure.block_preceq_trans hF (heA ▸ hDC))
  have hAt : A ∈ Next.tree p st := (Next.mem_tree p st A).mpr ⟨hA, hFA⟩
  have hBt : B ∈ Next.tree p st :=
    (Next.mem_tree p st B).mpr ⟨hB, KitFG.preceq_trans hFA hAB⟩
  have hb : B ∈ voterBlocks p st s := by
    apply Finset.mem_filter.mpr
    exact ⟨hBt, Bool.or_eq_true_iff.mpr (Or.inr
      (decide_eq_true ⟨B, hBt, hslot, KitFG.preceq_refl B⟩))⟩
  have ha : A ∈ voterBlocks p st s := by
    apply Finset.mem_filter.mpr
    exact ⟨hAt, Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true ⟨B, hBt, hslot, hAB⟩))⟩
  have hheight : (controls p st).lo ≤ hOf p.E p.cfg B :=
    hlo.trans (KitFG.h_mono p.E p.cfg (KitFG.preceq_trans hDA hAB))
  rw [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hheight
  have hm : A ∈ filteredFrom p.E p.cfg (controls p st) (voterBlocks p st s) := by
    rw [KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
    exact (KitFG.mem_filteredFromView (heightView p) _ _ A).mpr
      ⟨ha, hFA, KitFG.preceq_trans hZ hDA, B, hb, hAB, hheight⟩
  exact List.mem_filter.mpr ⟨(h.baseTree C).mpr ⟨A, hA, heA⟩,
    decide_eq_true ⟨A, hm, heA⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G11; blueprint 03:350–354,364–366.
DC: Goldfish/ProposalWalkTransportCore.lean:174–176, target path membership.
The legacy conclusion additionally requires retention of all off-J top blocks. -/
theorem fgsa_walkRun_path_domain_of_top_retained (p : Params) (st : State p.n)
    (hTop : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W)
    (h : CStoreInv p st) (s : Slot) (D : FGBlock (Fin p.n)) (C P : Block)
    (hF : Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hZ : FGBlock.Preceq (controls p st).Z D)
    (hlo : (controls p st).lo ≤ hOf p.E p.cfg D)
    (hP : P ∈ st.base.blocks) (hs : P.slot = s)
    (hDC : Block.Preceq (eraseFG D) C) (hCP : Block.Preceq C P) :
    C ∈ erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st s)) := by
  have hm := fgsa_walkRun_path_domain_filtered p st h s D C P hF hZ hlo hP hs hDC hCP
  rwa [fgsa_controls_eq_of_top_retained p st hTop] at hm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G11; blueprint 03:356–360,373.
DC: Goldfish/ProposalWalkTransportCore.lean:181,187, eligibility transport.
INTENTIONAL: the FG-SA low-parent and current-slot arms are excluded;
old-child eligibility on this suffix is exactly its strict majority test. -/
theorem fgsa_walkRun_eligible_iff (p : Params) (st : State p.n)
    (raw sup : List (GridCO.Wire p.n .root)) (D : FGBlock (Fin p.n)) (C : Block)
    (hlo : (controls p st).lo ≤ hOf p.E p.cfg D)
    (hparent : Block.Preceq (eraseFG D) C.parent)
    (hs : C.slot ≠ st.slot p) :
    eligible p st raw sup C = true ↔
      GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw sup C := by
  have hf : ¬ ∃ P ∈ st.fg.TF, eraseFG P = C.parent ∧
      hOf p.E p.cfg P < (controls p st).lo := by
    rintro ⟨P, -, he, hp⟩
    have hDP := walkRun_lift_prefix (he ▸ hparent)
    exact (Nat.not_lt_of_ge (hlo.trans (KitFG.h_mono p.E p.cfg hDP))) hp
  rw [fgsa_eligible_eq]
  simp only [hf, decide_false, Bool.false_or, beq_eq_false_iff_ne.mpr hs,
    Bool.or_false, decide_eq_true_eq]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b G11; blueprint 03:340–341.
DC: ChainState/ProposalBridge.lean:90, proposedBlockAt_parent.
INTENTIONAL: project only the parent selected at the FG-SA proposal read;
the selected row list remains opaque. -/
theorem fgsa_walkRun_proposal_parent (p : Params) (st : State p.n) (s : Slot)
    (a : Nat) (N : NamedProposal p.n)
    (he : (propose p st s).map (withApp p a) = some (.proposal N)) :
    0 < s ∧ N.erase.parent? = some (getHead p st (proposerVotes st s) (proposerSupport st s)) ∧
      N.erase.parent = getHead p st (proposerVotes st s) (proposerSupport st s) := by
  unfold propose at he
  split at he
  · cases he
  · rename_i hs
    simp only [Option.map_map] at he
    obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp he
    cases Msg.proposal.inj he
    have hparent := (namedByErase?_sound _ _ P hP).2
    exact ⟨Nat.pos_of_ne_zero hs, congrArg some hparent, hparent⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.4b G11; blueprint 03:367–369.
DC: ChainState/ProposalBridge.lean:243, proposedBlockAt_unique.
INTENTIONAL: authenticate every stored current-slot path witness against
the actual honest emission. The accepted row list is bound as A and is
passed unchanged to the existing authentication lemma. -/
theorem fgsa_walkRun_current_block_eq
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (s : Slot) (hs : 0 < s)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (B : Block) (hB : B ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hslot : B.slot = s) : B = N.erase := by
  have hg : B ≠ .genesis := by
    intro he
    have hz : B.slot = 0 := he ▸ rfl
    exact (Nat.ne_of_gt hs) (hslot.symm.trans hz)
  obtain ⟨w, hw, hb, -⟩ := fgsa_stored_block_origin E rho ih y B hB hg
  obtain ⟨r, M, rfl, -⟩ := (metaInv_stateBefore E rho ih y).wireTree w hw
  have hC : M.erase = B := Option.some.inj hb
  have hr := scoreRun_stored_label E rho hE ih y r M hw
  have hrs : r = s := hr.trans (hC ▸ hslot)
  rw [hrs] at hw
  have heq := fgsa_scoreRun_stored_proposal_eq E rho hE ih y s M hw
    (hseat ▸ hx) _ rfl ⟨_, by rw [hseat]; exact ⟨ip, hip, hem⟩⟩
  exact hC.symm.trans (congrArg NamedProposal.erase
    (Msg.proposal.inj (congrArg (fun w : Wire p.n => w.payload) heq)))

private theorem walkRun_parent_prefix {C X : Block} (h : C.parent? = some X) :
    Block.Preceq X C := by
  cases C with
  | genesis => cases h
  | node P s root r =>
    have he : P = X := Option.some.inj h
    subst P
    change (decide _ || Block.preceq X X) = true
    exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_refl _))

private theorem walkRun_parent_eq {C X : Block} (h : C.parent? = some X) : C.parent = X := by
  cases C with
  | genesis => cases h
  | node P s root r => exact Option.some.inj h

private theorem walkRun_child_before_parent {P Q X C : Block}
    (hP : P.parent? = some Q) (hC : C.parent? = some X)
    (hCP : Block.Preceq C P) (hne : X ≠ Q) : Block.Preceq C Q := by
  cases P with
  | genesis => cases hP
  | node A s root r =>
    have he : A = Q := Option.some.inj hP
    subst A
    change (decide (C = .node Q s root r) || Block.preceq C Q) = true at hCP
    rcases Bool.or_eq_true_iff.mp hCP with he | hp
    · have he := of_decide_eq_true he
      subst C
      exact (hne (Option.some.inj hC).symm).elim
    · exact hp

private theorem walkRun_head_stored (p : Params) (st : State p.n)
    (h : CStoreInv p st) (raw sup : List (GridCO.Wire p.n .root)) :
    getHead p st raw sup ∈ st.base.blocks := by
  rcases fgsa_headInTree_mem_or_anchor p st (erasedList st (fullTree p st)) raw sup with he | hm
  · change getHead p st raw sup = liveRoot p st at he
    rw [he]
    exact liveRoot_stored p st h
  · exact (List.mem_filter.mp hm).1

private theorem walkRun_ancestor_stored (p : Params) (st : State p.n)
    (h : CStoreInv p st) {B C : Block} (hB : B ∈ st.base.blocks)
    (hCB : Block.Preceq C B) : C ∈ st.base.blocks := by
  obtain ⟨W, hW, rfl⟩ := (h.baseTree B).mp hB
  obtain ⟨A, hA, he⟩ := eraseFG_ancestor_mem h.fg.closed hW hCB
  exact (h.baseTree C).mpr ⟨A, hA, he⟩

/-- Reflection uses only the frozen or authenticated proposal-path voter arm. -/
private theorem walkRun_reflected_voter_block
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D X C : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))) D)
    (hDX : Block.Preceq D X) (hXQ : Block.Prec X N.erase.parent)
    (hp : C.parent? = some X)
    (hm : C ∈ erasedList
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1)))
      (voterBlocks p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1)))
        (s + 1)))
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    C ∈ (clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams (s + 1))).base.blocks := by
  let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hCbase : C ∈ dst.base.blocks := (List.mem_filter.mp hm).1
  have hCpre : C ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks := by
    change C ∈ (clock p _ _).base.blocks at hCbase
    rwa [clock_base_blocks] at hCbase
  obtain ⟨A, hA, heA⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Bool.or_eq_true_iff.mp (Finset.mem_filter.mp hA).2 with hf | hc
  · have hf := of_decide_eq_true hf
    rw [heA] at hf
    change GridCO.stampBlock (clock p _ _).base C < _ at hf
    rw [fgsa_clock_block_stamp E rho ih y _ C hCpre] at hf
    have hf' : GridCO.stampBlock (V2.D.Run.stateBefore E rho ih y).st.base C <
        SA.freezeTime p.toParams s := by simpa only [Nat.add_sub_cancel] using hf
    have hb := fgsa_walkRun_frozen_block (hroots := hroots)
      E rho hE hN hDelta s hSync hx hy hip D C hgeom
      (Gen.Pure.block_preceq_trans hDX (walkRun_parent_prefix hp)) hCpre hf'
    exact ((actView_blocks src C).mp hb).1
  · obtain ⟨P, hP, hslot, hAP⟩ := of_decide_eq_true hc
    have hPbase : eraseFG P ∈ dst.base.blocks :=
      (ht.baseTree _).mpr ⟨P, Next.tree_subset_TF p dst hP, rfl⟩
    have hPpre : eraseFG P ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks := by
      change eraseFG P ∈ (clock p _ _).base.blocks at hPbase
      rwa [clock_base_blocks] at hPbase
    have heP := fgsa_walkRun_current_block_eq E rho hE (s + 1) (Nat.succ_pos s) hx hip
      hseat N hem (eraseFG P) hPpre ((eraseFG_slot P).trans hslot)
    have hCb : Block.Preceq C N.erase := by simpa only [heA, heP] using eraseFG_preceq hAP
    have hmem := hem
    rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
    have hem' := (fgsa_emits_proposal E rho _ x _ (s + 1) _).mp hmem
    have hparent := fgsa_walkRun_proposal_parent p src (s + 1) _ N hem'.2.2.2.2
    have hne : X ≠ N.erase.parent := by
      intro he
      have hn := (Bool.and_eq_true_iff.mp hXQ).1
      simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
    have hpB : N.erase.parent? = some N.erase.parent := by rw [hparent.2.2]; exact hparent.2.1
    have hCQ := walkRun_child_before_parent hpB hp hCb hne
    rw [hparent.2.2] at hCQ
    exact walkRun_ancestor_stored p src hs (walkRun_head_stored p src hs _ _) hCQ

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b N1 C14; blueprint 03:367–371.
DC: Goldfish/ProposalWalkTransportCore.lean:183–187, target-child reflection.
INTENTIONAL: split the actual FG-SA voter domain into its frozen arm and
its authenticated proposal-path arm. Only the frozen arm needs delivery,
with LabelSync at exactly (t_s - Δ, t_s).
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_walkRun_reflected_block
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D X C : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))) D)
    (hDX : Block.Preceq D X) (hXQ : Block.Prec X N.erase.parent)
    (hp : C.parent? = some X)
    (hm : C ∈ erasedList
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1)))
      (storeFrame p.E p.cfg
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))).fg
        (voterBlocks p
          (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1)))
          (s + 1))))
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    C ∈ (clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams (s + 1))).base.blocks := by
  apply walkRun_reflected_voter_block (hroots := hroots)
    E rho hE hN hDelta s hSync hx hy hip hseat N hem D X C hgeom hDX hXQ hp
  obtain ⟨hC, hm⟩ := List.mem_filter.mp hm
  obtain ⟨A, hA, heA⟩ := of_decide_eq_true hm
  exact List.mem_filter.mpr ⟨hC, decide_eq_true ⟨A,
    ((KitFG.mem_filteredFrom_of_bridge
      p.E p.cfg (heightView p) (heightView_bridge p) _ _ A).mp hA).1, heA⟩⟩

private theorem walkRun_fold_option_origin {α : Type}
    (f : Option α → α → Option α)
    (hchoose : ∀ acc x, f acc x = acc ∨ f acc x = some x)
    (xs : List α) (acc : Option α) (b : α)
    (hresult : xs.foldl f acc = some b) :
    acc = some b ∨ b ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl hresult
  | cons x xs ih =>
      rcases ih (f acc x) hresult with hfirst | htail
      · rcases hchoose acc x with hkeep | htake
        · exact Or.inl (hkeep.symm.trans hfirst)
        · have heq : x = b := Option.some.inj (htake.symm.trans hfirst)
          exact Or.inr (List.mem_cons.mpr (Or.inl heq.symm))
      · exact Or.inr (List.mem_cons.mpr (Or.inr htail))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A successful GHOST step selects a stored eligible child of its anchor. -/
private theorem walkRun_step_child (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor child : Block)
    (hstep : GridCO.ghostStep tree score eligible anchor = some child) :
    child ∈ tree ∧ child.parent? = some anchor ∧ eligible child = true := by
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  let select : Option Block → Block → Option Block := fun best b =>
    match best with
    | none => some b
    | some old =>
        if score old < score b || (score old == score b && old.root < b.root)
        then some b else best
  have hchoose : ∀ best b, select best b = best ∨ select best b = some b := by
    intro best b
    cases best with
    | none => exact Or.inr rfl
    | some old =>
        change (if score old < score b || (score old == score b && old.root < b.root)
          then some b else some old) = some old ∨
          (if score old < score b || (score old == score b && old.root < b.root)
          then some b else some old) = some b
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
  let best := children.foldl select none
  change (match best with
    | none => none
    | some b =>
      if children.any (fun c => c != b && score c == score b && c.root == b.root)
      then none else some b) = some child at hstep
  cases hbest : best with
  | none => rw [hbest] at hstep; cases hstep
  | some b =>
      have hb : b ∈ children := by
        rcases walkRun_fold_option_origin select hchoose children none b hbest with
          himpossible | hmem
        · cases himpossible
        · exact hmem
      rw [hbest] at hstep
      change (if children.any (fun c => c != b && score c == score b && c.root == b.root)
        then none else some b) = some child at hstep
      split at hstep
      · cases hstep
      · have hchild : b = child := Option.some.inj hstep
        subst b
        have hp := List.mem_filter.mp hb
        have ⟨hparent, helig⟩ := Bool.and_eq_true_iff.mp hp.2
        exact ⟨hp.1, by simpa using hparent, helig⟩


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.4b G11, N1 C14 with G25 C9/C11–C13/C19; blueprint 03:350–379.
DC: Goldfish/ProposalWalkTransportCore.lean:162–191.
INTENTIONAL: FG-SA transfers suffix coverage of the proposal parent.
The two N1 records have the exact G25 and G11 time pairs. Comparison-prefix
geometry permits different live roots; terminal adoption is a consumer task.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_ghost_transfer_sfx_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.proposalTime p.toParams s))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq N.erase.parent (headVote p dst s) := by
  intro dst
  let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have pools := fgsa_scoreRun_proposal_pools p src s _ N hp.2.2.2.2
  have hsInv : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have htInv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hsrcslot : src.slot p = s := fgsa_proposal_slot (c := c) _ s
  have hdstslot : dst.slot p = s := fgsa_vote_slot (c := c) _ s
  have hb : N.erase ∈ dst.base.blocks := by change N.erase ∈ (clock p _ _).base.blocks; rwa
      [clock_base_blocks]
  have hpB : N.erase.parent? = some N.erase.parent := by rw [hparent.2.2]; exact hparent.2.1
  have hQP := walkRun_parent_prefix hpB
  have hsRe := Gen.Pure.walk_reanchor_of_dominated_suffix _ _ _ _ _
    hgeom.source_anchor hgeom.source_prefix
  have htRe := Gen.Pure.walk_reanchor_of_dominated_suffix _ _ _ _ _
    hgeom.target_anchor hgeom.target_prefix
  have hDQ : Block.Preceq (eraseFG D) N.erase.parent := by
    rw [hparent.2.2]
    exact Gen.Pure.walk_covers_of_dominated_suffix _ _ _ _ _
      (Gen.Pure.block_compatible_of_common hgeom.source_anchor (Gen.Pure.block_preceq_refl _))
      hgeom.source_prefix
  have hFN : Block.Preceq (eraseFG dst.fg.F) N.erase :=
    Gen.Pure.block_preceq_trans hgeom.target_floor
      (Gen.Pure.block_preceq_trans hDQ hQP)
  have hscore := fgsa_score_eq_on_run (hroots := hroots)
    E rho hE hN hDelta s hScoreSync hx hy hip hih hseat
    N hem hadm hFN (eraseFG D) hgeom.toScoreRunGeometry
  have hcount := hscore.2.2.1
  have hscores := hscore.2.2.2
  have hcover : Block.Preceq N.erase.parent
      (GridCO.ghost (eraseFG D) (erasedList src (fullTree p src))
        (GridCO.goldfishScore src.base.blocks (proposerVotes src s) (proposerSupport src s))
        (eligible p src (proposerVotes src s) (proposerSupport src s))) := by
    rw [← hsRe]
    change Block.Preceq N.erase.parent (getHead p src _ _)
    rw [hparent.2.2]
    exact Gen.Pure.block_preceq_refl _
  have helig (C : Block) (hC : C ∈ src.base.blocks)
      (hDC : Block.Preceq (eraseFG D) C)
      (hDP : Block.Preceq (eraseFG D) C.parent) :
      eligible p src (proposerVotes src s) (proposerSupport src s) C =
        eligible p dst (headVotes p dst s) (headSupport p dst s) C := by
    have hCs : C.slot < s := (fgsa_stored_block_slots E rho hE.toScheduleWellFormed
      hip hparent.1).2.1 C hC
    apply Bool.eq_iff_iff.mpr
    rw [fgsa_walkRun_eligible_iff p src _ _ D C hgeom.source_lo hDP
      (by rw [hsrcslot]; exact Nat.ne_of_lt hCs)]
    rw [fgsa_walkRun_eligible_iff p dst _ _ D C hgeom.target_lo hDP
      (by rw [hdstslot]; exact Nat.ne_of_lt hCs)]
    rw [hcount, hscores C hDC]
  have hkeep : Gen.Pure.SuffixPersists (eraseFG D) N.erase.parent
      (erasedList src (fullTree p src))
      (erasedList dst (filteredFrom p.E p.cfg (controls p dst) (voterBlocks p dst s)))
      (GridCO.goldfishScore src.base.blocks (proposerVotes src s) (proposerSupport src s))
      (eligible p src (proposerVotes src s) (proposerSupport src s))
      (eligible p dst (headVotes p dst s) (headSupport p dst s)) := by
    intro X C hDX _ hstep hCQ
    obtain ⟨hC, hpC, heC⟩ := walkRun_step_child _ _ _ _ _ hstep
    have hDC := Gen.Pure.block_preceq_trans hDX (walkRun_parent_prefix hpC)
    refine ⟨fgsa_walkRun_path_domain_filtered p dst htInv s D C N.erase
      hgeom.target_floor hgeom.target_Z hgeom.target_lo hb pools.1 hDC
      (Gen.Pure.block_preceq_trans hCQ hQP), ?_⟩
    rw [← helig C (List.mem_filter.mp hC).1 hDC (by rw [walkRun_parent_eq hpC]; exact hDX)]
    exact heC
  have hreflect : Gen.Pure.SuffixReflects (eraseFG D) N.erase.parent
      (erasedList src (fullTree p src))
      (erasedList dst (filteredFrom p.E p.cfg (controls p dst) (voterBlocks p dst s)))
      (eligible p src (proposerVotes src s) (proposerSupport src s))
      (eligible p dst (headVotes p dst s) (headSupport p dst s)) := by
    intro X C hDX hXQ hC hpC heC
    have hDC := Gen.Pure.block_preceq_trans hDX (walkRun_parent_prefix hpC)
    have hstored : C ∈ src.base.blocks := by
      cases s with
      | zero => exact (Nat.lt_irrefl 0 hparent.1).elim
      | succ r =>
        apply walkRun_reflected_voter_block (hroots := hroots)
          E rho hE hN hDelta r hSync hx hy hip hseat
          N hem (eraseFG D) X C hgeom.toScoreRunGeometry hDX hXQ hpC
        obtain ⟨hCbase, hCframe⟩ := List.mem_filter.mp hC
        obtain ⟨A, hA, heA⟩ := of_decide_eq_true hCframe
        exact List.mem_filter.mpr ⟨hCbase, decide_eq_true ⟨A,
          ((KitFG.mem_filteredFrom_of_bridge
            p.E p.cfg (heightView p) (heightView_bridge p) _ _ A).mp hA).1, heA⟩⟩
    refine ⟨fgsa_walkRun_full_domain p src hsInv D C hgeom.source_floor hgeom.source_Z
      hgeom.source_lo hstored hDC, ?_⟩
    rw [helig C hstored hDC (by rw [walkRun_parent_eq hpC]; exact hDX)]
    exact heC
  have hsfx : Gen.Pure.SuffixScoresAgree (eraseFG D) N.erase.parent
      (erasedList dst (filteredFrom p.E p.cfg (controls p dst) (voterBlocks p dst s)))
      (GridCO.goldfishScore src.base.blocks (proposerVotes src s) (proposerSupport src s))
      (GridCO.goldfishScore dst.base.blocks (headVotes p dst s) (headSupport p dst s))
      (eligible p dst (headVotes p dst s) (headSupport p dst s)) := by
    intro X C hDX _ _ hpC _
    exact (hscores C (Gen.Pure.block_preceq_trans hDX (walkRun_parent_prefix hpC))).symm
  have hresult := Gen.Pure.ghost_transfer_sfx _ _ _ _ _ _ _ _ hDQ hcover hkeep hreflect hsfx
  change Block.Preceq N.erase.parent (headVote p dst s)
  rw [fgsa_headVote_eq_filtered]
  rw [ite_eq_right (Nat.ne_of_gt hparent.1)]
  change Block.Preceq N.erase.parent (GridCO.ghost _ _ _ _)
  rw [htRe]
  exact hresult

/-- A named target receipt persists from the strict time read to its tick. -/
theorem fgsa_target_receipt_at_tick_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {t : Time}
    (hx : x ∈ rho.honest) (hi : rho.events[i]? = some (.tick x t))
    (K : Block) (h : TargetReceiptService E rho K t x)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    K ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks := by
  have hid : V2.D.Run.idxBefore rho t ≤ i := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hE.toScheduleWellFormed hi t).mp
      (Nat.lt_of_not_ge hn)
    exact (lt_irrefl t ht).elim
  have hm := fgsa_target_receipt_on E rho hE.toScheduleWellFormed hroots K t x hx h
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho t hE.toScheduleWellFormed] at hm
  exact (fgsa_store_durable p c E rho hid x).2.1.subset hm

/-- Primitive receiver services for the frozen HEAD and named support targets.
The consumer supplies safe history for each retained object at its own anchor. -/
structure ScoreServiceScope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ip ih : Nat) (x y : V) (s : Slot) (D : Block) : Prop where
  sourceEpoch : V2.D.restartFree rho x
    (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s)) ip
  frozenHeads : ∀ seat b,
    (⟨.seat (s - 1) seat, .head b⟩ : GridCO.Wire p.n .root) ∈
      (rho.stateBefore E ih y).st.base.votes →
    GridCO.stampVote (rho.stateBefore E ih y).st.base
      ⟨.seat (s - 1) seat, .head b⟩ < SA.freezeTime p.toParams (s - 1) →
    (fgsa p c).excludes (rho.stateBeforeTime E (SA.proposalTime p.toParams s) x)
      (ofHead p ⟨.seat (.head (s - 1)) seat, b⟩) = false →
    ∃ send, Nonempty (ReceiverService E rho
      (ofHead p ⟨.seat (.head (s - 1)) seat, b⟩) send (SA.proposalTime p.toParams s) x)
  forward : ∀ B, Block.Preceq D B →
    B ∈ (rho.stateBefore E ip x).st.base.blocks →
    TargetReceiptService E rho B (SA.voteTime p.toParams s) y
  backward : ∀ B, Block.Preceq D B →
    B ∈ (rho.stateBefore E ih y).st.base.blocks →
    GridCO.stampBlock (rho.stateBefore E ih y).st.base B <
      SA.freezeTime p.toParams (s - 1) →
    TargetReceiptService E rho B (SA.proposalTime p.toParams s) x

/-- A local frozen HEAD service gives a proposal vote or its cap evidence. -/
theorem fgsa_scoreRun_frozen_vote_relay_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (D : Block) (hScope : ScoreServiceScope E rho ip ih x y (s + 1) D)
    (seat : Fin p.n) (B : BlockId)
    (hm : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n .root) ∈
      (rho.stateBefore E ih y).st.base.votes)
    (ht : GridCO.stampVote (rho.stateBefore E ih y).st.base
      ⟨.seat s seat, .head B⟩ < SA.freezeTime p.toParams s) :
    let U := proposerVotes (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1))) (s + 1)
    (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n .root) ∈ U ∨
      GridCO.equivocates U seat = true := by
  intro U
  have hid : V2.D.Run.idxBefore rho (SA.proposalTime p.toParams (s + 1)) ≤ ip := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hE.toScheduleWellFormed hip _).mp
      (Nat.lt_of_not_ge hn)
    exact (lt_irrefl _ ht).elim
  have keep (o : GridCO.Wire p.n .root)
      (ho : o ∈ (rho.stateBeforeTime E (SA.proposalTime p.toParams (s + 1)) x).st.base.votes)
      (hl : GridCO.headLabel? o = some s) : o ∈ U := by
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [Nat.add_sub_cancel, beq_iff_eq] using hl⟩
    rw [(clock_vn _ _).1]
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed] at ho
    exact fgsa_votes_cumulative_on p c E rho hid x hScope.sourceEpoch ho
  by_cases hn : (fgsa p c).excludes
      (rho.stateBeforeTime E (SA.proposalTime p.toParams (s + 1)) x)
      (ofHead p ⟨.seat (.head s) seat, B⟩) = false
  · obtain ⟨send, ⟨hs⟩⟩ := hScope.frozenHeads seat B hm ht hn
    have hp := hs.processed hE.toScheduleWellFormed hx (by change ¬ False; exact not_false)
    exact Or.inl (keep _ (of_decide_eq_true hp) rfl)
  · have hw : (rho.stateBeforeTime E (SA.proposalTime p.toParams (s + 1)) x).st.slot p ≤
        s + 1 := by
      have hb := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hE.toScheduleWellFormed hid x
      have hn : (rho.stateBefore E
          (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams (s + 1))) x).st.base.now ≤
          (rho.stateBefore E ip x).st.base.now :=
        (fgsa_clock_now p c (rho.stateBefore E
          (V2.D.Run.idxBefore rho (SA.proposalTime p.toParams (s + 1))) x)) ▸
          (fgsa_clock_now p c (rho.stateBefore E ip x)) ▸ hb
      have hr := Gen.V2.Duty.stateBefore_idxBefore E rho
        (SA.proposalTime p.toParams (s + 1)) hE.toScheduleWellFormed
      exact (hr ▸ (Internal.slotOf_mono
        (hn.trans (fgsa_preTick_now_le E rho hE.toScheduleWellFormed hip)))).trans_eq
        ((fgsa_postClock_slot (c := c) (rho.stateBefore E ip x) _).2.symm.trans
          (fgsa_proposal_slot (c := c) _ (s + 1)))
    obtain ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, _, _⟩ :=
      fgsa_head_excluded_before E rho hE.toScheduleWellFormed x
        (SA.proposalTime p.toParams (s + 1)) s seat B hw (Bool.eq_true_of_ne_false hn)
    exact Or.inr ((Gen.AC.Root.cap_pair U seat).mpr
      ⟨u, keep u hu hlu, v, keep v hv hlv, hne, hku, hkv⟩)

/-- Named support targets use receiver service at the exact HEAD freeze. -/
theorem fgsa_scoreRun_block_forward_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (s : Slot)
    {ip ih : Nat} {x y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (D B : Block) (hScope : ScoreServiceScope E rho ip ih x y s D)
    (hDB : Block.Preceq D B)
    (hm : B ∈ (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)).base.blocks)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    B ∈ (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)).base.blocks := by
  rw [clock_base_blocks] at hm ⊢
  exact fgsa_target_receipt_at_tick_on E rho hE hy hih B (hScope.forward B hDB hm) hroots

/-- A frozen named target service returns an active proposal block above the source floor. -/
theorem fgsa_scoreRun_block_backward_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (D B : Block) (hScope : ScoreServiceScope E rho ip ih x y (s + 1) D)
    (hFB : Block.Preceq (eraseFG (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1))).fg.F) D)
    (hDB : Block.Preceq D B)
    (hm : B ∈ (rho.stateBefore E ih y).st.base.blocks)
    (ht : GridCO.stampBlock (rho.stateBefore E ih y).st.base B < SA.freezeTime p.toParams s)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    B ∈ (actView (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))).blocks := by
  apply (actView_blocks _ B).mpr
  refine ⟨?_, Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl B)
    (Gen.Pure.block_preceq_trans hFB hDB)⟩
  rw [clock_base_blocks]
  exact fgsa_target_receipt_at_tick_on E rho hE hx hip B
    (hScope.backward B hDB hm ht) hroots

theorem fgsa_scoreRun_raw_extra_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (_hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : Block) (hScope : ScoreServiceScope E rho ip ih x y (s + 1) D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))
    ∀ o ∈ headVotes p dst (s + 1), ∀ seat, GridCO.headSeat? o = some seat →
      o ∉ proposerVotes src (s + 1) →
      GridCO.equivocates (proposerVotes src (s + 1)) seat = true := by
  intro src dst o ho seat hk hn
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ (s + 1) _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ (s + 1) _ N hp.2.2.2.2
  have hpairs : ∀ q ∈ proposalsAt dst (s + 1), q = (N.raw, N.support) := by
    have h := fgsa_scoreRun_proposalsAt_eq E rho hE ih y (s + 1) N
      (hseat ▸ hx) ⟨_, by rw [hseat]; exact ⟨ip, hip, hem⟩⟩
    dsimp only [proposalsAt, dst] at h ⊢
    rw [clock_proposals, clock_fg]
    exact h
  change o ∈ List.eraseDups (_ ++ _) at ho
  rw [List.mem_eraseDups, List.mem_append] at ho
  rcases ho with ho | ho
  · obtain ⟨hm, ht⟩ := List.mem_filter.mp ho
    obtain ⟨hm, hl⟩ := List.mem_filter.mp hm
    have hl' : GridCO.headLabel? o = some s := by
      simpa only [Nat.add_sub_cancel, beq_iff_eq] using hl
    have hm' : o ∈ (V2.D.Run.stateBefore E rho ih y).st.base.votes := by
      change o ∈ (clock p _ _).base.votes at hm
      rwa [(clock_vn _ _).1] at hm
    have ht' : GridCO.stampVote (V2.D.Run.stateBefore E rho ih y).st.base o <
        SA.freezeTime p.toParams s := by
      have ht' := of_decide_eq_true ht
      change GridCO.stampVote (clock p _ _).base o < _ at ht'
      rwa [scoreRun_clock_vote_stamp E rho ih y _ o hm', Nat.add_sub_cancel] at ht'
    obtain ⟨B, rfl⟩ := scoreRun_vote_shape o s seat hl' hk
    exact (fgsa_scoreRun_frozen_vote_relay_on E rho hE s hx hip D hScope seat B hm'
      ht').resolve_left hn
  · obtain ⟨hm, -⟩ := List.mem_filter.mp ho
    obtain ⟨q, hq, hraw⟩ := List.mem_flatMap.mp hm
    rw [hpairs q hq] at hraw
    exact (hn (pools.2.1 ▸ hraw)).elim

theorem fgsa_scoreRun_support_forward_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (_hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho ih y).st.proposals)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hScope : ScoreServiceScope E rho ip ih x y s D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    ∀ X, Block.Preceq D X → ∀ i,
      Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src s) i X = true →
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst s) i X = true := by
  intro src dst X hDX i hs
  obtain ⟨o, ho, hi, hv⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mp hs
  obtain ⟨hraw, hresolved⟩ := List.mem_filter.mp ho
  have hl : GridCO.headLabel? o = some (s - 1) := beq_iff_eq.mp (List.mem_filter.mp hraw).2
  obtain ⟨K, hk, hm, hslot, hXK⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hv
  have ht := resolvedTarget_root _ o hk
  have hslot' : K.slot ≤ s - 1 := by simpa only [hl, Option.getD_some] using hslot
  have hKdst := fgsa_scoreRun_block_forward_on (hroots := hroots)
    E rho hE s hy hih D K hScope (Gen.Pure.block_preceq_trans hDX hXK) hm
  have hInv : CStoreInv p dst :=
    cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hdomain : dst.base.headDomain = none :=
    base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ih y))
  have hres := base_resolve_target p dst hInv hdomain o hKdst ht
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2
  have hadm' := fgsa_scoreRun_metadata_retained_restart E rho (Nat.le_refl ih) y _ hadm s
  have hMeta := metaInv_clock p _ (metaInv_stateBefore E rho ih y)
    (SA.voteTime p.toParams s)
  have hheld := wire_block_mem p dst hInv hMeta hadm' (block?_proposal s N)
  have hcar := scoreRun_carried_support p dst s N hadm' pools.1
    (scoreRun_retained_tree p dst hInv _ hheld hFN) o
    (pools.2.2.symm ▸ ho) hl K hres
    (scoreRun_retained_tree p dst hInv K hKdst
      (Gen.Pure.block_preceq_trans hgeom.target_floor
        (Gen.Pure.block_preceq_trans hDX hXK))) hslot'
  apply (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mpr
  refine ⟨o, hcar, hi, ?_⟩
  exact (Gen.AC.Root.vote_support_body _ _ _).mpr
    ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst hInv) o hKdst ht, hKdst, hslot, hXK⟩

theorem fgsa_scoreRun_support_backward_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (_hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))) D)
    (hScope : ScoreServiceScope E rho ip ih x y (s + 1) D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))
    ∀ X, Block.Preceq D X → ∀ i, GridCO.equivocates (proposerVotes src (s + 1)) i = false →
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X = true →
      Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X = true := by
  intro src dst X hDX i hclean hs
  obtain ⟨o, ho, hi, hv⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mp hs
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ (s + 1) _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ (s + 1) _ N hp.2.2.2.2
  have hpairs : ∀ q ∈ proposalsAt dst (s + 1), q = (N.raw, N.support) := by
    have h := fgsa_scoreRun_proposalsAt_eq E rho hE ih y (s + 1) N
      (hseat ▸ hx) ⟨_, by rw [hseat]; exact ⟨ip, hip, hem⟩⟩
    dsimp only [proposalsAt, dst] at h ⊢
    rw [clock_proposals, clock_fg]
    exact h
  obtain ⟨K, hk, hKdst, hslotK, hXK⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hv
  have ht := resolvedTarget_root _ o hk
  have hDK := Gen.Pure.block_preceq_trans hDX hXK
  have hSrc : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hDst : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hdomain : src.base.headDomain = none :=
    base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ip x))
  have finish (hsource : o ∈ proposerSupport src (s + 1)) :
      Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X = true := by
    have hr := (List.mem_filter.mp hsource).2
    change (match GridCO.resolvedHead? (actView src) o with
      | some C => Block.preceq (eraseFG src.fg.F) C && decide (C.slot ≤ s + 1 - 1)
      | none => false) = true at hr
    cases hc : GridCO.resolvedHead? (actView src) o with
    | none => simp only [hc, Bool.false_eq_true] at hr
    | some C =>
      have hm := (List.mem_filter.mp (resolvedHead_mem _ o hc)).1
      have he : C = K := clock_stored_block_eq E rho
        (hroots.toNamedRootCollisionFree E rho) ip ih x y _ _ hm hKdst
        (Option.some.inj ((resolvedHead_root _ o hc).symm.trans ht))
      subst C
      apply (Gen.AC.Root.vote_pool_support_witness _ _ _ _).mpr
      refine ⟨o, hsource, hi, ?_⟩
      exact (Gen.AC.Root.vote_support_body _ _ _).mpr
        ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p src hSrc) o hm ht, hm, hslotK, hXK⟩
  change o ∈ List.eraseDups (_ ++ _) at ho
  rw [List.mem_eraseDups, List.mem_append] at ho
  rcases ho with ho | ho
  · obtain ⟨hm, hr⟩ := List.mem_filter.mp ho
    obtain ⟨hm, hl⟩ := List.mem_filter.mp hm
    have hl' : GridCO.headLabel? o = some s := by
      simpa only [Nat.add_sub_cancel, beq_iff_eq] using hl
    have hm' : o ∈ (V2.D.Run.stateBefore E rho ih y).st.base.votes := by
      change o ∈ (clock p _ _).base.votes at hm
      rwa [(clock_vn _ _).1] at hm
    change GridCO.resolvedBefore (actView dst) o _ = true at hr
    unfold GridCO.resolvedBefore at hr
    have hres : GridCO.resolvedHead? (actView dst) o = some K := by
      cases hc : GridCO.resolvedHead? (actView dst) o with
      | none => simp only [hc, Bool.false_eq_true] at hr
      | some C =>
        have hmC := (List.mem_filter.mp (resolvedHead_mem _ o hc)).1
        have he := baseBlocks_rootInj p dst hDst C hmC K hKdst
          (Option.some.inj ((resolvedHead_root _ o hc).symm.trans ht))
        exact congrArg some he
    have hactive := resolvedHead_mem _ o hres
    rw [hres, hl'] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.getD_some, Nat.add_sub_cancel] at hr
    obtain ⟨⟨hslot, hvstamp⟩, hbstamp⟩ := hr
    have hKpre : K ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks := by
      have hm := (List.mem_filter.mp hactive).1
      change K ∈ (clock p _ _).base.blocks at hm
      rwa [clock_base_blocks] at hm
    change GridCO.stampBlock (clock p _ _).base K < _ at hbstamp
    rw [fgsa_clock_block_stamp E rho ih y _ K hKpre] at hbstamp
    have hKsrc := fgsa_scoreRun_block_backward_on (hroots := hroots)
      E rho hE s hx hip D K hScope hgeom.source_floor hDK hKpre hbstamp
    change GridCO.stampVote (clock p _ _).base o < _ at hvstamp
    rw [scoreRun_clock_vote_stamp E rho ih y _ o hm'] at hvstamp
    obtain ⟨K', he⟩ := scoreRun_vote_shape o s i hl' hi
    have hraw : o ∈ proposerVotes src (s + 1) := by
      have hr := fgsa_scoreRun_frozen_vote_relay_on E rho hE s hx hip D hScope i K' (he ▸ hm')
        (he ▸ hvstamp)
      rw [← he] at hr
      exact hr.resolve_right (by rw [hclean]; exact Bool.noConfusion)
    apply finish
    apply List.mem_filter.mpr
    refine ⟨hraw, ?_⟩
    change (match GridCO.resolvedHead? (actView src) o with
      | some C => Block.preceq (eraseFG src.fg.F) C && decide (C.slot ≤ s + 1 - 1)
      | none => false) = true
    rw [actView_resolve_target p src hSrc hdomain o hKsrc ht]
    exact Bool.and_eq_true_iff.mpr
      ⟨Gen.Pure.block_preceq_trans hgeom.source_floor hDK,
        decide_eq_true (by simpa only [Nat.add_sub_cancel] using hslot)⟩
  · obtain ⟨hm, _⟩ := List.mem_filter.mp ho
    obtain ⟨q, hq, hsup⟩ := List.mem_flatMap.mp hm
    rw [hpairs q hq] at hsup
    exact finish (pools.2.2 ▸ hsup)

theorem fgsa_score_eq_on_run_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hScope : ScoreServiceScope E rho ip ih x y s D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  intro src dst U U'
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have pools := fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2
  cases s with
  | zero =>
    have he := hp.2.2.2.2
    change (none : Option (Msg p.n)) = some (.proposal N) at he
    cases he
  | succ s =>
    have hg : N.erase ≠ .genesis := by
      intro hg
      have hs := pools.1
      rw [hg] at hs
      change 0 = s + 1 at hs
      omega
    obtain ⟨w, hw, hb, -⟩ := fgsa_stored_block_origin E rho ih y N.erase hadm hg
    obtain ⟨r, M, rfl, -⟩ := (metaInv_stateBefore E rho ih y).wireTree w hw
    have hB : M.erase = N.erase := Option.some.inj hb
    have hr := scoreRun_stored_label E rho hE ih y r M hw
    have hrs : r = s + 1 := hr.trans (hB ▸ pools.1)
    rw [hrs] at hw
    have heq := fgsa_scoreRun_stored_proposal_eq E rho hE ih y (s + 1) M hw
      (hseat ▸ hx) _ rfl ⟨_, by rw [hseat]; exact ⟨ip, hip, hem⟩⟩
    rw [heq] at hw
    have hadm' : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
        (V2.D.Run.stateBefore E rho ih y).st.proposals := hw
    apply fgsa_score_eq_on_retained_suffix p src dst D U (proposerSupport src (s + 1))
      U' (headSupport p dst (s + 1))
    · exact fgsa_scoreRun_raw_subset_restart E rho hE (s + 1) hip hseat hx
        (Nat.le_refl ih) N hem N hadm' hFN
    · exact fgsa_scoreRun_raw_extra_on E rho hE s hx hy hip hseat N hem D hScope
    · intro X hDX i hclean
      apply Bool.eq_iff_iff.mpr
      exact ⟨fgsa_scoreRun_support_forward_on (hroots := hroots)
        E rho hE (s + 1) hx hy hip hih N hem hadm' hFN D hgeom hScope X hDX i,
        fgsa_scoreRun_support_backward_on (hroots := hroots) E rho hE s hx hy hip hseat
          N hem D hgeom hScope X hDX i hclean⟩

private theorem walkRun_reflected_voter_block_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (_hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D X C : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))) D)
    (hDX : Block.Preceq D X) (hXQ : Block.Prec X N.erase.parent)
    (hp : C.parent? = some X)
    (hm : C ∈ erasedList
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1)))
      (voterBlocks p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1)))
        (s + 1)))
    (hScope : ScoreServiceScope E rho ip ih x y (s + 1) D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    C ∈ (clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams (s + 1))).base.blocks := by
  let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hCbase : C ∈ dst.base.blocks := (List.mem_filter.mp hm).1
  have hCpre : C ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks := by
    change C ∈ (clock p _ _).base.blocks at hCbase
    rwa [clock_base_blocks] at hCbase
  obtain ⟨A, hA, heA⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Bool.or_eq_true_iff.mp (Finset.mem_filter.mp hA).2 with hf | hc
  · have hf := of_decide_eq_true hf
    rw [heA] at hf
    change GridCO.stampBlock (clock p _ _).base C < _ at hf
    rw [fgsa_clock_block_stamp E rho ih y _ C hCpre] at hf
    have hf' : GridCO.stampBlock (V2.D.Run.stateBefore E rho ih y).st.base C <
        SA.freezeTime p.toParams s := by simpa only [Nat.add_sub_cancel] using hf
    have hb := fgsa_scoreRun_block_backward_on (hroots := hroots)
      E rho hE s hx hip D C hScope hgeom.source_floor
      (Gen.Pure.block_preceq_trans hDX (walkRun_parent_prefix hp)) hCpre hf'
    exact ((actView_blocks src C).mp hb).1
  · obtain ⟨P, hP, hslot, hAP⟩ := of_decide_eq_true hc
    have hPbase : eraseFG P ∈ dst.base.blocks :=
      (ht.baseTree _).mpr ⟨P, Next.tree_subset_TF p dst hP, rfl⟩
    have hPpre : eraseFG P ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks := by
      change eraseFG P ∈ (clock p _ _).base.blocks at hPbase
      rwa [clock_base_blocks] at hPbase
    have heP := fgsa_walkRun_current_block_eq E rho hE (s + 1) (Nat.succ_pos s) hx hip
      hseat N hem (eraseFG P) hPpre ((eraseFG_slot P).trans hslot)
    have hCb : Block.Preceq C N.erase := by simpa only [heA, heP] using eraseFG_preceq hAP
    have hmem := hem
    rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
    have hem' := (fgsa_emits_proposal E rho _ x _ (s + 1) _).mp hmem
    have hparent := fgsa_walkRun_proposal_parent p src (s + 1) _ N hem'.2.2.2.2
    have hne : X ≠ N.erase.parent := by
      intro he
      have hn := (Bool.and_eq_true_iff.mp hXQ).1
      simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
    have hpB : N.erase.parent? = some N.erase.parent := by rw [hparent.2.2]; exact hparent.2.1
    have hCQ := walkRun_child_before_parent hpB hp hCb hne
    rw [hparent.2.2] at hCQ
    exact walkRun_ancestor_stored p src hs (walkRun_head_stored p src hs _ _) hCQ

theorem fgsa_walkRun_reflected_block_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (_hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D X C : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))) D)
    (hDX : Block.Preceq D X) (hXQ : Block.Prec X N.erase.parent)
    (hp : C.parent? = some X)
    (hm : C ∈ erasedList
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1)))
      (storeFrame p.E p.cfg
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1))).fg
        (voterBlocks p
          (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (s + 1)))
          (s + 1))))
    (hScope : ScoreServiceScope E rho ip ih x y (s + 1) D)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    C ∈ (clock p (V2.D.Run.stateBefore E rho ip x).st
      (SA.proposalTime p.toParams (s + 1))).base.blocks := by
  apply walkRun_reflected_voter_block_on (hroots := hroots)
    E rho hE s hx _hy hip hseat N hem D X C hgeom hDX hXQ hp (hScope := hScope)
  obtain ⟨hC, hm⟩ := List.mem_filter.mp hm
  obtain ⟨A, hA, heA⟩ := of_decide_eq_true hm
  exact List.mem_filter.mpr ⟨hC, decide_eq_true ⟨A,
    ((KitFG.mem_filteredFrom_of_bridge
      p.E p.cfg (heightView p) (heightView_bridge p) _ _ A).mp hA).1, heA⟩⟩

theorem fgsa_ghost_transfer_sfx_on_run_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D)
    (hScope : ScoreServiceScope E rho ip ih x y s (eraseFG D))
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq N.erase.parent (headVote p dst s) := by
  intro dst
  let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
  have hmem := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmem
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hmem
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have pools := fgsa_scoreRun_proposal_pools p src s _ N hp.2.2.2.2
  have hsInv : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have htInv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hsrcslot : src.slot p = s := fgsa_proposal_slot (c := c) _ s
  have hdstslot : dst.slot p = s := fgsa_vote_slot (c := c) _ s
  have hb : N.erase ∈ dst.base.blocks := by change N.erase ∈ (clock p _ _).base.blocks; rwa
      [clock_base_blocks]
  have hpB : N.erase.parent? = some N.erase.parent := by rw [hparent.2.2]; exact hparent.2.1
  have hQP := walkRun_parent_prefix hpB
  have hsRe := Gen.Pure.walk_reanchor_of_dominated_suffix _ _ _ _ _
    hgeom.source_anchor hgeom.source_prefix
  have htRe := Gen.Pure.walk_reanchor_of_dominated_suffix _ _ _ _ _
    hgeom.target_anchor hgeom.target_prefix
  have hDQ : Block.Preceq (eraseFG D) N.erase.parent := by
    rw [hparent.2.2]
    exact Gen.Pure.walk_covers_of_dominated_suffix _ _ _ _ _
      (Gen.Pure.block_compatible_of_common hgeom.source_anchor (Gen.Pure.block_preceq_refl _))
      hgeom.source_prefix
  have hFN : Block.Preceq (eraseFG dst.fg.F) N.erase :=
    Gen.Pure.block_preceq_trans hgeom.target_floor
      (Gen.Pure.block_preceq_trans hDQ hQP)
  have hscore := fgsa_score_eq_on_run_on (hroots := hroots)
    E rho hE s hx hy hip hih hseat
    N hem hadm hFN (eraseFG D) hgeom.toScoreRunGeometry hScope
  have hcount := hscore.2.2.1
  have hscores := hscore.2.2.2
  have hcover : Block.Preceq N.erase.parent
      (GridCO.ghost (eraseFG D) (erasedList src (fullTree p src))
        (GridCO.goldfishScore src.base.blocks (proposerVotes src s) (proposerSupport src s))
        (eligible p src (proposerVotes src s) (proposerSupport src s))) := by
    rw [← hsRe]
    change Block.Preceq N.erase.parent (getHead p src _ _)
    rw [hparent.2.2]
    exact Gen.Pure.block_preceq_refl _
  have helig (C : Block) (hC : C ∈ src.base.blocks)
      (hDC : Block.Preceq (eraseFG D) C)
      (hDP : Block.Preceq (eraseFG D) C.parent) :
      eligible p src (proposerVotes src s) (proposerSupport src s) C =
        eligible p dst (headVotes p dst s) (headSupport p dst s) C := by
    have hCs : C.slot < s := (fgsa_stored_block_slots E rho hE.toScheduleWellFormed
      hip hparent.1).2.1 C hC
    apply Bool.eq_iff_iff.mpr
    rw [fgsa_walkRun_eligible_iff p src _ _ D C hgeom.source_lo hDP
      (by rw [hsrcslot]; exact Nat.ne_of_lt hCs)]
    rw [fgsa_walkRun_eligible_iff p dst _ _ D C hgeom.target_lo hDP
      (by rw [hdstslot]; exact Nat.ne_of_lt hCs)]
    rw [hcount, hscores C hDC]
  have hkeep : Gen.Pure.SuffixPersists (eraseFG D) N.erase.parent
      (erasedList src (fullTree p src))
      (erasedList dst (filteredFrom p.E p.cfg (controls p dst) (voterBlocks p dst s)))
      (GridCO.goldfishScore src.base.blocks (proposerVotes src s) (proposerSupport src s))
      (eligible p src (proposerVotes src s) (proposerSupport src s))
      (eligible p dst (headVotes p dst s) (headSupport p dst s)) := by
    intro X C hDX _ hstep hCQ
    obtain ⟨hC, hpC, heC⟩ := walkRun_step_child _ _ _ _ _ hstep
    have hDC := Gen.Pure.block_preceq_trans hDX (walkRun_parent_prefix hpC)
    refine ⟨fgsa_walkRun_path_domain_filtered p dst htInv s D C N.erase
      hgeom.target_floor hgeom.target_Z hgeom.target_lo hb pools.1 hDC
      (Gen.Pure.block_preceq_trans hCQ hQP), ?_⟩
    rw [← helig C (List.mem_filter.mp hC).1 hDC (by rw [walkRun_parent_eq hpC]; exact hDX)]
    exact heC
  have hreflect : Gen.Pure.SuffixReflects (eraseFG D) N.erase.parent
      (erasedList src (fullTree p src))
      (erasedList dst (filteredFrom p.E p.cfg (controls p dst) (voterBlocks p dst s)))
      (eligible p src (proposerVotes src s) (proposerSupport src s))
      (eligible p dst (headVotes p dst s) (headSupport p dst s)) := by
    intro X C hDX hXQ hC hpC heC
    have hDC := Gen.Pure.block_preceq_trans hDX (walkRun_parent_prefix hpC)
    have hstored : C ∈ src.base.blocks := by
      cases s with
      | zero => exact (Nat.lt_irrefl 0 hparent.1).elim
      | succ r =>
        apply walkRun_reflected_voter_block_on (hroots := hroots)
          E rho hE r hx hy hip hseat
          N hem (eraseFG D) X C hgeom.toScoreRunGeometry hDX hXQ hpC (hScope := hScope)
        obtain ⟨hCbase, hCframe⟩ := List.mem_filter.mp hC
        obtain ⟨A, hA, heA⟩ := of_decide_eq_true hCframe
        exact List.mem_filter.mpr ⟨hCbase, decide_eq_true ⟨A,
          ((KitFG.mem_filteredFrom_of_bridge
            p.E p.cfg (heightView p) (heightView_bridge p) _ _ A).mp hA).1, heA⟩⟩
    refine ⟨fgsa_walkRun_full_domain p src hsInv D C hgeom.source_floor hgeom.source_Z
      hgeom.source_lo hstored hDC, ?_⟩
    rw [helig C hstored hDC (by rw [walkRun_parent_eq hpC]; exact hDX)]
    exact heC
  have hsfx : Gen.Pure.SuffixScoresAgree (eraseFG D) N.erase.parent
      (erasedList dst (filteredFrom p.E p.cfg (controls p dst) (voterBlocks p dst s)))
      (GridCO.goldfishScore src.base.blocks (proposerVotes src s) (proposerSupport src s))
      (GridCO.goldfishScore dst.base.blocks (headVotes p dst s) (headSupport p dst s))
      (eligible p dst (headVotes p dst s) (headSupport p dst s)) := by
    intro X C hDX _ _ hpC _
    exact (hscores C (Gen.Pure.block_preceq_trans hDX (walkRun_parent_prefix hpC))).symm
  have hresult := Gen.Pure.ghost_transfer_sfx _ _ _ _ _ _ _ _ hDQ hcover hkeep hreflect hsfx
  change Block.Preceq N.erase.parent (headVote p dst s)
  rw [fgsa_headVote_eq_filtered]
  rw [ite_eq_right (Nat.ne_of_gt hparent.1)]
  change Block.Preceq N.erase.parent (GridCO.ghost _ _ _ _)
  rw [htRe]
  exact hresult

/-- The frozen walk target uses the exact named backward target service. -/
theorem fgsa_walkRun_frozen_block_on : type_of% (@fgsa_scoreRun_block_backward_on) :=
  @fgsa_scoreRun_block_backward_on

end AvailableChain.FGSA.Run
end
