module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedPersist
public import AvailableChainFGSAProofs.Proofs.Shared.ExactHead

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure
open RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:956–958, H.17:3006–3012 (design 812–814,2865–2872);
spec 992–1017, 1555–1581. Class (iii). DC: INTENTIONAL; the scheduled HEAD clock
preserves stored blocks and bounds their slots by the current label. -/
theorem fgsa_headRead_block_slots (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.voteTime p.toParams s))) :
    ∀ C ∈ (clock p (rho.stateBefore E i v).st (SA.voteTime p.toParams s)).base.blocks,
      C.slot ≤ s := by
  intro C hm
  rw [clock_base_blocks] at hm
  have hn := fgsa_preTick_now_le E rho hs hi
  have hslot := Internal.slotOf_mono (p := p) hn
  have ht : p.slotOf (SA.voteTime p.toParams s) = s := by
    simpa only [(fgsa_postClock_slot (c := c) (rho.stateBefore E i v) _).2] using
      fgsa_vote_slot (c := c) (rho.stateBefore E i v) s
  exact ((fgsa_stateBefore_bounds E rho hs i v).1 C hm).trans (ht ▸ hslot)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:367–373; 21 H.17:3006–3012 (design 2865–2872);
spec 1387–1401, 1555–1581. Class (iii). DC: INTENTIONAL; accepted proposal validity
supplies strict parent-slot growth. Row metadata passes through unchanged. -/
theorem fgsa_headRead_child_slot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (v : V) (s : Slot) (B C : Block)
    (hm : C ∈ (clock p (rho.stateBefore E i v).st (SA.voteTime p.toParams s)).base.blocks)
    (hp : C.parent? = some B) : B.slot < C.slot := by
  rw [clock_base_blocks] at hm
  have hg : C ≠ .genesis := by rintro rfl; cases hp
  obtain ⟨w, hw, hb, j, o, t, -, hd, ho, -⟩ := fgsa_stored_block_origin E rho i v C hm hg
  obtain ⟨r, N, rfl, -⟩ := (metaInv_stateBefore E rho i v).wireTree w hw
  have hQ : N.erase = C := Option.some.inj hb
  have hf := hE.wire j v o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  have hlt : N.erase.parent.slot < N.erase.slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2
  rw [hQ] at hlt
  have hpar := fgsa_parent_eq_of_some hp
  simpa only [hpar] using hlt

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:956–958, H.17:3006–3012 (design 812–814,2865–2872);
spec 1387–1401, 1555–1581. Class (iii). DC: INTENTIONAL; old children reflect to the
terminal source, current children equal b, and future children are absent. -/
theorem fgsa_exactHeadGeometry_of_retained_endpoint
    (p : Params) (src dst : State p.n) (s : Slot) (b : Block)
    (hsourceStop : NoEligibleChild (S p src) (es p src s) b.parent)
    (h : RetainedEndpointGeometry p src dst s b) : ExactHeadGeometry p dst s b := by
  have hel : et p dst s b = true := by
    unfold et eligible
    rw [h.proposal_slot, h.target_slot]
    simp only [beq_self_eq_true, Bool.or_true]
  constructor
  · rw [fgsa_domainR_eq_treeStoreFrameView]
    refine ⟨h.proposal_mem, h.proposal_parent, hel, ?_⟩
    intro C hm hp he
    rcases Nat.lt_or_eq_of_le (h.no_future C hm) with hold | hcurrent
    · obtain ⟨hs, he'⟩ := h.old_reflects C hm hp hold he
      have hn := hsourceStop C hs hp
      simp only [he', Bool.true_eq_false] at hn
    · exact h.current_unique C hm hcurrent
  · rw [fgsa_domainR_eq_treeStoreFrameView]
    intro C hm hp
    have hlt := h.child_slot C hm hp
    have hle := h.no_future C hm
    rw [h.proposal_slot] at hlt
    exact (Nat.not_lt_of_ge hle hlt).elim

-- Local unfolding steps for two model definitions; stated by `rfl` here so that this
-- module exports no equation lemma of a definition it does not own (B3a).
private theorem erasedList_unfold {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) :
    erasedList st X = st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b)) := rfl

private theorem headInTree_unfold (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) :
    headInTree p st tree raw support =
      GridCO.ghost (liveRoot p st) tree (GridCO.goldfishScore st.base.blocks raw support)
        (eligible p st raw support) := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:947–958, H.17:2987–3012 (design 798–814,2847–2872);
spec 1387–1401, 1555–1581. Class (iii). DC: INTENTIONAL;
ProposalWalkTransportCore.lean:162,259 supplies retained walk transport.
ROOT-DIGEST W2. Use the named view bridge at the actual HEAD domain. -/
theorem fgsa_headVote_covers_parent_of_retained_geometry
    (p : Params) (src dst : State p.n) (s : Slot) (hs : s ≠ 0)
    (D : FGBlock (Fin p.n)) (b Kc : Block)
    (hsourceRoot : ∀ A ∈ S p src, ∀ B ∈ S p src, A.root = B.root → A = B)
    (htargetRoot : ∀ A ∈ T p dst s, ∀ B ∈ T p dst s, A.root = B.root → A = B)
    (hparent : getHead p src (proposerVotes src s) (proposerSupport src s) = b.parent)
    (h : RetainedWalkRunGeometry p src dst s D b Kc) :
    Block.Preceq b.parent (headVote p dst s) := by
  have hp := (fgsa_ordinary_parent_of_live_prefix_filtered p src
    (proposerVotes src s) (proposerSupport src s) b.parent hsourceRoot hparent
    (by simpa only [BestAncestry_def, S, fgsa_fullTree_eq_filtered, erasedList_unfold,
      z, ap, ss, es] using h.ordinary_prefix)).2
  have hsource : Block.Preceq b.parent (GridCO.ghost (z p src) (S p src)
      (ss src s) (es p src s)) := by
    simpa only [S, fgsa_fullTree_eq_filtered, erasedList_unfold, z, ss, es, hp] using
      block_preceq_refl b.parent
  have hc := walk_covers_of_retained_transport (z p src) (ay p dst) Kc b.parent
    (S p src) (T p dst s) (ss src s) (ts p dst s) (es p src s) (et p dst s)
    htargetRoot hsource h.source_cut h.target_cut h.cut_parent h.target_prefix
    h.persists h.reflects h.scores
  unfold headVote
  rw [ite_eq_right hs]
  simpa only [fgsa_domainR_eq_treeStoreFrameView, headInTree_unfold, ay, ts, et] using hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:956–958, H.17:3006–3012 (design 812–814,2865–2872);
spec 1387–1401, 1555–1581. Class (iii). DC: INTENTIONAL; complete the endpoint fields
from actual emission, current-slot uniqueness and accepted block bounds. -/
theorem fgsa_retainedEndpoint_geometry_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hmem : N.erase ∈ T p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s)
    (hold : ∀ C ∈ T p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s,
      C.parent? = some N.erase.parent → C.slot < s →
      et p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s C = true →
      C ∈ S p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)) ∧
      es p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)) s C = true) :
    RetainedEndpointGeometry p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s N.erase := by
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p _ s _ N hp.2.2.2.2
  refine ⟨hold, hmem, hparent.2.2 ▸ hparent.2.1,
    (fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2).1,
    fgsa_vote_slot (c := c) _ s, ?_, ?_, ?_⟩
  · intro C hm hs
    apply fgsa_walkRun_current_block_eq E rho hE s hparent.1 hx hip hseat N hem C
    · simpa only [clock_base_blocks] using (List.mem_filter.mp hm).1
    · exact hs
  · intro C hm
    exact fgsa_headRead_block_slots E rho hE.toScheduleWellFormed hih C (List.mem_filter.mp hm).1
  · intro C hm hp
    exact fgsa_headRead_child_slot E rho hE ih y s N.erase C (List.mem_filter.mp hm).1 hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:927–958, H.17:2957–3012 (design 783–814,2818–2872);
spec 1387–1401, 1555–1581. Class (iii). DC: INTENTIONAL; per-reader retained geometry
for the scheduled HEAD clause. Admission is at the actual pre-clock tick. -/
structure RetainedExactHeadRunGeometry
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ip : Nat) (x : V) (s : Slot) (D : FGBlock (Fin p.n)) (b : Block) : Prop where
  admitted : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      b ∈ (rho.stateBefore E ih y).st.base.blocks
  walk : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedWalkRunGeometry p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D b Kc
  endpoint : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedEndpointGeometry p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s b

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6:927–958, H.17:2957–3012 (design 783–814,2818–2872);
spec 1387–1401, 1555–1581. Class (iii). DC: INTENTIONAL; S1–S8 produce all fields
from per-reader premises. E.proposal_mem supplies pre-clock admission, so
reflection has no outstanding admission premise at this packaging point. -/
theorem fgsa_retainedExactHead_geometry_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hWalkSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.proposalTime p.toParams s))
    (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    RetainedExactHeadRunGeometry E rho ip x s D N.erase := by
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hs := (fgsa_walkRun_proposal_parent p _ s _ N hp.2.2.2.2).1
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have supply : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))) →
      ∃ Kc, RetainedWalkRunGeometry p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (r + 1)))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) D N.erase
            Kc ∧
      RetainedEndpointGeometry p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (r + 1)))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) N.erase := by
    intro y hy ih hih
    obtain ⟨Kc, hr⟩ := hreads y hy ih hih
    obtain ⟨hw, hm, ho⟩ := fgsa_retainedWalk_geometry_on_run (hroots := hroots) E rho hE hN hDelta r
      hWalkSync hScoreSync hx hy hip hih hseat N hem D Kc hr
    exact ⟨Kc, hw, fgsa_retainedEndpoint_geometry_on_run E rho hE (r + 1)
      hx hip hih hseat N hem hm ho⟩
  constructor
  · intro y hy ih hih
    obtain ⟨Kc, hw, he⟩ := supply y hy ih hih
    simpa only [clock_base_blocks] using (List.mem_filter.mp he.proposal_mem).1
  · intro y hy ih hih
    obtain ⟨Kc, hw, he⟩ := supply y hy ih hih
    exact ⟨Kc, hw⟩
  · intro y hy ih hih
    obtain ⟨Kc, hw, he⟩ := supply y hy ih hih
    exact he

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:341–373; 21 H.6:956–958 (design 812–814); spec 1387–1394.
Class (iii). DC: INTENTIONAL; the full proposer tree is ancestor closed
above its actual anchor, so its finite walk has no eligible child. -/
theorem fgsa_retained_source_stop (p : Params) (src : State p.n) (s : Slot)
    (h : CStoreInv p src) (b : Block)
    (hp : getHead p src (proposerVotes src s) (proposerSupport src s) = b.parent) :
    NoEligibleChild (S p src) (es p src s) b.parent := by
  have ht := fgsa_headInTree_noEligibleChild p src h src.fg.TF (fun _ hm => hm)
    (KitFG.ancestor_closed_of_parent_closed _ h.fg.closed)
    (proposerVotes src s) (proposerSupport src s)
  have he : fullTree p src = filteredFrom p.E p.cfg (controls p src) src.fg.TF := by
    rw [fgsa_fullTree_eq_filtered]
  rw [← he] at ht
  rw [← hp]
  exact ht

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 00:126–142; 21 H.6:956–958, H.17:3006–3012,
H.22:3109–3114 (design 812–814,2865–2872). Class (iii).
DC: INTENTIONAL; the HEAD reader has the approved joined scope.
Apply EH:57 at the local pivot ay. Timing and admission are already
resolved by the geometry supplier; gate service remains separate. -/
theorem exactService_head_of_retained_proposal
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V}
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : RetainedExactHeadRunGeometry E rho ip x s D N.erase) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  intro hhorizon y hy hjoined
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hstop := fgsa_retained_source_stop p src s
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _) N.erase hparent.2.2.symm
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨ih, hih, _⟩ := fgsa_tick_total E rho hE.toScheduleWellFormed hDelta y hy
    (4 * s + 1) (hvt ▸ hhorizon)
    (by simpa only [hvt] using hjoined.1)
  rw [hvt] at hih
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  obtain ⟨Kc, hw⟩ := hgeom.walk y hy ih hih
  have hc := fgsa_headVote_covers_parent_of_retained_geometry p src dst s
    (Nat.ne_of_gt hparent.1) D N.erase Kc
    (erasedList_rootInj p src (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _) _)
    (erasedList_rootInj p dst (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _) _)
    hparent.2.2.symm hw
  have he := fgsa_exactHeadGeometry_of_retained_endpoint p src dst s N.erase hstop
    (hgeom.endpoint y hy ih hih)
  have hexact := fgsa_headVote_exact_of_covered_parent p dst s (Nat.ne_of_gt hparent.1)
    (ay p dst) N.erase
    (erasedList_rootInj p dst (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _) _)
    (Or.inr ⟨block_preceq_refl _, hw.target_parent⟩) hw.target_parent hc he
  have ht := fgsa_tickIdx_of_event p c E rho hE.toScheduleWellFormed hih
  change (postClock E rho y (SA.voteTime p.toParams s)).map _ = some N.erase
  rw [postClock_def, preTick_def, ht]
  change some (headVote p dst s) = some N.erase
  exact congrArg some hexact

structure RetainedExactHeadRunGeometryOn
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ip : Nat) (x : V) (s : Slot) (D : FGBlock (Fin p.n)) (b : Block) : Prop where
  admitted : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
    joinedAt p E rho y s (SA.voteTime p.toParams s) →
      b ∈ (rho.stateBefore E ih y).st.base.blocks
  walk : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
    joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∃ Kc, RetainedWalkRunGeometry p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D b Kc
  endpoint : ∀ y ∈ rho.honest, ∀ ih,
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
    joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedEndpointGeometry p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s b


theorem fgsa_retainedExactHead_geometry_on_run_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc)
    (hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedServiceScope E rho ip ih x y s N)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    RetainedExactHeadRunGeometryOn E rho ip x s D N.erase := by
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hs := (fgsa_walkRun_proposal_parent p _ s _ N hp.2.2.2.2).1
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have supply : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))) →
      joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1)) →
      ∃ Kc, RetainedWalkRunGeometry p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (r + 1)))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) D N.erase
            Kc ∧
      RetainedEndpointGeometry p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (r + 1)))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) N.erase := by
    intro y hy ih hih hjoined
    obtain ⟨Kc, hr⟩ := hreads y hy ih hih hjoined
    obtain ⟨hw, hm, ho⟩ := fgsa_retainedWalk_geometry_on_run_on (hroots := hroots) E rho hE r
      hx hy hip hih hseat N hem D Kc hr (hScopes y hy ih hih hjoined)
    exact ⟨Kc, hw, fgsa_retainedEndpoint_geometry_on_run E rho hE (r + 1)
      hx hip hih hseat N hem hm ho⟩
  constructor
  · intro y hy ih hih hjoined
    obtain ⟨Kc, hw, he⟩ := supply y hy ih hih hjoined
    simpa only [clock_base_blocks] using (List.mem_filter.mp he.proposal_mem).1
  · intro y hy ih hih hjoined
    obtain ⟨Kc, hw, he⟩ := supply y hy ih hih hjoined
    exact ⟨Kc, hw⟩
  · intro y hy ih hih hjoined
    obtain ⟨Kc, hw, he⟩ := supply y hy ih hih hjoined
    exact he

theorem exactService_head_of_retained_proposal_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V}
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : RetainedExactHeadRunGeometryOn E rho ip x s D N.erase) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  intro hhorizon y hy hjoined
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hstop := fgsa_retained_source_stop p src s
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _) N.erase hparent.2.2.symm
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨ih, hih, _⟩ := fgsa_tick_total E rho hE.toScheduleWellFormed hDelta y hy
    (4 * s + 1) (hvt ▸ hhorizon)
    (by simpa only [hvt] using hjoined.1)
  rw [hvt] at hih
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  obtain ⟨Kc, hw⟩ := hgeom.walk y hy ih hih hjoined
  have hc := fgsa_headVote_covers_parent_of_retained_geometry p src dst s
    (Nat.ne_of_gt hparent.1) D N.erase Kc
    (erasedList_rootInj p src (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _) _)
    (erasedList_rootInj p dst (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _) _)
    hparent.2.2.symm hw
  have he := fgsa_exactHeadGeometry_of_retained_endpoint p src dst s N.erase hstop
    (hgeom.endpoint y hy ih hih hjoined)
  have hexact := fgsa_headVote_exact_of_covered_parent p dst s (Nat.ne_of_gt hparent.1)
    (ay p dst) N.erase
    (erasedList_rootInj p dst (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _) _)
    (Or.inr ⟨block_preceq_refl _, hw.target_parent⟩) hw.target_parent hc he
  have ht := fgsa_tickIdx_of_event p c E rho hE.toScheduleWellFormed hih
  change (postClock E rho y (SA.voteTime p.toParams s)).map _ = some N.erase
  rw [postClock_def, preTick_def, ht]
  change some (headVote p dst s) = some N.erase
  exact congrArg some hexact

end AvailableChain.FGSA.Run
end
