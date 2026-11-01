module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.SupportPerm -- shake: keep

public section

/-! H-REPAIR G-H6 (plan steps 2, 6, 7, 8; blueprint 21 H.6:910–986). The retained H.6
input at an honest proposal after a repair threshold. The prior support of every live
lease target is measured in the ACTUAL proposer pool of the preceding honest HEAD batch.
The lease premise `RepairLeaseCover` is the output of the last-write split. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Receiver-local retained services for one repaired proposal slot.
Every retained score and history obligation stays in its own object service scope. -/
structure RepairHeadServices (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (s : Slot)
    (ip : Nat) (x : V) (N : NamedProposal p.n) : Prop where
  prior : ProposalSupportScope E rho ip x (s - 1) (SA.proposalTime p.toParams s)
  scopes : ∀ y ∈ rho.honest, ∀ (ih : Nat),
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
    joinedAt p E rho y s (SA.voteTime p.toParams s) →
    Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams s) y).st.fg.F) N.erase →
    RetainedServiceScope E rho ip ih x y s N

/-- The retained proposal service supplies its exact target under the same reader floor. -/
theorem RepairHeadServices.target {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {s : Slot} {ip : Nat} {x : V} {N : NamedProposal p.n}
    (h : RepairHeadServices E rho s ip x N) {ih : Nat} {y : V}
    (hy : y ∈ rho.honest)
    (hi : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hj : joinedAt p E rho y s (SA.voteTime p.toParams s))
    (hf : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams s) y).st.fg.F) N.erase) :
    TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y :=
  fgsa_target_service_of_proposal E rho s N _ _ y (h.scopes y hy ih hi hj hf).proposal

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:928–944 (H.6, live leases at the preceding HEAD batch); plan H-REPAIR
step 4–6. DC: INTENTIONAL every live lease row at an honest proposal or HEAD read of slot s
targets a prefix of every honest HEAD of label s − 1. The last-write split supplies it. -/
def RepairLeaseCover (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (s : Slot) : Prop :=
  ∀ i z t (row : Block × Nat × Time), z ∈ rho.honest →
    rho.events[i]? = some (.tick z t) → SA.proposalTime p.toParams s ≤ t →
    t ≤ SA.voteTime p.toParams s → row ∈ (storeAt p c E rho i z).base.obligations →
    t < row.2.2 → ∀ y ∈ rho.honest, ∀ K, headAtLabel p c E rho y (s - 1) = some K →
      Block.Preceq row.1 K

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:928–944; spec 648–655. DC: SAME the live root is the root Z or a live lease
target in the full filtered tree. -/
theorem repair_liveRoot_cases (st : State p.n) :
    liveRoot p st = eraseFG (controls p st).Z ∨
      ∃ row ∈ st.base.obligations, st.base.now < row.2.2 ∧
        (∃ X ∈ fullTree p st, eraseFG X = row.1) ∧ liveRoot p st = row.1 := by
  unfold liveRoot
  dsimp only
  rcases Gen.Pure.foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
  · exact Or.inl he
  · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
    split at hrow
    · rename_i hc
      have hb := Bool.and_eq_true_iff.mp hc
      exact Or.inr ⟨row, hr, of_decide_eq_true hb.1, of_decide_eq_true hb.2,
        (Option.some.inj hrow).symm⟩
    · cases hrow

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 01 §4.3; spec 616–633. DC: SAME F is below the active root Z. -/
theorem repair_F_preceq_Z (st : State p.n) (hs : CStoreInv p st) :
    FGBlock.Preceq st.fg.F (controls p st).Z := by
  unfold Controls.Z
  split
  · exact hs.fg.FJ
  · exact KitFG.preceq_refl _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:928–944 (H.6 prior support), 709–715 (H.2 S2 counts); plan
H-REPAIR step 6.
DC: INTENTIONAL a target L that every honest label-r HEAD covers is, at the honest
proposer read of slot r + 1 inside the phase, below the ordinary root or has retained prior
support in the ACTUAL proposer pool: an honest strict majority, smaller rival scores, and a
full-store witness of L at the floor. The count uses the honest batch of label r. -/
theorem repair_prior_support [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {r : Slot} {L : Block} (hhead : u ≤ SA.voteTime p.toParams r)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq L K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hScope : ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1)))
    (hCut : HealingWindow p E 1 r)
    (hv : SA.proposalTime p.toParams (r + 1) ≤ v) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (r + 1))
    Block.Preceq L (z p src) ∨ RetainedPriorSupport p src (r + 1) L := by
  classical
  intro src
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hvp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams r ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvp).trans hv
  have hgstr : E.t_GST ≤ SA.voteTime p.toParams r := hgst.trans hhead
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon := hvv.trans hphase.2.1
  have hinv : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hdfg : src.fg = (storeAt p c E rho ip x).fg := clock_fg p _ _
  have hRd : controls p src = R_at p c E rho ip x := by
    change KitFG.treeStoreControlsView (heightView p) src.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho ip x).fg
    rw [hdfg]
  -- The frame witness of the proposer's own label-r HEAD.
  obtain ⟨jx, hjx⟩ := healing_support_vote_tick E rho hS hDelta hx r hhorr
    (hrec.awake x hx _ hgstr hhorr)
  have hhl : headAtLabel p c E rho x r = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jx x).st (SA.voteTime p.toParams r)) r) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjx]
    rfl
  obtain ⟨W, hW, hLW, hZW, hFW, hloW⟩ := healing_support_frame_at
    (hroots := hrec.base.receiptIdealization)
    E rho (fun _ => mono) crossing hE
    hDelta hrec.sync hgst hphase hhead (hvp.trans hv) hx hjx
    x (healing_carriers_window_at p c E rho hrec hCut
        hScope.carriers hx hip hvp
      jx x hx hjx) (hcover x hx _ hhl) hx
    (healing_support_idxBefore_le p c E rho hS hip hvp)
    (healing_support_idxBefore_le p c E rho hS hip
      (hhead.trans ((le_add_of_nonneg_right hd.le).trans hvp)))
    (healing_phase_lt_timeIdx p c E rho hS hip hv).le
  have hWs : W ∈ src.fg.TF := hdfg ▸ hW
  have hFW' : Block.Preceq (eraseFG src.fg.F) (eraseFG W) := by
    rw [hdfg]
    exact eraseFG_preceq hFW
  rcases Gen.Pure.block_preceq_total_of_common hFW' hLW with hFL | hLF
  swap
  · left
    exact Gen.Pure.block_preceq_trans hLF (eraseFG_preceq (repair_F_preceq_Z src hinv))
  right
  have hFL0 : Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) L := hdfg ▸ hFL
  -- The selected joined batch in the actual proposer pool.
  let Hon : Finset (Fin p.n) := healingJoinedSeats E rho r
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := healing_proposal_batch_seat E rho hrec mono
    crossing hgst hphase hhead hcover hx hip hScope hCut hv hFL0 k
    ((healingJoinedSeats_mem E rho r k).mp hk).1
    ((healingJoinedSeats_mem E rho r k).mp hk).2
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := hScope.batch
  have hother : ((GridCO.seats p.n (proposerVotes src (r + 1))).toFinset \ Hon).card ≤
      (Gen.V2.Duty.faulty rho).card := hScope.rivals
  obtain ⟨_, _, hpath, hconflict, _⟩ := Gen.AC.Root.batch_counts src.base.blocks
    (proposerVotes src (r + 1)) (proposerVotes src (r + 1)) (proposerSupport src (r + 1))
    Hon Hon.card (Gen.V2.Duty.faulty rho).card L (fun _ h => h)
    (fun _ ho => (List.mem_filter.mp ho).1) rfl (fun k hk => (hseat k hk).2)
    (fun k hk => (hseat k hk).1) hother hb
  obtain ⟨hscore, hmajority⟩ := hpath L (Gen.Pure.block_preceq_refl L)
  refine ⟨?_, ⟨W, hWs, hLW, ?_⟩, hmajority, ?_⟩
  · have hZW' : Block.Preceq (z p src) (eraseFG W) := by
      change Block.Preceq (eraseFG (controls p src).Z) (eraseFG W)
      rw [hRd]
      exact eraseFG_preceq hZW
    exact Gen.Pure.block_compatible_of_common hZW' hLW
  · rw [hRd]
    exact hloW
  · intro B hB
    have h1 := hconflict B hB
    have h2 := hb.lt
    change GridCO.goldfishScore src.base.blocks (proposerVotes src (r + 1))
      (proposerSupport src (r + 1)) B < GridCO.goldfishScore src.base.blocks
        (proposerVotes src (r + 1)) (proposerSupport src (r + 1)) L
    omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783; spec 616–633. DC: SAME the clock keeps the FG controls. -/
theorem repair_controls_clock (st : State p.n) (t : Time) :
    controls p (clock p st t) = controls p st := by
  change KitFG.treeStoreControlsView (heightView p) (clock p st t).fg =
    KitFG.treeStoreControlsView (heightView p) st.fg
  rw [clock_fg]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783 (H.3); plan H-REPAIR step 6 (H-FRAME witness).
DC: INTENTIONAL the live start of a store with a nonempty full domain is below a full-store
witness at the floor. A copy of the private H-FRAME selector argument. -/
theorem repair_liveRoot_witness (st : State p.n) (hi : CStoreInv p st)
    (hne : (fullTree p st).Nonempty) :
    ∃ W ∈ st.fg.TF, Block.Preceq (liveRoot p st) (eraseFG W) ∧
      (controls p st).lo ≤ (heightView p W).h := by
  have hZ : (controls p st).Z ∈ fullTree p st := by
    have hclosed : ∀ B ∈ st.fg.TF, ∀ A, FGBlock.Preceq A B → A ∈ st.fg.TF := by
      intro B hB A hAB
      obtain ⟨Q, hQ, he⟩ := eraseFG_ancestor_mem hi.fg.closed hB (eraseFG_preceq hAB)
      exact (eraseFG_injective he) ▸ hQ
    rw [fgsa_fullTree_eq_filtered] at hne ⊢
    apply KitFG.filteredFrom_Z_mem p.E p.cfg _ _ hclosed _ hne
    unfold Controls.Z
    split
    · exact hi.fg.FJ
    · exact KitFG.preceq_refl _
  have hmem : ∃ B ∈ fullTree p st, eraseFG B = liveRoot p st := by
    rcases repair_liveRoot_cases st with he | ⟨row, _, _, ⟨B, hB, heB⟩, he⟩
    · exact ⟨_, hZ, he.symm⟩
    · exact ⟨B, hB, heB.trans he.symm⟩
  obtain ⟨B, hB, heB⟩ := hmem
  obtain ⟨_, _, _, W, hW, hBW, hlo⟩ := (KitFG.mem_filteredFromView _ _ _ _).mp hB
  exact ⟨W, hW, heB ▸ eraseFG_preceq hBW, hlo⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1153–1171; plan H-REPAIR step 6. DC: INTENTIONAL a local frontier carrier
makes the full domain of an honest store nonempty (copy of the private H-FRAME lemma). -/
theorem repair_fullTree_nonempty (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho) {i : Nat} {x : V} (hx : x ∈ rho.honest) :
    (fullTree p (storeAt p c E rho i x)).Nonempty := by
  obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho i x
  obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
  exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
    ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:749–783; plan H-REPAIR step 2. DC: SAME an earlier event time gives an
earlier index in the sorted schedule. -/
theorem repair_idx_lt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {a b : Nat} {ea eb : V2.Event V (Obj p)}
    (ha : rho.events[a]? = some ea) (hb : rho.events[b]? = some eb)
    (hlt : ea.time < eb.time) : a < b :=
  lt_of_lt_of_le ((Gen.V2.Duty.index_lt_idxBefore_iff hs ha eb.time).mpr hlt)
    (healing_support_idxBefore_le p c E rho hs hb le_rfl)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:947–958 (H.6 trunk), H.5:856–889, IF.3(c); plan H-REPAIR step 6.
DC: INTENTIONAL the fixed-phase frame of an honest proposer read at t_s and an honest HEAD
read at v_s: equal floors; the proposer live start has a full-store witness; when the
reader starts strictly below the proposer root (F-root phase only), RXing puts the
proposer F below every reader block at the floor. -/
theorem repair_h6_frame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho) (hS : V2.D.ScheduleWellFormed E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} (hu : u ≤ SA.proposalTime p.toParams s) (hvq : SA.voteTime p.toParams s ≤ v)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s))) :
    RetainedH6Frame p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s := by
  have hd := p.deltaPos
  have htv : SA.proposalTime p.toParams s < SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + p.Δ
    linarith
  have hip_ih : ip < ih := repair_idx_lt E rho hS hip hih htv
  have hxi := healing_settled_frame_strict p c E rho crossing u v m J contested hphase ip x
    (healing_support_idxBefore_le p c E rho hS hip hu)
    (healing_phase_lt_timeIdx p c E rho hS hip (htv.le.trans hvq)).le hx
  have hyi := healing_settled_frame_strict p c E rho crossing u v m J contested hphase ih y
    (healing_support_idxBefore_le p c E rho hS hih (hu.trans htv.le))
    (healing_phase_lt_timeIdx p c E rho hS hih hvq).le hy
  have hcs := repair_controls_clock (storeAt p c E rho ip x) (SA.proposalTime p.toParams s)
  have hcd := repair_controls_clock (storeAt p c E rho ih y) (SA.voteTime p.toParams s)
  have hlo : (controls p (storeAt p c E rho ip x)).lo =
      (controls p (storeAt p c E rho ih y)).lo := hxi.2.2.1.trans hyi.2.2.1.symm
  have hfgs : (clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams s)).fg =
      (storeAt p c E rho ip x).fg := clock_fg p _ _
  have hfgd : (clock p (storeAt p c E rho ih y) (SA.voteTime p.toParams s)).fg =
      (storeAt p c E rho ih y).fg := clock_fg p _ _
  have hinvs : CStoreInv p (clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams s)) :=
    cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hne : (fullTree p (clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams s))).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) _ _).Nonempty
    rw [hfgs]
    exact repair_fullTree_nonempty E rho crossing hx
  change RetainedH6Frame p (clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams s))
    (clock p (storeAt p c E rho ih y) (SA.voteTime p.toParams s)) s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcs, hcd]
    exact hlo
  · exact repair_liveRoot_witness _ hinvs hne
  · intro hlt W hW hloW
    cases J with
    | some J0 =>
      exfalso
      obtain ⟨_, _, hZx, _⟩ := hxi.2.2.2.1
      obtain ⟨_, _, hZy, _⟩ := hyi.2.2.2.1
      have hza : Block.Preceq (z p (clock p (storeAt p c E rho ip x)
          (SA.proposalTime p.toParams s))) (ay p (clock p (storeAt p c E rho ih y)
          (SA.voteTime p.toParams s))) := by
        have h := fgsa_Z_preceq_liveRoot p (clock p (storeAt p c E rho ih y)
          (SA.voteTime p.toParams s))
        change Block.Preceq (eraseFG (controls p _).Z) _
        rw [hcs, hZx, ← hZy, ← hcd]
        exact h
      have hb := Bool.and_eq_true_iff.mp hlt
      have he := block_preceq_antisymm hb.2 hza
      simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, false_and] at hb
    | none =>
      obtain ⟨_, hZx, ⟨K, hK, hKF, hKlt⟩, _⟩ := hxi.2.2.2.1
      have hWd : W ∈ (storeAt p c E rho ih y).fg.TF := by
        have h := Next.tree_subset_TF p _ (Finset.mem_filter.mp hW).1
        rwa [hfgd] at h
      have hloW' : (controls p (storeAt p c E rho ip x)).lo ≤ (heightView p W).h := by
        rw [hlo, ← hcd]
        exact hloW
      have hFW := crossing ip ih x y K W hx hip_ih.le hK hKF ⟨hy, hWd⟩
        (lt_of_lt_of_le hKlt hloW')
      change Block.Preceq (eraseFG (controls p _).Z) (eraseFG W)
      rw [hcs, hZx]
      exact eraseFG_preceq hFW
  · intro hlt P hP hPz
    cases J with
    | some J0 =>
      exfalso
      obtain ⟨_, _, hZx, _⟩ := hxi.2.2.2.1
      obtain ⟨_, _, hZy, _⟩ := hyi.2.2.2.1
      have hza : Block.Preceq (z p (clock p (storeAt p c E rho ip x)
          (SA.proposalTime p.toParams s))) (ay p (clock p (storeAt p c E rho ih y)
          (SA.voteTime p.toParams s))) := by
        have h := fgsa_Z_preceq_liveRoot p (clock p (storeAt p c E rho ih y)
          (SA.voteTime p.toParams s))
        change Block.Preceq (eraseFG (controls p _).Z) _
        rw [hcs, hZx, ← hZy, ← hcd]
        exact h
      have hb := Bool.and_eq_true_iff.mp hlt
      have he := block_preceq_antisymm hb.2 hza
      simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, false_and] at hb
    | none =>
      obtain ⟨_, hZx, ⟨K, hK, hKF, hKlt⟩, _⟩ := hxi.2.2.2.1
      by_contra hn
      have hloP : (controls p (storeAt p c E rho ip x)).lo ≤ (heightView p P).h := by
        rw [hlo, ← hcd]
        exact Nat.le_of_not_gt hn
      have hPd : P ∈ (storeAt p c E rho ih y).fg.TF := by rwa [hfgd] at hP
      have hFP := crossing ip ih x y K P hx hip_ih.le hK hKF ⟨hy, hPd⟩
        (lt_of_lt_of_le hKlt hloP)
      have hz : z p (clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams s)) =
          eraseFG (storeAt p c E rho ip x).fg.F := by
        change eraseFG (controls p _).Z = _
        rw [hcs, hZx]
      rw [hz] at hPz
      have hb := Bool.and_eq_true_iff.mp hPz
      have he := block_preceq_antisymm hb.2 (eraseFG_preceq hFP)
      simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, false_and] at hb

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:924–944; plan H-REPAIR steps 4–6. DC: SAME a proposal or HEAD read is not
a gate time, so its clock writes no lease row; the clock sets the store time. -/
theorem repair_read_row {st : State p.n} {s : Slot} {t : Time}
    (ht : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s)
    {row : Block × Nat × Time} (hrow : row ∈ (clock p st t).base.obligations) :
    row ∈ st.base.obligations ∧ (clock p st t).base.now = t := by
  refine ⟨healing_lease_clock_nongate st t ?_ row hrow, (clock_vn st t).2⟩
  intro w hw
  have hd := p.deltaPos
  rcases ht with rfl | rfl
  · have h : (4 * (s : Int)) * p.Δ = (4 * (w : Int) + 6) * p.Δ := by
      change 4 * p.Δ * (s : Int) = 4 * p.Δ * (w : Int) + 6 * p.Δ at hw
      linarith
    have h2 := Int.eq_of_mul_eq_mul_right (ne_of_gt hd) h
    omega
  · have h : (4 * (s : Int) + 1) * p.Δ = (4 * (w : Int) + 6) * p.Δ := by
      change 4 * p.Δ * (s : Int) + p.Δ = 4 * p.Δ * (w : Int) + 6 * p.Δ at hw
      linarith
    have h2 := Int.eq_of_mul_eq_mul_right (ne_of_gt hd) h
    omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:928–958 (H.6), H.3:769–775, IF.3(c); plan H-REPAIR step 6 (G-H6 core).
DC: INTENTIONAL the retained H.6 input at an honest proposer read of slot r + 1 and an
honest HEAD read, from the lease cover of the preceding honest batch: each live start is
the root, or a live lease target below the root, or a target with prior support in the
actual proposer pool. A reader at its F-root start uses the high-witness arm (RXing). -/
theorem repair_h6_input [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {r : Slot} (hhead : u ≤ SA.voteTime p.toParams r)
    (hvq : SA.voteTime p.toParams (r + 1) ≤ v)
    (hlease : RepairLeaseCover E rho (r + 1))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hScope : ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1)))
    (hCut : HealingWindow p E 1 r)
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1)))) :
    RetainedH6Input p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (r + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have htv : SA.proposalTime p.toParams (r + 1) < SA.voteTime p.toParams (r + 1) := by
    change 4 * p.Δ * ((r + 1 : Nat) : Int) < 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
    linarith
  have hvt : SA.voteTime p.toParams r ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hu : u ≤ SA.proposalTime p.toParams (r + 1) := hhead.trans hvt
  have hv : SA.proposalTime p.toParams (r + 1) ≤ v := htv.le.trans hvq
  have hip_ih : ip < ih := repair_idx_lt E rho hS hip hih htv
  have hframe := repair_h6_frame E rho crossing hS hphase hu hvq hx hip hy hih
  have hcover (i : Nat) (z0 : V) (t : Time) (row : Block × Nat × Time) (hz : z0 ∈ rho.honest)
      (hi : rho.events[i]? = some (.tick z0 t))
      (ht : t = SA.proposalTime p.toParams (r + 1) ∨ t = SA.voteTime p.toParams (r + 1))
      (hrow : row ∈ (clock p (rho.stateBefore E i z0).st t).base.obligations)
      (hlive : (clock p (rho.stateBefore E i z0).st t).base.now < row.2.2) :
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq row.1 K := by
    obtain ⟨hrow', hnow⟩ := repair_read_row ht hrow
    rw [hnow] at hlive
    have ht1 : SA.proposalTime p.toParams (r + 1) ≤ t := by
      rcases ht with rfl | rfl
      · exact le_rfl
      · exact htv.le
    have ht2 : t ≤ SA.voteTime p.toParams (r + 1) := by
      rcases ht with rfl | rfl
      · exact htv.le
      · exact le_rfl
    have h := hlease i z0 t row hz hi ht1 ht2 hrow' hlive
    simpa only [Nat.add_sub_cancel] using h
  refine ⟨hframe, ?_, ?_⟩
  · rcases repair_liveRoot_cases (clock p (rho.stateBefore E ip x).st
        (SA.proposalTime p.toParams (r + 1))) with he | ⟨row, hrow, hlive, _, he⟩
    · left
      change Block.Preceq (liveRoot p _) (eraseFG (controls p _).Z)
      rw [he]
      exact block_preceq_refl _
    · have hc := hcover ip x _ row hx hip (Or.inl rfl) hrow hlive
      change Block.Preceq (liveRoot p _) _ ∨ RetainedPriorSupport p _ _ (liveRoot p _)
      rw [he]
      exact repair_prior_support E rho hrec mono crossing hgst hphase hhead hc hx hip hScope hCut hv
  · rcases repair_liveRoot_cases (clock p (rho.stateBefore E ih y).st
        (SA.voteTime p.toParams (r + 1))) with he | ⟨row, hrow, hlive, _, he⟩
    · have hxi := healing_settled_frame_strict p c E rho crossing u v m J contested hphase ip x
        (healing_support_idxBefore_le p c E rho hS hip hu)
        (healing_phase_lt_timeIdx p c E rho hS hip hv).le hx
      have hyi := healing_settled_frame_strict p c E rho crossing u v m J contested hphase ih y
        (healing_support_idxBefore_le p c E rho hS hih (hu.trans htv.le))
        (healing_phase_lt_timeIdx p c E rho hS hih hvq).le hy
      have hcs : controls p (clock p (rho.stateBefore E ip x).st
          (SA.proposalTime p.toParams (r + 1))) = controls p (storeAt p c E rho ip x) :=
        repair_controls_clock _ _
      have hcd : controls p (clock p (rho.stateBefore E ih y).st
          (SA.voteTime p.toParams (r + 1))) = controls p (storeAt p c E rho ih y) :=
        repair_controls_clock _ _
      change Block.Preceq (liveRoot p _) (eraseFG (controls p _).Z) ∨ _ ∨
        ∀ W ∈ (clock p (rho.stateBefore E ip x).st _).fg.TF,
          (controls p (clock p (rho.stateBefore E ip x).st _)).lo ≤ (heightView p W).h →
          Block.Preceq (liveRoot p _) (eraseFG W)
      rw [he, hcs, hcd]
      cases J with
      | some J0 =>
        left
        obtain ⟨_, _, hZx, _⟩ := hxi.2.2.2.1
        obtain ⟨_, _, hZy, _⟩ := hyi.2.2.2.1
        rw [hZx, hZy]
        exact block_preceq_refl _
      | none =>
        right; right
        obtain ⟨_, hZy, ⟨K, hK, hKF, hKlt⟩, _⟩ := hyi.2.2.2.1
        intro W hW hloW
        rw [clock_fg] at hW
        have hWy : W ∈ (storeAt p c E rho ih x).fg.TF :=
          (fgsa_store_durable p c E rho hip_ih.le x).1 hW
        have e : (controls p (storeAt p c E rho ih y)).lo =
            (controls p (storeAt p c E rho ip x)).lo := hyi.2.2.1.trans hxi.2.2.1.symm
        have hlo : (controls p (storeAt p c E rho ih y)).lo ≤ (heightView p W).h := by
          rw [e]
          exact hloW
        have hFW := crossing ih ih y x K W hy le_rfl hK hKF ⟨hx, hWy⟩ (lt_of_lt_of_le hKlt hlo)
        rw [hZy]
        exact eraseFG_preceq hFW
    · have hc := hcover ih y _ row hy hih (Or.inr rfl) hrow hlive
      change Block.Preceq (liveRoot p _) _ ∨ RetainedPriorSupport p _ _ (liveRoot p _) ∨ _
      rw [he]
      rcases repair_prior_support E rho hrec mono crossing hgst hphase hhead hc hx hip
        hScope hCut hv with
        h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:960–963 (one authenticated current proposal); plan H-REPAIR step 7.
DC: SAME an honest proposal unpacks to the proposer tick, the proposal seat and the
emitted wire (Run/Emission.lean:72). -/
theorem repair_proposal_emission (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {s : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∃ ip x N, N.erase = Q ∧ x ∈ rho.honest ∧
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) ∧
      rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x ∧
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
        V2.D.Run.emitsAt E rho ip := by
  obtain ⟨⟨_, hxh⟩, o, ⟨j, hj, hem⟩, hb⟩ := hp
  rw [proposalTime_fgsa p c s] at hj
  obtain ⟨auth, m⟩ := o
  cases m with
  | head _ => cases hb
  | row _ => cases hb
  | proposal N =>
    have he : N.erase = Q := Option.some.inj hb
    subst Q
    refine ⟨j, _, N, rfl, hxh, hj, rfl, ?_⟩
    have hem0 := hem
    rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
    change (⟨auth, .proposal N⟩ : Obj p) ∈
      (if E.awake _ (SA.proposalTime p.toParams s) then
        (duties p (SA.proposalTime p.toParams s)).flatMap (fun d =>
          (rho.ownSeats (RunDuty.signLabel d) _).filterMap (fun i =>
            (act p c ((fgsa p c).clock _ _) d (rho.input _ _)).map
              (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Obj p)))) ++
                ([] : List (Obj p)) else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, hd, hem⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hem
      obtain ⟨m, hm, ho⟩ := Option.map_eq_some_iff.mp hm
      have he : m = .proposal N := congrArg V2.Signed.payload ho
      subst m
      cases d with
      | headAction _ =>
        change (if joinedNow p _ then some (Msg.head _) else none) = some (Msg.proposal N) at hm
        split at hm <;> cases hm
      | fgAction _ =>
        change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hm
        obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hm
        cases he
      | propAction s' =>
        have ht := (duties_spec p _ _).mp hd
        have hss : s' = s := by
          change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
          have hΔ := p.deltaPos
          have he : (s' : Int) = s := by nlinarith
          exact_mod_cast he
        subst s'
        have ha : auth = .seat (.prop s) i := (congrArg V2.Signed.auth ho).symm
        have hi : i = ⟨0, Nat.one_pos⟩ := Fin.ext (by
          have h := i.isLt
          change i.val < 1 at h
          change i.val = 0
          omega)
        rw [ha, hi] at hem0
        exact hem0
    · exact (List.not_mem_nil hem).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:915–963 (H.6 exact HEAD); plan H-REPAIR steps 6–8 (G-H6).
DC: INTENTIONAL the repaired-slot unanimous HEAD. Under the lease cover of the preceding
honest batch, the retained H.6 input holds at every honest reader, so the Shared retained
exact-head supplier gives the honest proposal as every honest label-(r + 1) HEAD. -/
theorem repair_head_exact_legacy [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {r : Slot} (hhead : u ≤ SA.voteTime p.toParams r)
    (hvq : SA.voteTime p.toParams (r + 1) ≤ v)
    (hlease : RepairLeaseCover E rho (r + 1))
    (hCut : HealingWindow p E 1 r)
    (hServices : ∀ (ip : Nat) (x : V) (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))) →
      (⟨.seat (.prop (r + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip →
      RepairHeadServices E rho (r + 1) ip x N)
    {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) (r + 1) Q) :
    ∀ y ∈ rho.honest, joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1)) →
      headAtLabel p c E rho y (r + 1) = some Q := by
  have hE := hrec.base.valid
  have hd := p.deltaPos
  obtain ⟨ip, x, N, heN, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  have hGST : E.t_GST ≤ SA.proposalTime p.toParams (r + 1) - p.Δ := by
    refine hgst.trans (hhead.trans ?_)
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) - p.Δ
    push_cast
    linarith
  have hhor : SA.voteTime p.toParams (r + 1) ≤ rho.horizon := hvq.trans hphase.2.1
  have hPrior : ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1)) := by
    simpa only [Nat.add_sub_cancel] using (hServices ip x N hx hip hem).prior
  have hFloors (y : V) (hy : y ∈ rho.honest) (ih : Nat)
      (hi : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1)))) :
      Block.Preceq (eraseFG (rho.stateBeforeTime E
        (SA.voteTime p.toParams (r + 1)) y).st.fg.F) Q := by
    have hinput := repair_h6_input E rho hrec mono crossing hgst hphase hhead hvq
      hlease hx hip hPrior hCut hy hi
    simpa only [heN] using fgsa_retainedH6_time_floor E rho hE mono hy hip hi N hem hinput
  have h := repair_head_exact E rho hrec.toRecovery₂ (r + 1) hGST hx hip hseat N hem
    (fun y hy ih hih _ => repair_h6_input E rho hrec mono crossing hgst hphase hhead hvq
      hlease hx hip hPrior hCut hy hih)
    (fun y hy ih hi hj => (hServices ip x N hx hip hem).target hy hi hj
      (by simpa only [heN] using hFloors y hy ih hi))
    (fun y hy ih hi hj => (hServices ip x N hx hip hem).scopes y hy ih hi hj
      (by simpa only [heN] using hFloors y hy ih hi)) hhor
  simpa only [heN] using h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan H-REPAIR step 3. DC: SAME proposal times are strictly ordered by slot. -/
theorem repair_slot_lt_of_time {l s : Nat}
    (h : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s) : l < s := by
  have hd := p.deltaPos
  change 4 * p.Δ * (l : Int) < 4 * p.Δ * (s : Int) at h
  have h' : (l : Int) < s := by nlinarith
  exact_mod_cast h'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:928–944, 972; plan H-REPAIR steps 4–5. DC: INTENTIONAL the last-write split
gives the lease cover after its threshold l: an old write expires by v_(s−1) (equality
included); a later write at label w ≤ s − 2 has Transfers, so its target is below every
honest HEAD of label s − 1. -/
theorem repair_lease_cover_of_split (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {v : Time} {l a : Nat}
    (hsplit : ∀ i x (row : Block × Nat × Time), i ≤ timeIdx rho v → x ∈ rho.honest →
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ w C, IsGateTick p c rho j x w ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
        ((row.2.2 ≤ SA.voteTime p.toParams l ∧
            ∀ s, SA.proposalTime p.toParams l < SA.proposalTime p.toParams s →
              row.2.2 ≤ SA.voteTime p.toParams (s - 1)) ∨
          (a ≤ w ∧ Transfers p c E rho w row.1 v)))
    {s : Slot} (hls : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) : RepairLeaseCover E rho s := by
  have hd := p.deltaPos
  have hlt := repair_slot_lt_of_time hls
  intro i z t row hz hi hts htv hrow hlive y hy K hK
  have hiv : i ≤ timeIdx rho v :=
    ((V2.D.Engine.index_lt_read_length_iff hS v hi).mpr (htv.trans hvs)).le
  obtain ⟨j, hji, w, C, ht, _, _, _, hcase⟩ := hsplit i z row hiv hz hrow
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
  have hvp : SA.voteTime p.toParams (s - 1) < SA.proposalTime p.toParams s := by
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int)
    rw [hs1]
    linarith
  rcases hcase with ⟨_, hold⟩ | ⟨_, htr⟩
  · exfalso
    have h := hold s hls
    linarith
  · have hwt := fgsa_tick_time_strict E rho hS ht hi hji
    have hws : w + 1 ≤ s - 1 := by
      change 4 * p.Δ * (w : Int) + 6 * p.Δ < t at hwt
      have htv' : t ≤ 4 * p.Δ * (s : Int) + p.Δ := htv
      have h : ¬ ((s : Int) ≤ w + 1) := fun hc => by nlinarith
      have h2 : (w : Int) + 1 < s := by omega
      exact Nat.le_sub_one_of_lt (by exact_mod_cast h2)
    have hv : SA.voteTime p.toParams (s - 1) ≤ v := by
      have htsv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
        change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
        linarith
      exact (hvp.le.trans htsv).trans hvs
    exact htr.1 y (s - 1) K hy hws hv hK

/-- The repair adapter consumes the local lease cover at this actual label.
The joined-start TPerm input supplies both branches of the last-write split.
The phase-service producer of TPerm remains OPEN/P-H1. -/
theorem repair_lease_cover_two [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (_mono : RMonoAll p c E rho) (_crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (perm : TPerm p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β) {s : Slot}
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
 : RepairLeaseCover E rho s := by
  exact repair_lease_cover_of_split E rho hrec.base.valid.toScheduleWellFormed
    (healing_last_write_two_lease p c E rho
      hrec.base.valid.toScheduleWellFormed perm writes hready hphase hβ) hls hvs

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan H-REPAIR step 3. DC: SAME a slot after β + 2k − 1, with u < t_β, has its preceding
HEAD at or after u. -/
theorem repair_head_after_two {u : Time} {β r : Slot} (hβ : u < SA.proposalTime p.toParams β)
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams (r + 1)) :
    u ≤ SA.voteTime p.toParams r := by
  have hd := p.deltaPos
  have hk := p.kLarge
  have hlt := repair_slot_lt_of_time hls
  have hr : (β : Int) ≤ r := by omega
  refine hβ.le.trans ?_
  change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * (r : Int) + p.Δ
  nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:915–963 (H.6); plan H-REPAIR G-H6 (R1), steps 4–8. DC: INTENTIONAL the
retained H.6 input at every actual honest proposal/HEAD read pair of a slot s after
β + 2k − 1 with v_s ≤ v. The prior support is in the ACTUAL proposer pool. -/
theorem retainedH6Input_on_repaired_reads [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (perm : TPerm p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β) {s : Slot}
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hScope : ProposalSupportScope E rho ip x (s - 1) (SA.proposalTime p.toParams s))
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s))) :
    RetainedH6Input p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s := by
  have hgst : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (Nat.ne_zero_of_lt (repair_slot_lt_of_time hls))
  have hWindow : HealingWindow p E 2 (r + 1) :=
    healing_ready_proposal_window E ((hready.trans (repair_head_after_two hβ hls)).trans (by
      change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
      push_cast
      linarith [p.deltaPos]))
  exact repair_h6_input E rho hrec mono crossing hgst hphase (repair_head_after_two hβ hls) hvs
    (repair_lease_cover_two E rho hrec mono crossing writes perm hready hphase hβ hls hvs)
    hx hip (by simpa only [Nat.add_sub_cancel] using hScope)
    (by simpa only [Nat.add_sub_cancel] using hWindow.prior) hy hih

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:915–963 (H.6 unanimous HEAD); plan H-REPAIR G-H6 (R1), step 8.
DC: INTENTIONAL every honest HEAD of a repaired slot s after β + 2k − 1 with v_s ≤ v is its
honest proposal. -/
theorem repair_head_two [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (perm : TPerm p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β) {s : Slot}
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
    (hServices : ∀ (ip : Nat) (x : V) (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip →
      RepairHeadServices E rho s ip x N)
    {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some Q := by
  have hgst : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (Nat.ne_zero_of_lt (repair_slot_lt_of_time hls))
  have hWindow : HealingWindow p E 2 (r + 1) :=
    healing_ready_proposal_window E ((hready.trans (repair_head_after_two hβ hls)).trans (by
      change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
      push_cast
      linarith [p.deltaPos]))
  exact repair_head_exact_legacy E rho hrec mono crossing hgst hphase
    (repair_head_after_two hβ hls) hvs
    (repair_lease_cover_two E rho hrec mono crossing writes perm hready hphase hβ hls hvs)
    (by simpa only [Nat.add_sub_cancel] using hWindow.prior) hServices hp

end AvailableChain.FGSA.Run
end
