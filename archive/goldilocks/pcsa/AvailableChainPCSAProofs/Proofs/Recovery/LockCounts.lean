module
public import AvailableChainPCSA.Model.Handlers
public import AvailableChainPCSAProofs.Proofs.Recovery.LockDomain
public import AvailableChainPCSAProofs.Proofs.Shared.CleanGate
public import AvailableChainPCSAProofs.Proofs.Shared.Count
public import AvailableChainPCSAProofs.Proofs.Foundations.NamedScope
public import AvailableChainFGSARun.Proofs.RootResolution

public section

/-! Count transfer at the actual recovery reads. -/
namespace AvailableChain.PCSA
private def LockCountData {n : Nat} (st : State n) :=
  (st.fg.F, st.base.blocks, st.base.votes, st.base.blockStamp,
    st.base.voteStamp, st.base.headDomain, st.base.now)
private theorem lock_countData_normalize {n : Nat} (st : State n) :
    LockCountData (normalizeS st) = LockCountData st := by
  delta normalizeS
  split <;> rfl
private theorem lock_countData_gate {n : Nat} (p : Params) (st : State n)
    (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    LockCountData (gateFrom p a cs rank st s) = LockCountData st := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => LockCountData acc = LockCountData st)
      · rfl
      · intro acc ha B _
        apply List.foldlRecOn (motive := fun acc : State n => LockCountData acc = LockCountData st)
        · exact ha
        · intro acc' ha' g _
          exact ha'
private theorem lock_countData_clock (p : Params) (st : State p.n) (t : Time) :
    LockCountData (clock p st t) = LockCountData (clockPre p st t) := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def, lock_countData_normalize]
    split
    · rfl
    · exact lock_countData_gate p _ _ _ _ _
  · rfl
private theorem lock_grid_confirmation_fields {n : Nat} (q : GridCO.Params)
    (v w : GridCO.State n .root) (a : Block) (s : Slot)
    (hb : v.blocks = w.blocks) (hv : v.votes = w.votes)
    (hbs : v.blockStamp = w.blockStamp) (hvs : v.voteStamp = w.voteStamp)
    (hd : v.headDomain = w.headDomain) (hn : v.now = w.now) :
    GridCO.confirmationFrom q a v s = GridCO.confirmationFrom q a w s := by
  have htree : GridCO.resolutionTree v = GridCO.resolutionTree w := by
    change v.headDomain.getD v.blocks = w.headDomain.getD w.blocks
    rw [hd, hb]
  have hhead (o : GridCO.Wire n .root) :
      GridCO.resolvedHead? v o = GridCO.resolvedHead? w o := by
    delta GridCO.resolvedHead?
    rw [htree, hb]
  have hsv (o : GridCO.Wire n .root) : GridCO.stampVote v o = GridCO.stampVote w o := by
    delta GridCO.stampVote
    rw [hvs, hn]
  have hsb (B : Block) : GridCO.stampBlock v B = GridCO.stampBlock w B := by
    delta GridCO.stampBlock
    rw [hbs, hn]
  have hbefore (o : GridCO.Wire n .root) (t : Time) :
      GridCO.resolvedBefore v o t = GridCO.resolvedBefore w o t := by
    delta GridCO.resolvedBefore
    rw [hhead]
    cases GridCO.resolvedHead? w o with
    | none => rfl
    | some B =>
      change (decide (B.slot ≤ (GridCO.headLabel? o).getD 0) &&
        decide (GridCO.stampVote v o < t) && decide (GridCO.stampBlock v B < t)) =
        (decide (B.slot ≤ (GridCO.headLabel? o).getD 0) &&
          decide (GridCO.stampVote w o < t) && decide (GridCO.stampBlock w B < t))
      rw [hsv, hsb]
  have hearly : GridCO.earlyVotes q v s = GridCO.earlyVotes q w s := by
    delta GridCO.earlyVotes GridCO.votesAt
    rw [hv]
    apply List.filter_congr
    intro o _
    exact hbefore o _
  have hlate : GridCO.lateVotes q v s = GridCO.lateVotes q w s := by
    delta GridCO.lateVotes GridCO.votesAt
    rw [hv]
    apply List.filter_congr
    intro o _
    rw [hsv]
  have hclean : GridCO.cleanSupport q v s = GridCO.cleanSupport q w s := by
    delta GridCO.cleanSupport
    rw [hearly, hlate]
  delta GridCO.confirmationFrom
  rw [hclean, hlate, htree, hb]
private theorem lock_confirmation_of_countData {n : Nat} (p : Params) (st st' : State n)
    (s : Slot) (h : LockCountData st = LockCountData st') :
    SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s =
      SA.Root.confirmationFrom p.toParams (eraseFG st'.fg.F) (actView st') s := by
  change (_, _, _, _, _, _, _) = (_, _, _, _, _, _, _) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hF, hblocks, hvotes, hbstamps, hvstamps, hdomain, hnow⟩ := h
  rw [hF]
  apply lock_grid_confirmation_fields
  · change st.base.blocks.filter (activeCompatible st) =
      st'.base.blocks.filter (activeCompatible st')
    delta activeCompatible
    rw [hblocks, hF]
  · exact hvotes
  · exact hbstamps
  · exact hvstamps
  · change some (st.base.headDomain.getD st.base.blocks) =
      some (st'.base.headDomain.getD st'.base.blocks)
    rw [hdomain, hblocks]
  · exact hnow
/-- The post-clock gate has the same raw confirmation as its pre-gate input. -/
theorem recovery_clock_confirmation_eq_pre (p : Params) (st : State p.n) (t : Time) (s : Slot) :
    SA.Root.confirmationFrom p.toParams (eraseFG (clock p st t).fg.F) (actView (clock p st t)) s =
      SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st t).fg.F) (actView (clockPre p
        st t)) s :=
  lock_confirmation_of_countData p _ _ s (lock_countData_clock p st t)
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- The exact clock store at a scheduled read. -/
theorem recovery_postClock_store (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) :
    ∃ k, rho.events[k]? = some (.tick x t) ∧
      nd.st = clock p (V2.D.Run.stateBefore E rho k x).st t := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hn
  obtain ⟨pre, hp, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact ⟨k, V2.D.Run.tickIdx?_spec hk, rfl⟩

/-- A raw saved result has a post-clock gate source with the same result. -/
theorem recovery_gate_result_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (X : Block)
    (h : gateResultAt p c E rho x s = some (some X)) :
    ∃ nd, pcsa_postClock E rho x (SA.gateTime p.toParams s) = some nd ∧
      SA.Root.confirmationFrom p.toParams (eraseFG nd.st.fg.F) (actView nd.st) s = some X := by
  rw [pcsa_gateResultAt_def, pcsa_gateInAt_def] at h
  obtain ⟨st, hst, hr⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨pre, hp, rfl⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨(pcsaWith m p c).clock pre (SA.gateTime p.toParams s), ?_, ?_⟩
  · rw [pcsa_postClock_def, hp]; rfl
  · change SA.Root.confirmationFrom p.toParams (eraseFG (clock p _ _).fg.F)
      (actView (clock p _ _)) s = some X
    rwa [recovery_clock_confirmation_eq_pre]

/-- Recovery reads retain the support/raw subset law, including carried support. -/
theorem recovery_headSupport_subset (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (x : V) (t : Time) (nd : Node p) (hn : pcsa_postClock E rho x t = some nd) (s : Slot) :
    headSupport p nd.st s ⊆ headVotes p nd.st s := by
  have hwf : ∀ w ∈ nd.st.proposals, wellFormed p w = true := by
    obtain ⟨k, _, he⟩ := recovery_postClock_store E rho x t nd hn
    intro w hw
    rw [he, pcsa_clock_proposals] at hw
    obtain ⟨j, o, u, _, hj, ho⟩ := pcsa_stored_proposal_delivered E rho k x w hw
    have hh := h.valid.toDeliveryWellFormed.wire j x o u hj
    change wellFormed p (toWire p o) = true at hh
    rwa [ho] at hh
  intro o ho
  delta headSupport at ho
  delta headVotes
  apply List.mem_eraseDups.mpr
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hf | hc
  · obtain ⟨hm, hf⟩ := List.mem_filter.mp hf
    apply List.mem_append_left
    refine List.mem_filter.mpr ⟨hm, ?_⟩
    delta GridCO.resolvedBefore at hf
    cases hr : GridCO.resolvedHead? (actView nd.st) o with
    | none => rw [hr] at hf; cases hf
    | some B =>
      rw [hr] at hf
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).2
  · obtain ⟨hm, ht⟩ := List.mem_filter.mp hc
    obtain ⟨row, hrow, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp hrow
    cases hd : w.decode with
    | none => rw [hd] at he; cases he
    | some msg =>
      rw [hd] at he
      cases msg with
      | vote r i root => cases he
      | row i body => cases he
      | ack r i root => cases he
      | pc C => cases he
      | block r N =>
        dsimp only at he
        split at he
        · cases he
          have hh := hwf w hw
          unfold AvailableChain.PCSA.wellFormed at hh
          rw [hd] at hh
          have hsup := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hh).1).1).1).2
          have har : a ∈ N.raw := of_decide_eq_true (List.all_eq_true.mp hsup a ha)
          apply List.mem_append_right
          apply List.mem_filter.mpr
          exact ⟨List.mem_flatMap.mpr ⟨(N.raw, N.support), hrow,
            List.mem_map.mpr ⟨a, har, rfl⟩⟩, (Bool.and_eq_true_iff.mp ht).1⟩
        · cases he

/-- Stage-one reads use the cumulative body domain. -/
theorem recovery_read_count_domain (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (x : V) (hx : x ∈ rho.honest) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) :
    nd.st.fg.F = .genesis ∧ nd.st.base.headDomain = none := by
  obtain ⟨k, _, he⟩ := recovery_postClock_store E rho x t nd hn
  rw [he, pcsa_body_clock_fg, recovery_clock_headDomain, recovery_headDomain_stateBefore_none]
  exact ⟨(hF x hx k).1, rfl⟩

/-- A resolved body in the cumulative domain supplies the exact prefix support. -/
theorem recovery_resolved_support (st : State p.n) (hd : st.base.headDomain = none)
    (o : GridCO.Wire p.n .root) (H B : Block)
    (hr : GridCO.resolvedHead? st.base o = some H)
    (hl : H.slot ≤ (GridCO.headLabel? o).getD 0) (hb : Block.Preceq B H) :
    Gen.AC.Root.voteSupports st.base.blocks B o = true := by
  apply (Gen.AC.Root.vote_support_body _ B o).mpr
  refine ⟨H, ?_, FGSA.resolvedHead_mem _ _ hr, hl, hb⟩
  have hh := FGSA.Run.resolvedHead_target _ _ hr
  change Gen.AC.Root.resolvedTarget? (st.base.headDomain.getD st.base.blocks) o = some H at hh
  simpa only [hd, Option.getD_none] using hh

/-- A gate prefix is covered at the next actual voter read, once its root is compatible.
Both the majority and the retained path come from the selected gate result. -/
theorem recovery_gate_prefix_next_head (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (g s : Slot)
    (transport : RecoveryLockTransport p c E rho g) (hg : g ≤ s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (X B : Block)
    (hX : gateResultAt p c E rho x s = some (some X)) (hBX : Block.Preceq B X)
    (dst : Node p) (hn : pcsa_postClock E rho y (SA.voteTime p.toParams (s + 1)) = some dst)
    (hanchor : Block.Compatible (liveRoot p dst.st (voterPC p dst.st (s + 1))) B) :
    Block.Preceq B (headVote p dst.st (s + 1)) := by
  obtain ⟨src, hs, hresult⟩ := recovery_gate_result_source E rho x s X hX
  obtain ⟨hFs, hDs⟩ := recovery_read_count_domain E rho hF x hx _ src hs
  obtain ⟨_, hDd⟩ := recovery_read_count_domain E rho hF y hy _ dst hn
  let P := GridCO.cleanSupport p.toParams.engine (actView src.st) s
  let L := GridCO.lateVotes p.toParams.engine (actView src.st) s
  have hmaj := pcsa_gate_result_majority p (actView src.st) _ X s hresult
  rw [pcsa_gate_score_of_genesis p src.st s X hFs hDs] at hmaj
  have hmono := Gen.AC.Root.goldfishScore_antitone src.st.base.blocks P P B X hBX
  have hmajB : GridCO.voterCount L < 2 * GridCO.goldfishScore src.st.base.blocks P P B := by
    dsimp only [P, L] at *
    omega
  have resolve (o : GridCO.Wire p.n .root)
      (hsup : Gen.AC.Root.voteSupports src.st.base.blocks B o = true) :
      ∃ H, GridCO.resolvedHead? (actView src.st) o = some H ∧
        H.slot ≤ (GridCO.headLabel? o).getD 0 ∧ Block.Preceq B H := by
    obtain ⟨H, hl, hm, ht, hp⟩ := (Gen.AC.Root.vote_support_body _ B o).mp hsup
    refine ⟨H, ?_, ht, hp⟩
    apply FGSA.Run.resolvedHead_of_lookup
    · change Gen.AC.Root.resolvedTarget? (src.st.base.headDomain.getD src.st.base.blocks) o = some H
      simpa only [hDs, Option.getD_none] using hl
    · rwa [pcsa_actView_blocks_of_genesis src.st hFs]
  have hpath : ∀ C, Block.Preceq C B → C ∈ erasedList dst.st
      (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (s + 1))) := by
    have hpos : 0 < GridCO.goldfishScore src.st.base.blocks P P B := by omega
    rw [Gen.AC.Root.vote_pool_score_card] at hpos
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    have hp := (Finset.mem_filter.mp hi).2
    have hcap := FGSA.fgsa_cleanSupport_no_equivocation p (actView src.st) s i
    change GridCO.equivocates P i = false at hcap
    rw [hcap, Bool.false_or] at hp
    obtain ⟨o, ho, hoi, hsup⟩ := (Gen.AC.Root.vote_pool_support_witness _ P i B).mp hp
    obtain ⟨H, hr, _, hb⟩ := resolve o hsup
    have hf := transport.earlyForward s hg horizon x hx y hy src dst hs hn o
      (List.mem_filter.mp ho).1 i hoi H hr
    intro C hCB
    exact hf.2.2.2 C (Gen.Pure.block_preceq_trans hCB hb)
  change Block.Preceq B (if s + 1 = 0 then .genesis else _)
  rw [ite_eq_right (Nat.succ_ne_zero s)]
  apply pcsa_cl2_head_extends_majority p dst.st _ _ src.st.base.blocks P L
    (headVotes p dst.st (s + 1)) (headSupport p dst.st (s + 1)) B
    ?_ ?_ ?_ ?_ (recovery_headSupport_subset E rho h y _ dst hn _) hmajB hanchor
    (fun C _ hCB => hpath C hCB)
  · intro o ho
    exact FGSA.fgsa_early_subset_late p (actView src.st) s (List.mem_filter.mp ho).1
  · intro o ho i hi
    exact pcsa_clean_support_seat p (actView src.st) s o ho i hi
  · intro o ho i hi hsup
    obtain ⟨H, hr, ht, hb⟩ := resolve o hsup
    rcases (transport.earlyForward s hg horizon x hx y hy src dst hs hn o
      (List.mem_filter.mp ho).1 i hi H hr).1 with hh | hc
    · exact Or.inl ⟨hh.1, recovery_resolved_support dst.st hDd o H B hh.2.1 ht hb⟩
    · exact Or.inr hc
  · exact transport.voterBackward s hg horizon x hx y hy src dst hs hn

end AvailableChain.PCSA.Run
end
