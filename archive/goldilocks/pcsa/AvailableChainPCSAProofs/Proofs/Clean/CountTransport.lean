module
public import AvailableChainPCSAProofs.Proofs.Clean.BackwardInputs
public import AvailableChainPCSAProofs.Proofs.Clean.ForwardReceipt
public import AvailableChainFGSARun.Proofs.RootResolution
public import AvailableChainPCSAProofs.Proofs.Shared.Count

public section

/-! C6 CountTransport: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- A clean source support seat is not capped in its late denominator. -/
theorem pcsa_clean_input_not_capped (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (o : GridCO.Wire p.n .root) (i : Fin p.n)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s)
    (hi : GridCO.headSeat? o = some i) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine v s) i = false := by
  exact pcsa_clean_support_seat p v s o ho i hi
/-- A clean support HEAD is the only late HEAD with its seat and label. -/
theorem pcsa_clean_input_unique_late (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (o : GridCO.Wire p.n .root) (i : Fin p.n)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s)
    (hi : GridCO.headSeat? o = some i) (a : GridCO.Wire p.n .root)
    (ha : a ∈ GridCO.lateVotes p.toParams.engine v s)
    (hai : GridCO.headSeat? a = some i) : a = o := by
  have hc := pcsa_clean_input_not_capped p v s o i ho hi
  by_contra hne
  have he := (Gen.AC.Root.cap_pair _ i).mpr
    ⟨a, ha, o, FGSA.fgsa_early_subset_late p v s (List.mem_filter.mp ho).1, hne, hai, hi⟩
  rw [he] at hc
  cases hc
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem count_read_domain (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) (u : Time) :
    GridCO.resolutionTree (actView (clock p (V2.D.Run.stateBefore E rho k x).st u)) =
      (clock p (V2.D.Run.stateBefore E rho k x).st u).base.blocks := by
  change (clock p (V2.D.Run.stateBefore E rho k x).st u).base.headDomain.getD _ = _
  rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  rfl
/-- At a stage-1 read, support has a resolved body above the supported prefix. -/
theorem pcsa_read_vote_support_body (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (u : Time)
    (o : GridCO.Wire p.n .root) (X : Block)
    (hv : Gen.AC.Root.voteSupports (clock p (V2.D.Run.stateBefore E rho k x).st u).base.blocks X
      o = true) :
    ∃ H, GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k x).st u)) o = some H ∧
      Block.Preceq X H := by
  obtain ⟨H, hl, hm, _, hp⟩ := (Gen.AC.Root.vote_support_body _ X o).mp hv
  refine ⟨H, ?_, hp⟩
  apply FGSA.Run.resolvedHead_of_lookup
  · rw [count_read_domain]
    exact hl
  · have hf : (clock p (V2.D.Run.stateBefore E rho k x).st u).fg.F = .genesis := by
      rw [pcsa_body_clock_fg]
      exact (hF x hx k).1
    rw [pcsa_actView_blocks_of_genesis _ hf]
    exact hm
/-- Gate-to-voter counts need a floor at the early time of label `s`. -/
theorem pcsa_gate_voter_walk_counts_from_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X : Block) (view : Option (PC p.n)) (tree : List Block)
    (hT : T₀ ≤ SA.earlyTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s = some X)
    (hanchor : Block.Compatible
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        view) X)
    (hpath : ∀ B, Block.Prec
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        view) B →
      Block.Preceq B X → B ∈ tree) :
    Block.Preceq X (headInTree p
      (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))) view tree
      (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        (s + 1))
      (headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s +
        1))) (s + 1))) := by
  have hfreeze : T₀ ≤ SA.freezeTime p.toParams s := by
    apply hT.trans
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  let src := clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)
  let dst := clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))
  have hFs : src.fg.F = .genesis := by
    change (clock p _ _).fg.F = _
    rw [pcsa_body_clock_fg]
    exact (hF x hx a).1
  have hDs : src.base.headDomain = none := by
    change (clock p _ _).base.headDomain = none
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  have hmaj := pcsa_gate_result_majority p (actView src) (eraseFG src.fg.F) X s hresult
  rw [pcsa_gate_score_of_genesis p src s X hFs hDs] at hmaj
  have hfcut : SA.freezeTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hfk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ at ht
    push_cast at ht
    have hp := p.deltaPos
    nlinarith
  apply pcsa_cl2_head_extends_majority p dst view tree src.base.blocks
    (GridCO.cleanSupport p.toParams.engine (actView src) s)
    (GridCO.lateVotes p.toParams.engine (actView src) s)
    (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) X
    ?_ ?_ ?_ ?_ (pcsa_headSupport_subset_at_read E rho h.valid.toDeliveryWellFormed k y _ _) hmaj
      hanchor hpath
  · intro o ho
    exact FGSA.fgsa_early_subset_late p (actView src) s (List.mem_filter.mp ho).1
  · intro o ho i hi
    exact pcsa_clean_input_not_capped p (actView src) s o i ho hi
  · intro o ho i hi hv
    have hl : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).2
    obtain ⟨H, hlookup, hmem, hslot, hprefix⟩ := (Gen.AC.Root.vote_support_body src.base.blocks X
      o).mp hv
    have hr : GridCO.resolvedHead? (actView src) o = some H := by
      apply FGSA.Run.resolvedHead_of_lookup
      · rw [count_read_domain]
        exact hlookup
      · rw [pcsa_actView_blocks_of_genesis src hFs]
        exact hmem
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
    have hroot := FGSA.Run.resolvedHead_root _ _ hr
    change some r = some H.root at hroot
    have heq := Option.some.inj hroot
    subst r
    rcases pcsa_early_input_relay_support_win E rho h hF hD (hT := hT) a k x y hx
      hy s i H _ _ hfcut hfk (List.mem_filter.mp ho).1 hr with hh | hcap
    · refine Or.inl ⟨hh.1, ?_⟩
      apply (Gen.AC.Root.vote_support_body dst.base.blocks X _).mpr
      refine ⟨H, ?_, ?_, hslot, hprefix⟩
      · have hlook := FGSA.Run.resolvedHead_target _ _ hh.2.2
        rw [count_read_domain] at hlook
        exact hlook
      · exact (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hh.2.2)).1
    · exact Or.inr hcap.1
  · intro o ho i hi
    have hl : GridCO.headLabel? o = some s := by
      rcases pcsa_headVotes_mem p dst (s + 1) o ho with hf | hc
      · simpa only [Nat.add_sub_cancel] using beq_iff_eq.mp (List.mem_filter.mp hf.1).2
      · obtain ⟨_, _, _, _, _, _, _, _, _, hl⟩ := hc
        simpa only [Nat.add_sub_cancel] using hl
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
    exact pcsa_voter_tick_input_relay_late_win E rho h hD (hT := hfreeze) k a y x hy hx
      s i r hc hk ha ho
/-- In the delivery window: Actual gate-to-voter counts discharge CL2 once the root and retained
path are supplied. -/
theorem pcsa_gate_voter_walk_counts_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X : Block) (view : Option (PC p.n)) (tree : List Block)
    (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s = some X)
    (hanchor : Block.Compatible
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        view) X)
    (hpath : ∀ B, Block.Prec
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        view) B →
      Block.Preceq B X → B ∈ tree) :
    Block.Preceq X (headInTree p
      (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))) view tree
      (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        (s + 1))
      (headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s +
        1))) (s + 1))) :=
  pcsa_gate_voter_walk_counts_from_early E rho h hF hD a k x y hx hy s X view tree
    (pcsa_floor_early hT) hc ha hk hresult hanchor hpath
/-- Actual gate-to-voter counts discharge CL2 once the root and retained path are supplied. -/
theorem pcsa_gate_voter_walk_counts (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X : Block) (view : Option (PC p.n)) (tree : List Block)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s = some X)
    (hanchor : Block.Compatible
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        view) X)
    (hpath : ∀ B, Block.Prec
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        view) B →
      Block.Preceq B X → B ∈ tree) :
    Block.Preceq X (headInTree p
      (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))) view tree
      (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1)))
        (s + 1))
      (headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s +
        1))) (s + 1))) := by
  let src := clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)
  let dst := clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))
  have hFs : src.fg.F = .genesis := by
    change (clock p _ _).fg.F = _
    rw [pcsa_body_clock_fg]
    exact (hF x hx a).1
  have hDs : src.base.headDomain = none := by
    change (clock p _ _).base.headDomain = none
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  have hmaj := pcsa_gate_result_majority p (actView src) (eraseFG src.fg.F) X s hresult
  rw [pcsa_gate_score_of_genesis p src s X hFs hDs] at hmaj
  have hfcut : SA.freezeTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hfk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ at ht
    push_cast at ht
    have hp := p.deltaPos
    nlinarith
  apply pcsa_cl2_head_extends_majority p dst view tree src.base.blocks
    (GridCO.cleanSupport p.toParams.engine (actView src) s)
    (GridCO.lateVotes p.toParams.engine (actView src) s)
    (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) X
    ?_ ?_ ?_ ?_ (pcsa_headSupport_subset_at_read E rho h.valid.toDeliveryWellFormed k y _ _) hmaj
      hanchor hpath
  · intro o ho
    exact FGSA.fgsa_early_subset_late p (actView src) s (List.mem_filter.mp ho).1
  · intro o ho i hi
    exact pcsa_clean_input_not_capped p (actView src) s o i ho hi
  · intro o ho i hi hv
    have hl : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).2
    obtain ⟨H, hlookup, hmem, hslot, hprefix⟩ := (Gen.AC.Root.vote_support_body src.base.blocks X
      o).mp hv
    have hr : GridCO.resolvedHead? (actView src) o = some H := by
      apply FGSA.Run.resolvedHead_of_lookup
      · rw [count_read_domain]
        exact hlookup
      · rw [pcsa_actView_blocks_of_genesis src hFs]
        exact hmem
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
    have hroot := FGSA.Run.resolvedHead_root _ _ hr
    change some r = some H.root at hroot
    have heq := Option.some.inj hroot
    subst r
    rcases pcsa_early_input_relay_support E rho h hF hD a k x y hx hy s i H _ _
      hfcut hfk (List.mem_filter.mp ho).1 hr with hh | hcap
    · refine Or.inl ⟨hh.1, ?_⟩
      apply (Gen.AC.Root.vote_support_body dst.base.blocks X _).mpr
      refine ⟨H, ?_, ?_, hslot, hprefix⟩
      · have hlook := FGSA.Run.resolvedHead_target _ _ hh.2.2
        rw [count_read_domain] at hlook
        exact hlook
      · exact (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hh.2.2)).1
    · exact Or.inr hcap.1
  · intro o ho i hi
    have hl : GridCO.headLabel? o = some s := by
      rcases pcsa_headVotes_mem p dst (s + 1) o ho with hf | hc
      · simpa only [Nat.add_sub_cancel] using beq_iff_eq.mp (List.mem_filter.mp hf.1).2
      · obtain ⟨_, _, _, _, _, _, _, _, _, hl⟩ := hc
        simpa only [Nat.add_sub_cancel] using hl
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
    exact pcsa_voter_tick_input_relay_late E rho h hD k a y x hy hx s i r hc hk ha ho
/-- In the delivery window: Actual gate-to-proposer counts discharge CL2 once the root and retained
path are supplied. -/
theorem pcsa_gate_proposer_walk_counts_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X : Block) (view : Option (PC p.n)) (tree : List Block)
    (hT : T₀ ≤ SA.earlyTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hk : rho.events[k]? = some (.tick y (GridCO.proposalTime p.toParams.engine (s + 1))))
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s = some X)
    (hanchor : Block.Compatible
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime
        p.toParams.engine (s + 1))) view) X)
    (hpath : ∀ B, Block.Prec
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime
        p.toParams.engine (s + 1))) view) B →
      Block.Preceq B X → B ∈ tree) :
    Block.Preceq X (headInTree p
      (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime p.toParams.engine (s +
        1))) view tree
      (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime
        p.toParams.engine (s + 1))) (s + 1))
      (proposerSupport (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime
        p.toParams.engine (s + 1))) (s + 1))) := by
  let src := clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)
  let dst := clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime p.toParams.engine
    (s + 1))
  have hFs : src.fg.F = .genesis := by
    change (clock p _ _).fg.F = _
    rw [pcsa_body_clock_fg]
    exact (hF x hx a).1
  have hDs : src.base.headDomain = none := by
    change (clock p _ _).base.headDomain = none
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  have hmaj := pcsa_gate_result_majority p (actView src) (eraseFG src.fg.F) X s hresult
  rw [pcsa_gate_score_of_genesis p src s X hFs hDs] at hmaj
  have hfcut : SA.freezeTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hfk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * ((s + 1 : Nat) : Int) < 4 * p.Δ * (s : Int) + 3 * p.Δ at ht
    push_cast at ht
    have hp := p.deltaPos
    nlinarith
  apply pcsa_cl2_head_extends_majority p dst view tree src.base.blocks
    (GridCO.cleanSupport p.toParams.engine (actView src) s)
    (GridCO.lateVotes p.toParams.engine (actView src) s)
    (proposerVotes dst (s + 1)) (proposerSupport dst (s + 1)) X
    ?_ ?_ ?_ ?_ (fun _ ho => (List.mem_filter.mp ho).1) hmaj hanchor hpath
  · intro o ho
    exact FGSA.fgsa_early_subset_late p (actView src) s (List.mem_filter.mp ho).1
  · intro o ho i hi
    exact pcsa_clean_input_not_capped p (actView src) s o i ho hi
  · intro o ho i hi hv
    have hl : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).2
    obtain ⟨H, hlookup, hmem, hslot, hprefix⟩ := (Gen.AC.Root.vote_support_body src.base.blocks X
      o).mp hv
    have hr : GridCO.resolvedHead? (actView src) o = some H := by
      apply FGSA.Run.resolvedHead_of_lookup
      · rw [count_read_domain]
        exact hlookup
      · rw [pcsa_actView_blocks_of_genesis src hFs]
        exact hmem
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
    have hroot := FGSA.Run.resolvedHead_root _ _ hr
    change some r = some H.root at hroot
    have heq := Option.some.inj hroot
    subst r
    rcases pcsa_early_input_relay_support_win E rho h hF hD (hT := hT) a k x y hx hy s i H _ _
      hfcut hfk (List.mem_filter.mp ho).1 hr with hh | hcap
    · refine Or.inl ⟨hh.2.1, ?_⟩
      apply (Gen.AC.Root.vote_support_body dst.base.blocks X _).mpr
      refine ⟨H, ?_, ?_, hslot, hprefix⟩
      · have hlook := FGSA.Run.resolvedHead_target _ _ hh.2.2
        rw [count_read_domain] at hlook
        exact hlook
      · exact (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hh.2.2)).1
    · exact Or.inr hcap.2
  · intro o ho i hi
    have hl : GridCO.headLabel? o = some s := by
      simpa only [Nat.add_sub_cancel] using beq_iff_eq.mp (List.mem_filter.mp ho).2
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
    exact pcsa_proposer_tick_input_relay_late_win E rho h hD (hT := pcsa_floor_early_next hT) k a
      y x hy hx s i r hc hk ha ho
/-- Actual gate-to-proposer counts discharge CL2 once the root and retained path are supplied. -/
theorem pcsa_gate_proposer_walk_counts (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (X : Block) (view : Option (PC p.n)) (tree : List Block)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hk : rho.events[k]? = some (.tick y (GridCO.proposalTime p.toParams.engine (s + 1))))
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s = some X)
    (hanchor : Block.Compatible
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime
        p.toParams.engine (s + 1))) view) X)
    (hpath : ∀ B, Block.Prec
      (liveRoot p (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime
        p.toParams.engine (s + 1))) view) B →
      Block.Preceq B X → B ∈ tree) :
    Block.Preceq X (headInTree p
      (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime p.toParams.engine (s +
        1))) view tree
      (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime
        p.toParams.engine (s + 1))) (s + 1))
      (proposerSupport (clock p (V2.D.Run.stateBefore E rho k y).st (GridCO.proposalTime
        p.toParams.engine (s + 1))) (s + 1))) :=
  pcsa_gate_proposer_walk_counts_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx
    hy s X view tree (pcsa_floor_early (pcsa_zero_le_proposal s)) hc ha hk hresult hanchor hpath
end AvailableChain.PCSA.Run

end
