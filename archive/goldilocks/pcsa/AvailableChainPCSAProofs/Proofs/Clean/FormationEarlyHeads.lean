module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadBody
public import AvailableChainPCSAProofs.Proofs.Clean.HonestReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.BodyRelayTime
public import AvailableChainPCSAProofs.Proofs.Shared.HonestProposal
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow

public section

/-! Early HEAD receipt in the Formation window. For an object sent at `t`
with `z_{s-1} ≤ t`, the Formation deadline `max t z_{s-1} + Δ` is `t + Δ`,
the strict non-row deadline of the Clean receipt proofs. The HEAD of each
honest seat awake at `v_s`, and its exact body, then reach every honest node
with stamps before `e_s`. Given exact honest HEADs, this closes the early
HEAD input of Formation. -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
  {m : FGMode}

omit [DecidableEq V] [Fintype V] in
/-- An object whose payload is not a row is a non-row object. -/
theorem pcsa_formation_isNonRow (o : Obj p) (hn : ∀ body, o.payload ≠ .row body) :
    IsNonRow o := by
  rw [pcsa_IsNonRow_def]
  cases he : o.payload <;> try trivial
  exact (hn _ he).elim

omit [DecidableEq V] [Fintype V] in
/-- The slot-`s` vote time is after `z_{s-1}`. -/
theorem pcsa_formation_freeze_prev_le_vote (p : Params) (s : Slot) (hs : 0 < s) :
    SA.freezeTime p.toParams (s - 1) ≤ SA.voteTime p.toParams s := by
  have hd := p.deltaPos
  have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
    have h1 : 1 ≤ s := hs
    push_cast [Nat.cast_sub h1]
    ring
  change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
  rw [hcast]
  linarith

/-- After `z_{s-1}`, Formation delivery gives the strict broadcast deadline. -/
theorem pcsa_formation_strict_broadcast (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (o : Obj p) (hn : ∀ body, o.payload ≠ .row body) (x y : V) (t : Time)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (he : V2.D.Run.emits E rho x o t)
    (hz : SA.freezeTime p.toParams (s - 1) ≤ t)
    (hc : t + E.Δ ≤ SA.freezeTime p.toParams s)
    (hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (t + E.Δ) y) o = false) :
    ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧ ∃ j, V2.D.Run.handlesAt E rho j y o t' := by
  have hm : max t (SA.freezeTime p.toParams (s - 1)) + E.Δ = t + E.Δ := by
    rw [max_eq_left hz]
  have hr := h.delivery.broadcast x hx o (pcsa_formation_isNonRow o hn) t he y hy
    (by rw [hm]; exact hc) (by rw [hm]; exact hNX)
  rwa [hm] at hr

/-- After `z_{s-1}`, Formation delivery gives the strict relay deadline. -/
theorem pcsa_formation_strict_relay (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (o : Obj p) (hn : ∀ body, o.payload ≠ .row body) (x y : V) (i : Nat) (t : Time)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (ha : V2.D.Run.acceptsAt E rho i x o t)
    (hneed : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (i + 1) y) o = false)
    (hz : SA.freezeTime p.toParams (s - 1) ≤ t)
    (hc : t + E.Δ ≤ SA.freezeTime p.toParams s)
    (hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (t + E.Δ) y) o = false) :
    ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧ ∃ j, V2.D.Run.handlesAt E rho j y o t' := by
  have hm : max t (SA.freezeTime p.toParams (s - 1)) + E.Δ = t + E.Δ := by
    rw [max_eq_left hz]
  have hr := h.delivery.relay x hx i o (pcsa_formation_isNonRow o hn) t ha y hy hneed
    (by rw [hm]; exact hc) (by rw [hm]; exact hNX)
  rwa [hm] at hr

omit [DecidableEq V] [Fintype V] in
private theorem early_vote_add (E : Generic.Env V) (hd : E.Δ = p.Δ) (s : Slot) :
    SA.voteTime p.toParams s + E.Δ = SA.earlyTime p.toParams s := by
  rw [hd]
  change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
  ring

omit [DecidableEq V] [Fintype V] in
private theorem early_le_freeze (p : Params) (s : Slot) :
    SA.earlyTime p.toParams s ≤ SA.freezeTime p.toParams s := by
  have hd := p.deltaPos
  change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
  linarith

omit [DecidableEq V] [Fintype V] in
private theorem early_times_before (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (k : Nat) (x : V) (t : Time) (hk : rho.events[k]? = some (.tick x t)) :
    ∀ k' < k, ∀ e, rho.events[k']? = some e → e.time ≤ t := by
  intro k' hk' e he
  have h1 := (Gen.V2.Duty.index_lt_idxBefore_iff hS hk (t + 1)).mpr (lt_add_one t)
  have h2 := (Gen.V2.Duty.index_lt_idxBefore_iff hS he (t + 1)).mp (lt_trans hk' h1)
  exact Int.lt_add_one_iff.mp h2

/-- Formation delivery puts each honest HEAD in the pool with a stamp before
`e_s`. -/
theorem pcsa_formation_head_before_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (x y : V) (hy : y ∈ rho.honest) (i : Fin p.n) (H : Block)
    (hi : rho.seatOf (.base (.head s)) i = x) (hH : HonestHeadAt p c E rho x s H) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) :
    (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k y).st.base.votes ∧
    GridCO.stampVote (V2.D.Run.stateBefore E rho k y).st.base
      ⟨.seat s i, .head H.root⟩ < SA.earlyTime p.toParams s := by
  have hh : rho.seatOf (.base (.head s)) i ∈ rho.honest := by rw [hi]; exact hH.1
  have he := pcsa_honest_head_emits E rho x s i H hi hH
  have htime := early_vote_add E h.base.delta s
  have hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s + E.Δ) y)
      (⟨.seat (.base (.head s)) i, .head H.root⟩ : Obj p) = false := by
    rw [htime]
    exact pcsa_honest_head_not_excluded_early E rho h.base y s i H.root hh
  obtain ⟨t, hlo, hhi, j, hhandle⟩ := pcsa_formation_strict_broadcast E rho s N ΔF h _
    (by intro body heq; cases heq) x y _ hH.1 hy he
    (pcsa_formation_freeze_prev_le_vote p s h.slotPos)
    (by rw [htime]; exact early_le_freeze p s) hNX
  rw [htime] at hhi
  have hstart : GridCO.proposalTime p.toParams.engine s ≤ t := by
    change 4 * p.Δ * (s : Int) ≤ t
    change 4 * p.Δ * (s : Int) + p.Δ ≤ t at hlo
    have hp := p.deltaPos
    linarith
  have hgate : t < SA.gateTime p.toParams s := by
    change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at hhi
    change t < 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hj : j + 1 ≤ V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) := by
    obtain ⟨parent, hevent, _⟩ := hhandle
    exact Nat.succ_le_of_lt
      ((Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed hevent _).mpr hhi)
  have hm : (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho (j + 1) y).st.base.votes := by
    rcases pcsa_handled_head_stateBefore_mem_or_cap E rho h.base j y t s i H.root hstart hgate
      hhandle with hm | he
    · exact hm
    · have hf := pcsa_honest_head_pool_not_capped E rho h.base.valid (j + 1) y s i hh
      rw [he] at hf
      cases hf
  refine ⟨pcsa_heads_stateBefore_mono E rho h.base.noRestart y (hj.trans hk) hm, ?_⟩
  rw [pcsa_head_stamp_stateBefore_eq E rho h.base.noRestart y (hj.trans hk) _ hm]
  exact pcsa_head_stamp_lt_of_index_cut E rho h.base.valid.toScheduleWellFormed
    h.base.noRestart (j + 1) y s i H.root _ hj hm

/-- Formation delivery puts the exact body of each honest HEAD at every honest
node with a stamp before `e_s`. -/
theorem pcsa_formation_head_body_before_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (x y : V) (hy : y ∈ rho.honest) (H : Block) (hH : HonestHeadAt p c E rho x s H)
    (k : Nat) (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) :
    H ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks ∧
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base H <
        SA.earlyTime p.toParams s := by
  have hS := h.base.valid.toScheduleWellFormed
  by_cases hg : H = .genesis
  · subst H
    obtain ⟨hm, ht⟩ := pcsa_genesis_body_stamp E rho h.base.noRestart k y
    refine ⟨hm, ?_⟩
    rw [ht]
    have hp := p.deltaPos
    change 0 < 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  · obtain ⟨a, ha, hm, _⟩ := pcsa_honest_head_body_before_vote E rho h.base h.frame x s H hH
    have hdl : max (SA.voteTime p.toParams s) (SA.freezeTime p.toParams (s - 1)) + E.Δ =
        SA.earlyTime p.toParams s := by
      rw [max_eq_left (pcsa_formation_freeze_prev_le_vote p s h.slotPos),
        early_vote_add E h.base.delta s]
    have hmono : Monotone (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) := by
      intro u w huw
      dsimp only
      exact Int.add_le_add_right (max_le_max huw (le_refl _)) E.Δ
    have hR := pcsa_indexed_body_within_on E rho h.base h.frame h.delivery
      (fun o r M hdec => pcsa_block_isNonRow o r M hdec) hmono
      (fun t => lt_of_le_of_lt (le_max_left t _) (lt_add_of_pos_right _ E.Δ_pos))
      x y hH.1 hy a (SA.voteTime p.toParams s) (early_times_before E rho hS a x _ ha)
      (by rw [hdl]; exact early_le_freeze p s) H hm
    rw [hdl, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hR
    have hst := pcsa_body_stamp_lt_of_index_cut E rho hS h.base.noRestart _ y H _ le_rfl hg hR
    refine ⟨pcsa_body_stateBefore_mono E rho h.base.noRestart y hk hR, ?_⟩
    rw [pcsa_body_stamp_stateBefore_eq E rho h.base.noRestart y hk H hR]
    exact hst

/-- Every honest node holds each honest HEAD of slot `s` in its early pool,
resolved to the exact HEAD body. -/
theorem pcsa_formation_head_early_resolved (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (x y : V) (hy : y ∈ rho.honest) (i : Fin p.n) (H : Block)
    (hi : rho.seatOf (.base (.head s)) i = x) (hH : HonestHeadAt p c E rho x s H) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) (u : Time) :
    (⟨.seat s i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      GridCO.earlyVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∧
    GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k y).st u))
      ⟨.seat s i, .head H.root⟩ = some H := by
  obtain ⟨hh, ht⟩ := pcsa_formation_head_before_early E rho s N ΔF h x y hy i H hi hH k hk
  obtain ⟨hb, hbt⟩ := pcsa_formation_head_body_before_early E rho s N ΔF h x y hy H hH k hk
  have hr := pcsa_resolved_head_of_held_body E rho h.base h.frame k y hy s i H u hb
  have hslot := pcsa_honest_head_slot_le E rho h.base h.frame x s H hH
  obtain ⟨headRow, hheadRow⟩ := pcsa_head_stamp_lookup E rho k y ⟨.seat s i, .head H.root⟩ hh
  obtain ⟨bodyRow, hbodyRow⟩ := pcsa_body_stamp_lookup E rho k y H hb
  have hheads : (V2.D.Run.stateBefore E rho k y).st.base.voteStamp <+:
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)).voteStamp := by
    change _ <+: (clock p _ u).base.voteStamp
    rw [pcsa_clock_headStamps]
  have hbodies : (V2.D.Run.stateBefore E rho k y).st.base.blockStamp <+:
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)).blockStamp := by
    change _ <+: (clock p _ u).base.blockStamp
    rw [pcsa_clock_bodyStamps]
  have ht' := pcsa_stampVote_eq_of_prefix _ _ ⟨.seat s i, .head H.root⟩ headRow hheads hheadRow
  have hbt' := pcsa_stampBlock_eq_of_prefix _ _ H bodyRow hbodies hbodyRow
  refine ⟨?_, hr⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · change _ ∈ (clock p (V2.D.Run.stateBefore E rho k y).st u).base.votes
    rw [pcsa_clock_heads]
    exact hh
  · change (some s == some s) = true
    exact beq_self_eq_true _
  · delta GridCO.resolvedBefore
    rw [hr]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hslot, ?_⟩, ?_⟩
    · apply decide_eq_true
      rw [ht']
      exact ht
    · apply decide_eq_true
      rw [hbt']
      exact hbt

/-- Exact honest HEADs give the early HEAD input of Formation. Each counted
seat holder is honest and awake at `v_s`. Its HEAD is `N.erase`, and every
honest node holds it resolved in its early pool at `e_s`. -/
theorem pcsa_formation_early_heads_of_exact (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hExact : ∀ x H, HonestHeadAt p c E rho x s H → H = N.erase) :
    ∀ y ∈ rho.honest, ∀ nd,
      pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
      ∀ i : Fin p.n, rho.seatOf (.base (.head s)) i ∈ awakeHonestLabel p c E rho s →
        ∃ o ∈ GridCO.earlyVotes p.toParams.engine (actView nd.st) s,
          GridCO.headSeat? o = some i ∧
            GridCO.resolvedHead? (actView nd.st) o = some N.erase := by
  intro y hy nd hnd i hi
  have hS := h.base.valid.toScheduleWellFormed
  let x := rho.seatOf (.base (.head s)) i
  have hx : x ∈ rho.honest ∧ E.awake x (SA.voteTime p.toParams s) = true := by
    rw [pcsa_awakeHonestLabel_def] at hi
    have hm := (Finset.mem_inter.mp hi).1
    rw [Gen.V2.Duty.awakeHonest_def] at hm
    exact Finset.mem_filter.mp hm
  have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.voteTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    positivity
  have hvz : SA.voteTime p.toParams s ≤ SA.freezeTime p.toParams s := by
    have hd := p.deltaPos
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith
  have hm := h.base.valid.tick_total x hx.1 _ hpub hz (le_trans hvz h.horizon)
  have hsome : (V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams s)).isSome = true := by
    delta V2.D.Run.tickIdx?
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, hm, decide_eq_true ⟨rfl, rfl⟩⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  let dst : Node p := (pcsaWith m p c).clock (V2.D.Run.stateBefore E rho a x)
    (SA.voteTime p.toParams s)
  have hdst : pcsa_postClock E rho x (SA.voteTime p.toParams s) = some dst := by
    rw [pcsa_postClock_def, pcsa_preTick_def, ha]
    rfl
  have hH : HonestHeadAt p c E rho x s (headVote p dst.st s) := by
    rw [pcsa_HonestHeadAt_def, pcsa_voteHeadAt_def, hdst]
    exact ⟨hx.1, hx.2, rfl⟩
  have hHN := hExact x _ hH
  obtain ⟨k, hk, hst⟩ := pcsa_postClock_source E rho y _ nd hnd
  have hkk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_lt
    intro hlt
    exact lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hS hk _).mp hlt)
  obtain ⟨he, hr⟩ := pcsa_formation_head_early_resolved E rho s N ΔF h x y hy i _ rfl hH k
    hkk (SA.earlyTime p.toParams s)
  refine ⟨⟨.seat s i, .head (headVote p dst.st s).root⟩, ?_, rfl, ?_⟩
  · rw [hst]
    exact he
  · rw [hst, hr, hHN]

end AvailableChain.PCSA.Run
end
