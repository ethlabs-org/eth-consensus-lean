module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.HeadRelay -- shake: keep
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.AnchorCoverage
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}

/-- An enabled tick gives environment joinedness at its exact time and slot. -/
theorem wc_tick_joinedAt (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {t : Time} {s : Slot}
    (hi : rho.events[i]? = some (.tick x t)) (hs : p.slotOf t = s)
    (hJ : joinedNow p (clock p (storeAt p c E rho i x) t) = true) :
    joinedAt p E rho x s t := by
  have bound (w : Time) (_hw : 0 ≤ w) (hwt : w ≤ t)
      (hr : V2.Event.restart x w ∈ rho.events) : w ≤ slotStartZ p ((s : Int) - 1) := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hji := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hj hi hwt
      (show (0 : Nat) < 1 from by decide)
    obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hV.toScheduleWellFormed hj hji
    have hg := hJ
    change joinedNow p (clock p (rho.stateBefore E i x).st t) = true at hg
    unfold joinedNow at hg
    change joinedNow p (clock p (rho.stateBefore E i x).st t) = true at hJ
    rw [fgsa_clock_restartTime, hu, (clock_vn _ _).2] at hg
    have hub : u ≤ slotStartZ p ((s : Int) - 1) := by
      change decide (u ≤ 4 * p.Δ * ((p.slotOf t : Int) - 1)) = true at hg
      rw [hs] at hg
      exact of_decide_eq_true hg
    exact hwu.trans hub
  refine ⟨hV.tick_awake x t (List.mem_of_getElem? hi), ?_, bound⟩
  intro w hw hwt hW
  exact bound w hw.le hwt (hV.wake_restart x
    (hV.honest_only _ (List.mem_of_getElem? hi)) w hw
    (hwt.trans (hV.in_horizon _ (List.mem_of_getElem? hi)).2) hW)

/-- An enabled proposal or HEAD read supplies its current-duty joined scope. -/
theorem wc_duty_joinedAt (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {s : Slot} {st : State p.n} {t : Time}
    (he : rho.events[i]? = some (.tick x t))
    (hst : st = clock p (storeAt p c E rho i x) t)
    (ht : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s)
    (hj : joinedNow p st = true) : joinedAt p E rho x s t := by
  rw [hst] at hj
  apply wc_tick_joinedAt hV he _ hj
  rcases ht with rfl | rfl
  · change p.slotOf (4 * p.Δ * (s : Int)) = s
    simpa only [add_zero] using slotOf_offset p s 0 (by omega)
      (by have hd := p.deltaPos; dsimp [Time] at *; omega)
  · exact slotOf_offset p s p.Δ p.deltaPos.le
      (by have hd := p.deltaPos; dsimp [Time] at *; omega)

/-- A joined current duty bounds earlier restarts and supplies the receipt interval. -/
theorem wc_duty_receiver (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {r : Slot} {t : Time}
    (he : rho.events[i]? = some (.tick x t))
    (hJ : joinedAt p E rho x (r + 1) t) :
    (∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams r) ∧
    AwakeClosed E x (SA.proposalTime p.toParams r) t := by
  constructor
  · intro j w hji hj
    have ht : w ≤ t := by
      by_contra hn
      have hij := V2.D.Engine.eventIndex_lt_of_time_lt hV.toScheduleWellFormed he hj
        (lt_of_not_ge hn)
      omega
    have hb := hJ.2.2 w (hV.in_horizon _ (List.mem_of_getElem? hj)).1 ht
      (List.mem_of_getElem? hj)
    change w ≤ 4 * p.Δ * (r : Int)
    change w ≤ 4 * p.Δ * (((r + 1 : Nat) : Int) - 1) at hb
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hb
  · intro u h0 hu hut
    apply fgsa_awake_of_joinedAt E rho x (r + 1) t u hJ h0 _ hut
    change 4 * p.Δ * (((r + 1 : Nat) : Int) - 1) ≤ u
    change 4 * p.Δ * (r : Int) ≤ u at hu
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hu

/-- A current-duty receiver has proposal service at the previous vote anchor. -/
private theorem wc_duty_path_anchor (hV : V2.D.ExecutionValid E rho)
    (_hR : V2.D.RestartsAtWakes E rho) (hDelta : E.Δ = p.Δ)
    {i k : Nat} {x y : V} {r u : Slot} {t send : Time} {o : Obj p}
    {N : NamedProposal p.n} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (he : rho.events[i]? = some (.tick x t)) (hJ : joinedAt p E rho x (r + 1) t)
    (het : SA.earlyTime p.toParams r ≤ t)
    (hd : (toWire p o).decode = some (.block u N))
    (ha : rho.acceptsAt E k y o send) (hsend : send < SA.voteTime p.toParams r) :
    Gen.V2.Duty.ReadyTrigger E rho o send x (SA.voteTime p.toParams r)
      (SA.earlyTime p.toParams r) ∧
    Gen.V2.Duty.HistorySafeAt E rho x o (SA.voteTime p.toParams r) ∧
    V2.D.restartFree rho x (rho.actionCut (SA.voteTime p.toParams r))
      (rho.idxBefore (SA.earlyTime p.toParams r)) ∧
    (∀ j z, SA.voteTime p.toParams r ≤ z → z < SA.earlyTime p.toParams r →
      rho.handlesAt E j x o z → (fgsa p c).wellFormed o = true ∧
        (fgsa p c).depsPresent (rho.stateBefore E j x) o = true ∧
        fgsaTimely p (rho.stateBefore E j x) o) := by
  obtain ⟨hBound, hAw⟩ := wc_duty_receiver hV he hJ
  have h0 : 0 ≤ SA.voteTime p.toParams r := by
    change 0 ≤ 4 * p.Δ * (r : Int) + p.Δ
    have hd := p.deltaPos
    positivity
  have hpv : SA.proposalTime p.toParams r < SA.voteTime p.toParams r := by
    change 4 * p.Δ * (r : Int) < 4 * p.Δ * (r : Int) + p.Δ
    linarith [p.deltaPos]
  have hve : SA.voteTime p.toParams r < SA.earlyTime p.toParams r := by
    change 4 * p.Δ * (r : Int) + p.Δ < 4 * p.Δ * (r : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have hdi : rho.idxBefore (SA.earlyTime p.toParams r) ≤ i := by
    by_contra hn
    exact (not_lt_of_ge het) ((Gen.V2.Duty.index_lt_idxBefore_iff
      hV.toScheduleWellFormed he _).mp (Nat.lt_of_not_ge hn))
  have hRF : V2.D.restartFree rho x (rho.actionCut (SA.voteTime p.toParams r))
      (rho.idxBefore (SA.earlyTime p.toParams r)) := by
    intro j w hj hje hh
    have hb := hBound j w (hje.trans_le hdi) hh
    have hjv := (V2.D.Engine.index_lt_actionCut_iff hV.toScheduleWellFormed hh _).mpr
      (Or.inl (hb.trans_lt hpv))
    omega
  have hpub : V2.PublicTime E (SA.voteTime p.toParams r) := by
    refine ⟨4 * r + 1, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (r : Int) + p.Δ = _
    push_cast
    ring
  refine ⟨⟨y, hy, Or.inr ⟨k, ha⟩, ?_⟩,
    fgsa_historySafeAt_of_proposal x o _ hd, hRF,
    fgsa_proposal_handlers_at_anchor hV hDelta hx hd ha hsend.le h0 hpub
      (hAw _ h0 hpv.le (hve.le.trans het)) hve
      (het.trans (hV.in_horizon _ (List.mem_of_getElem? he)).2) hRF⟩
  intro z hvz hze
  exact hAw z (h0.trans hvz) (hpv.le.trans hvz) (hze.le.trans het)

/-- Gate coverage uses this receiver and the vote-time anchor. -/
theorem wc_duty_path_coverage (hE : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i k : Nat} {x y : V} {s : Slot} {K : Block}
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    {t : Time} (he : rho.events[i]? = some (.tick x t))
    (hJ : joinedAt p E rho x (s + 1) t)
    (het : SA.earlyTime p.toParams s ≤ t) (hcut : SA.earlyTime p.toParams s ≤ rho.horizon)
    (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hF : ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) K) :
    ∃ required paths,
      ReceiptCoverageAnchorPremises E rho (fun t => max t E.t_GST + p.Δ) rho.horizon
        (SA.earlyTime p.toParams s) 0 x K required paths
        (fun _ _ => SA.voteTime p.toParams s) ∧
      paths K (SA.earlyTime p.toParams s) := by
  have ht := he
  have hx : x ∈ rho.honest := hE.honest_only _ (List.mem_of_getElem? ht)
  let required := fun o t => ∃ l < k, V2.D.Run.acceptsAt E rho l y o t ∧
    ∃ b, blockOf? p o = some b ∧ Block.Preceq b K
  let paths := fun B d => B = K ∧ d = SA.earlyTime p.toParams s
  have hsch := hE.toScheduleWellFormed
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hh
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hsch ht (SA.earlyTime p.toParams s)).mp
      (Nat.lt_of_not_ge hh)
    exact (not_lt.mpr het) hlt
  have htime : ∀ o t, required o t → 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
    rintro o t ⟨l, hl, ha, _⟩
    obtain ⟨parent, hd, _⟩ := ha.1
    refine ⟨(hsch.in_horizon _ (List.mem_of_getElem? hd)).1, ?_⟩
    obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
    rw [hle, hke] at hkey
    change toLex (t, (2 : Nat)) ≤
      toLex (SA.voteTime p.toParams s, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hh | ⟨_, hh⟩
    · exact hh
    · omega
  have hve : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have hmax : max (SA.voteTime p.toParams s) E.t_GST = SA.voteTime p.toParams s :=
    max_eq_left hGST
  have decode {o : Obj p} {b : Block} (hb : blockOf? p o = some b) :
      ∃ r N, (toWire p o).decode = some (.block r N) := by
    change (match (toWire p o).decode with
      | some (.block _ N) => some N.erase | _ => none) = _ at hb
    cases hd : (toWire p o).decode with
    | none => rw [hd] at hb; contradiction
    | some m => cases m <;> simp_all
  refine ⟨required, paths, ?_, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro o t hr
    have htt := htime o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨r, N, hd⟩ := decode hb
    obtain ⟨hT, hH, hRF, _⟩ := wc_duty_path_anchor hE hR hDelta hx hy he hJ het hd ha
      htt.2
    have h0 : 0 ≤ SA.voteTime p.toParams s := by
      change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
      have := p.deltaPos
      positivity
    refine ⟨htt.1, htt.2.le, h0,
      (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos), ?_, Nat.zero_le _, ?_, hH, hRF,
      (fgsa_proposal_acceptance_facts hE hd ha).2⟩
    · simp only [hmax, hve, le_refl]
    · simpa only [hmax, hve] using hT
  · rintro o t ⟨l, _, ha, b, hb, _⟩ r signer B hv
    obtain ⟨u, N, hd⟩ := decode hb
    rw [hd] at hv
    cases hv
  · intro o t hr
    have htt := htime o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨r, N, hd⟩ := decode hb
    have hh := (wc_duty_path_anchor hE hR hDelta hx hy he hJ het hd ha
      htt.2).2.2.2
    simpa only [hmax, hve] using hh
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl K) (hF j (hj.trans hidx))
  · exact ⟨fun _ _ hab => add_le_add (max_le_max hab le_rfl) le_rfl,
      hcut, le_rfl, Nat.zero_le _⟩
  · rintro B d ⟨hBK, hdD⟩
    subst B
    subst d
    refine ⟨block_preceq_refl K, le_rfl, ?_⟩
    intro b hb hne
    obtain ⟨l, hl, t, o, ho, ha, _, ht'⟩ := wc_head_source_path hsch hk hK b hb hne
    have hdecode : ∃ r N, N.erase = b ∧ (toWire p o).decode = some (.block r N) := by
      change (match (toWire p o).decode with
        | some (.block _ N) => some N.erase | _ => none) = _ at ho
      cases he : (toWire p o).decode with
      | none => rw [he] at ho; contradiction
      | some m =>
        cases m <;> simp only [he, reduceCtorEq, Option.some.injEq] at ho
        exact ⟨_, _, ho, rfl⟩
    obtain ⟨r, N, heN, hdec⟩ := hdecode
    refine ⟨o, t, r, N, heN, ⟨l, hl, ha, b, ho, hb⟩, hdec, ?_⟩
    simp only [hmax, hve, le_refl]
  · intro o t r N hr hdec
    obtain ⟨l, hl, ha, b', hb', hBK⟩ := hr
    have hb : blockOf? p o = some N.erase := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hdec]
    have heq := Option.some.inj (hb'.symm.trans hb)
    subst b'
    exact ⟨K, SA.earlyTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩



/-- The current joined duty receives a previous HEAD path in its local epoch. -/
theorem wc_duty_head_path (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) (hDelta : E.Δ = p.Δ)
    (hroots : NamedReceiptRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
    (hmono : RMonoAll p c E rho)
    {i k : Nat} {x y : V} {r : Slot} {t : Time} {D : Block}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (he : rho.events[i]? = some (.tick x t))
    (hJ : joinedAt p E rho x (r + 1) t)
    (het : SA.earlyTime p.toParams r ≤ t)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams r)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams r)))
    (hDmem : D ∈ (storeAt p c E rho k y).base.blocks)
    (hFD : Block.Preceq (F_at p c E rho i x) D) :
    ∀ A, Block.Preceq A D →
      A ∈ (clock p (storeAt p c E rho i x) t).base.blocks ∧
      GridCO.stampBlock (clock p (storeAt p c E rho i x) t).base A <
        SA.earlyTime p.toParams r := by
  have hS := hV.toScheduleWellFormed
  have hF : ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) D := by
    intro j hj
    exact block_preceq_trans (eraseFG_preceq (hmono j i x hx hj).1) hFD
  have hcut := het.trans (hV.in_horizon _ (List.mem_of_getElem? he)).2
  obtain ⟨required, paths, hcov, hpath⟩ := wc_duty_path_coverage hV hR hDelta hsync
    hGST he hJ het hcut hy hk hDmem hF
  let cut := SA.earlyTime p.toParams r
  let j := rho.idxBefore cut
  have hji : j ≤ i := by
    by_contra hn
    exact (not_lt_of_ge het) ((Gen.V2.Duty.index_lt_idxBefore_iff hS he cut).mp
      (Nat.lt_of_not_ge hn))
  have hp : ∀ A, Block.Preceq A D →
      A ∈ (actView (rho.stateBeforeTime E cut x).st).blocks := by
    apply fgsa_active_path_of_coverage_anchor (hroots := hroots) E rho hV hDelta
      (fun t => max t E.t_GST + p.Δ) rho.horizon cut 0 x D required paths
      (fun _ _ => SA.voteTime p.toParams r) hx hcov hpath
    have h := hF j hji
    change Block.Preceq (eraseFG (rho.stateBefore E (rho.idxBefore cut) x).st.fg.F) D at h
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho cut hS] at h
    exact h
  have hread : storeAt p c E rho j x = (rho.stateBeforeTime E cut x).st := by
    change (rho.stateBefore E (rho.idxBefore cut) x).st = _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho cut hS]
  obtain ⟨hBound, _⟩ := wc_duty_receiver hV he hJ
  have hRF : V2.D.restartFree rho x j i := by
    intro l w hjl hli hl
    have hb := hBound l w hli hl
    have hwc : w < cut := by
      apply hb.trans_lt
      change 4 * p.Δ * (r : Int) < 4 * p.Δ * (r : Int) + 2 * p.Δ
      linarith [p.deltaPos]
    have hlj := (Gen.V2.Duty.index_lt_idxBefore_iff hS hl cut).mpr hwc
    omega
  have hilen := Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1
  have hkeep := hcumul.1 j i x hx hji hilen
  have hstamp := hcumul.2 j i x hx hji hilen hRF
  intro A hAD
  have hAm := ((actView_blocks _ A).mp (hp A hAD)).1
  have hAs := fgsa_block_stamp_before_read E rho hS x cut (by
    change 0 < 4 * p.Δ * (r : Int) + 2 * p.Δ
    have hd := p.deltaPos
    positivity) A hAm
  rw [← hread] at hAm hAs
  have hkeys : A ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change A ∈ (rho.stateBefore E j x).st.base.blockStamp.map Prod.fst
    rw [(metaInv_stateBefore E rho j x).stampKeys]
    exact hAm
  refine ⟨?_, ?_⟩
  · rw [clock_base_blocks]
    exact hkeep.2.1.subset hAm
  · rw [inclusion_stampBlock_of_prefix
      (show (storeAt p c E rho j x).base.blockStamp <+:
        (clock p (storeAt p c E rho i x) t).base.blockStamp by
        rw [(clock_cumulative p _ _).2.2.1]
        exact hstamp.1) hkeys]
    exact hAs


theorem wc_joined_rest_bound [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (hE : V2.D.ExecutionValid E rho)
    (r : Slot) (H : Finset (Fin p.n))
    (hH : ∀ k, rho.seatOf (.base (.head r)) k ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head r)) k) r (SA.voteTime p.toParams r) → k ∈ H)
    (L : List (GridCO.Wire p.n .root))
    (hL : ∀ o ∈ L, ∀ k, GridCO.headSeat? o = some k →
      ∃ i x, ∃ o' ∈ (storeAt p c E rho i x).base.votes,
        GridCO.headLabel? o' = some r ∧ GridCO.headSeat? o' = some k) :
    ((GridCO.seats p.n L).toFinset \ H).card ≤ (Gen.V2.Duty.faulty rho).card := by
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head r)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    rw [Gen.V2.Duty.faulty_def]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hh
    apply hn (hH k hh ?_)
    obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
    obtain ⟨i, x, o', ho', hl', hs'⟩ := hL o ho k hs
    exact fgsa_stored_honest_head_joined E rho hE i x r k o' ho' hl' hs' hh
  · intro k _ j _ he
    exact (hC (.base (.head r)) trivial).injective he


end AvailableChain.FGSA.Run
end
