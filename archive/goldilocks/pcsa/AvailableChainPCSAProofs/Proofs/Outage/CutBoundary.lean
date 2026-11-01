module
public import AvailableChainPCSAProofs.Proofs.Outage.CutFacts

public section

/-! The Clean-lane boundary of the S case of slow P1 (pcsa34-r4.3 §5.5 steps
1–2) from the Clean facts at the cut, stage 1, under the lag
`T + 4(k − 1)Δ ≤ b₀` of `Outage₂`. The last clean gate `d_J`
(`d_J ≤ b₀ < d_{J+1}`) has a result `⪰ A = S_u(T)` compatible with every lock,
so it sets `S ⪰ A` at every honest node; the deliveries at `d_J` keep it; the
S-case induction from `d_J` carries the invariant to `b₀`.

No lock on `A` is required before the pending gate `d_{J+1}`: no gate runs in
`(d_J, d_{J+1})`. The lag puts `j₁ + k ≤ J + 1`, so the pending gate has the
`k − 1` saved results `⪰ A` it needs to write the lock (the result of label
`j₁` at another node is only compatible with `A`, CL1). The only possible
HEAD read in `(d_J, d_{J+1})` is that of label `J + 2`. It covers `A`: the
clean-gate bridge puts `A = R_u(j₁)` below every honest HEAD of label
`j₁ + 1` (`d_{j₁} ≤ b₀`), and the HEAD cone carries it up to label `J + 2`
(`e_{J+1} = d_J ≤ b₀`). -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-! ### The last clean gate -/

/-- [§5.5 step 2] The gate of a clean label `J > j₁` at an honest node sets
`S ⪰ A`, and `A` is in its tree: its result `R ⪰ A` is above every lock. -/
theorem pcsa_cut_gate (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) {b₀ ΔF : Time}
    (hC : Clean₂ p c E rho b₀ ΔF) (hfr : StageOneFrame p c E rho)
    (hK : CutFacts p c E rho b₀) {u : V} (hu : u ∈ rho.honest) {j₁ : Nat} {A : Block}
    (hA : gateResultAt p c E rho u j₁ = some (some A)) (hAg : A ≠ .genesis) {J : Nat}
    (hjJ : j₁ < J) (hdJ : SA.gateTime p.toParams J ≤ b₀) {x : V} (hx : x ∈ rho.honest)
    {kJ : Nat} (hkJ : rho.events[kJ]? = some (.tick x (SA.gateTime p.toParams J))) :
    Block.Preceq A (V2.D.Run.stateBefore E rho (kJ + 1) x).st.base.stableRecord ∧
      A ∈ (V2.D.Run.stateBefore E rho (kJ + 1) x).st.base.blocks := by
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (1 : Int) ≤ p.Δ := p.deltaPos
  set st₀ := (V2.D.Run.stateBefore E rho kJ x).st with hst₀
  have hF : st₀.fg.F = .genesis := ((FrameVacuous_def p _).mp (hfr x hx kJ)).1
  have hF' : (clockPre p st₀ (SA.gateTime p.toParams J)).fg.F = .genesis := by
    rw [(pcsa_clockPre_frame p _ _).2.2.2.1]
    exact hF
  have hun := pcsa_unsaved_before E rho h.noRestart hfr x hx J kJ
    (pcsa_node_events_before_tick E rho hs h.noRestart hkJ)
  have hns : (GridCO.savedGenuine (clockPre p st₀ (SA.gateTime p.toParams J)).base J).isSome =
      false := by
    change (((clockPre p st₀ _).base.genuine.find? (fun row => row.1 == J)).map
      Prod.snd).isSome = false
    rw [(pcsa_clockPre_slow p _ _).2.1]
    change (GridCO.savedGenuine st₀.base J).isSome = false
    rw [hun]
    rfl
  -- the result of `J`
  have hgr := pcsa_gate_tick_result E rho hs hfr hx hkJ
  have heJ : SA.earlyTime p.toParams J ≤ b₀ := le_trans (pcsa_early_le_gate J) hdJ
  obtain ⟨R, hRe, hAR⟩ := pcsa_cut_res hK hu hA hx (i := J) hjJ heJ hgr
  have hc : SA.Root.confirmationFrom p.toParams .genesis
      (actView (clockPre p st₀ (SA.gateTime p.toParams J))) J = some R := hRe
  have hgR : gateResultAt p c E rho x J = some (some R) := by rw [hgr, hRe]
  -- the rows at the gate are below `R`
  have hpre := pcsa_preTick_read E rho hs h.noRestart hkJ
  have hd0 : 0 ≤ SA.gateTime p.toParams J - 1 := by
    have := pcsa_gate_nonneg (p := p) J
    change 0 ≤ 4 * p.Δ * (J : Int) + 6 * p.Δ - 1
    have : (0 : Int) ≤ (J : Int) := Int.natCast_nonneg _
    nlinarith
  have hrows0 := pcsa_cut_rows h hfr hK hx hd0 (by linarith)
  rw [hpre] at hrows0
  have hSR : Block.Preceq st₀.base.stableRecord R :=
    pcsa_cut_record_below h hfr hK hx (pcsa_node_events_before_tick E rho hs h.noRestart hkJ)
      heJ hgR
  have hrowsR : ∀ row ∈ (clockPre p st₀ (SA.gateTime p.toParams J)).base.obligations,
      Block.Preceq row.1 R := fun row hr =>
    Gen.Pure.block_preceq_trans (hrows0 row ((pcsa_clockPre_slow p _ _).2.2.2.1 hr)) hSR
  -- the tree
  have hAb : A ∈ (clockPre p st₀ (SA.gateTime p.toParams J)).base.blocks := by
    rcases pcsa_confirmationFrom_path p .genesis _ J R A hc (Gen.Pure.block_genesis_preceq A)
      hAR with he | hm
    · exact absurd he hAg
    · change A ∈ (clockPre p st₀ _).base.blocks.filter _ at hm
      exact (List.mem_filter.mp hm).1
  rw [V2.D.Run.stateBefore_succ E rho hkJ, pcsa_step_tick_st, pcsa_clock_at_gate,
    pcsa_gateStep_genesis p _ _ hF', hns, ite_eq_right (by decide)]
  obtain ⟨g1, g2⟩ := pcsa_gateFrom_pass p .genesis
    (clockPre p st₀ (SA.gateTime p.toParams J)).pcs
    (gateRank p (clockPre p st₀ (SA.gateTime p.toParams J)) J)
    (clockPre p st₀ (SA.gateTime p.toParams J)) J A R hc hAR
    (fun row hr => Gen.Pure.block_compatible_of_common (hrowsR row hr)
      (Gen.Pure.block_preceq_refl R))
  exact ⟨g1, by rw [g2]; exact hAb⟩

/-- [§5.5 step 2] The deliveries after the tick of a node at `t`, up to the
read index of `t`, keep `S ⪰ A` and `A` in the tree. -/
theorem pcsa_cut_deliveries (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hfr : StageOneFrame p c E rho) {A : Block}
    {x : V} (hx : x ∈ rho.honest) {t : Time} {kt : Nat}
    (hkt : rho.events[kt]? = some (.tick x t))
    (h0 : Block.Preceq A (V2.D.Run.stateBefore E rho (kt + 1) x).st.base.stableRecord ∧
      A ∈ (V2.D.Run.stateBefore E rho (kt + 1) x).st.base.blocks) :
    Block.Preceq A (storeAt p c E rho x t).base.stableRecord ∧
      A ∈ (storeAt p c E rho x t).base.blocks := by
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  have hlt : kt < (rho.events.filter (fun e => decide (e.time ≤ t))).length :=
    (V2.D.Engine.index_lt_read_length_iff hs t hkt).mpr le_rfl
  rw [pcsa_storeAt_index E rho hs]
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => Block.Preceq A nd.st.base.stableRecord ∧ A ∈ nd.st.base.blocks)
    hlt x ?_ h0
  intro k e hk1 hk2 he hn hQ
  beta_reduce at hQ ⊢
  have het : e.time ≤ t := (V2.D.Engine.index_lt_read_length_iff hs t he).mp hk2
  have hte : t ≤ e.time := pcsa_event_time_mono E rho hs hkt he (by omega)
  cases e with
  | restart u t' => exact absurd he (h.noRestart k u t')
  | tick u t' =>
    exfalso
    change u = x at hn
    change t' ≤ t at het
    change t ≤ t' at hte
    subst u
    have heq : t' = t := le_antisymm het hte
    subst heq
    have := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp he).1 hs.nodup).mp
      (he.trans hkt.symm)
    omega
  | deliver u o t' =>
    change u = x at hn
    subst u
    have hF0 := ((FrameVacuous_def p _).mp (hfr x hx k)).1
    have hF := pcsa_deliver_frame E rho hfr hx he
    obtain ⟨hb, -, hbl⟩ := pcsa_process_slow p _ (toWire p o) hF0 hF
    rw [pcsa_step_deliver_st]
    exact ⟨hb.stable ▸ hQ.1, hbl hQ.2⟩

/-! ### The HEAD past the cut -/

omit [Fintype V] in
/-- [§5.5 step 2] Every honest HEAD of a label `r` with `d_J < v_r < d_{J+1}`
(so `r = J + 2`) extends `A`: the bridge puts `A` below every honest HEAD of
label `j₁ + 1`, and the HEAD cone carries it to label `J + 2`, since
`e_{J+1} = d_J ≤ b₀`. -/
theorem pcsa_cut_pendingHead {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)}
    {b₀ : Time} (hK : CutFacts p c E rho b₀) {u : V} (hu : u ∈ rho.honest) {j₁ : Nat} {A : Block}
    (hA : gateResultAt p c E rho u j₁ = some (some A)) {J : Nat} (hjJ : j₁ < J + 1)
    (hdJ : SA.gateTime p.toParams J ≤ b₀) {z : V} {r' : Slot} {H : Block}
    (hH : HonestHeadAt p c E rho z r' H) (h1 : SA.gateTime p.toParams J < SA.voteTime p.toParams r')
    (h2 : SA.voteTime p.toParams r' < SA.gateTime p.toParams (J + 1)) :
    Block.Preceq A H := by
  obtain ⟨r, rfl⟩ : ∃ r : Nat, r = r' := ⟨_, rfl⟩
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hr : r = J + 2 := by
    change 4 * p.Δ * (J : Int) + 6 * p.Δ < 4 * p.Δ * (r : Int) + p.Δ at h1
    change 4 * p.Δ * (r : Int) + p.Δ < 4 * p.Δ * ((J + 1 : Nat) : Int) + 6 * p.Δ at h2
    push_cast at h2
    have h3 : (J : Int) + 1 < r := by
      by_contra hn
      have : (r : Int) ≤ J + 1 := not_lt.mp hn
      nlinarith
    have h4 : (r : Int) < J + 3 := by
      by_contra hn
      have : (J : Int) + 3 ≤ r := not_lt.mp hn
      nlinarith
    omega
  subst hr
  have heJ : SA.earlyTime p.toParams (J + 1) ≤ b₀ := by
    rw [← pcsa_gate_pred_early (p := p) (J + 1) (Nat.succ_pos J)]
    exact hdJ
  have hB : ∀ y G, HonestHeadAt p c E rho y (j₁ + 1) G → Block.Preceq A G :=
    fun y G hG =>
      hK.bridge j₁ u y A G (le_trans (pcsa_gate_mono (Nat.le_of_lt_succ hjJ)) hdJ) hu hA hG
  obtain ⟨n, hn⟩ : ∃ n, J + 1 = j₁ + 1 + n := ⟨J - j₁, by omega⟩
  rw [hn] at heJ
  have hH' : HonestHeadAt p c E rho z (j₁ + 1 + n + 1) H := by
    rw [← hn]
    exact hH
  exact pcsa_cone_up hK.toCutChain hB n heJ z H hH'

/-! ### The boundary at the last clean gate -/

/-- [§5.5 step 2] The boundary facts at the last clean gate `d_J` for the
pending label `J + 1`. -/
theorem pcsa_cut_boundary_gate (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho) (hK : CutFacts p c E rho b₀) {u : V}
    (hu : u ∈ rho.honest) {j₁ : Nat} {A : Block}
    (hA : gateResultAt p c E rho u j₁ = some (some A))
    (hd1 : SA.gateTime p.toParams (j₁ + 1) ≤ b₀) (hAg : A ≠ .genesis) {J : Nat}
    (hjJ : j₁ + p.k ≤ J + 1) (hdJ : SA.gateTime p.toParams J ≤ b₀) :
    CleanSlowBoundary p c E rho A (SA.gateTime p.toParams J) (J + 1) := by
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (1 : Int) ≤ p.Δ := p.deltaPos
  have hk2 := p.kLarge
  have hj1J : j₁ < J := by omega
  have hsucc := pcsa_gate_succ (p := p) J
  have hd0 := pcsa_gate_nonneg (p := p) J
  have hst : ∀ x ∈ rho.honest,
      Block.Preceq A (storeAt p c E rho x (SA.gateTime p.toParams J)).base.stableRecord ∧
      A ∈ (storeAt p c E rho x (SA.gateTime p.toParams J)).base.blocks := by
    intro x hx
    obtain ⟨kJ, hkJ⟩ := pcsa_tick_exists E rho hs x hx _ (pcsa_gate_public E h.delta J) hd0
      (le_trans hdJ hC.cut.2)
    exact pcsa_cut_deliveries E rho hC hfr hx hkJ
      (pcsa_cut_gate E rho hC hfr hK hu hA hAg hj1J hdJ hx hkJ)
  have hrows : ∀ x ∈ rho.honest,
      ∀ row ∈ (storeAt p c E rho x (SA.gateTime p.toParams J)).base.obligations,
        Block.Preceq row.1 (storeAt p c E rho x (SA.gateTime p.toParams J)).base.stableRecord :=
    fun x hx => pcsa_cut_rows h hfr hK hx hd0 hdJ
  have hres : ∀ x ∈ rho.honest, ∀ i : Nat, j₁ < i → i ≤ J →
      ∃ C, gateResultAt p c E rho x i = some (some C) ∧ Block.Preceq A C ∧
        ∃ k', rho.events[k']? = some (.tick x (SA.gateTime p.toParams i)) ∧
          k' < (rho.events.filter
            (fun e => decide (e.time ≤ SA.gateTime p.toParams J))).length := by
    intro x hx i hi hiJ
    have hgi : SA.gateTime p.toParams i ≤ SA.gateTime p.toParams J := pcsa_gate_mono hiJ
    obtain ⟨k', hk'⟩ := pcsa_tick_exists E rho hs x hx _ (pcsa_gate_public E h.delta i)
      (pcsa_gate_nonneg i) (le_trans hgi (le_trans hdJ hC.cut.2))
    have hgr := pcsa_gate_tick_result E rho hs hfr hx hk'
    obtain ⟨C, hCe, hAC⟩ := pcsa_cut_res hK hu hA hx (i := i) hi
      (le_trans (pcsa_early_le_gate i) (le_trans hgi hdJ)) hgr
    exact ⟨C, by rw [hgr, hCe], hAC, k', hk',
      (V2.D.Engine.index_lt_read_length_iff hs _ hk').mpr hgi⟩
  refine ⟨by linarith, fun s hs' => ?_, by omega, fun x hx => (hst x hx).1, ?_,
    fun x hx => (hst x hx).2, ?_, ?_, ?_, ?_, ?_⟩
  · exact pcsa_gate_lt_slot hs'
  · intro x hx row hr
    exact Gen.Pure.block_compatible_of_common (hrows x hx row hr) (hst x hx).1
  · intro x hx j hj
    obtain ⟨C, hCe, hAC, k', hk', hk'K⟩ := hres x hx (J + 1 - (j + 1)) (by omega) (by omega)
    refine ⟨C, ?_, hAC⟩
    rw [pcsa_storeAt_index E rho hs x, pcsa_saved_of_gate E rho h hfr x hx hk' hk'K, hCe]
  · intro x hx r hr
    have heJ : SA.earlyTime p.toParams (J + 1) ≤ b₀ := by
      have := pcsa_gate_pred_early (p := p) (J + 1) (Nat.succ_pos J)
      rw [Nat.add_sub_cancel] at this
      rw [← this]
      exact hdJ
    obtain ⟨R, hRe, hAR⟩ := pcsa_cut_res hK hu hA hx (i := J + 1) (show j₁ < J + 1 by omega)
      heJ hr
    refine ⟨R, hRe, hAR, fun row hrow => ?_⟩
    subst hRe
    have hSR := pcsa_cut_record_below h hfr hK hx
      (K := (rho.events.filter (fun e => decide (e.time ≤ SA.gateTime p.toParams J))).length)
      (fun k hk e he _ => lt_of_le_of_lt (pcsa_read_events_le E rho hs _ k hk e he)
        (by linarith)) heJ hr
    have hrow := hrows x hx row hrow
    rw [pcsa_storeAt_index E rho hs x] at hrow
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_trans hrow hSR)
      (Gen.Pure.block_preceq_refl R)
  · exact fun y s X hX hv => pcsa_cut_ack hC hf hfr hK hu hA hd1 hX (le_trans hv hdJ)
  · intro y r H hH hq _ hv
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl H)
      (pcsa_cut_head hK hu hA (le_trans (pcsa_gate_mono (Nat.le_succ j₁)) hd1)
        (lt_trans hj1J (pcsa_release_gt_slot hq)) (le_trans hv hdJ) hH)
  · exact fun z r H hH h1 h2 _ => pcsa_cut_pendingHead hK hu hA (by omega) hdJ hH h1 h2

/-- [§5.5 steps 1–4] Under the lag `T + 4(k − 1)Δ ≤ b₀` of `Outage₂`, the
boundary facts at `b₀` hold for `A = S_u(T) ≠ genesis` from the Clean facts at
the cut. -/
theorem pcsa_cut_boundary (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {T b₀ b₁ ΔF : Time} (hO : Outage₂ p c E rho T b₀ b₁ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho) (hK : CutFacts p c E rho b₀) {u : V} (hu : u ∈ rho.honest)
    (hAg : (storeAt p c E rho u T).base.stableRecord ≠ .genesis) :
    ∃ ps, CleanSlowBoundary p c E rho (storeAt p c E rho u T).base.stableRecord b₀ ps := by
  have hC := hO.pre
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (1 : Int) ≤ p.Δ := p.deltaPos
  have hk2 := p.kLarge
  -- the origin label of `A`
  obtain ⟨K, hKs, hKT⟩ : ∃ K, storeAt p c E rho u T = (V2.D.Run.stateBefore E rho K u).st ∧
      ∀ k < K, ∀ e, rho.events[k]? = some e → e.time ≤ T :=
    ⟨_, pcsa_storeAt_index E rho hs u T, pcsa_read_events_le E rho hs T⟩
  rcases pcsa_record_origin E rho h hfr u hu K with hg | ⟨j', k₁, hk₁, hek₁, hA⟩
  · rw [hKs] at hAg
    exact absurd hg hAg
  rw [← hKs] at hA
  obtain ⟨j₁, rfl⟩ : ∃ j₁ : Nat, j₁ = j' := ⟨_, rfl⟩
  generalize (storeAt p c E rho u T).base.stableRecord = A at hA hAg ⊢
  have hdT : SA.gateTime p.toParams j₁ ≤ T := hKT k₁ hk₁ _ hek₁
  obtain ⟨k', hk'⟩ : ∃ k' : Nat, p.k = k' + 1 := ⟨p.k - 1, by omega⟩
  have hdk : SA.gateTime p.toParams (j₁ + k') ≤ b₀ := by
    have hlag := hO.lag
    rw [hk'] at hlag
    change 4 * p.Δ * ((j₁ + k' : Nat) : Int) + 6 * p.Δ ≤ b₀
    change 4 * p.Δ * (j₁ : Int) + 6 * p.Δ ≤ T at hdT
    push_cast at hlag ⊢
    linarith
  -- the pending label
  have hex : ∃ s : Nat, b₀ < SA.gateTime p.toParams s := by
    refine ⟨b₀.toNat, ?_⟩
    change b₀ < 4 * p.Δ * ((b₀.toNat : Nat) : Int) + 6 * p.Δ
    have h1 := Int.self_le_toNat b₀
    have h2 : (0 : Int) ≤ (b₀.toNat : Int) := Int.natCast_nonneg _
    nlinarith
  classical
  have hspec := Nat.find_spec hex
  have hps : j₁ + k' < Nat.find hex :=
    pcsa_gate_lt_slot (lt_of_le_of_lt hdk hspec)
  obtain ⟨J, hJ⟩ : ∃ J, Nat.find hex = J + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hjJ : j₁ + p.k ≤ J + 1 := by omega
  have hj1J : j₁ < J := by omega
  have hdJ : SA.gateTime p.toParams J ≤ b₀ :=
    not_lt.mp (Nat.find_min hex (show J < Nat.find hex by omega))
  have hbJ : b₀ < SA.gateTime p.toParams (J + 1) := hJ ▸ hspec
  have hd1 : SA.gateTime p.toParams (j₁ + 1) ≤ b₀ :=
    le_trans (pcsa_gate_mono (show j₁ + 1 ≤ j₁ + k' by omega)) hdk
  have hBJ := pcsa_cut_boundary_gate E rho hC hf hfr hK hu hA hd1 hAg hjJ hdJ
  -- the induction from `d_J` to `b₀`
  have hsucc := pcsa_gate_succ (p := p) J
  have hL := pcsa_lifetime_gt (p := p)
  have hd0 := pcsa_gate_nonneg (p := p) J
  have hsp : SlowSpan p (SA.gateTime p.toParams J) (b₀ + 1) := by
    refine ⟨hd0, ?_, (pcsa_lifetime_facts hO).1, ?_⟩
    · change 4 * p.Δ ≤ 4 * p.Δ * (J : Int) + 6 * p.Δ
      have : (0 : Int) ≤ (J : Int) := Int.natCast_nonneg _
      nlinarith
    · have := Int.add_one_le_of_lt hbJ
      linarith
  have hle := V2.D.Engine.read_length_mono (rho := rho) _ _ hdJ
  obtain ⟨hinv, -⟩ := pcsa_slow_induction E rho h hf hfr hsp hBJ hAg b₀ (lt_add_one b₀) _
    (by rw [Nat.add_sub_cancel' hle])
  rw [Nat.add_sub_cancel' hle, SlowInvAt_def] at hinv
  have hpre : ∀ x, ¬ ∃ k < (rho.events.filter (fun e => decide (e.time ≤ b₀))).length,
      rho.events[k]? = some (.tick x (SA.gateTime p.toParams (J + 1))) := by
    rintro x ⟨k, hk, hk'⟩
    exact absurd (pcsa_read_events_le E rho hs b₀ k hk _ hk') (not_le.mpr hbJ)
  refine ⟨J + 1, hbJ, fun s hs' => hJ ▸ Nat.find_min' hex hs', by omega, fun x hx => ?_,
    fun x hx => ?_, fun x hx => ?_, fun x hx j hj => ?_, fun x hx r hr => ?_,
    fun y s X hX hv => pcsa_cut_ack hC hf hfr hK hu hA hd1 hX hv, ?_,
    fun z r H hH h1 h2 _ => pcsa_cut_pendingHead hK hu hA (by omega) hdJ hH
      (lt_of_le_of_lt hdJ h1) h2⟩
  · rw [pcsa_storeAt_index E rho hs x b₀]
    exact (hinv x hx).stable
  · rw [pcsa_storeAt_index E rho hs x b₀]
    exact (hinv x hx).rows
  · rw [pcsa_storeAt_index E rho hs x b₀]
    exact (hinv x hx).tree
  · obtain ⟨C, hCe, hAC⟩ := hBJ.saved x hx j hj
    refine ⟨C, ?_, hAC⟩
    rw [pcsa_storeAt_index E rho hs x b₀]
    change ((V2.D.Run.stateBefore E rho _ x).st.base.genuine.find?
      (fun row => row.1 == J + 1 - (j + 1))).map Prod.snd = _
    rw [(hinv x hx).genuine (hpre x)]
    exact hCe
  · obtain ⟨R, hRe, hAR, hrows⟩ := hBJ.result x hx r hr
    refine ⟨R, hRe, hAR, fun row hrow => hrows row ?_⟩
    rw [pcsa_storeAt_index E rho hs x b₀] at hrow
    exact (hinv x hx).sub (hpre x) hrow
  · intro y r H hH hq _ hv
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl H)
      (pcsa_cut_head hK hu hA (le_trans (pcsa_gate_mono (Nat.le_succ j₁)) hd1) (lt_trans hj1J
        (pcsa_release_gt_slot (lt_of_le_of_lt hdJ hq))) hv hH)

/-! ### The boundary under the lag of `Outage₂` -/

/-- [pcsa34-r4.3 §5.5 steps 1–2] The boundary facts from the Clean facts at
the cut (OPEN: `hK`). -/
theorem pcsa_cleanSlowItems_of (p : Params) (hK : CleanCutItems p) : CleanSlowItems p := by
  rw [CleanSlowItems_def]
  rw [CleanCutItems_def] at hK
  intro V _ _ In c m E rho T b₀ b₁ ΔF hO hf hfr u hu hAg
  exact pcsa_cut_boundary E rho hO hf hfr (hK c m E rho b₀ ΔF hO.pre hf hfr) hu hAg

end AvailableChain.PCSA.Run
end
