module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationGate
public import AvailableChainPCSAProofs.Proofs.Clean.FormationEarlyHeads
public import AvailableChainPCSAProofs.Proofs.Clean.HonestBatch
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths

public section

/-! Formation step 5 counts at the gate input (pcsa34-r4.3 §5.3). The
batch is every honest HEAD seat awake at `v_s`; its size dominates `h_s`.
Exact honest HEADs and Formation receipt put each batch seat in the clean
support on `P`. All other late seats are faulty. -/

namespace AvailableChain.PCSA

private def gateCountData {n : Nat} (st : State n) :=
  (st.fg.F, st.base.blocks, st.base.votes, st.base.blockStamp,
    st.base.voteStamp, st.base.headDomain, st.base.now)

private theorem gateCountData_normalize {n : Nat} (st : State n) :
    gateCountData (normalizeS st) = gateCountData st := by
  delta normalizeS
  split <;> rfl

private theorem gateCountData_gate {n : Nat} (p : Params) (st : State n)
    (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    gateCountData (gateFrom p a cs rank st s) = gateCountData st := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => gateCountData acc = gateCountData st)
      · rfl
      · intro acc ha B _
        apply List.foldlRecOn (motive := fun acc : State n =>
          gateCountData acc = gateCountData st)
        · exact ha
        · intro acc' ha' g _
          exact ha'

private theorem gateCountData_clock (p : Params) (st : State p.n) (t : Time) :
    gateCountData (clock p st t) = gateCountData (clockPre p st t) := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def, gateCountData_normalize]
    split
    · rfl
    · exact gateCountData_gate p _ _ _ _ _
  · rfl

/-- Late votes and prefix support read only the count fields of a view. -/
private theorem grid_count_fields {n : Nat} (q : SA.Params)
    (v w : GridCO.State n .root) (s : Slot)
    (hb : v.blocks = w.blocks) (hv : v.votes = w.votes)
    (hbs : v.blockStamp = w.blockStamp) (hvs : v.voteStamp = w.voteStamp)
    (hd : v.headDomain = w.headDomain) (hn : v.now = w.now) :
    GridCO.lateVotes q.engine v s = GridCO.lateVotes q.engine w s ∧
      ∀ B, SA.Root.prefixSupport q v s B = SA.Root.prefixSupport q w s B := by
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
  have hearly : GridCO.earlyVotes q.engine v s = GridCO.earlyVotes q.engine w s := by
    delta GridCO.earlyVotes GridCO.votesAt
    rw [hv]
    apply List.filter_congr
    intro o _
    exact hbefore o _
  have hlate : GridCO.lateVotes q.engine v s = GridCO.lateVotes q.engine w s := by
    delta GridCO.lateVotes GridCO.votesAt
    rw [hv]
    apply List.filter_congr
    intro o _
    rw [hsv]
  have hclean : GridCO.cleanSupport q.engine v s = GridCO.cleanSupport q.engine w s := by
    delta GridCO.cleanSupport
    rw [hearly, hlate]
  refine ⟨hlate, fun B => ?_⟩
  delta SA.Root.prefixSupport GridCO.prefixSupport
  rw [hclean, htree, hb]

/-- The gate counts of the full clock hold at its pre-gate input. -/
private theorem gate_counts_clockPre (p : Params) (st : State p.n) (t : Time) (s : Slot)
    (P : Block) (h f : Nat) (hc : FormationGateCounts p (clock p st t) s P h f) :
    FormationGateCounts p (clockPre p st t) s P h f := by
  have hdata := gateCountData_clock p st t
  change (_, _, _, _, _, _, _) = (_, _, _, _, _, _, _) at hdata
  simp only [Prod.mk.injEq] at hdata
  obtain ⟨hF, hblocks, hvotes, hbstamps, hvstamps, hdomain, hnow⟩ := hdata
  have hb : (actView (clock p st t)).blocks = (actView (clockPre p st t)).blocks := by
    change (clock p st t).base.blocks.filter (activeCompatible (clock p st t)) =
      (clockPre p st t).base.blocks.filter (activeCompatible (clockPre p st t))
    delta activeCompatible
    rw [hblocks, hF]
  have hd : (actView (clock p st t)).headDomain = (actView (clockPre p st t)).headDomain := by
    change some ((clock p st t).base.headDomain.getD (clock p st t).base.blocks) =
      some ((clockPre p st t).base.headDomain.getD (clockPre p st t).base.blocks)
    rw [hdomain, hblocks]
  obtain ⟨hl, hs⟩ := grid_count_fields p.toParams _ _ s hb hvotes hbstamps hvstamps hd hnow
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hl]
    exact hc.hVoters
  · intro C h1 h2
    rw [← hb, ← hs]
    rw [← hF] at h1
    exact hc.hPath C h1 h2
  · intro C h1 h2 D hD
    rw [← hs]
    rw [← hF] at h1
    rw [← hb] at hD
    exact hc.hRivals C h1 h2 D hD
  · intro D hD hpar
    rw [← hs, ← hl]
    rw [← hb] at hD
    exact hc.hChildren D hD hpar

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
  {m : FGMode}

/-- The gate counts at the full clock of an indexed gate tick. -/
private theorem gate_counts_clock (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF)
    (hExact : ∀ x H, HonestHeadAt p c E rho x s H → H = N.erase)
    (y : V) (hy : y ∈ rho.honest) (k : Nat)
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (Hon : Finset (Fin p.n))
    (hHon : ∀ i, i ∈ Hon ↔ rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head s)) i) (SA.voteTime p.toParams s) = true)
    (hne : Hon.Nonempty) :
    FormationGateCounts p (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.gateTime p.toParams s)) s N.erase Hon.card (Gen.V2.Duty.faulty rho).card := by
  classical
  have hS := h.base.valid.toScheduleWellFormed
  have hpre := h.toPreFreeze p c E rho
  let S := (V2.D.Run.stateBefore E rho k y).st
  let X := clock p S (SA.gateTime p.toParams s)
  let v := actView X
  let L := GridCO.lateVotes p.toParams.engine v s
  let Q := GridCO.cleanSupport p.toParams.engine v s
  let SL := (GridCO.seats p.n L).toFinset
  have hp := p.deltaPos
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hS hk _).mp hlt
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    linarith
  have hvote : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ h.horizon
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hf : X.fg.F = .genesis := by
    change (clock p _ _).fg.F = _
    rw [pcsa_body_clock_fg]
    exact (h.frame y hy k).1
  have hd : X.base.headDomain = none := by
    change (clock p _ _).base.headDomain = none
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  have hdom : GridCO.resolutionTree v = X.base.blocks := by
    change X.base.headDomain.getD X.base.blocks = X.base.blocks
    rw [hd]
    rfl
  have hscore (B : Block) : SA.Root.prefixSupport p.toParams v s B =
      GridCO.goldfishScore X.base.blocks Q Q B :=
    pcsa_gate_score_of_genesis p X s B hf hd
  have hQL : Q ⊆ L := fun _ ho =>
    FGSA.fgsa_early_subset_late p v s (List.mem_filter.mp ho).1
  -- Each batch seat has one clean HEAD in `Q`, resolved to `N.erase`.
  have hseat : ∀ i ∈ Hon,
      (⟨.seat s i, .head N.erase.root⟩ : GridCO.Wire p.n .root) ∈ Q ∧
      Gen.AC.Root.resolvedTarget? X.base.blocks
        (⟨.seat s i, .head N.erase.root⟩ : GridCO.Wire p.n .root) = some N.erase ∧
      N.erase ∈ X.base.blocks ∧ N.erase.slot ≤ s ∧
      GridCO.equivocates Q i = false := by
    intro i hi
    obtain ⟨hih, hiw⟩ := (hHon i).mp hi
    obtain ⟨H, hH⟩ := pcsa_honest_head_exists E rho h.base _ hih s hiw hvote
    have hslot := pcsa_honest_head_slot_le E rho h.base h.frame _ s H hH
    have hHN := hExact _ H hH
    subst hHN
    obtain ⟨he, hr⟩ := pcsa_formation_head_early_resolved E rho s N ΔF hpre _ y hy i _ rfl
      hH k hidx (SA.gateTime p.toParams s)
    have hc := pcsa_honest_late_not_capped E rho h.base.valid k y
      (SA.gateTime p.toParams s) s i hih
    have hlook := FGSA.Run.resolvedHead_target _ _ hr
    rw [hdom] at hlook
    refine ⟨pcsa_early_uncapped_clean p v s i _ he hc, hlook,
      (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1, hslot, ?_⟩
    exact Gen.AC.Root.vote_pool_clean_subset Q L i hQL hc
  -- A batch seat supports exactly the prefixes of `N.erase`.
  have hsupp : ∀ i ∈ Hon, ∀ B,
      Gen.AC.Root.poolSupports X.base.blocks Q i B = true ↔ Block.Preceq B N.erase := by
    intro i hi B
    obtain ⟨hm, hlook, hmem, hslot, hclean⟩ := hseat i hi
    constructor
    · intro hb
      obtain ⟨o, ho, hos, hov⟩ :=
        (Gen.AC.Root.vote_pool_support_witness X.base.blocks Q i B).mp hb
      have hoi := Gen.AC.Root.vote_pool_clean_unique Q i hclean o _ ho hm hos rfl
      subst hoi
      obtain ⟨H', hH', _, _, hBH⟩ :=
        (Gen.AC.Root.vote_support_body X.base.blocks B _).mp hov
      rw [hlook] at hH'
      cases hH'
      exact hBH
    · intro hB
      apply (Gen.AC.Root.vote_pool_support_witness X.base.blocks Q i B).mpr
      refine ⟨_, hm, rfl, ?_⟩
      exact (Gen.AC.Root.vote_support_body X.base.blocks B _).mpr
        ⟨N.erase, hlook, hmem, hslot, hB⟩
  -- Count split: the batch is in the late seats, and the rest are faulty.
  have hHonSL : Hon ⊆ SL := by
    intro i hi
    exact (Gen.AC.Root.vote_pool_mem_seats L i).mpr ⟨_, hQL (hseat i hi).1, rfl⟩
  have hbound := pcsa_late_participant_bound E rho h.base k y (SA.gateTime p.toParams s) s
    Hon hHon
  have hcardL : GridCO.voterCount L = SL.card := Gen.AC.Root.vote_pool_voterCount_card L
  have hsplit : (SL \ Hon).card + Hon.card = SL.card :=
    Finset.card_sdiff_add_card_eq_card hHonSL
  change GridCO.voterCount L ≤ Hon.card + (Gen.V2.Duty.faulty rho).card at hbound
  have hrest : (SL \ Hon).card ≤ (Gen.V2.Duty.faulty rho).card := by omega
  have hscoreRest (B : Block) (hB : ¬ Block.Preceq B N.erase) :
      GridCO.goldfishScore X.base.blocks Q Q B ≤ (SL \ Hon).card := by
    rw [Gen.AC.Root.vote_pool_score_card]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hm, hv⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_sdiff.mpr ⟨Gen.AC.Root.vote_pool_seats_subset Q L hQL hm, ?_⟩
    intro hiH
    have hs : Gen.AC.Root.poolSupports X.base.blocks Q i B = false := by
      cases hb : Gen.AC.Root.poolSupports X.base.blocks Q i B with
      | false => rfl
      | true => exact absurd ((hsupp i hiH B).mp hb) hB
    simp [(hseat i hiH).2.2.2.2, hs] at hv
  obtain ⟨i₀, hi₀⟩ := hne
  have hNS : N.erase ∈ S.base.blocks := by
    have hm := (hseat i₀ hi₀).2.2.1
    change N.erase ∈ (clock p S _).base.blocks at hm
    rwa [pcsa_clock_blocks] at hm
  refine ⟨hbound, ?_, ?_, ?_⟩
  · intro C _ hC
    refine ⟨?_, ?_⟩
    · change C ∈ (actView X).blocks
      rw [pcsa_actView_blocks_of_genesis X hf]
      change C ∈ (clock p S _).base.blocks
      rw [pcsa_clock_blocks]
      exact pcsa_body_prefix_mem p S (pcsa_reachable_stateBefore E rho k y) N.erase hNS C hC
    · rw [hscore, Gen.AC.Root.vote_pool_score_card]
      apply Finset.card_le_card
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨(Gen.AC.Root.vote_pool_mem_seats Q i).mpr ⟨_, (hseat i hi).1, rfl⟩, ?_⟩
      exact Bool.or_eq_true_iff.mpr (Or.inr ((hsupp i hi C).mpr hC))
  · intro C _ hC D _ hpar hneq
    rw [hscore]
    refine (hscoreRest D ?_).trans hrest
    intro hDN
    have hdepth : D.depth = C.depth := by
      cases D with
      | genesis =>
        cases C with
        | genesis => rfl
        | node P₂ s₂ r₂ b₂ =>
          change (none : Option Block) = some P₂ at hpar
          cases hpar
      | node P₁ s₁ r₁ b₁ =>
        cases C with
        | genesis =>
          change some P₁ = (none : Option Block) at hpar
          cases hpar
        | node P₂ s₂ r₂ b₂ =>
          change some P₁ = some P₂ at hpar
          change P₁.depth + 1 = P₂.depth + 1
          rw [Option.some.inj hpar]
    rcases Gen.Pure.block_preceq_total_of_common hDN hC with hDC | hCD
    · exact hneq (Gen.Pure.prefix_eq_of_depth D C hDC (le_of_eq hdepth.symm))
    · exact hneq (Gen.Pure.prefix_eq_of_depth C D hCD (le_of_eq hdepth)).symm
  · intro D _ hpar
    have hDN : ¬ Block.Preceq D N.erase := by
      intro hDN
      have hdep := Gen.Pure.prefix_depth D N.erase hDN
      cases D with
      | genesis => cases hpar
      | node P' s' r' b' =>
        have hP : P' = N.erase := Option.some.inj hpar
        have hd' : (Block.node P' s' r' b').depth = P'.depth + 1 := rfl
        rw [hd', hP] at hdep
        omega
    have hle := hscoreRest D hDN
    rw [hscore]
    refine ⟨hle.trans hrest, ?_⟩
    change Hon.card + GridCO.goldfishScore X.base.blocks Q Q D ≤ GridCO.voterCount L
    omega

/-- [pcsa34-r4.3 §5.3, step 5] The Formation counts at each honest gate
input. `H` is the number of honest HEAD seats awake at `v_s`; it dominates
`h_s`. Each such seat has its exact HEAD on `P` in the clean support, and
every other late seat is faulty. -/
theorem pcsa_formation_gate_counts (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF)
    (hExact : ∀ x H, HonestHeadAt p c E rho x s H → H = N.erase) :
    ∀ y ∈ rho.honest, ∀ st, gateInAt p c E rho y s = some st →
      ∃ H, (awakeHonestLabel p c E rho s).card ≤ H ∧
        FormationGateCounts p st s N.erase H (Gen.V2.Duty.faulty rho).card := by
  classical
  intro y hy st hr
  rw [pcsa_gateInAt_def] at hr
  obtain ⟨nd, hpt, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hpt
  obtain ⟨k, hk, he⟩ := Option.map_eq_some_iff.mp hpt
  subst nd
  subst st
  let Hon := Finset.univ.filter (fun i : Fin p.n =>
    rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head s)) i) (SA.voteTime p.toParams s) = true)
  have hHon : ∀ i, i ∈ Hon ↔ rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head s)) i) (SA.voteTime p.toParams s) = true := by
    intro i
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbatch : (awakeHonestLabel p c E rho s).card ≤ Hon.card := by
    have hsub : awakeHonestLabel p c E rho s ⊆ Hon.image (rho.seatOf (.base (.head s))) := by
      intro x hx
      rw [pcsa_awakeHonestLabel_def] at hx
      have hm := (Finset.mem_inter.mp hx).1
      rw [Gen.V2.Duty.awakeHonest_def] at hm
      obtain ⟨hxh, hxw⟩ := Finset.mem_filter.mp hm
      obtain ⟨i, hi⟩ := (h.base.cstar (.base (.head s)) trivial).2 x
      refine Finset.mem_image.mpr ⟨i, (hHon i).mpr ⟨?_, ?_⟩, hi⟩
      · rw [hi]
        exact hxh
      · rw [hi]
        exact hxw
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hne : Hon.Nonempty := by
    apply Finset.card_pos.mp
    have hq : 0 < nQuorum p.n := by
      have hn := p.nPos
      delta nQuorum
      omega
    exact lt_of_lt_of_le hq (h.participation.trans hbatch)
  exact ⟨Hon.card, hbatch, gate_counts_clockPre p _ _ s N.erase _ _
    (gate_counts_clock E rho s N ΔF h hExact y hy k (V2.D.Run.tickIdx?_spec hk) Hon hHon hne)⟩

end AvailableChain.PCSA.Run

end
