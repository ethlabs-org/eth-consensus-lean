module
public import AvailableChainPCSAProofs.Proofs.Outage.SlowP1
public import AvailableChainPCSAProofs.Proofs.Outage.SlowStep
public import AvailableChainPCSAProofs.Proofs.Outage.SlowRoot

public section

/-! The S case of slow P1 in the run (pcsa34-r4.3 §5.5 steps 1–4). From the
Clean-lane boundary facts at `b₀` (`CleanSlowBoundary`), an induction over the
events after `b₀` keeps, at every honest node, `S ⪰ A`, every lock compatible
with `A`, and, from the pending gate `d_{p*}`, a live lock on `A`, and
makes every honest HEAD after `b₀` extend `A`. Every PC then has an honest ack
compatible with `A` (5.1), and no release count reaches the threshold. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-! ### Slot times -/

omit [DecidableEq V] [Fintype V] in
/-- A gate time is public. -/
theorem pcsa_gate_public (E : Generic.Env V) (hΔ : E.Δ = p.Δ) (s : Slot) :
    V2.PublicTime E (SA.gateTime p.toParams s) := by
  refine ⟨4 * s + 6, ?_⟩
  rw [hΔ]
  change 4 * p.Δ * (s : Int) + 6 * p.Δ = ((4 * s + 6 : Nat) : Int) * p.Δ
  push_cast
  ring

omit [DecidableEq V] [Fintype V] in
/-- Gate times increase with the slot. -/
theorem pcsa_gate_mono {a b : Slot} (h : a ≤ b) :
    SA.gateTime p.toParams a ≤ SA.gateTime p.toParams b := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (a : Int) + 6 * p.Δ ≤ 4 * p.Δ * (b : Int) + 6 * p.Δ
  have : (a : Int) ≤ b := by exact_mod_cast h
  nlinarith

omit [DecidableEq V] [Fintype V] in
/-- The clock reads the gate label of a gate time back. -/
theorem pcsa_gate_slot (s : Slot) :
    ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change ((4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ) / (4 * p.Δ)).toNat = s
  rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ (by positivity)]
  exact Int.toNat_natCast s

omit [DecidableEq V] [Fintype V] in
/-- The vote time is before the release time of a slot. -/
theorem pcsa_vote_lt_release (s : Slot) :
    SA.voteTime p.toParams s < SA.releaseTime p.toParams s := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 5 * p.Δ
  linarith

omit [DecidableEq V] [Fintype V] in
/-- A release time after a gate time is of a later label. -/
theorem pcsa_release_gt_slot {r J : Slot}
    (h : SA.gateTime p.toParams J < SA.releaseTime p.toParams r) : J < r := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (J : Int) + 6 * p.Δ < 4 * p.Δ * (r : Int) + 5 * p.Δ at h
  by_contra hn
  have : (r : Int) ≤ J := by exact_mod_cast Nat.le_of_not_lt hn
  nlinarith

omit [DecidableEq V] [Fintype V] in
/-- The early time of a label is before its release time. -/
theorem pcsa_early_lt_release (r : Slot) :
    SA.earlyTime p.toParams r < SA.releaseTime p.toParams r := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (r : Int) + 2 * p.Δ < 4 * p.Δ * (r : Int) + 5 * p.Δ
  linarith

omit [DecidableEq V] [Fintype V] in
/-- The next gate is `4Δ` later. -/
theorem pcsa_gate_succ (J : Slot) :
    SA.gateTime p.toParams (J + 1) = SA.gateTime p.toParams J + 4 * p.Δ := by
  change 4 * p.Δ * ((J + 1 : Nat) : Int) + 6 * p.Δ = 4 * p.Δ * (J : Int) + 6 * p.Δ + 4 * p.Δ
  push_cast
  ring

/-! ### HEADs and PCs -/

variable (p c) in
omit [Fintype V] in
/-- [pcsa34-r4.3 §5.5 step 3] Every honest HEAD sent at a tick before index
`K` with `v_j > b₀` and `e_j` in the run is `⪰ A`. -/
def SlowHeads (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (A : Block)
    (b₀ : Time) (K : Nat) : Prop :=
  ∀ z ∈ rho.honest, ∀ (j : Slot) (k : Nat), k < K →
    rho.events[k]? = some (.tick z (SA.voteTime p.toParams j)) →
    b₀ < SA.voteTime p.toParams j → E.awake z (SA.voteTime p.toParams j) = true →
    SA.earlyTime p.toParams j ≤ rho.horizon →
    Block.Preceq A (headVote p (clock p (V2.D.Run.stateBefore E rho k z).st
      (SA.voteTime p.toParams j)) j)

variable (p c) in
omit [Fintype V] in
theorem SlowHeads_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (A : Block)
    (b₀ : Time) (K : Nat) : SlowHeads p c E rho A b₀ K =
      (∀ z ∈ rho.honest, ∀ (j : Slot) (k : Nat), k < K →
        rho.events[k]? = some (.tick z (SA.voteTime p.toParams j)) →
        b₀ < SA.voteTime p.toParams j → E.awake z (SA.voteTime p.toParams j) = true →
        SA.earlyTime p.toParams j ≤ rho.horizon →
        Block.Preceq A (headVote p (clock p (V2.D.Run.stateBefore E rho k z).st
          (SA.voteTime p.toParams j)) j)) := by
  delta SlowHeads
  rfl

omit [Fintype V] in
/-- An honest HEAD whose tick is before index `K` is `⪰ A`. -/
theorem pcsa_slowHeads_read (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {A : Block} {b₀ : Time} {K : Nat} (hH : SlowHeads p c E rho A b₀ K) (tb : Time)
    (hidx : ∀ k z t, rho.events[k]? = some (.tick z t) → t < tb → k < K)
    (z : V) (j : Slot) (H : Block) (hzH : HonestHeadAt p c E rho z j H)
    (hb : b₀ < SA.voteTime p.toParams j) (ht : SA.voteTime p.toParams j < tb)
    (he : SA.earlyTime p.toParams j ≤ rho.horizon) :
    Block.Preceq A H := by
  rw [SlowHeads_def] at hH
  obtain ⟨hz, haw, hr⟩ := hzH
  rw [pcsa_voteHeadAt_def] at hr
  obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨k, hk, hst⟩ := pcsa_postClock_some E rho hnd
  rw [hst]
  exact hH z hz j k (hidx k z _ hk ht) hk hb haw he

omit [Fintype V] in
/-- An honest ack is sent in the run: its early time is at most the horizon. -/
theorem pcsa_ack_early_horizon (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {y : V} {s : Slot} {X : Block}
    (hX : HonestAckAt p c E rho y s X) : SA.earlyTime p.toParams s ≤ rho.horizon := by
  obtain ⟨-, -, hread⟩ := hX
  rw [pcsa_ackAt_def] at hread
  obtain ⟨nd, hnd, -⟩ := Option.map_eq_some_iff.mp hread
  obtain ⟨k, hk, -⟩ := pcsa_postClock_some E rho hnd
  exact pcsa_tick_le_horizon E rho hs hk

/-- [pcsa34-r4.3 §5.5 step 3, 5.1] A PC held, frozen or carried at an honest
node is compatible with `A`: it has an honest ack on its target; an ack of a
label with `v_s ≤ b₀` is compatible with `A` (boundary), and a later one names
an honest HEAD `⪰ A`. -/
theorem pcsa_slow_pc_compat (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {A : Block} {b₀ : Time}
    (hacks : ∀ y s X, HonestAckAt p c E rho y s X → SA.voteTime p.toParams s ≤ b₀ →
      Block.Compatible X A)
    (x : V) (hx : x ∈ rho.honest) (K : Nat) (T : Time)
    (hT : ∀ k < K, ∀ e, rho.events[k]? = some e → e.time ≤ T)
    (hH : ∀ z j H, HonestHeadAt p c E rho z j H → b₀ < SA.voteTime p.toParams j →
      SA.voteTime p.toParams j < T → SA.earlyTime p.toParams j ≤ rho.horizon →
      Block.Preceq A H)
    (k s : Slot) (d : PC p.n)
    (hd : d ∈ (V2.D.Run.stateBefore E rho K x).st.pcs ∨
      d ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho K x).st k ∨
      d ∈ carriedPCs (V2.D.Run.stateBefore E rho K x).st s) :
    Block.Compatible d.target A := by
  have hO := pcsa_outageStore_stateBefore E rho K x hx
  obtain ⟨hw, ho, hb⟩ := pcsa_source_facts _ rho T _ hO (pcsa_certSafe_by E rho K x T hT) k s
    d hd
  obtain ⟨hT', y, X, hX, hroot⟩ := pcsa_pc_honest_ack_by E rho h hf T d hw ho
  have he := pcsa_outage_rootBlock_eq E rho h (pcsa_honest_ack_support E rho h y _ X hX).1
    (pcsa_outage_block_prop hO _ hb) hroot
  subst he
  by_cases hv : SA.voteTime p.toParams d.slot ≤ b₀
  · exact hacks y _ _ hX hv
  · obtain ⟨z, hz⟩ := pcsa_honest_ack_head E rho h hf hfr y _ _ hX
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
      (hH z _ _ hz (lt_of_not_ge hv) (lt_of_lt_of_le (pcsa_vote_lt_early _) hT')
        (pcsa_ack_early_horizon E rho h.valid.toScheduleWellFormed hX))

/-! ### The release count -/

omit [Fintype V] in
/-- A HEAD wire with a seat and a label is a seat HEAD of that label. -/
theorem pcsa_head_wire_shape (o : GridCO.Wire p.n .root) (r : Slot) (i : Fin p.n)
    (hl : GridCO.headLabel? o = some r) (hs : GridCO.headSeat? o = some i) :
    ∃ root, o = ⟨.seat r i, .head root⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | seat r' i' =>
    cases payload with
    | head root =>
      have h1 : r' = r := Option.some.inj hl
      have h2 : i' = i := Option.some.inj hs
      subst h1
      subst h2
      exact ⟨root, rfl⟩
    | proposal _ _ _ => cases hl
  | proposer _ => cases payload <;> cases hl
  | none => cases payload <;> cases hl

/-- A resolved root HEAD has the voted root. -/
theorem pcsa_resolvedHead_root (v : GridCO.State p.n .root) (r : Slot) (i : Fin p.n)
    (root : BlockId) (B : Block)
    (h : GridCO.resolvedHead? v ⟨.seat r i, .head root⟩ = some B) : B.root = root := by
  delta GridCO.resolvedHead? at h
  obtain ⟨tg, htg, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨B', hB', h3⟩ := Option.bind_eq_some_iff.mp h2
  have htg' : tg = root := (Option.some.inj htg).symm
  split at h3
  · cases Option.some.inj h3
    exact (Block.findByRoot?_root hB').trans htg'
  · contradiction

/-- [pcsa34-r4.3 §5.5 step 2, 5.1] At a release tick `t = q_r > b₀` of an
honest node, fewer than `⌈n/2⌉` seats count against `A`: a counted seat has a
resolved label-`r` HEAD conflicting with `A`; an honest seat's HEAD is its
exact honest HEAD of label `r`, which is compatible with `A` (boundary for
`v_r ≤ b₀`, `hH` after). So only faulty seats count. -/
theorem pcsa_slow_release (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {A : Block} {b₀ : Time} {ps : Slot} (hB : CleanSlowBoundary p c E rho A b₀ ps)
    (x : V) (hx : x ∈ rho.honest) (K : Nat) (r : Slot)
    (hbt : b₀ < SA.releaseTime p.toParams r) (hq : SA.releaseTime p.toParams r ≤ rho.horizon)
    (hH : ∀ z j H, HonestHeadAt p c E rho z j H → b₀ < SA.voteTime p.toParams j →
      SA.voteTime p.toParams j < SA.releaseTime p.toParams r →
      SA.earlyTime p.toParams j ≤ rho.horizon → Block.Preceq A H)
    (X : State p.n) (hv : X.base.votes = (V2.D.Run.stateBefore E rho K x).st.base.votes)
    (hbl : X.base.blocks = (V2.D.Run.stateBefore E rho K x).st.base.blocks) :
    GridCO.releaseCount p.toParams.engine (actView X) r A < SA.releaseThreshold p.toParams := by
  have hO := pcsa_outageStore_stateBefore E rho K x hx
  have hev := evidence_stateBefore E rho h.valid.toUnforgeableSignatures K x hx
  rw [StoreEvidence_def] at hev
  delta GridCO.releaseCount
  dsimp only
  generalize hraw : GridCO.votesAt (actView X) r = raw
  generalize hres : raw.filter (fun o => GridCO.resolvedBefore (actView X) o
    (GridCO.releaseTime p.toParams.engine r)) = resolved
  have hcount : ∀ L : List (Fin ((pcsaWith m p c).seats (.base (.head r)))), L.Nodup →
      (∀ i ∈ L, rho.seatOf (.base (.head r)) i ∉ rho.honest) →
      L.length < SA.releaseThreshold p.toParams := by
    intro L hnd hL
    rw [← List.toFinset_card_of_nodup hnd]
    have hsub := Finset.card_le_card (s := L.toFinset)
      (t := Finset.univ.filter (fun i => rho.seatOf (.base (.head r)) i ∉ rho.honest))
      (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL i (List.mem_toFinset.mp hi)⟩)
    have hcard := pcsa_faulty_seats_card rho (.base (.head r))
      (h.cstar (.base (.head r)) trivial).injective
    rw [FaultsBelowQA_def] at hf
    exact lt_of_le_of_lt hsub (lt_of_le_of_lt hcard hf)
  refine hcount _ (List.Nodup.filter _ (List.nodup_dedup _)) ?_
  intro i hi hhon
  have hP := (List.mem_filter.mp hi).2
  rw [Bool.and_eq_true] at hP
  obtain ⟨o, ho, hm⟩ := List.any_eq_true.mp hP.2
  have ho' := List.mem_filter.mp ho
  have hor : o ∈ raw := by
    rw [← hres] at ho'
    exact (List.mem_filter.mp ho'.1).1
  rw [← hraw] at hor
  have hor' := List.mem_filter.mp hor
  have hlab : GridCO.headLabel? o = some r := beq_iff_eq.mp hor'.2
  have hseat : GridCO.headSeat? o = some i := beq_iff_eq.mp ho'.2
  have hvo : o ∈ (V2.D.Run.stateBefore E rho K x).st.base.votes := by
    rw [← hv]
    exact hor'.1
  cases hrh : GridCO.resolvedHead? (actView X) o with
  | none =>
    rw [hrh] at hm
    cases hm
  | some B =>
    rw [hrh] at hm
    change (!Block.compatible B A) = true at hm
    obtain ⟨root, rfl⟩ := pcsa_head_wire_shape _ r i hlab hseat
    have ha := hev.2.2 _ hvo
    rw [HeadAuthentic_def] at ha
    obtain ⟨a, kz, hkz, hoz⟩ := ha r i root rfl hhon
    obtain ⟨hat, haw, hroot, hread⟩ := pcsa_head_emission_read E rho
      h.valid.toScheduleWellFormed _ r i root a kz hkz hoz
    have hHH : HonestHeadAt p c E rho (rho.seatOf (.base (.head r)) i) r
        (headVote p (clock p (V2.D.Run.stateBefore E rho kz
          (rho.seatOf (.base (.head r)) i)).st a) r) :=
      ⟨hhon, hat ▸ haw, hread⟩
    have hBm : B ∈ X.base.blocks :=
      (List.mem_filter.mp (pcsa_resolvedHead_mem _ _ B hrh)).1
    have hBroot : B.root = root := by
      exact pcsa_resolvedHead_root _ _ _ _ _ hrh
    have hBH : B = headVote p (clock p (V2.D.Run.stateBefore E rho kz
        (rho.seatOf (.base (.head r)) i)).st a) r :=
      pcsa_outage_rootBlock_eq E rho h (pcsa_outage_block_prop hO B (hbl ▸ hBm))
        (pcsa_clocked_head_rootBlock E rho hfr _ hhon kz a r) (hBroot.trans hroot.symm)
    have hc : Block.Compatible B A := by
      rw [hBH]
      by_cases hvr : SA.voteTime p.toParams r ≤ b₀
      · exact hB.heads _ r _ hHH hbt hq hvr
      · exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
          (hH _ r _ hHH (lt_of_not_ge hvr) (pcsa_vote_lt_release r)
            (le_trans (pcsa_early_lt_release r).le hq))
    rw [Block.Compatible] at hc
    rw [hc] at hm
    cases hm

/-! ### Events -/

omit [DecidableEq V] [Fintype V] in
/-- Event times grow with the index. -/
theorem pcsa_event_time_mono (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k K : Nat} {e e' : V2.Event V (Obj p)}
    (hk : rho.events[k]? = some e) (hK : rho.events[K]? = some e') (h : k ≤ K) :
    e.time ≤ e'.time := by
  rcases Nat.lt_or_eq_of_le h with hlt | rfl
  · obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hKl, hKe⟩ := List.getElem?_eq_some_iff.mp hK
    have hkey := (List.pairwise_iff_getElem.mp hs.sorted) k K hkl hKl hlt
    rw [hke, hKe] at hkey
    exact V2.D.Engine.time_le_of_key_le _ _ hkey
  · rw [hk] at hK
    cases Option.some.inj hK
    exact le_rfl

omit [DecidableEq V] [Fintype V] in
/-- An event other than the tick `(x, d)` keeps the phase "no tick `(x, d)` yet". -/
theorem pcsa_phase_succ (rho : V2.D.Run V (pcsaWith m p c)) {K : Nat} {x : V} {d : Time}
    {e : V2.Event V (Obj p)} (he : rho.events[K]? = some e) (hne : e ≠ .tick x d) :
    (¬ ∃ k < K + 1, rho.events[k]? = some (.tick x d)) ↔
      (¬ ∃ k < K, rho.events[k]? = some (.tick x d)) := by
  constructor
  · rintro hn ⟨k, hk, hk'⟩
    exact hn ⟨k, Nat.lt_succ_of_lt hk, hk'⟩
  · rintro hn ⟨k, hk, hk'⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · exact hn ⟨k, hlt, hk'⟩
    · rw [he] at hk'
      exact hne (Option.some.inj hk')

/-- The invariant reads its phase only through its truth. -/
theorem pcsa_slowInv_congr {A : Block} {g : Nat} {D₂ : Time} {bound st : State p.n}
    {pre pre' : Prop} (h : SlowInv A g D₂ bound pre st) (hp : pre ↔ pre') :
    SlowInv A g D₂ bound pre' st :=
  ⟨h.stable, h.rows, h.tree, fun hn => h.renewed (fun hp' => hn (hp.mp hp')),
    fun hp' => h.sub (hp.mpr hp'), fun hp' => h.genuine (hp.mpr hp')⟩

omit [Fintype V] in
/-- [stage 1] A label whose gate is after every earlier event of the node is
not saved. -/
theorem pcsa_unsaved_before (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hnr : V2.D.NoRestart rho) (hfr : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (K : Nat)
    (hK : ∀ k < K, ∀ e, rho.events[k]? = some e → e.node = x →
      e.time < SA.gateTime p.toParams s) :
    GridCO.savedGenuine (V2.D.Run.stateBefore E rho K x).st.base s = none := by
  have hz : GridCO.savedGenuine (initial p.n).base s = none := rfl
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => GridCO.savedGenuine nd.st.base s = none) (Nat.zero_le K) x ?_ hz
  intro k e _ hkK he hn hnone
  cases e with
  | restart u t => exact absurd he (hnr k u t)
  | tick u t =>
    change u = x at hn
    subst u
    change GridCO.savedGenuine
      (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base s = none
    rw [Function.update_self]
    have H : GridCO.savedGenuine (clock p (V2.D.Run.stateBefore E rho k x).st t).base s =
        none := by
      cases hc : GridCO.savedGenuine (clock p (V2.D.Run.stateBefore E rho k x).st t).base s with
      | none => rfl
      | some y =>
        exfalso
        have hF := ((FrameVacuous_def p _).mp (hfr x hx k)).1
        rcases pcsa_clock_genuine p _ t s hF (by rw [hc]; rfl) with h1 | h1
        · change (GridCO.savedGenuine (V2.D.Run.stateBefore E rho k x).st.base s).isSome =
            true at h1
          rw [hnone] at h1
          cases h1
        · have := hK k hkK _ he rfl
          change t < _ at this
          rw [h1] at this
          exact lt_irrefl _ this
    rw [pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t]
    exact H
  | deliver u o t =>
    change u = x at hn
    subst u
    have hF0 := ((FrameVacuous_def p _).mp (hfr x hx k)).1
    have hF : (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).fg.F = .genesis := by
      have hv := hfr x hx (k + 1)
      rw [V2.D.Run.stateBefore_succ E rho he] at hv
      change FrameVacuous p (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st at hv
      rw [Function.update_self] at hv
      exact ((FrameVacuous_def p _).mp hv).1
    change GridCO.savedGenuine
      (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base s = none
    rw [Function.update_self]
    have hg := (pcsa_process_slow p _ (toWire p o) hF0 hF).1.genuine
    change ((process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).base.genuine.find?
      (fun row => row.1 == s)).map Prod.snd = none
    rw [hg]
    exact hnone

/-! ### The induction -/

variable (p c) in
omit [Fintype V] in
/-- [pcsa34-r4.3 §5.5 steps 2–4] The S-case invariant at every honest node at
index `K`: the bound is the store at `b₀`, the deadline is `d_{p*} + L`, and
the phase is "no tick at `d_{p*}` before `K`". -/
def SlowInvAt (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (A : Block) (b₀ : Time)
    (ps : Slot) (K : Nat) : Prop :=
  ∀ x ∈ rho.honest, SlowInv A (SA.releaseThreshold p.toParams)
    (SA.gateTime p.toParams ps + SA.lifetime p.toParams) (storeAt p c E rho x b₀)
    (¬ ∃ k < K, rho.events[k]? = some (.tick x (SA.gateTime p.toParams ps)))
    (V2.D.Run.stateBefore E rho K x).st

variable (p c) in
omit [Fintype V] in
theorem SlowInvAt_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (A : Block)
    (b₀ : Time) (ps : Slot) (K : Nat) : SlowInvAt p c E rho A b₀ ps K =
      (∀ x ∈ rho.honest, SlowInv A (SA.releaseThreshold p.toParams)
        (SA.gateTime p.toParams ps + SA.lifetime p.toParams)
        (storeAt p c E rho x b₀)
        (¬ ∃ k < K, rho.events[k]? = some (.tick x (SA.gateTime p.toParams ps)))
        (V2.D.Run.stateBefore E rho K x).st) := by
  delta SlowInvAt
  rfl

omit [Fintype V] in
/-- [pcsa34-r4.3 §5.5 steps 1–2] The invariant at the read index of `b₀`. -/
theorem pcsa_slowInvAt_base (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) {A : Block} {b₀ : Time} {ps : Slot}
    (hB : CleanSlowBoundary p c E rho A b₀ ps) :
    SlowInvAt p c E rho A b₀ ps (rho.events.filter (fun e => decide (e.time ≤ b₀))).length := by
  have hs := h.valid.toScheduleWellFormed
  rw [SlowInvAt_def]
  intro x hx
  rw [← pcsa_storeAt_index E rho hs x b₀]
  have hpre : ¬ ∃ k < (rho.events.filter (fun e => decide (e.time ≤ b₀))).length,
      rho.events[k]? = some (.tick x (SA.gateTime p.toParams ps)) := by
    rintro ⟨k, hk, hk'⟩
    have := pcsa_read_events_le E rho hs b₀ k hk _ hk'
    exact absurd this (not_le.mpr hB.pending)
  exact ⟨hB.stable x hx, hB.locks x hx, hB.tree x hx,
    fun hn => absurd hpre hn, fun _ => List.Subset.refl _, fun _ => rfl⟩

omit [Fintype V] in
/-- No HEAD tick before the read index of `b₀` is after `b₀`. -/
theorem pcsa_slowHeads_base (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (A : Block) (b₀ : Time) :
    SlowHeads p c E rho A b₀ (rho.events.filter (fun e => decide (e.time ≤ b₀))).length := by
  rw [SlowHeads_def]
  intro z _ j k hk hev hb _ _
  exact absurd (pcsa_read_events_le E rho h.valid.toScheduleWellFormed b₀ k hk _ hev)
    (not_le.mpr hb)

variable (p) in
/-- The timing facts of the S-case induction from `b₀` to `b₁`: `b₀ ≥ 4Δ`,
the lock lifetime is at least `1`, and `b₁ ≤ b₀ + L`. -/
structure SlowSpan (b₀ b₁ : Time) : Prop where
  start : 0 ≤ b₀
  four : 4 * p.Δ ≤ b₀
  life : (1 : Time) ≤ SA.lifetime p.toParams
  budget : b₁ ≤ b₀ + SA.lifetime p.toParams

/-- The lock lifetime is at least `1`, and the budget ends before `b₀ + L`. -/
theorem pcsa_lifetime_facts {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)}
    {T b₀ b₁ ΔF : Time} (hO : Outage₂ p c E rho T b₀ b₁ ΔF) :
    (1 : Time) ≤ SA.lifetime p.toParams ∧ b₁ ≤ b₀ + SA.lifetime p.toParams ∧
      4 * p.Δ ≤ b₀ := by
  have hΔ : (1 : Int) ≤ p.Δ := p.deltaPos
  have hk : (2 : Int) ≤ (p.k : Int) := by exact_mod_cast p.kLarge
  have hL : SA.lifetime p.toParams = pcsaL p := rfl
  rw [hL, pcsaL_def]
  have hb := hO.budget
  have hlag := hO.lag
  have hT := hO.order.1
  rw [pcsaL_def] at hb
  refine ⟨by nlinarith, by linarith [min_le_right p.η ((4 * (p.k : Time) - 1) * p.Δ)], ?_⟩
  nlinarith

/-- An outage gives the timing facts of the S-case induction. -/
theorem pcsa_slowSpan_of_outage {E : Generic.Env V} {rho : V2.D.Run V (pcsaWith m p c)}
    {T b₀ b₁ ΔF : Time} (hO : Outage₂ p c E rho T b₀ b₁ ΔF) : SlowSpan p b₀ b₁ :=
  have hl := pcsa_lifetime_facts hO
  ⟨hO.pre.cut.1, hl.2.2, hl.1, hl.2.1⟩

/-- [pcsa34-r4.3 §5.5 steps 2–4] One event after `b₀` and before `b₁` keeps the
invariant at every honest node. -/
theorem pcsa_slowInvAt_step (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {b₀ b₁ : Time} (hO : SlowSpan p b₀ b₁) {A : Block} {ps : Slot}
    (hB : CleanSlowBoundary p c E rho A b₀ ps) (hAg : A ≠ .genesis) (K : Nat)
    (hK : (rho.events.filter (fun e => decide (e.time ≤ b₀))).length ≤ K)
    (e : V2.Event V (Obj p)) (he : rho.events[K]? = some e) (heb : e.time < b₁)
    (hinv : SlowInvAt p c E rho A b₀ ps K) (hH : SlowHeads p c E rho A b₀ K) :
    SlowInvAt p c E rho A b₀ ps (K + 1) := by
  have hs := h.valid.toScheduleWellFormed
  have hL := hO.life
  have hb1 := hO.budget
  have hpend := hB.pending
  rw [SlowInvAt_def] at hinv ⊢
  intro x hx
  have hbe : b₀ < e.time := by
    by_contra hn
    have := (V2.D.Engine.index_lt_read_length_iff hs b₀ he).mpr (not_lt.mp hn)
    omega
  have hHe : ∀ z j H, HonestHeadAt p c E rho z j H → b₀ < SA.voteTime p.toParams j →
      SA.voteTime p.toParams j < e.time → SA.earlyTime p.toParams j ≤ rho.horizon →
      Block.Preceq A H :=
    pcsa_slowHeads_read E rho hH e.time
      (fun k z t hk ht => pcsa_index_lt_of_time_lt E rho hs hk he ht)
  have hiv := hinv x hx
  by_cases hn : e.node = x
  swap
  · have hst : V2.D.Run.stateBefore E rho (K + 1) x = V2.D.Run.stateBefore E rho K x := by
      rw [V2.D.Run.stateBefore_succ E rho he]
      exact V2.D.World.step_apply_of_node_ne E rho _ hn
    rw [hst]
    refine pcsa_slowInv_congr hiv (pcsa_phase_succ rho he ?_).symm
    intro hex
    apply hn
    rw [hex]
    rfl
  cases e with
  | restart u t => exact absurd he (h.noRestart K u t)
  | tick u t =>
    change u = x at hn
    subst u
    change b₀ < t at hbe
    change t < b₁ at heb
    rw [← pcsa_clock_tick_succ E rho hs he]
    have hF : (V2.D.Run.stateBefore E rho K x).st.fg.F = .genesis :=
      ((FrameVacuous_def p _).mp (hfr x hx K)).1
    have hT : ∀ k < K, ∀ e', rho.events[k]? = some e' → e'.time ≤ t :=
      pcsa_events_before_tick E rho hs he
    have hrel : 0 ≤ t - 5 * p.Δ →
        t = SA.releaseTime p.toParams ((t - 5 * p.Δ) / (4 * p.Δ)).toNat →
        ∀ X : State p.n, X.base.votes = (V2.D.Run.stateBefore E rho K x).st.base.votes →
        X.base.blocks = (V2.D.Run.stateBefore E rho K x).st.base.blocks →
        GridCO.releaseCount p.toParams.engine (actView X)
          ((t - 5 * p.Δ) / (4 * p.Δ)).toNat A < SA.releaseThreshold p.toParams := by
      intro _ h2 X hv hbl
      exact pcsa_slow_release E rho h hf hfr hB x hx K _ (h2 ▸ hbe)
        (h2 ▸ pcsa_tick_le_horizon E rho hs he)
        (fun z j H hz hb hv' => hHe z j H hz hb (lt_of_lt_of_eq hv' h2.symm)) X hv hbl
    by_cases hpre : ¬ ∃ k < K, rho.events[k]? = some (.tick x (SA.gateTime p.toParams ps))
    · by_cases htd : t = SA.gateTime p.toParams ps
      · -- The pending gate: renewal.
        have hgate : clock p (V2.D.Run.stateBefore E rho K x).st t =
            gateStep p (clockPre p (V2.D.Run.stateBefore E rho K x).st t) ps := by
          rcases pcsa_clock_cases p (V2.D.Run.stateBefore E rho K x).st t with
            ⟨-, hng⟩ | ⟨-, -, hg⟩
          · exfalso
            apply hng
            rw [htd, pcsa_gate_slot]
            refine ⟨?_, rfl⟩
            have hΔ : (0 : Int) < p.Δ := p.deltaPos
            change 0 ≤ 4 * p.Δ * (ps : Int) + 6 * p.Δ - 6 * p.Δ
            have : (0 : Int) ≤ (ps : Int) := Int.natCast_nonneg _
            nlinarith
          · rw [hg, htd, pcsa_gate_slot]
        have hgr : gateResultAt p c E rho x ps = some (SA.Root.confirmationFrom p.toParams
            .genesis (actView (clockPre p (V2.D.Run.stateBefore E rho K x).st t)) ps) := by
          have he' := he
          rw [htd] at he'
          rw [pcsa_gateResultAt_def, pcsa_gateInAt_def, pcsa_preTick_def,
            pcsa_tickIdx_of_event E rho hs he', ← htd]
          change some (SA.Root.confirmationFrom p.toParams
            (eraseFG (clockPre p (V2.D.Run.stateBefore E rho K x).st t).fg.F)
            (actView (clockPre p (V2.D.Run.stateBefore E rho K x).st t)) ps) = _
          rw [(pcsa_clockPre_frame p _ t).2.2.2.1, hF]
          rfl
        obtain ⟨hh, hr, hAh, hrows⟩ := hB.result x hx _ hgr
        refine pcsa_tick_renew_inv p _ t ps hiv hpre hF hgate
          (by
            rw [pcsa_storeAt_index E rho hs x b₀]
            exact pcsa_unsaved_before E rho h.noRestart hfr x hx ps _
              (fun k hk e' he' _ => lt_of_le_of_lt
                (pcsa_read_events_le E rho hs b₀ k hk e' he') hpend))
          ⟨hh, hr, hAh, hrows⟩ hAg
          (fun d hd => pcsa_slow_pc_compat E rho h hf hfr hB.acks x hx K t hT hHe 0 0 d (Or.inl hd))
          hB.window (hB.saved x hx) le_rfl _ ?_
        intro hn'
        exact hn' ⟨K, Nat.lt_succ_self K, by rw [he, htd]; rfl⟩
      · -- Before the pending gate: no gate runs.
        have htl : t < SA.gateTime p.toParams ps := by
          rcases lt_or_gt_of_ne htd with h1 | h1
          · exact h1
          · exfalso
            obtain ⟨k, hk⟩ := pcsa_tick_exists E rho hs x hx _ (pcsa_gate_public E h.delta ps)
              (by linarith [hO.start]) (le_trans h1.le (pcsa_tick_le_horizon E rho hs he))
            exact hpre ⟨k, pcsa_index_lt_of_time_lt E rho hs hk he h1, hk⟩
        have hng : clock p (V2.D.Run.stateBefore E rho K x).st t =
            clockPre p (V2.D.Run.stateBefore E rho K x).st t := by
          rcases pcsa_clock_cases p (V2.D.Run.stateBefore E rho K x).st t with
            ⟨hc, -⟩ | ⟨-, hts, -⟩
          · exact hc
          · exfalso
            have h1 := pcsa_gate_mono (p := p) (hB.first _ (hts ▸ hbe))
            rw [← hts] at h1
            linarith
        refine pcsa_slowInv_congr (pcsa_tick_pre_inv p _ t hiv hpre hng)
          (pcsa_phase_succ rho he ?_).symm
        intro hex
        apply htd
        cases hex
        rfl
    · -- After the pending gate.
      obtain ⟨k, hk, hk'⟩ := not_not.mp hpre
      have hdt : SA.gateTime p.toParams ps ≤ t :=
        pcsa_event_time_mono E rho hs hk' he hk.le
      refine pcsa_tick_post_inv p _ t hiv hpre hF (by linarith) hrel ?_ _ ?_
      · intro s hts
        rw [← hts]
        linarith
      · intro hn'
        exact hn' ⟨k, Nat.lt_succ_of_lt hk, hk'⟩
  | deliver u o t =>
    change u = x at hn
    subst u
    change b₀ < t at hbe
    have hst : (V2.D.Run.stateBefore E rho (K + 1) x).st =
        process p (V2.D.Run.stateBefore E rho K x).st (toWire p o) := by
      rw [V2.D.Run.stateBefore_succ E rho he]
      change (Function.update (V2.D.Run.stateBefore E rho K) x _ x).st = _
      rw [Function.update_self]
      rfl
    have hF0 : (V2.D.Run.stateBefore E rho K x).st.fg.F = .genesis :=
      ((FrameVacuous_def p _).mp (hfr x hx K)).1
    have hF : (process p (V2.D.Run.stateBefore E rho K x).st (toWire p o)).fg.F = .genesis := by
      rw [← hst]
      exact ((FrameVacuous_def p _).mp (hfr x hx (K + 1))).1
    have hT : ∀ k < K + 1, ∀ e', rho.events[k]? = some e' → e'.time ≤ t :=
      fun k hk e' he' => pcsa_event_time_mono E rho hs he' he (Nat.le_of_lt_succ hk)
    have hU : ∀ d, UsedPC (process p (V2.D.Run.stateBefore E rho K x).st (toWire p o)) d →
        Block.Compatible d.target A := by
      intro d hd
      rw [UsedPC_def, ← hst] at hd
      rcases hd with hd | ⟨s, hd⟩
      · exact pcsa_slow_pc_compat E rho h hf hfr hB.acks x hx (K + 1) t hT hHe 0 0 d (Or.inl hd)
      · exact pcsa_slow_pc_compat E rho h hf hfr hB.acks x hx (K + 1) t hT hHe 0 s d
          (Or.inr (Or.inr hd))
    rw [hst]
    refine pcsa_slowInv_congr (pcsa_process_inv p _ _ hiv hF0 hF hU)
      (pcsa_phase_succ rho he ?_).symm
    intro hex
    cases hex

/-- [pcsa34-r4.3 §5.5 steps 2–3] The HEAD of a tick after `b₀` is `⪰ A`.
Before the pending gate `d_{p*}` it is a boundary fact (the HEAD past the
cut). After it, its live root is `⪰ A`, since every lock and view source is
compatible with `A` and the lock on `A` is live. -/
theorem pcsa_slowHeads_step (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {b₀ b₁ : Time} (hO : SlowSpan p b₀ b₁) {A : Block} {ps : Slot}
    (hB : CleanSlowBoundary p c E rho A b₀ ps) (K : Nat)
    (e : V2.Event V (Obj p)) (he : rho.events[K]? = some e) (heb : e.time < b₁)
    (hinv : SlowInvAt p c E rho A b₀ ps (K + 1)) (hH : SlowHeads p c E rho A b₀ K) :
    SlowHeads p c E rho A b₀ (K + 1) := by
  have hs := h.valid.toScheduleWellFormed
  have hb1 := hO.budget
  have h4 := hO.four
  have hpend := hB.pending
  have hH' := hH
  rw [SlowHeads_def] at hH ⊢
  rw [SlowInvAt_def] at hinv
  intro z hz j k hk hev hbv haw hej
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
  · exact hH z hz j k hlt hev hbv haw hej
  rw [hev] at he
  cases Option.some.inj he
  change SA.voteTime p.toParams j < b₁ at heb
  by_cases hpre : ¬ ∃ k' < k + 1,
      rho.events[k']? = some (.tick z (SA.gateTime p.toParams ps))
  · -- Before the pending gate: the HEAD past the cut.
    have hlt : SA.voteTime p.toParams j < SA.gateTime p.toParams ps := by
      by_contra hge
      rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
      · exact hpre ⟨k, Nat.lt_succ_self k, by rw [hev, heq]⟩
      · obtain ⟨k', hk'⟩ := pcsa_tick_exists E rho hs z hz _ (pcsa_gate_public E h.delta ps)
          (by linarith [hO.start]) (le_trans hgt.le (pcsa_tick_le_horizon E rho hs hev))
        exact hpre ⟨k', Nat.lt_succ_of_lt (pcsa_index_lt_of_time_lt E rho hs hk' hev hgt), hk'⟩
    refine hB.pendingHeads z j _ ⟨hz, haw, ?_⟩ hbv hlt hej
    rw [pcsa_voteHeadAt_def, pcsa_postClock_def, pcsa_preTick_def,
      pcsa_tickIdx_of_event E rho hs hev]
    rfl
  rw [pcsa_clock_tick_succ E rho hs hev]
  have hiv := hinv z hz
  have hv := hfr z hz (k + 1)
  have hO' := pcsa_outageStore_stateBefore E rho (k + 1) z hz
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hj : j ≠ 0 := by
    rintro rfl
    have : SA.voteTime p.toParams 0 = p.Δ := by
      change 4 * p.Δ * ((0 : Nat) : Int) + p.Δ = p.Δ
      simp
    linarith
  have hZ : eraseFG (controls p (V2.D.Run.stateBefore E rho (k + 1) z).st).Z = .genesis := by
    rw [((FrameVacuous_def p _).mp hv).2.1]
    rfl
  have hnow : (V2.D.Run.stateBefore E rho (k + 1) z).st.base.now = SA.voteTime p.toParams j := by
    rw [← pcsa_clock_tick_succ E rho hs hev]
    exact pcsa_clock_now p _ _
  have hT : ∀ k' < k + 1, ∀ e', rho.events[k']? = some e' → e'.time ≤ SA.voteTime p.toParams j :=
    fun k' hk' e' he' => pcsa_event_time_mono E rho hs he' hev (Nat.le_of_lt_succ hk')
  have hHv : ∀ z' j' H, HonestHeadAt p c E rho z' j' H → b₀ < SA.voteTime p.toParams j' →
      SA.voteTime p.toParams j' < SA.voteTime p.toParams j →
      SA.earlyTime p.toParams j' ≤ rho.horizon → Block.Preceq A H :=
    pcsa_slowHeads_read E rho hH' _
      (fun k' z' t hk' ht => pcsa_index_lt_of_time_lt E rho hs hk' hev ht)
  refine pcsa_headVote_above_lock p _ j hj A hZ hiv.rows ?_ ?_ ?_
  · intro d hd
    rcases List.mem_append.mp hd with h1 | h1
    · exact pcsa_slow_pc_compat E rho h hf hfr hB.acks z hz (k + 1) _ hT hHv (j - 1) j d
        (Or.inr (Or.inl h1))
    · exact pcsa_slow_pc_compat E rho h hf hfr hB.acks z hz (k + 1) _ hT hHv (j - 1) j d
        (Or.inr (Or.inr h1))
  · right
    rw [hnow]
    have hl := hiv.renewed hpre
    rw [LockRow_def] at hl
    obtain ⟨row, hr, hA, -, hd⟩ := hl
    exact ⟨row, hr, hA, by linarith⟩
  · obtain ⟨B, hB', hBe⟩ := hO'.lift A hiv.tree
    refine ⟨B, ?_, hBe⟩
    rw [pcsa_fullTree_vacuous p _ hv]
    exact hB'

/-- [pcsa34-r4.3 §5.5 steps 2–4] The invariant and the HEAD facts hold at
every index from the read index of `b₀` up to the read index of `t < b₁`. -/
theorem pcsa_slow_induction (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) (hfr : StageOneFrame p c E rho)
    {b₀ b₁ : Time} (hO : SlowSpan p b₀ b₁) {A : Block} {ps : Slot}
    (hB : CleanSlowBoundary p c E rho A b₀ ps) (hAg : A ≠ .genesis) (t : Time) (ht : t < b₁)
    (n : Nat) (hn : (rho.events.filter (fun e => decide (e.time ≤ b₀))).length + n ≤
      (rho.events.filter (fun e => decide (e.time ≤ t))).length) :
    SlowInvAt p c E rho A b₀ ps ((rho.events.filter (fun e => decide (e.time ≤ b₀))).length + n) ∧
      SlowHeads p c E rho A b₀
        ((rho.events.filter (fun e => decide (e.time ≤ b₀))).length + n) := by
  have hs := h.valid.toScheduleWellFormed
  induction n with
  | zero => exact ⟨pcsa_slowInvAt_base E rho h hB, pcsa_slowHeads_base E rho h A b₀⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hlt : (rho.events.filter (fun e => decide (e.time ≤ b₀))).length + n <
        (rho.events.filter (fun e => decide (e.time ≤ t))).length := by omega
    have hlen : (rho.events.filter (fun e => decide (e.time ≤ b₀))).length + n <
        rho.events.length := lt_of_lt_of_le hlt (List.length_filter_le _ _)
    obtain ⟨e, he⟩ : ∃ e, rho.events[(rho.events.filter (fun e => decide (e.time ≤ b₀))).length
        + n]? = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
    have het : e.time < b₁ :=
      lt_of_le_of_lt ((V2.D.Engine.index_lt_read_length_iff hs t he).mp hlt) ht
    have hinv := pcsa_slowInvAt_step E rho h hf hfr hO hB hAg _ (Nat.le_add_right _ _) e he het
      h1 h2
    exact ⟨hinv, pcsa_slowHeads_step E rho h hf hfr hO hB _ e he het hinv h2⟩

/-- [pcsa34-r4.3 §5.5 steps 1–4] From the Clean-lane boundary facts, every
honest `S` in `[b₀, b₁)` is `⪰ S_u(T)` and every PC held there is compatible
with `S_u(T)`. -/
theorem pcsa_slowStable_of (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {T b₀ b₁ ΔF : Time} (hO : Outage₂ p c E rho T b₀ b₁ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho)
    (hitems : ∀ u ∈ rho.honest, (storeAt p c E rho u T).base.stableRecord ≠ .genesis →
      ∃ ps, CleanSlowBoundary p c E rho (storeAt p c E rho u T).base.stableRecord b₀ ps) :
    SlowStableHolds p c E rho T b₀ b₁ := by
  have h := hO.pre.base
  have hs := h.valid.toScheduleWellFormed
  rw [SlowStableHolds_def]
  intro u hu w hw t hbt htb
  by_cases hAg : (storeAt p c E rho u T).base.stableRecord = .genesis
  · rw [hAg]
    refine ⟨Gen.Pure.block_genesis_preceq _, fun d _ => ?_⟩
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
      (Gen.Pure.block_genesis_preceq _)
  obtain ⟨ps, hB⟩ := hitems u hu hAg
  have hle := V2.D.Engine.read_length_mono (rho := rho) b₀ t hbt
  obtain ⟨hinv, hH⟩ := pcsa_slow_induction E rho h hf hfr (pcsa_slowSpan_of_outage hO) hB hAg
    t htb _
    (by rw [Nat.add_sub_cancel' hle])
  rw [Nat.add_sub_cancel' hle] at hinv hH
  rw [SlowInvAt_def] at hinv
  rw [pcsa_storeAt_index E rho hs w t]
  refine ⟨(hinv w hw).stable, fun d hd => ?_⟩
  have hidx : ∀ k z t', rho.events[k]? = some (.tick z t') → t' < t →
      k < (rho.events.filter (fun e => decide (e.time ≤ t))).length :=
    fun k z t' hk ht' => (V2.D.Engine.index_lt_read_length_iff hs t hk).mpr ht'.le
  exact pcsa_slow_pc_compat E rho h hf hfr hB.acks w hw _ t (pcsa_read_events_le E rho hs t)
    (pcsa_slowHeads_read E rho hH t hidx) 0 0 d (Or.inl hd)

/-- [pcsa34-r4.3 §5.5 steps 1–4] The S-case facts from the Clean-lane
boundary facts. -/
theorem pcsa_slowStableItems (p : Params) (hslow : CleanSlowItems p) : SlowStableItems p := by
  rw [SlowStableItems_def]
  rw [CleanSlowItems_def] at hslow
  intro V _ _ In c m E rho T b₀ b₁ ΔF hO hf hfr
  exact pcsa_slowStable_of E rho hO hf hfr (hslow c m E rho T b₀ b₁ ΔF hO hf hfr)

end AvailableChain.PCSA.Run
end
