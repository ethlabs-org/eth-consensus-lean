module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Premises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
@[expose] public section

/-! # A two-validator run with an honest validator that never wakes

The tick run of `Goldilocks/Runs/OneValidator/TickRun` with its awake function restricted to
validator `0`: `asleepRun A dg` has the same cuts, states and labels as `tickRun A dg` (validator
`0` ticks at every time `t ≥ 0`, nothing else happens), and validator `v0` is the only validator
awake, at every `t ≥ 0`. With more than one validator, the others are honest and never awake: they
make no call, receive nothing, and their state stays the initial one.

* **Generic part** (any node AC `A`, any `n`): the one-validator facts of
  `Goldilocks/Runs/OneValidator/TickRun` that hold for `v0` without `n = 1` (`tickRun_state_v0`,
  `tickRun_groupAt_v0`, `tickRun_cutStep_v0`, `tickRun_pool_v0`), and the states of the other
  validators (`tickRun_state_ne`).
* **The Goldilocks node with two validators** (`Two`: `goldilocksNode` with `n = 2`, `k = 2`,
  `c = 2`, `Δ = 1`, `δ_t = 2`, `t_s = 4s`, a collision-free digest `dg2`):
  (a) `asleepRun_localRun`, `asleepRun_goldilocksRun`: the run is a `Node.LocalRun` and a
  `GoldilocksRun` for the honest set of both validators (the vote pool holds only votes `v0`
  emitted earlier, `asleepRun_votes`).

`Goldilocks/Runs/Asleep/Sleepy` shows `Sleepy` on it; `Goldilocks/AC/InclusionUpdateRejection` uses
it for the rejection of A1.7's update clause. -/

namespace Consensus.Goldilocks.Witness

open Node

section Generic

variable {P : Params} (A : NodeAC P) (dg : Digest (List (FG.Att P.n)) A.Payload)

/-- The tick run with only `v0` awake (at every `t ≥ 0`). -/
noncomputable def asleepRun : RunTrace A :=
  { tickRun A dg with awake := fun y t => y = v0 ∧ 0 ≤ t }

variable {A dg}

theorem asleepRun_awake (y : Fin P.n) (t : Time) :
    (asleepRun A dg).awake y t ↔ y = v0 ∧ 0 ≤ t := Iff.rfl

/-- The run's states are the tick run's. -/
theorem asleepRun_state (y : Fin P.n) : ∀ i, (asleepRun A dg).state y i = (tickRun A dg).state y i
  | 0 => rfl
  | i + 1 => by
    simp only [Trace.state]
    rw [asleepRun_state y i]
    rfl

/-- The run's groups are the tick run's. -/
theorem asleepRun_groupAt {proposer : Nat → Fin P.n} {y : Fin P.n} {j : Nat} {t : Time}
    {e : Node.Event A} :
    (asleepRun A dg).GroupAt proposer dg y j t e ↔ (tickRun A dg).GroupAt proposer dg y j t e := by
  simp only [RunTrace.GroupAt, asleepRun_state]
  exact Iff.rfl

/-- The run's ticks are the tick run's. -/
theorem asleepRun_tickAt {proposer : Nat → Fin P.n} {y : Fin P.n} {j : Nat} {t : Time} :
    (asleepRun A dg).TickAt proposer dg y j t ↔ (tickRun A dg).TickAt proposer dg y j t := by
  simp only [RunTrace.TickAt, asleepRun_groupAt]

/-- Every cut of the run is a cut of `v0`. -/
theorem eq_v0_of_callAt {y : Fin P.n} {i : Nat} {c : Cut A}
    (h : (tickRun A dg).CallAt y i c) : y = v0 := h.1.symm

/-- The state of `v0` before cut `i` (as `tickRun_state`, without `n = 1`). -/
theorem tickRun_state_v0 : ∀ i, (tickRun A dg).state v0 i = tickMid A dg (i / 8) (i % 8)
  | 0 => rfl
  | i + 1 => by
    have ih := tickRun_state_v0 i
    have hlen := tickCuts_length A dg (i / 8)
    simp only [Trace.state]
    by_cases h7 : i % 8 = 7
    · have hq : (i + 1) / 8 = i / 8 + 1 := by omega
      have hr : (i + 1) % 8 = 0 := by omega
      have hl : (tickRun A dg).label i = none := by
        rw [tickRun_label, h7]; exact List.getElem?_eq_none (by omega)
      have hn : ¬ ((tickRun A dg).node i = v0 ∧ (tickRun A dg).label i ≠ none) := fun h => h.2 hl
      simp only [hn, ↓reduceIte]
      rw [ih, hq, hr, tickMid_zero, h7, tickMid_of_le A dg (by omega)]
    · have hq : (i + 1) / 8 = i / 8 := by omega
      have hr : (i + 1) % 8 = i % 8 + 1 := by omega
      rw [hq, hr]
      split_ifs with h
      · rfl
      · rw [ih]
        have hl : (tickCuts A dg (i / 8)).length ≤ i % 8 := by
          by_contra hc
          have hlt : i % 8 < (tickCuts A dg (i / 8)).length := by omega
          exact h ⟨rfl, by rw [tickRun_label, List.getElem?_eq_getElem hlt]; simp⟩
        rw [tickMid_of_le A dg hl, tickMid_of_le A dg (by omega)]

/-- A validator other than `v0` keeps its initial state. -/
theorem tickRun_state_ne {y : Fin P.n} (hy : y ≠ v0) :
    ∀ i, (tickRun A dg).state y i = Node.init A
  | 0 => rfl
  | i + 1 => by
    simp only [Trace.state]
    split_ifs with h
    · exact absurd h.1.symm hy
    · exact tickRun_state_ne hy i

theorem tickRun_state_tick_v0 (t : Nat) : (tickRun A dg).state v0 (8 * t) = tickState A dg t := by
  rw [tickRun_state_v0, show 8 * t / 8 = t by omega, show 8 * t % 8 = 0 by omega]; rfl

/-- The tick of time `t` is a group of `v0` at cut `8t` (as `tickRun_groupAt`, without
`n = 1`). -/
theorem tickRun_groupAt_v0 (t : Nat) :
    (tickRun A dg).GroupAt (fun _ => v0) dg v0 (8 * t) (t : Int) (.tick 0) := by
  have hcs : (exec (fun _ => v0) dg v0
      ((tickRun A dg).state v0 (8 * t)) (t : Int) (.tick 0)).2 =
      tickCuts A dg t := by rw [tickRun_state_tick_v0]; rfl
  have hlen := tickCuts_length A dg t
  have hpos := List.length_pos_of_ne_nil (tickCuts_ne_nil A dg t)
  have hev : (tickRun A dg).event (8 * t) = 2 * t := by
    change (if 8 * t % 8 < (tickCuts A dg (8 * t / 8)).length then 2 * (8 * t / 8)
      else 2 * (8 * t) + 1) = _
    rw [show 8 * t / 8 = t by omega, show 8 * t % 8 = 0 by omega]
    simp only [hpos, ↓reduceIte]
  refine ⟨by rw [hcs]; exact tickCuts_ne_nil A dg t, fun k hk0 => ?_, fun i hi => ?_⟩
  · have hk : k < (tickCuts A dg t).length := hcs ▸ hk0
    have hq : (8 * t + k) / 8 = t := by omega
    have hr : (8 * t + k) % 8 = k := by omega
    refine ⟨rfl, by rw [tickRun_time, hq], ?_, hr, ?_⟩
    · rw [hev]
      change (if (8 * t + k) % 8 < (tickCuts A dg ((8 * t + k) / 8)).length then
        2 * ((8 * t + k) / 8) else 2 * (8 * t + k) + 1) = _
      rw [hq, hr]
      simp only [hk, ↓reduceIte]
    · rw [tickRun_label, hq, hr, List.getElem_of_eq hcs hk0]
      exact List.getElem?_eq_getElem hk
  · rw [hev] at hi
    change (if i % 8 < (tickCuts A dg (i / 8)).length then 2 * (i / 8) else 2 * i + 1) =
      2 * t at hi
    rw [hcs]
    split_ifs at hi with h
    · have : i / 8 = t := by omega
      subst this
      omega
    · omega

/-- The cut law at every labelled cut (as `tickRun_cutStep`, without `n = 1`). -/
theorem tickRun_cutStep_v0 {y : Fin P.n} {i : Nat} {c : Cut A}
    (hc : (tickRun A dg).CallAt y i c) :
    CutStep y ((tickRun A dg).time i) ((tickRun A dg).state y i) c ((tickRun A dg).post i) := by
  obtain rfl := eq_v0_of_callAt hc
  obtain ⟨hk, rfl⟩ := tickRun_label_get hc.2
  rw [tickRun_state_v0]
  exact chain_step
    (Compose.exec_is_cut_chain (fun _ => v0) dg v0 (tickState A dg (i / 8)) _ (.tick 0)) _ hk

/-- Every attestation in `v0`'s pool before cut `i` was signed by `v0` at an earlier cut (as
`tickRun_pool`, without `n = 1`). -/
theorem tickRun_pool_v0 :
    ∀ i, ∀ a ∈ ((tickRun A dg).state v0 i).fg.atts, ∃ j < i, (tickRun A dg).SignAt v0 j a := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro a ha
    rcases i with _ | i
    · simp [Trace.state, tickRun, Node.init, Store.init] at ha
    simp only [Trace.state] at ha
    split_ifs at ha with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun A dg).CallAt v0 i c := ⟨hl.1, hc⟩
      rcases cutStep_atts A (tickRun_cutStep_v0 hcall) a ha with h | ⟨B, rfl, hB⟩ | rfl
      · obtain ⟨j, hj, hs⟩ := ih i (by omega) a h
        exact ⟨j, by omega, hs⟩
      · obtain ⟨hk, he⟩ := tickRun_label_get hc
        have hpay := onBlock_tick_payload_aux (A := A) (dg := dg) (i / 8) (i % 8) (by
          rw [List.getElem?_eq_getElem hk, he]) a hB
        rw [← tickRun_state_tick_v0] at hpay
        obtain ⟨j, hj, hs⟩ := ih (8 * (i / 8)) (by omega) a hpay
        exact ⟨j, by omega, hs⟩
      · obtain ⟨hk, he⟩ := tickRun_label_get hc
        obtain ⟨k', C, hk', hsig⟩ := onTick_att_pos (A := A) (dg := dg) v0 _ _ 0 (k := i % 8)
          (by change (tickCuts A dg (i / 8))[i % 8]? = _; rw [List.getElem?_eq_getElem hk, he])
        refine ⟨8 * (i / 8) + k', by omega, C, rfl, ?_⟩
        rw [tickRun_label, show (8 * (i / 8) + k') / 8 = i / 8 by omega,
          show (8 * (i / 8) + k') % 8 = k' by omega]
        exact hsig
    · obtain ⟨j, hj, hs⟩ := ih i (by omega) a ha
      exact ⟨j, by omega, hs⟩

/-- A block of a cut of the run is `v0`'s own proposal. -/
theorem tickRun_block_proposer {i : Nat} {B : A.Blk} {y : Fin P.n}
    (h : (tickRun A dg).BlockCallAt y i B) : B.proposer = v0 := by
  obtain ⟨acc, hc⟩ := h
  obtain ⟨d, p, -, rfl⟩ := onTick_block_made A dg _ _ _ _ (tickRun_label_mem hc.2)
    (Or.inl ⟨acc, rfl⟩)
  rfl

end Generic

/-! ## The Goldilocks node with two validators -/

namespace Two

open SA

/-- The shared parameters: two validators, `Δ = 1`, `t_s = 4s`, genesis root `0`, `δ_t = 2`. -/
abbrev P2 : Params where
  n := 2
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 2

/-- The SA parameters: `P2` with `k = 2`, `c = 2`. -/
abbrev sp2 : SAParams where
  toParams := P2
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl

/-- A replay order (never used: nobody restarts). -/
noncomputable abbrev ro2 : ReplayOrder sp2 (List (FG.Att sp2.n)) := ReplayOrder.choice sp2

/-- The node: the Goldilocks SA with these parameters. -/
noncomputable abbrev N2 : NodeAC sp2.toParams := goldilocksNode sp2 ro2

/-- The awake validator. -/
abbrev w0 : Fin sp2.n := v0

/-- The honest validator that never wakes. -/
abbrev w1 : Fin sp2.n := ⟨1, by decide⟩

theorem w1_ne : w1 ≠ w0 := by decide

theorem eq_w0_or_w1 (y : Fin sp2.n) : y = w0 ∨ y = w1 := by
  rcases y with ⟨_ | _ | y, hy⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hy (by change ¬ (y + 2 < 2); omega)

/-- The content of a block (what its root digests). -/
abbrev Content := Option Nat × Nat × Nat × List (FG.Att sp2.n) × Payload sp2.n

/-- An injective code of block contents. -/
noncomputable def code : Content → Nat := (Countable.exists_injective_nat Content).choose

theorem code_injective : Function.Injective code :=
  (Countable.exists_injective_nat Content).choose_spec

/-- The genesis content. -/
def genContent : Content := (none, 0, 0, [], ([], []))

open Classical in
/-- A collision-free digest whose value at the genesis content is the genesis root `0`. -/
noncomputable def dg2 : Digest (List (FG.Att sp2.n)) (Payload sp2.n) := fun p s x a q =>
  if (p, s, x, a, q) = genContent then 0 else code (p, s, x, a, q) + 1

theorem dg2_injective {p s x a q p' s' x' a' q'} (h : dg2 p s x a q = dg2 p' s' x' a' q') :
    (p, s, x, a, q) = ((p', s', x', a', q') : Content) := by
  unfold dg2 at h
  split_ifs at h with h₁ h₂ h₃ <;> first
    | exact h₁.trans h₂.symm
    | exact code_injective (by omega)

theorem dg2_genesis : (sp2.toParams.genesisBlock N2.genesisPayload).RootOk dg2 := by
  change (0 : Nat) = dg2 none 0 0 [] ([], [])
  unfold dg2; simp [genContent]

theorem dg2_noColl (tr : RunTrace N2) : Compose.NoCollRun dg2 tr := by
  intro B _ C _ h
  have := dg2_injective h
  simp only [Prod.mk.injEq] at this
  exact this

/-- The run. -/
noncomputable abbrev tr2 : RunTrace N2 := asleepRun N2 dg2

theorem tr2_state (y : Fin sp2.n) (i : Nat) : tr2.state y i = (tickRun N2 dg2).state y i :=
  asleepRun_state y i

theorem tr2_callAt {y : Fin sp2.n} {i : Nat} {c : Cut N2} :
    tr2.CallAt y i c ↔ (tickRun N2 dg2).CallAt y i c := Iff.rfl

/-- **The run is a run of the node** (`Node.LocalRun`), for the honest set of both validators and
any signer map: only `w0` is awake and calls, and `w1` never wakes. -/
theorem asleepRun_localRun (sg : N2.Msg → Fin sp2.n) :
    Node.LocalRun (fun _ => w0) dg2 Set.univ sg tr2 where
  init _ _ := rfl
  grouped y _ i c hc := by
    obtain rfl := eq_v0_of_callAt (tr2_callAt.1 hc)
    obtain ⟨hk, -⟩ := tickRun_label_get hc.2
    refine ⟨8 * (i / 8), .tick 0, asleepRun_groupAt.2 (tickRun_groupAt_v0 (i / 8)), by omega, ?_⟩
    rw [tr2_state, tickRun_state_tick_v0]
    change i < 8 * (i / 8) + (tickCuts N2 dg2 (i / 8)).length
    omega
  cutLaw y _ i c hc := by
    rw [tr2_state]
    exact tickRun_cutStep_v0 (tr2_callAt.1 hc)
  wire y _ j t e h := by
    obtain ⟨-, -, x, rfl⟩ := tickRun_groupAt_inv (A := N2) (dg := dg2) (asleepRun_groupAt.1 h)
    trivial
  proposerCredential _ _ _ _ B h := by
    obtain ⟨-, -, x, hx⟩ := tickRun_groupAt_inv (A := N2) (dg := dg2) (asleepRun_groupAt.1 h)
    cases hx
  time_nonneg _ := Int.natCast_nonneg _
  time_mono _ _ h := Int.ofNat_le.mpr (Nat.div_le_div_right h)
  finite T := (Set.finite_Iio (8 * (T.toNat + 1))).subset fun i hi => by
    obtain ⟨-, hT⟩ := hi
    change ((i / 8 : Nat) : Int) ≤ T at hT
    have h0 : 0 ≤ T := le_trans (Int.natCast_nonneg _) hT
    have : i / 8 ≤ T.toNat := (Int.le_toNat h0).mpr hT
    change i < 8 * (T.toNat + 1)
    omega
  phase_order y _ y' _ j j' t e e' h h' hlt :=
    absurd (tickRun_groupAt_unique (A := N2) (dg := dg2) (asleepRun_groupAt.1 h)
      (asleepRun_groupAt.1 h')) (Nat.ne_of_lt hlt)
  tick_public y _ j t h := by
    obtain ⟨_, h⟩ := asleepRun_tickAt.1 h
    obtain ⟨-, rfl, -⟩ := tickRun_groupAt_inv (A := N2) (dg := dg2) h
    exact one_dvd _
  tick_unique y _ j j' t h h' := by
    obtain ⟨_, h⟩ := asleepRun_tickAt.1 h
    obtain ⟨_, h'⟩ := asleepRun_tickAt.1 h'
    exact tickRun_groupAt_unique (A := N2) (dg := dg2) h h'
  tick_of_awake y _ t h0 _ h := by
    obtain ⟨rfl, -⟩ := h
    have htt : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg h0
    refine ⟨8 * t.toNat, asleepRun_tickAt.2 ⟨0, ?_⟩⟩
    rw [← htt]
    exact tickRun_groupAt_v0 t.toNat
  awake_in_horizon y _ t h := by
    have ht := h.2
    have htt : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht
    refine ⟨8 * t.toNat, ?_, ?_⟩
    · left
      change (tickRun N2 dg2).label (8 * t.toNat) ≠ none
      rw [tickRun_label, show 8 * t.toNat / 8 = t.toNat by omega,
        show 8 * t.toNat % 8 = 0 by omega, tickCuts_head]
      simp
    · change ((8 * t.toNat / 8 : Nat) : Int) ≥ t
      rw [show 8 * t.toNat / 8 = t.toNat by omega, htt]
  awake_of_call y _ i h := by
    obtain ⟨c, hc⟩ := h
    exact ⟨eq_v0_of_callAt (tr2_callAt.1 hc), Int.natCast_nonneg _⟩
  restart_of_sleep y _ i u h hu _ hnu _ := by
    obtain ⟨c, hc⟩ := h
    exact absurd ⟨eq_v0_of_callAt (tr2_callAt.1 hc), hu⟩ hnu
  restart_at_wake y _ u v hu _ hnu hv := absurd ⟨hv.1, hu⟩ hnu
  sleep_of_restart y _ i h := absurd h (tickRun_no_restart (A := N2) (dg := dg2) y i)
  block_unforgeable y _ i B h _ := by
    have hprop := tickRun_block_proposer (A := N2) (dg := dg2) h
    obtain ⟨acc, hc⟩ := h
    obtain ⟨hk, he⟩ := tickRun_label_get hc.2
    have hpos := onTick_fg_pos (A := N2) (dg := dg2) v0 _ _ 0 (k := i % 8)
      (by change (tickCuts N2 dg2 (i / 8))[i % 8]? = _; rw [List.getElem?_eq_getElem hk, he])
    refine ⟨i, le_rfl, ⟨acc, ?_⟩, ?_⟩
    · rw [hprop]; exact ⟨rfl, hc.2⟩
    · change i % 8 ≠ 0; omega
  att_unforgeable y _ i a h _ := by
    have hsig : ∃ j < i, (tickRun N2 dg2).SignAt v0 j a := by
      rcases h with h | ⟨B, ⟨acc, hc⟩, ha⟩
      · exact tickRun_att_signed h
      · obtain ⟨hk, he⟩ := tickRun_label_get hc.2
        have hpay := onBlock_tick_payload_aux (A := N2) (dg := dg2) (i / 8) (i % 8) (by
          rw [List.getElem?_eq_getElem hk, he]) a ha
        rw [← tickRun_state_tick_v0] at hpay
        obtain ⟨j, hj, hs⟩ := tickRun_pool_v0 (8 * (i / 8)) a hpay
        exact ⟨j, by omega, hs⟩
    obtain ⟨j, hj, C, hc⟩ := hsig
    have hval : a.val = v0 := Simulation.attest_val_of_mem_exec (fun _ => v0) dg2 v0
      (tickState N2 dg2 (j / 8)) _ (.tick 0) (tickRun_label_mem hc.2)
    rw [hval]
    exact ⟨j, hj, C, hc⟩
  msg_unforgeable y _ i m h _ := absurd h (tickRun_no_msg (A := N2) (dg := dg2) y i m)

/-- The votes `ac_proposal` puts in the payload are in the pool. -/
theorem acProposal_payload (st : NodeState N2) (t : Time) {d : DutyHead sp2.n _ (Payload sp2.n)}
    {p : Payload sp2.n} (h : (Node.acProposal st t).2.2 = some (d, p)) :
    ∀ v ∈ p.1, ∃ σ, v ∈ st.ac.pool σ := by
  intro v hv
  change (SA.acProposal sp2 st.ac (frame st) t).2 = some (d, p) at h
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [voteViewList, List.mem_filter] at hv
  unfold SAState.poolAt at hv
  split_ifs at hv
  · simp at hv
  · exact ⟨_, hv.1⟩

/-- A cut that is not its tick's `ac_on_tick` has a position `≥ 1`. -/
theorem pos_of_ne_tick {i : Nat} {c : Cut N2} (h : (tickRun N2 dg2).label i = some c)
    (hne : ∀ ℓ : ACLabel N2, c = .ac ℓ → ℓ.call ≠ .tick) : 1 ≤ i % 8 := by
  by_contra h0
  have := tickRun_label_zero h (by omega)
  exact hne _ this rfl

/-- The state after the first cut of the tick of `⌊i/8⌋`. -/
theorem state_one (i : Nat) :
    (tickRun N2 dg2).state v0 (8 * (i / 8) + 1) = tickMid N2 dg2 (i / 8) 1 := by
  rw [tickRun_state_v0]; congr 1 <;> omega

/-- Every vote in `w0`'s pool before cut `i` was emitted by `w0` at an earlier cut. -/
theorem asleepRun_votes :
    ∀ i σ, ∀ v ∈ ((tickRun N2 dg2).state v0 i).ac.pool σ,
      ∃ j < i, (tickRun N2 dg2).EmitAt v0 j v := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro σ v hv
    rcases i with _ | i
    · simp [Trace.state, tickRun, Node.init, SAState.initial] at hv
    simp only [Trace.state] at hv
    split_ifs at hv with hl
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hl.2
      have hcall : (tickRun N2 dg2).CallAt v0 i c := ⟨hl.1, hc⟩
      have hstep := cutStep_ac (tickRun_cutStep_v0 hcall)
      have old : v ∈ ((tickRun N2 dg2).state v0 i).ac.pool σ →
          ∃ j < i + 1, (tickRun N2 dg2).EmitAt v0 j v := fun h => by
        obtain ⟨j, hj, he⟩ := ih i (by omega) σ v h
        exact ⟨j, by omega, he⟩
      have hmem := tickRun_label_mem hc
      cases c with
      | fg ℓ => exact old (hstep.1 ℓ rfl ▸ hv)
      | ac ℓ =>
        have hs := hstep.2 ℓ rfl
        have hac : ((tickRun N2 dg2).post i).ac = (ACInterface.step N2 v0
            ((tickRun N2 dg2).state v0 i).ac ℓ.frame ((tickRun N2 dg2).time i) ℓ.call).1 :=
          (congrArg Prod.fst hs).symm
        have hem : ℓ.emits = (ACInterface.step N2 v0
            ((tickRun N2 dg2).state v0 i).ac ℓ.frame ((tickRun N2 dg2).time i) ℓ.call).2 :=
          (congrArg Prod.snd hs).symm
        rw [hac] at hv
        have emitted : (∃ e ∈ ℓ.emits, e.msg = v) → ∃ j < i + 1, (tickRun N2 dg2).EmitAt v0 j v :=
          fun ⟨e, he, hm⟩ => ⟨i, by omega, ℓ, hcall, e, he, hm⟩
        rcases onTick_ac_call N2 dg2 _ _ _ _ hmem with hcl | hcl | ⟨B, hcl⟩ | hcl <;>
          rw [hcl] at hv hem
        · rcases SAPool.acOnTick_pool sp2 v0 _ _ _ σ v hv with h | h
          · exact old h
          · exact emitted (by rw [hem]; exact h)
        · exact old (by rw [ACInterface.step, SAPool.acProposal_pool] at hv; exact hv)
        · rcases SAPool.acOnBlock_pool sp2 v0 _ _ _ B σ v hv with h | h | h
          · exact old h
          · obtain ⟨d, p, hr, hB⟩ := onTick_block_made N2 dg2 _ _ _ _ hmem (Or.inr ⟨ℓ, rfl, hcl⟩)
            rw [hB] at h
            obtain ⟨σ', h'⟩ := acProposal_payload _ _ hr v h
            rw [← tickMid_one, ← state_one] at h'
            have hp := pos_of_ne_tick hc (fun ℓ' h'' => by
              cases h''; rw [hcl]; exact fun h => by cases h)
            obtain ⟨j, hj, he⟩ := ih (8 * (i / 8) + 1) (by omega) σ' v h'
            exact ⟨j, by omega, he⟩
          · exact emitted (by rw [hem]; exact h)
        · exact old (by rw [ACInterface.step, SAPool.acToFG_pool] at hv; exact hv)
    · obtain ⟨j, hj, he⟩ := ih i (by omega) σ v hv
      exact ⟨j, by omega, he⟩

/-- An emitted vote of `w0` is signed by `w0`. -/
theorem emit_val {j : Nat} {v : Vote sp2.n} (h : (tickRun N2 dg2).EmitAt v0 j v) : v.val = v0 := by
  obtain ⟨ℓ, hc, e, he, rfl⟩ := h
  have hmem := tickRun_label_mem hc.2
  exact Simulation.emits_val_of_mem_exec (fun _ => v0) dg2 v0 (tickState N2 dg2 (j / 8)) _
    (.tick 0) hmem e he

/-- **The run is a Goldilocks run.** -/
theorem asleepRun_goldilocksRun :
    GoldilocksRun (sp := sp2) (ro := ro2) (fun _ => w0) dg2 Set.univ tr2 where
  stock := rfl
  toLocalRun := asleepRun_localRun _
  genesis_root_ok := dg2_genesis
  vstart := fun _ => SA.voteStart_initial _
  carried_vote_unforgeable y _ i B hB v hv _ := by
    obtain ⟨acc, hc⟩ := hB
    obtain ⟨d, p, hr, hB⟩ := onTick_block_made N2 dg2 _ _ _ _ (tickRun_label_mem hc.2)
      (Or.inl ⟨acc, rfl⟩)
    rw [hB] at hv
    obtain ⟨σ', h'⟩ := acProposal_payload _ _ hr v hv
    rw [← tickMid_one, ← state_one] at h'
    have hp := pos_of_ne_tick hc.2 (fun ℓ h => by cases h)
    obtain ⟨j, hj, he⟩ := asleepRun_votes (8 * (i / 8) + 1) σ' v h'
    rw [emit_val he]
    exact ⟨j, by omega, he⟩

end Two

end Consensus.Goldilocks.Witness

end
