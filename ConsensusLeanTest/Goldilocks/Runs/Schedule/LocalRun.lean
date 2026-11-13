module
public import ConsensusLeanTest.Goldilocks.Runs.Schedule.Run
@[expose] public section

/-! # The run trace of a schedule is a run of the node

For the schedules of `ConsensusLeanTest/Goldilocks/Runs/Schedule/Run`:

* `trace_localRun`: under the entry-level laws `RunLaws` (non-empty groups, time order, phase
  order, ticks, sleep and restarts, horizon, finiteness, wire checks, credentials), and the three
  unforgeability fields stated on the trace, the trace is a `Node.LocalRun`;
  `trace_goldilocksRun` adds the genesis root and carried-vote unforgeability for the Goldilocks
  node. Nothing uses finiteness of the schedule except the law `RunLaws.finite`.
* Time-indexed schedules: `ofSegs segs` flattens the event lists `segs t` of the integer times
  `t = 0, 1, …` (index lemmas `segEntry_add`, `segEntry_eq_some`); its time order, finiteness,
  ticks and horizon laws hold by construction (`ofSegs_mono`, `ofSegs_nonneg`, `ofSegs_finite`,
  `ofSegs_ticks`, `ofSegs_horizon`); its states advance one time at a time
  (`ofSegs_stBefore_succ`). A causal generator `gen t (states at the start of t)` resolves to such
  lists by `genSegs`, whose states at the start of each time are `genStates`
  (`ofSegs_genSegs_stBefore`).
* `empty_localRun`: the empty schedule, nobody awake, is a run (a sanity check of the stutter). -/

namespace Consensus.Goldilocks.Test.ScheduleRun

open Node
open SA (SAParams ReplayOrder Payload blockVotes Vote)

variable {P : Params} {A : NodeAC P}

namespace Schedule

variable {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {sch : Schedule A}

/-! ## The laws of a run, on entries -/

/-- The entry-level laws under which the trace of a schedule is a `Node.LocalRun` for the
honest validators `H` (`trace_localRun`). -/
structure RunLaws (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Set (Fin P.n)) (sch : Schedule A) : Prop where
  /-- Every entry makes a cut (a dropped future-slot block is not an entry). -/
  ne : ∀ k y t e, sch.entry k = some (y, t, e) →
    (exec proposer dg y (sch.stBefore proposer dg y k) t e).2 ≠ []
  /-- Entries in time order. -/
  mono : ∀ k k' y y' t t' e e', k ≤ k' → sch.entry k = some (y, t, e) →
    sch.entry k' = some (y', t', e') → t ≤ t'
  /-- Entries at times from `0` on. -/
  nonneg : ∀ k y t e, sch.entry k = some (y, t, e) → 0 ≤ t
  /-- At one time, honest entries in phase order (restart, tick, delivery). -/
  phase : ∀ k k' y y' t e e', y ∈ H → y' ∈ H → k < k' → sch.entry k = some (y, t, e) →
    sch.entry k' = some (y', t, e') → e.phase ≤ e'.phase
  /-- Honest ticks at public times. -/
  tick_public : ∀ k y t x, y ∈ H → sch.entry k = some (y, t, .tick x) → P.IsPublic t
  /-- At most one tick per honest node and time. -/
  tick_unique : ∀ k k' y t x x', y ∈ H → sch.entry k = some (y, t, .tick x) →
    sch.entry k' = some (y, t, .tick x') → k = k'
  /-- An honest node awake at a public time from `0` on ticks there. -/
  ticks : ∀ y ∈ H, ∀ t, 0 ≤ t → P.IsPublic t → sch.awake y t →
    ∃ k x, sch.entry k = some (y, t, .tick x)
  /-- Honest entries only while awake. -/
  awake_call : ∀ k y t e, y ∈ H → sch.entry k = some (y, t, e) → sch.awake y t
  /-- The first honest entry after a sleep is a restart. -/
  restart_of_sleep : ∀ k y t e (u : Time), y ∈ H → sch.entry k = some (y, t, e) → 0 ≤ u →
    u < t → ¬ sch.awake y u → (∀ k' < k, ∀ t' e', sch.entry k' = some (y, t', e') → t' < u) →
    e = .restart
  /-- A wake is a restart entry. -/
  restart_at_wake : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v → ¬ sch.awake y u → sch.awake y v →
    ∃ k t, sch.entry k = some (y, t, .restart) ∧ u < t ∧ t ≤ v
  /-- A restart entry follows a sleep. -/
  sleep_of_restart : ∀ k y t, y ∈ H → sch.entry k = some (y, t, .restart) →
    ∃ u : Time, 0 ≤ u ∧ u < t ∧ ¬ sch.awake y u ∧
      ∀ k' < k, ∀ t' e', sch.entry k' = some (y, t', e') → t' < u
  /-- An honest node is awake only up to an entry's time or the horizon. -/
  horizon : ∀ y ∈ H, ∀ t, sch.awake y t →
    (∃ k y' t' e, sch.entry k = some (y', t', e) ∧ t ≤ t') ∨ ∃ T, sch.horizon = some T ∧ t ≤ T
  /-- Finitely many entries up to every time. -/
  finite : ∀ T : Time, {k | ∃ y t e, sch.entry k = some (y, t, e) ∧ t ≤ T}.Finite
  /-- Honest deliveries pass the wire checks. -/
  wire : ∀ k y t e, y ∈ H → sch.entry k = some (y, t, e) → WireOK dg e
  /-- A block delivered to an honest node names its slot's proposer. -/
  credential : ∀ k y t B, y ∈ H → sch.entry k = some (y, t, .block B) →
    B.proposer = proposer B.slot

variable {H : Set (Fin P.n)}

/-- With non-empty entries, a stuttering cut means the schedule is finite. -/
private theorem exists_none_of_stutter (h : sch.RunLaws proposer dg H) {c : Nat}
    (hc : sch.entryOf proposer dg c = none) : ∃ N, sch.entry N = none := by
  by_contra hall
  replace hall := not_exists.mp hall
  have hge : ∀ k, k ≤ sch.start proposer dg k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      rw [start_succ]
      obtain ⟨⟨y, t, e⟩, he⟩ := Option.ne_none_iff_exists'.1 (hall k)
      have := List.length_pos_of_ne_nil (cutsAt_some he ▸ h.ne k y t e he)
      omega
  have := entryOf_eq_none_iff.1 hc c
  have := hge (c + 1)
  omega

/-- An entry's time is at most the stuttering time of a finite schedule. -/
private theorem le_endTime (h : sch.RunLaws proposer dg H) {k : Nat} {y : Fin P.n} {t : Time}
    {e : Event A} (he : sch.entry k = some (y, t, e)) (hfin : ∃ N, sch.entry N = none) :
    t ≤ sch.endTime := by
  classical
  have hlast : sch.lastTime = sch.entryTime (Nat.find hfin - 1) := by
    simp only [lastTime, hfin, ↓reduceDIte]
  have hk : k < Nat.find hfin := by
    by_contra hle
    rw [entry_none_of_le (Nat.find_spec hfin) (not_lt.mp hle)] at he
    cases he
  have hsome := Nat.find_min hfin (m := Nat.find hfin - 1) (by omega)
  obtain ⟨⟨y', t', e'⟩, he'⟩ := Option.ne_none_iff_exists'.1 hsome
  have := h.mono _ _ _ _ _ _ _ _ (by omega : k ≤ Nat.find hfin - 1) he he'
  rw [endTime, hlast, entryTime_of he']
  exact le_max_of_le_right this

private theorem endTime_nonneg (h : sch.RunLaws proposer dg H) : 0 ≤ sch.endTime := by
  classical
  refine le_max_of_le_right ?_
  rw [lastTime]
  split_ifs with hfin
  · cases he : sch.entry (Nat.find hfin - 1) with
    | none => simp [entryTime, he]
    | some v => rw [entryTime_of he]; exact h.nonneg _ _ _ _ he
  · exact le_rfl

/-- The trace's cut times are monotone. -/
theorem trace_time_mono (h : sch.RunLaws proposer dg H) :
    Monotone (sch.trace proposer dg).time := by
  intro c c' hcc
  cases hk : sch.entryOf proposer dg c with
  | none =>
    have hk' : sch.entryOf proposer dg c' = none :=
      entryOf_eq_none_iff.2 fun k => (entryOf_eq_none_iff.1 hk k).trans hcc
    rw [(trace_of_entryOf_none hk).1, (trace_of_entryOf_none hk').1]
  | some k =>
    obtain ⟨h1, h2⟩ := entryOf_eq_some_iff.1 hk
    obtain ⟨y, t, e, he⟩ := entry_of_entryOf hk
    rw [(trace_of_entryOf hk).2.1, entryTime_of he]
    cases hk' : sch.entryOf proposer dg c' with
    | none =>
      rw [(trace_of_entryOf_none hk').1]
      exact le_endTime h he (exists_none_of_stutter h hk')
    | some k' =>
      obtain ⟨h1', h2'⟩ := entryOf_eq_some_iff.1 hk'
      obtain ⟨y', t', e', he'⟩ := entry_of_entryOf hk'
      rw [(trace_of_entryOf hk').2.1, entryTime_of he']
      have hkk : k ≤ k' := by
        by_contra hlt
        have : sch.start proposer dg (k' + 1) ≤ sch.start proposer dg k :=
          start_mono (Nat.succ_le_of_lt (not_le.mp hlt))
        omega
      exact h.mono _ _ _ _ _ _ _ _ hkk he he'

/-- An honest node awake at `t` has `t` within the trace's horizon. -/
private theorem trace_inHorizon (h : sch.RunLaws proposer dg H) {y : Fin P.n} (hy : y ∈ H)
    {t : Time} (ht : sch.awake y t) : (sch.trace proposer dg).InHorizon t := by
  have entry_case : ∀ k y' t' e, sch.entry k = some (y', t', e) → t ≤ t' →
      (sch.trace proposer dg).InHorizon t := by
    intro k y' t' e he hle
    have hpos : 0 < (sch.cutsAt proposer dg k).length := by
      rw [cutsAt_some he]; exact List.length_pos_of_ne_nil (h.ne k y' t' e he)
    obtain ⟨-, htk, -, -, hl, -⟩ := trace_of_entryOf (entryOf_add hpos)
    rw [Nat.add_zero, Nat.sub_self, List.getElem?_eq_getElem hpos] at hl
    rw [Nat.add_zero, entryTime_of he] at htk
    exact ⟨_, Or.inl (by rw [hl]; exact Option.some_ne_none _), htk ▸ hle⟩
  rcases h.horizon y hy t ht with ⟨k, y', t', e, he, hle⟩ | ⟨T, hT, htT⟩
  · exact entry_case k y' t' e he hle
  by_cases hfin : ∃ N, sch.entry N = none
  · obtain ⟨N, hN⟩ := hfin
    have hst : sch.entryOf proposer dg (sch.start proposer dg N) = none := by
      refine entryOf_eq_none_iff.2 fun k => ?_
      rcases Nat.lt_or_ge k N with hk | hk
      · exact start_mono hk
      · have hstab : ∀ m, N ≤ m → sch.start proposer dg m = sch.start proposer dg N := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base => rfl
          | succ m hm ih => rw [start_succ, cutsAt_none (entry_none_of_le hN hm), ih]; rfl
        rw [hstab (k + 1) (by omega)]
    refine ⟨sch.start proposer dg N, Or.inr ⟨T, hT, htT⟩, ?_⟩
    rw [(trace_of_entryOf_none hst).1, endTime, hT]
    exact le_max_of_le_left htT
  · replace hfin := not_exists.mp hfin
    obtain ⟨k, hk⟩ := (h.finite t).exists_notMem
    obtain ⟨⟨y', t', e⟩, he⟩ := Option.ne_none_iff_exists'.1 (hfin k)
    exact entry_case k y' t' e he (le_of_lt (not_le.mp fun hle => hk ⟨y', t', e, he, hle⟩))

/-- **The trace of a schedule is a run of the node** (`Node.LocalRun`), under the entry-level laws
and the three unforgeability fields of the trace. -/
theorem trace_localRun {sg : A.Msg → Fin P.n} (h : sch.RunLaws proposer dg H)
    (hblock : ∀ y ∈ H, ∀ i B, (sch.trace proposer dg).BlockCallAt y i B → B.proposer ∈ H →
      ∃ j ≤ i, (sch.trace proposer dg).OwnBlockAt B.proposer j B)
    (hatt : ∀ y ∈ H, ∀ i a, ((sch.trace proposer dg).AttCallAt y i a ∨
      ∃ B, (sch.trace proposer dg).BlockCallAt y i B ∧ a ∈ B.fgPayload) → a.val ∈ H →
        ∃ j < i, (sch.trace proposer dg).SignAt a.val j a)
    (hmsg : ∀ y ∈ H, ∀ i m, (sch.trace proposer dg).MsgCallAt y i m → sg m ∈ H →
      ∃ j < i, (sch.trace proposer dg).EmitAt (sg m) j m) :
    Node.LocalRun proposer dg H sg (sch.trace proposer dg) where
  init _ _ := rfl
  grouped y _ i c hc := by
    obtain ⟨k, t, e, p, he, rfl, ⟨hp, -⟩, ht⟩ := call_inv hc
    refine ⟨sch.start proposer dg k, e, ?_, Nat.le_add_right _ _, ?_⟩
    · rw [ht]; exact groupAt_entry he (h.ne k y t e he)
    · rw [ht, state_groupStart, ← cutsAt_some he]; omega
  cutLaw _ _ _ _ hc := cutStep_of_callAt hc
  wire y hy j t e hg := by
    obtain ⟨k, e', he, -, hs⟩ := groupAt_inv hg
    rcases hs with rfl | ⟨x, x', rfl, rfl⟩
    · exact h.wire k y t e hy he
    · trivial
  proposerCredential y hy j t B hg := by
    obtain ⟨k, e', he, -, hs⟩ := groupAt_inv hg
    rcases hs with rfl | ⟨x, x', hx, -⟩
    · exact h.credential k y t B hy he
    · cases hx
  time_nonneg c := by
    cases hk : sch.entryOf proposer dg c with
    | none => rw [(trace_of_entryOf_none hk).1]; exact endTime_nonneg h
    | some k =>
      obtain ⟨y, t, e, he⟩ := entry_of_entryOf hk
      rw [(trace_of_entryOf hk).2.1, entryTime_of he]
      exact h.nonneg k y t e he
  time_mono := trace_time_mono h
  finite T := by
    refine ((h.finite T).biUnion fun k _ =>
      Set.finite_Ico (sch.start proposer dg k) (sch.start proposer dg (k + 1))).subset ?_
    rintro c ⟨hl, hT⟩
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨k, t, e, p, he, rfl, ⟨hp, -⟩, ht⟩ := call_inv (y := _) (ℓ := ℓ) ⟨rfl, hℓ⟩
    simp only [Set.mem_iUnion]
    exact ⟨k, ⟨_, t, e, he, ht ▸ hT⟩, Nat.le_add_right _ _, by rw [start_succ]; omega⟩
  phase_order y hy y' hy' j j' t e e' hg hg' hlt := by
    obtain ⟨k, ek, he, rfl, hs⟩ := groupAt_inv hg
    obtain ⟨k', ek', he', rfl, hs'⟩ := groupAt_inv hg'
    have hkk : k < k' := by
      by_contra hle
      have := start_mono (proposer := proposer) (dg := dg) (sch := sch) (not_lt.mp hle)
      omega
    rw [phase_eq_of_sim hs, phase_eq_of_sim hs']
    exact h.phase k k' y y' t ek ek' hy hy' hkk he he'
  tick_public y hy j t := by
    rintro ⟨x, hg⟩
    obtain ⟨k, e', he, -, hs⟩ := groupAt_inv hg
    rcases hs with rfl | ⟨_, x', -, rfl⟩
    · exact h.tick_public k y t x hy he
    · exact h.tick_public k y t x' hy he
  tick_unique y hy j j' t := by
    rintro ⟨x, hg⟩ ⟨x', hg'⟩
    obtain ⟨k, e, he, rfl, hs⟩ := groupAt_inv hg
    obtain ⟨k', e', he', rfl, hs'⟩ := groupAt_inv hg'
    obtain ⟨z, hz⟩ : ∃ z, e = .tick z := by
      rcases hs with rfl | ⟨_, z, -, rfl⟩ <;> exact ⟨_, rfl⟩
    obtain ⟨z', hz'⟩ : ∃ z, e' = .tick z := by
      rcases hs' with rfl | ⟨_, z, -, rfl⟩ <;> exact ⟨_, rfl⟩
    subst hz hz'
    rw [h.tick_unique k k' y t z z' hy he he']
  tick_of_awake y hy t h0 hpub haw := by
    obtain ⟨k, x, he⟩ := h.ticks y hy t h0 hpub haw
    exact ⟨_, x, groupAt_entry he (h.ne k y t _ he)⟩
  awake_in_horizon y hy t ht := trace_inHorizon h hy ht
  awake_of_call y hy i := by
    rintro ⟨c, hc⟩
    obtain ⟨k, t, e, p, he, rfl, -, ht⟩ := call_inv hc
    rw [ht, trace_awake]
    exact h.awake_call k y t e hy he
  restart_of_sleep y hy i u := by
    rintro ⟨c, hc⟩ hu hut hnu hbefore
    obtain ⟨k, t, e, p, he, rfl, ⟨hp, hl⟩, ht⟩ := call_inv hc
    rw [ht] at hut
    have hre := h.restart_of_sleep k y t e u hy he hu hut hnu fun k' hk' t' e' he' => by
      have hpos : 0 < (sch.cutsAt proposer dg k').length := by
        rw [cutsAt_some he']; exact List.length_pos_of_ne_nil (h.ne k' y t' e' he')
      have hlt : sch.start proposer dg (k' + 1) ≤ sch.start proposer dg k :=
        start_mono (Nat.succ_le_of_lt hk')
      have := hbefore _ (by rw [start_succ] at hlt; omega) (isCall_start he' hpos)
      rwa [(trace_of_entryOf (entryOf_start hpos)).2.1, entryTime_of he'] at this
    subst hre
    have hcs := cutsAt_some (proposer := proposer) (dg := dg) he
    rw [exec_restart] at hcs
    have hp0 : p = 0 := by rw [hcs] at hp; simp at hp; exact hp
    subst hp0
    rw [Nat.add_zero]
    exact restartAt_start he
  restart_at_wake y hy u v hu huv hnu hv := by
    obtain ⟨k, t, he, hut, htv⟩ := h.restart_at_wake y hy u v hu huv hnu hv
    have hcs := cutsAt_some (proposer := proposer) (dg := dg) he
    rw [exec_restart] at hcs
    have hpos : 0 < (sch.cutsAt proposer dg k).length := by rw [hcs]; exact Nat.one_pos
    have ht := (trace_of_entryOf (entryOf_start hpos)).2.1
    rw [entryTime_of he] at ht
    exact ⟨_, restartAt_start he, ht ▸ hut, ht ▸ htv⟩
  sleep_of_restart y hy i := by
    rintro ⟨ℓ, hc, hℓ⟩
    obtain ⟨k, t, e, p, he, rfl, ⟨hp, hl⟩, ht⟩ := call_inv hc
    have hmem : Cut.ac ℓ ∈ (exec proposer dg y (sch.stBefore proposer dg y k) t e).2 := by
      rw [← cutsAt_some he, ← hl]; exact List.getElem_mem hp
    have hre := restart_of_mem_exec y _ t e hmem hℓ
    subst hre
    have hcs := cutsAt_some (proposer := proposer) (dg := dg) he
    rw [exec_restart] at hcs
    have hp0 : p = 0 := by rw [hcs] at hp; simp at hp; exact hp
    subst hp0
    obtain ⟨u, hu, hut, hnu, hbefore⟩ := h.sleep_of_restart k y t hy he
    refine ⟨u, hu, by rw [ht]; exact hut, hnu, fun j hj hcall => ?_⟩
    obtain ⟨c', hc'⟩ := hcall
    obtain ⟨k', t', e', p', he', rfl, ⟨hp', -⟩, ht'⟩ := call_inv hc'
    rw [ht']
    exact hbefore k' (lt_of_start_le (Nat.le_add_right _ _) (by omega)) t' e' he'
  block_unforgeable := hblock
  att_unforgeable := hatt
  msg_unforgeable := hmsg

end Schedule

/-- **The trace of a schedule of the Goldilocks node is a Goldilocks run**, under the
entry-level laws, the unforgeability fields of the trace, the genesis root and carried-vote
unforgeability. -/
theorem trace_goldilocksRun {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (hstock : sp.committeeSize = sp.n)
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {sch : Schedule (goldilocksNode sp ro)}
    (h : sch.RunLaws proposer dg H)
    (hblock : ∀ y ∈ H, ∀ i B, (sch.trace proposer dg).BlockCallAt y i B → B.proposer ∈ H →
      ∃ j ≤ i, (sch.trace proposer dg).OwnBlockAt B.proposer j B)
    (hatt : ∀ y ∈ H, ∀ i a, ((sch.trace proposer dg).AttCallAt y i a ∨
      ∃ B, (sch.trace proposer dg).BlockCallAt y i B ∧ a ∈ B.fgPayload) → a.val ∈ H →
        ∃ j < i, (sch.trace proposer dg).SignAt a.val j a)
    (hmsg : ∀ y ∈ H, ∀ i (m : Vote sp.n), (sch.trace proposer dg).MsgCallAt y i m → m.val ∈ H →
      ∃ j < i, (sch.trace proposer dg).EmitAt m.val j m)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg)
    (hcarried : ∀ y ∈ H, ∀ i B, (sch.trace proposer dg).BlockCallAt y i B →
      ∀ v ∈ blockVotes B, v.val ∈ H → ∃ j < i, (sch.trace proposer dg).EmitAt v.val j v) :
    GoldilocksRun proposer dg H (sch.trace proposer dg) where
  stock := hstock
  toLocalRun := Schedule.trace_localRun h hblock hatt hmsg
  genesis_root_ok := hroot
  carried_vote_unforgeable := hcarried
  vstart := fun _ => SA.voteStart_initial _

/-! ## Time-indexed schedules -/

section Segs

variable (segs : Nat → List (Fin P.n × Event A))

/-- The number of events at time `t`. -/
def segLen (t : Nat) : Nat := (segs t).length

/-- Entry `k` of the flattened event lists: event `k - psum t` of the time `t` that contains
`k`. -/
noncomputable def segEntry (k : Nat) : Option (Entry A) :=
  (locate (segLen segs) k).bind fun s =>
    ((segs s)[k - psum (segLen segs) s]?).map fun ye => (ye.1, (s : Time), ye.2)

variable {segs} in
/-- Event `p` of time `s` is entry `psum s + p`. -/
theorem segEntry_add {s p : Nat} (hp : p < (segs s).length) :
    segEntry segs (psum (segLen segs) s + p) = some ((segs s)[p].1, (s : Time), (segs s)[p].2) := by
  simp [segEntry, locate_add (len := segLen segs) hp, List.getElem?_eq_getElem hp]

variable {segs} in
/-- Every entry is an event of its time. -/
theorem segEntry_eq_some {k : Nat} {y : Fin P.n} {t : Time} {e : Event A}
    (h : segEntry segs k = some (y, t, e)) :
    ∃ s p, k = psum (segLen segs) s + p ∧ t = (s : Time) ∧ (segs s)[p]? = some (y, e) := by
  cases hs : locate (segLen segs) k with
  | none => simp [segEntry, hs] at h
  | some s =>
    obtain ⟨h1, -⟩ := locate_eq_some_iff.1 hs
    simp only [segEntry, hs, Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨⟨y', e'⟩, hget, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨s, k - psum (segLen segs) s, by omega, rfl, hget⟩

theorem segEntry_prefix_closed (k : Nat) (hk : segEntry segs k = none) :
    segEntry segs (k + 1) = none := by
  cases hs : locate (segLen segs) k with
  | none =>
    have h := locate_eq_none_iff.1 hs
    have : locate (segLen segs) (k + 1) = none :=
      locate_eq_none_iff.2 fun s => (h s).trans (Nat.le_succ k)
    simp [segEntry, this]
  | some s =>
    obtain ⟨h1, h2⟩ := locate_eq_some_iff.1 hs
    rw [psum_succ] at h2
    simp only [segEntry, hs, Option.bind_some, Option.map_eq_none_iff,
      List.getElem?_eq_none_iff] at hk
    have hlt : k - psum (segLen segs) s < segLen segs s := by omega
    exact absurd hk (not_le.mpr hlt)

/-- The schedule of the event lists `segs t` at the integer times `t = 0, 1, …`, in order. -/
noncomputable def ofSegs (awake : Fin P.n → Time → Prop) (horizon : Option Time) : Schedule A where
  entry := segEntry segs
  prefix_closed := segEntry_prefix_closed segs
  awake := awake
  horizon := horizon

variable {segs} {awake : Fin P.n → Time → Prop} {horizon : Option Time}

theorem ofSegs_entry : (ofSegs segs awake horizon).entry = segEntry segs := rfl

/-- `ofSegs` entries are in time order. -/
theorem ofSegs_mono : ∀ k k' y y' t t' e e', k ≤ k' →
    (ofSegs segs awake horizon).entry k = some (y, t, e) →
    (ofSegs segs awake horizon).entry k' = some (y', t', e') → t ≤ t' := by
  intro k k' y y' t t' e e' hkk he he'
  obtain ⟨s, p, rfl, rfl, hp⟩ := segEntry_eq_some he
  obtain ⟨s', p', rfl, rfl, hp'⟩ := segEntry_eq_some he'
  by_contra hlt
  have hss : s' + 1 ≤ s := by exact_mod_cast not_le.mp hlt
  have := psum_mono (segLen segs) hss
  rw [psum_succ] at this
  have : p' < segLen segs s' := (List.getElem?_eq_some_iff.1 hp').1
  omega

/-- `ofSegs` entries are at times from `0` on. -/
theorem ofSegs_nonneg : ∀ k y t e, (ofSegs segs awake horizon).entry k = some (y, t, e) →
    0 ≤ t := by
  intro k y t e he
  obtain ⟨s, p, -, rfl, -⟩ := segEntry_eq_some he
  exact Int.natCast_nonneg s

/-- Finitely many `ofSegs` entries up to every time. -/
theorem ofSegs_finite (T : Time) :
    {k | ∃ y t e, (ofSegs segs awake horizon).entry k = some (y, t, e) ∧ t ≤ T}.Finite := by
  refine (Set.finite_Iio (psum (segLen segs) (T.toNat + 1))).subset ?_
  rintro k ⟨y, t, e, he, hT⟩
  obtain ⟨s, p, rfl, rfl, hp⟩ := segEntry_eq_some he
  have hp1 : p < segLen segs s := (List.getElem?_eq_some_iff.1 hp).1
  have hs : s ≤ T.toNat := (Int.le_toNat (le_trans (Int.natCast_nonneg _) hT)).mpr hT
  have : psum (segLen segs) (s + 1) ≤ psum (segLen segs) (T.toNat + 1) :=
    psum_mono (segLen segs) (Nat.succ_le_succ hs)
  rw [psum_succ] at this
  rw [Set.mem_Iio]
  omega

/-- An event of the list of time `s` is an `ofSegs` entry at time `s`. -/
theorem ofSegs_entry_of_mem {s : Nat} {y : Fin P.n} {e : Event A} (h : (y, e) ∈ segs s) :
    ∃ k, (ofSegs segs awake horizon).entry k = some (y, (s : Time), e) := by
  obtain ⟨p, hp, hpe⟩ := List.getElem_of_mem h
  refine ⟨_, (segEntry_add hp).trans ?_⟩
  rw [hpe]

/-- With a tick of every honest node at every public time from `0` on, `ofSegs` has the tick
law. -/
theorem ofSegs_ticks {H : Set (Fin P.n)}
    (htick : ∀ y ∈ H, ∀ s : Nat, P.IsPublic s → ∃ x, (y, .tick x) ∈ segs s) :
    ∀ y ∈ H, ∀ t, 0 ≤ t → P.IsPublic t → (ofSegs segs awake horizon).awake y t →
      ∃ k x, (ofSegs segs awake horizon).entry k = some (y, t, .tick x) := by
  intro y hy t h0 hpub _
  have htt : ((t.toNat : Nat) : Time) = t := Int.toNat_of_nonneg h0
  obtain ⟨x, hx⟩ := htick y hy t.toNat (htt ▸ hpub)
  obtain ⟨k, hk⟩ := ofSegs_entry_of_mem (awake := awake) (horizon := horizon) hx
  exact ⟨k, x, htt ▸ hk⟩

/-- With the awake function `0 ≤ t`, no horizon, and a tick of every honest node at every public
time from `0` on, `ofSegs` has the horizon law. -/
theorem ofSegs_horizon {H : Set (Fin P.n)}
    (htick : ∀ y ∈ H, ∀ s : Nat, P.IsPublic s → ∃ x, (y, .tick x) ∈ segs s) :
    ∀ y ∈ H, ∀ t, (ofSegs segs (fun _ t => 0 ≤ t) none).awake y t →
      (∃ k y' t' e, (ofSegs segs (fun _ t => 0 ≤ t) none).entry k = some (y', t', e) ∧
        t ≤ t') ∨ ∃ T, (ofSegs segs (fun _ t => 0 ≤ t) none).horizon = some T ∧ t ≤ T := by
  intro y hy t ht
  have h0 : (0 : Time) ≤ t := ht
  have hΔ : 1 ≤ P.Δ := P.hΔ
  have hpub : P.IsPublic (P.Δ * t) := Dvd.intro t rfl
  have hle : t ≤ P.Δ * t := le_mul_of_one_le_left h0 hΔ
  obtain ⟨k, x, hk⟩ := ofSegs_ticks (awake := fun _ t => 0 ≤ t) (horizon := none) htick y hy
    (P.Δ * t) (le_trans h0 hle) hpub (le_trans h0 hle)
  exact Or.inl ⟨k, y, _, _, hk, hle⟩

/-- Event lists applied to the state `st` of `y` at time `t`. -/
noncomputable def segStep (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (y : Fin P.n) (t : Time) (st : NodeState A) (es : List (Fin P.n × Event A)) : NodeState A :=
  es.foldl (fun st xe => if xe.1 = y then (exec proposer dg xe.1 st t xe.2).1 else st) st

variable {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}

/-- Inside time `s`, the state of `y` is its state at the start of `s` advanced by the events of
`s` so far. -/
theorem ofSegs_stBefore_add (y : Fin P.n) (s : Nat) :
    ∀ p ≤ (segs s).length,
      (ofSegs segs awake horizon).stBefore proposer dg y (psum (segLen segs) s + p) =
        segStep proposer dg y s
          ((ofSegs segs awake horizon).stBefore proposer dg y (psum (segLen segs) s))
          ((segs s).take p) := by
  intro p hp
  induction p with
  | zero => simp [segStep]
  | succ p ih =>
    have hp' : p < (segs s).length := hp
    rw [← Nat.add_assoc, Schedule.stBefore_succ, ih hp'.le,
      Schedule.stepAt_some (segEntry_add hp'), List.take_add_one, segStep, segStep,
      List.foldl_append, List.getElem?_eq_getElem hp']
    rfl

/-- **The states of `ofSegs` advance one time at a time.** -/
theorem ofSegs_stBefore_succ (y : Fin P.n) (s : Nat) :
    (ofSegs segs awake horizon).stBefore proposer dg y (psum (segLen segs) (s + 1)) =
      segStep proposer dg y s
        ((ofSegs segs awake horizon).stBefore proposer dg y (psum (segLen segs) s)) (segs s) := by
  rw [psum_succ]
  exact (ofSegs_stBefore_add y s (segs s).length le_rfl).trans (by rw [List.take_length])

variable (proposer dg)

/-- A causal generator `gen t states` resolved: the node states at the start of each time. -/
noncomputable def genStates (gen : Nat → (Fin P.n → NodeState A) → List (Fin P.n × Event A)) :
    Nat → Fin P.n → NodeState A
  | 0 => fun _ => Node.init A
  | t + 1 => fun y => segStep proposer dg y t (genStates gen t y) (gen t (genStates gen t))

/-- The event lists of a causal generator: those of time `t` from the states at the start of
`t`. -/
noncomputable def genSegs (gen : Nat → (Fin P.n → NodeState A) → List (Fin P.n × Event A))
    (t : Nat) : List (Fin P.n × Event A) :=
  gen t (genStates proposer dg gen t)

/-- **The states of a causal generator's schedule** at the start of each time are
`genStates`. -/
theorem ofSegs_genSegs_stBefore
    (gen : Nat → (Fin P.n → NodeState A) → List (Fin P.n × Event A)) (y : Fin P.n) (t : Nat) :
    (ofSegs (genSegs proposer dg gen) awake horizon).stBefore proposer dg y
        (psum (segLen (genSegs proposer dg gen)) t) = genStates proposer dg gen t y := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [ofSegs_stBefore_succ, ih]
    rfl

end Segs

/-! ## Sanity check: the empty schedule -/

/-- The empty schedule: no entry, nobody awake. -/
def emptySchedule (A : NodeAC P) : Schedule A where
  entry _ := none
  prefix_closed _ _ := rfl
  awake _ _ := False
  horizon := none

/-- The empty schedule's trace has no labelled cut. -/
theorem emptySchedule_label (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (i : Nat) :
    ((emptySchedule A).trace proposer dg).label i = none := by
  cases h : ((emptySchedule A).trace proposer dg).label i with
  | none => rfl
  | some ℓ =>
    obtain ⟨k, y, t, e, p, he, -⟩ := Schedule.label_eq_some h
    cases he

/-- **The empty schedule's trace is a run** (`Node.LocalRun`), for any honest set and signer
map. -/
theorem empty_localRun (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Set (Fin P.n)) (sg : A.Msg → Fin P.n) :
    Node.LocalRun proposer dg H sg ((emptySchedule A).trace proposer dg) := by
  have hcall : ∀ y i c, ¬ ((emptySchedule A).trace proposer dg).CallAt y i c := fun y i c h => by
    rw [Trace.CallAt, emptySchedule_label] at h
    exact absurd h.2 (by simp)
  refine Schedule.trace_localRun
    { ne := fun _ _ _ _ he => by cases he
      mono := fun _ _ _ _ _ _ _ _ _ he => by cases he
      nonneg := fun _ _ _ _ he => by cases he
      phase := fun _ _ _ _ _ _ _ _ _ _ he => by cases he
      tick_public := fun _ _ _ _ _ he => by cases he
      tick_unique := fun _ _ _ _ _ _ _ he => by cases he
      ticks := fun _ _ _ _ _ haw => haw.elim
      awake_call := fun _ _ _ _ _ he => by cases he
      restart_of_sleep := fun _ _ _ _ _ _ he => by cases he
      restart_at_wake := fun _ _ _ _ _ _ _ hv => hv.elim
      sleep_of_restart := fun _ _ _ _ he => by cases he
      horizon := fun _ _ _ haw => haw.elim
      finite := fun _ => Set.finite_empty.subset fun _ ⟨_, _, _, he, _⟩ => by cases he
      wire := fun _ _ _ _ _ he => by cases he
      credential := fun _ _ _ _ _ he => by cases he } ?_ ?_ ?_
  · rintro y - i B ⟨acc, hc⟩
    exact absurd hc (hcall _ _ _)
  · rintro y - i a (hc | ⟨B, ⟨acc, hc⟩, -⟩)
    · exact absurd hc (hcall _ _ _)
    · exact absurd hc (hcall _ _ _)
  · rintro y - i m ⟨ℓ, hc, -⟩
    exact absurd hc (hcall _ _ _)

end Consensus.Goldilocks.Test.ScheduleRun

end
