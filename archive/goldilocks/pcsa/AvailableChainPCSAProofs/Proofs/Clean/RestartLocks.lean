module
public import AvailableChainPCSAProofs.Proofs.Clean.RestartRecord
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents
public import AvailableChainPCSAProofs.Proofs.Clean.AckDecisions
public import AvailableChainPCSAProofs.Proofs.Clean.StorePCInputs
public import AvailableChainPCSAProofs.Proofs.Shared.LockRankSafe

public section

/-! K2 of the CI restart: from `z_a` to the input of gate `a`, every stored lock is
below the seed block. A stored lease rank comes from an earlier own gate `s' < a`,
so the held seed PC of slot `a` ranks above it; rank safety makes the lock
compatible with the seed, and the slot bound of its result excludes the other
order. -/
namespace AvailableChain.PCSA
variable {n : Nat}

private def RanksAre (L : List (Block × Option PCRank)) (st : State n) : Prop :=
  st.leaseRanks = L

private theorem ranks_install (st : State n) (pc : PC n) :
    (installPC st pc).leaseRanks = st.leaseRanks := by
  rw [installPC_def]
  split <;> rfl

private theorem ranks_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).leaseRanks = st.leaseRanks := by
  delta admitRow
  cases a.decode? <;> dsimp only
  split <;> rfl

private theorem ranks_raw (st : State n) (a : AckWire n) :
    (poolAckRaw st a).leaseRanks = st.leaseRanks := by
  delta poolAckRaw
  cases a.decode? <;> dsimp only
  split <;> rfl

/-- A delivery keeps the stored lease ranks. -/
theorem pcsa_process_leaseRanks (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).leaseRanks = st.leaseRanks := by
  have hc := collectPCs_invariant (n := p.n) (RanksAre st.leaseRanks)
    (fun st' pc h _ => (ranks_install st' pc).trans h)
  have ha (st' : State p.n) (as : List (AckWire p.n)) (h : RanksAre st.leaseRanks st') :
      RanksAre st.leaseRanks (as.foldl poolAckRaw st') :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => (ranks_raw acc a).trans hh)
  change RanksAre st.leaseRanks (process p st o)
  delta process
  cases hd : o.decode with
  | none => rfl
  | some msg => cases msg with
    | vote s i r => rfl
    | row i body => exact ranks_row p st _
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · rfl
      · cases hp : parentFG st N.erase
        · rfl
        · dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | rfl
                | (delta reconcile normalizeS; dsimp only; split <;> rfl)
            · intro acc hh a _
              exact (ranks_row p acc a).trans hh
          · rfl
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      · rfl
      · rename_i v
        rcases v with ⟨_, _, _⟩
        split
        · rfl
        · split <;> rfl
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ rfl)
      · rfl

/-- A gate stores only lease ranks that were stored or equal to its write rank. -/
theorem pcsa_gateFrom_leaseRanks (p : Params) (st : State p.n) (a : Block)
    (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot) :
    ∀ e ∈ (gateFrom p a cs rank st s).leaseRanks, e ∈ st.leaseRanks ∨ e.2 = rank := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · exact fun e he => Or.inl he
  · dsimp only
    split
    · exact fun e he => Or.inl he
    · apply List.foldlRecOn (motive := fun acc : State p.n =>
        ∀ e ∈ acc.leaseRanks, e ∈ st.leaseRanks ∨ e.2 = rank)
      · exact fun e he => Or.inl he
      · intro acc hh b _
        apply List.foldlRecOn (motive := fun acc' : State p.n =>
          ∀ e ∈ acc'.leaseRanks, e ∈ st.leaseRanks ∨ e.2 = rank)
        · exact hh
        · intro acc' hh' g _ e he
          change e ∈ acc'.leaseRanks.filter (fun row => row.1 != b) ++ [(b, rank)] at he
          rcases List.mem_append.mp he with he | he
          · exact hh' e (List.mem_filter.mp he).1
          · rw [List.mem_singleton.mp he]
            exact Or.inr rfl

/-- A tick stores only lease ranks that were stored or are the gate rank of its gate. -/
theorem pcsa_clock_leaseRanks (p : Params) (st : State p.n) (t : Time) :
    ∀ e ∈ (clock p st t).leaseRanks, e ∈ st.leaseRanks ∨
      ∃ s, t = SA.gateTime p.toParams s ∧ e.2 = gateRank p (clockPre p st t) s := by
  have hpre : (clockPre p st t).leaseRanks = st.leaseRanks := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  have hn (st : State p.n) : (normalizeS st).leaseRanks = st.leaseRanks := by
    delta normalizeS
    split <;> rfl
  delta clock
  dsimp only
  split
  · rename_i hg
    have he : t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat :=
      eq_of_beq (Bool.and_eq_true_iff.mp hg).2
    rw [gateStep_def]
    dsimp only
    rw [hn]
    split
    · intro e he'
      exact Or.inl (hpre ▸ he')
    · intro e he'
      rcases pcsa_gateFrom_leaseRanks p _ _ _ _ _ e he' with hm | hr
      · exact Or.inl (hpre ▸ hm)
      · exact Or.inr ⟨_, he, hr⟩
  · intro e he'
    exact Or.inl (hpre ▸ he')

/-- A nonempty gate rank is the rank of a held PC. -/
theorem pcsa_gateRank_mem (p : Params) (st : State p.n) (s : Slot) (r : PCRank)
    (hr : gateRank p st s = some r) : ∃ C ∈ st.pcs, C.rank = r := by
  rw [gateRank_def] at hr
  obtain ⟨C, hC, he⟩ := Option.map_eq_some_iff.mp hr
  exact ⟨C, (List.mem_filter.mp (bestPC_mem _ C hC)).1, he⟩

/-- A stored lease rank is an entry of the rank list. -/
theorem pcsa_leaseRank_mem (st : State n) (b : Block) (r : PCRank)
    (hr : leaseRank st b = some r) : ∃ e ∈ st.leaseRanks, e.2 = some r := by
  rw [leaseRank_def] at hr
  cases hf : st.leaseRanks.find? (fun row => row.1 == b) with
  | none =>
    rw [hf] at hr
    cases hr
  | some e =>
    rw [hf] at hr
    exact ⟨e, List.mem_of_find?_eq_some hf, hr⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- Every stored lease rank of an honest node was written by an earlier own gate whose
label bounds the rank slot. -/
theorem pcsa_leaseRanks_gate_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (x : V) (hx : x ∈ rho.honest) (k : Nat) :
    ∀ e ∈ (V2.D.Run.stateBefore E rho k x).st.leaseRanks, ∀ r, e.2 = some r →
      ∃ j < k, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
        r.slot ≤ s := by
  have hs := h.valid.toScheduleWellFormed
  induction k with
  | zero =>
    intro e he
    exact absurd he List.not_mem_nil
  | succ k ih =>
    have carry (hsub : ∀ e ∈ (V2.D.Run.stateBefore E rho (k + 1) x).st.leaseRanks,
        e ∈ (V2.D.Run.stateBefore E rho k x).st.leaseRanks) :
        ∀ e ∈ (V2.D.Run.stateBefore E rho (k + 1) x).st.leaseRanks, ∀ r, e.2 = some r →
          ∃ j < k + 1, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
            r.slot ≤ s := by
      intro e he r hr
      obtain ⟨j, hj, rest⟩ := ih e (hsub e he) r hr
      exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    cases hev : rho.events[k]? with
    | none =>
      apply carry
      have hsame : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
        delta V2.D.Run.stateBefore
        rw [List.take_add_one, hev]
        simp only [Option.toList_none, List.append_nil]
      rw [hsame]
      exact fun e he => he
    | some ev =>
      have hstep := V2.D.Run.stateBefore_succ E rho hev
      by_cases hn : ev.node = x
      · cases ev with
        | restart y t => exact (h.noRestart k y t hev).elim
        | deliver y o t =>
          change y = x at hn
          subst y
          apply carry
          intro e he
          rw [hstep] at he
          change e ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.leaseRanks at he
          rw [Function.update_self] at he
          change e ∈ (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).leaseRanks at he
          rwa [pcsa_process_leaseRanks] at he
        | tick y t =>
          change y = x at hn
          subst y
          have hclock : (V2.D.Run.stateBefore E rho (k + 1) x).st =
              clock p (V2.D.Run.stateBefore E rho k x).st t := by
            rw [hstep, pcsa_tick_step]
          intro e he r hr
          rw [hclock] at he
          rcases pcsa_clock_leaseRanks p _ t e he with hm | ⟨s, ht, hrank⟩
          · obtain ⟨j, hj, rest⟩ := ih e hm r hr
            exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
          · rw [hr] at hrank
            obtain ⟨C, hC, hCr⟩ := pcsa_gateRank_mem p _ s r hrank.symm
            have hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)) := ht ▸ hev
            rw [clockPre_pcs] at hC
            have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.noRestart hk
            rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hpre
            rw [hpre] at hC
            obtain ⟨_, _, _, hte⟩ := pcsa_pc_honest_ack_before E rho h hFault _ x hx _
              (le_refl _) C hC
            refine ⟨k, Nat.lt_succ_self k, s, hk, ?_⟩
            rw [← hCr]
            exact pcsa_early_label_before_gate p C.slot s hte
      · apply carry
        have hh := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hn
        rw [hstep, hh]
        exact fun e he => he

omit [Fintype V] in
/-- A PC stamped before `t` is held at every index from the strict cut of `t`. -/
theorem pcsa_stamped_held_from (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (t : Time) (s : Slot) (B : Block) (hp : PCStampedBefore p c E rho x t s B)
    (i : Nat) (hi : rho.events[i]? = some (.tick x t))
    (k : Nat) (hk : V2.D.Run.idxBefore rho t ≤ k) :
    ∃ C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs, C.slot = s ∧ C.target = B := by
  have hs := h.valid.toScheduleWellFormed
  obtain ⟨C, hC, hslot, hb⟩ := hp
  have hr : storeAfterTicks p c E rho x t = clock p (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho t) x).st t := by
    change (FGSA.Run.afterTicks E rho t x).st = _
    rw [FGSA.Run.afterTicks_node E rho hs hi]
    refine (pcsa_tick_st E rho _ x t).trans ?_
    rw [V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.noRestart hi,
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
  rw [hr, pcsa_clock_pcs] at hC
  exact ⟨C, pcsa_run_pcs_mono E rho hf h.noRestart x hx _ _ hk hC, hslot, hb⟩

/-- K2: from `z_a` to the input of gate `a`, every stored lock of an honest node is
below the seed block. -/
theorem pcsa_restart_locks_from_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (a : Slot) (A : Block) (hslot : A.slot = a)
    (hstamp : ∀ x ∈ rho.honest, PCStampedBefore p c E rho x (SA.freezeTime p.toParams a) a A)
    (hz : SA.freezeTime p.toParams a ≤ rho.horizon) :
    ∀ x ∈ rho.honest, ∀ k, V2.D.Run.idxBefore rho (SA.freezeTime p.toParams a) ≤ k →
      k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams a) →
      ∀ row ∈ (V2.D.Run.stateBefore E rho k x).st.base.obligations, Block.Preceq row.1 A := by
  intro x hx k hzk hkd row hr
  have hs := h.valid.toScheduleWellFormed
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams a) := by
    refine ⟨4 * a + 3, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (a : Int) + 3 * p.Δ = ((4 * a + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz0 : 0 ≤ SA.freezeTime p.toParams a := by
    change 0 ≤ 4 * p.Δ * (a : Int) + 3 * p.Δ
    positivity
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (h.valid.tick_total x hx _ hpub hz0 hz)
  obtain ⟨C₀, hC₀, hC₀s, hC₀t⟩ := pcsa_stamped_held_from E rho h hF x hx _ a A
    (hstamp x hx) i hi k hzk
  -- A gate event before `k` has a label below `a`.
  have below (j : Nat) (hj : j < k) (s : Slot)
      (hev : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s))) : s < a := by
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hev _).mp (hj.trans_le hkd)
    by_contra hn
    exact absurd (pcsa_gate_time_mono p (Nat.le_of_not_gt hn)) (not_le.mpr ht)
  obtain ⟨j, hj, s', Y, hev, hY, hrowY, _⟩ := pcsa_lock_stateBefore_origin E rho h k x row hr
  have hs' := below j hj s' hev
  have hrank : rankAtLeast C₀ (leaseRank (V2.D.Run.stateBefore E rho k x).st row.1) = true := by
    cases hl : leaseRank (V2.D.Run.stateBefore E rho k x).st row.1 with
    | none => rfl
    | some r =>
      obtain ⟨e, he, her⟩ := pcsa_leaseRank_mem _ row.1 r hl
      obtain ⟨j', hj', s'', hev', hrs⟩ :=
        pcsa_leaseRanks_gate_slot E rho h hFault x hx k e he r her
      have hlt : r.slot < C₀.slot := hC₀s ▸ (hrs.trans_lt (below j' hj' s'' hev'))
      rw [rankAtLeast_def]
      simp [Nat.not_lt.mpr hlt.le, Nat.ne_of_gt hlt]
  have hcomp := pcsa_lock_rank_compatible p _ (pcsa_reachable_stateBefore E rho k x) row hr
    C₀ hC₀ hrank
  rw [hC₀t] at hcomp
  rcases Bool.or_eq_true_iff.mp hcomp with hAr | hrA
  · exfalso
    obtain ⟨i', _, hc⟩ := pcsa_gateResultAt_source E rho x s' Y hY
    have hord := pcsa_reachable_slot_order p _
      (Reachable.tick (SA.gateTime p.toParams s') (pcsa_reachable_stateBefore E rho i' x))
    have hAs := pcsa_result_prefix_slot p _ _ Y A s'
      (fun D hD => hord D (List.mem_filter.mp hD).1) hc
      (Gen.Pure.block_preceq_trans hAr hrowY)
    rw [hslot] at hAs
    exact absurd hAs (Nat.not_le.mpr hs')
  · exact hrA

/-- The restart seed from its formation facts: K2 supplies the lock field. -/
theorem pcsa_cleanRestartSeed_mk (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (a : Slot) (A : Block) (hpos : 0 < a) (hslot : A.slot = a)
    (hstamp : ∀ x ∈ rho.honest, PCStampedBefore p c E rho x (SA.freezeTime p.toParams a) a A)
    (hheads : ∀ x H, HonestHeadAt p c E rho x a H → H = A)
    (hprop : ∀ P, Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface
      rho a P → P = A)
    (hres : ∀ x ∈ rho.honest, ∀ R, gateResultAt p c E rho x a = some R → R = some A)
    (harm : ArmConcl p c E rho a A (a + 1))
    (hz : SA.freezeTime p.toParams a ≤ rho.horizon) :
    CleanRestartSeed p c E rho a A :=
  ⟨hpos, hslot, hstamp, hheads, hprop, hres,
    pcsa_restart_locks_from_freeze E rho h hF hFault a A hslot hstamp hz, harm⟩
end AvailableChain.PCSA.Run

end
