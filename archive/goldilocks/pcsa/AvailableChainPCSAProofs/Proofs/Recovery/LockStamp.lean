module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockOverlap
public import AvailableChainPCSAProofs.Proofs.Recovery.RunInputs
public import AvailableChainPCSAProofs.Proofs.Shared.StageRun

public section

/-! PC stamp history for the last-write rank witness. -/
namespace AvailableChain.PCSA

private def LockStampHistory {n : Nat} (src dst : State n) : Prop :=
  ∀ row ∈ dst.pcStamps, row ∈ src.pcStamps ∨
    row.2.2 = src.base.now ∧ ∃ C ∈ dst.pcs,
      C.slot = row.1 ∧ C.target.root = row.2.1

private theorem lock_stamp_install {n : Nat} (src st : State n) (C : PC n)
    (h : LockStampHistory src st) (hn : st.base.now = src.base.now) :
    LockStampHistory src (installPC st C) := by
  rw [installPC_def]
  split
  · exact h
  · intro row hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases h row (List.mem_filter.mp hr).1 with ho | ⟨ht, D, hD, hs, hb⟩
      · exact Or.inl ho
      · exact Or.inr ⟨ht, D, List.mem_append_left _ hD, hs, hb⟩
    · cases List.mem_singleton.mp hr
      exact Or.inr ⟨hn, C, List.mem_append_right _ (by simp), rfl, rfl⟩

private theorem lock_stamp_collect {n : Nat} (src st : State n)
    (h : LockStampHistory src st) (hn : st.base.now = src.base.now) :
    LockStampHistory src (collectPCs st) := by
  have hh := collectPCs_invariant
    (fun st => LockStampHistory src st ∧ st.base.now = src.base.now)
    (fun st C h _ => ⟨lock_stamp_install src st C h.1 h.2,
      (installPC_frame st C).1.trans h.2⟩) st ⟨h, hn⟩
  exact hh.1

private theorem lock_stamp_raw {n : Nat} (st : State n) (a : AckWire n) :
    (poolAckRaw st a).pcStamps = st.pcStamps ∧
    (poolAckRaw st a).pcs = st.pcs ∧ (poolAckRaw st a).base.now = st.base.now := by
  delta poolAckRaw
  cases a.decode? <;> dsimp only
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl⟩

private theorem lock_stamp_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).pcStamps = st.pcStamps ∧ (admitRow p st a).pcs = st.pcs := by
  delta admitRow
  cases a.decode? <;> dsimp only
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

private theorem lock_stamp_norm {n : Nat} (st : State n) :
    (normalizeS st).pcStamps = st.pcStamps := by
  delta normalizeS
  split <;> rfl

private theorem lock_stamp_reconcile {n : Nat} (st : State n) :
    (reconcile st).pcStamps = st.pcStamps := by
  delta reconcile
  rw [lock_stamp_norm]

/-- A new stamp comes from a PC held after this delivery, at the pre-step clock. -/
theorem recovery_process_pc_stamp_origin (p : Params) (st : State p.n) (o : Wire p.n)
    (row : Slot × BlockId × Time) (hr : row ∈ (process p st o).pcStamps) :
    row ∈ st.pcStamps ∨ row.2.2 = st.base.now ∧
      ∃ C ∈ (process p st o).pcs, C.slot = row.1 ∧ C.target.root = row.2.1 := by
  suffices h : LockStampHistory st (process p st o) from h row hr
  have ha (src acc : State p.n) (as : List (AckWire p.n))
      (h : LockStampHistory src acc) (hn : acc.base.now = src.base.now) :
      LockStampHistory src (as.foldl poolAckRaw acc) ∧
        (as.foldl poolAckRaw acc).base.now = src.base.now := by
    apply List.foldlRecOn (motive := fun acc =>
      LockStampHistory src acc ∧ acc.base.now = src.base.now) as poolAckRaw ⟨h, hn⟩
    intro acc hh a _
    obtain ⟨h1, h2, h3⟩ := lock_stamp_raw acc a
    exact ⟨by dsimp only [LockStampHistory] at *; simpa only [h1, h2] using hh.1, h3.trans hh.2⟩
  have hb (src acc : State p.n) (as : List (RowWire p.n))
      (h : LockStampHistory src acc) : LockStampHistory src (as.foldl (admitRow p) acc) := by
    apply List.foldlRecOn as (admitRow p) h
    intro acc hh a _
    obtain ⟨h1, h2⟩ := lock_stamp_row p acc a
    dsimp only [LockStampHistory] at *
    simpa only [h1, h2] using hh
  have hid : LockStampHistory st st := fun _ hr => Or.inl hr
  delta process
  cases hd : o.decode with
  | none => exact hid
  | some msg => cases msg with
    | vote s i r => exact fun _ hr => Or.inl hr
    | row i body =>
      dsimp only [LockStampHistory] at *
      simpa only [(lock_stamp_row p st _).1,
        (lock_stamp_row p st _).2] using hid
    | ack s i r =>
      dsimp only
      delta admitAck
      apply lock_stamp_collect
      · delta poolAck
        cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
        · exact hid
        · rename_i v
          rcases v with ⟨_, _, _⟩
          split
          · exact hid
          · split <;> exact hid
      · exact (pcsa_poolAck_frame p st _).2.2.2.2 |> congrArg GridCO.State.now
    | pc C =>
      dsimp only
      delta admitPC
      split
      · exact lock_stamp_collect st _ (ha st st C.acks hid rfl).1
          (ha st st C.acks hid rfl).2
      · exact hid
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact hid
      · cases hp : parentFG st N.erase
        · exact hid
        · dsimp only
          split
          · apply hb
            apply lock_stamp_collect
            · apply (ha _ _ _ ?_ ?_).1
              · cases N.pc <;> dsimp only <;> split_ifs <;>
                  first
                  | (intro row hr; exact Or.inl hr)
                  | (intro row hr; rw [lock_stamp_reconcile] at hr; exact Or.inl hr)
              · cases N.pc <;> dsimp only <;> split_ifs <;>
                  try (delta reconcile normalizeS; dsimp only; split)
                all_goals exact FGSA.Run.Internal.grid_admitProposal_now _ _ _ _
            · apply (ha _ _ _ ?_ ?_).2
              · cases N.pc <;> dsimp only <;> split_ifs <;>
                  first
                  | (intro row hr; exact Or.inl hr)
                  | (intro row hr; rw [lock_stamp_reconcile] at hr; exact Or.inl hr)
              · cases N.pc <;> dsimp only <;> split_ifs
                all_goals try (delta reconcile normalizeS; dsimp only; split)
                all_goals exact FGSA.Run.Internal.grid_admitProposal_now _ _ _ _
          · exact hid

/-- The clock does not create or change PC stamps. -/
theorem recovery_clock_pcStamps (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).pcStamps = st.pcStamps := by
  have hg (a : Block) (cs : List (PC p.n)) (rank : Option PCRank)
      (st : State p.n) (s : Slot) : (gateFrom p a cs rank st s).pcStamps = st.pcStamps := by
    rw [gateFrom_def]
    dsimp only
    cases SA.Root.confirmationFrom p.toParams a (actView st) s
    · rfl
    · dsimp only
      split
      · rfl
      · apply List.foldlRecOn (motive := fun acc : State p.n => acc.pcStamps = st.pcStamps)
        · rfl
        · intro acc hh b _
          apply List.foldlRecOn (motive := fun acc : State p.n => acc.pcStamps = st.pcStamps)
          · exact hh
          · intro acc' hh' g _
            exact hh'
  delta clock
  dsimp only
  split
  · rw [gateStep_def, lock_stamp_norm]
    split
    · exact clockPre_pcStamps p st t
    · rw [hg, clockPre_pcStamps]
  · exact clockPre_pcStamps p st t

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every stored PC stamp identifies an earlier delivery and a held key after it. -/
theorem recovery_pc_stamp_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V)
    (row : Slot × BlockId × Time)
    (hm : row ∈ (V2.D.Run.stateBefore E rho k x).st.pcStamps) :
    ∃ j < k, ∃ t o, rho.events[j]? = some (.deliver x o t) ∧
      row.2.2 = (V2.D.Run.stateBefore E rho j x).st.base.now ∧
      ∃ C ∈ (V2.D.Run.stateBefore E rho (j + 1) x).st.pcs,
        C.slot = row.1 ∧ C.target.root = row.2.1 := by
  induction k with
  | zero => exact (List.not_mem_nil hm).elim
  | succ k ih =>
    have carry (hm : row ∈ (V2.D.Run.stateBefore E rho k x).st.pcStamps) :
        ∃ j < k + 1, ∃ t o, rho.events[j]? = some (.deliver x o t) ∧
          row.2.2 = (V2.D.Run.stateBefore E rho j x).st.base.now ∧
          ∃ C ∈ (V2.D.Run.stateBefore E rho (j + 1) x).st.pcs,
            C.slot = row.1 ∧ C.target.root = row.2.1 := by
      obtain ⟨j, hj, rest⟩ := ih hm
      exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    cases he : rho.events[k]? with
    | none =>
      have hs : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
        delta V2.D.Run.stateBefore
        rw [List.take_add_one, he]
        simp only [Option.toList_none, List.append_nil]
      exact carry (hs ▸ hm)
    | some e =>
      rw [V2.D.Run.stateBefore_succ E rho he] at hm
      by_cases hx : e.node = x
      · cases e with
        | restart y t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcStamps at hm
          rw [Function.update_self] at hm
          exact (List.not_mem_nil hm).elim
        | tick y t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcStamps at hm
          rw [Function.update_self, pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t,
            recovery_clock_pcStamps] at hm
          exact carry hm
        | deliver y o t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcStamps at hm
          rw [Function.update_self] at hm
          rcases recovery_process_pc_stamp_origin p _ (toWire p o) row hm with hm | ⟨ht, hc⟩
          · exact carry hm
          · refine ⟨k, Nat.lt_succ_self k, t, o, he, ht, ?_⟩
            rw [V2.D.Run.stateBefore_succ E rho he]
            change ∃ C ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcs, _
            rw [Function.update_self]
            exact hc
      · apply carry
        rwa [V2.D.World.step_apply_of_node_ne E rho _ hx] at hm

/-- A stamp before a public cutoff gives a matching key held before that cutoff.
The result identifies the slot and root; collision freedom identifies the body. -/
theorem recovery_pc_stamp_before_cut (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hF : StageOneFrame p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (C : PC p.n)
    (cut stamp : Time) (hpub : V2.PublicTime E cut) (hzero : 0 ≤ cut)
    (hst : pcStamp? (V2.D.Run.stateBefore E rho k x).st C = some stamp)
    (hlt : stamp < cut) :
    ∃ D ∈ (V2.D.Run.stateBeforeTime E rho cut x).st.pcs,
      D.slot = C.slot ∧ D.target.root = C.target.root := by
  rw [pcStamp?_def] at hst
  obtain ⟨row, hr, he⟩ := Option.map_eq_some_iff.mp hst
  have hkey := List.find?_some hr
  obtain ⟨hslot, hroot⟩ := Bool.and_eq_true_iff.mp hkey
  have hslot : row.1 = C.slot := beq_iff_eq.mp hslot
  have hroot : row.2.1 = C.target.root := beq_iff_eq.mp hroot
  obtain ⟨j, _, t, o, hj, ht, D, hD, hdslot, hdroot⟩ :=
    recovery_pc_stamp_source E rho k x row (List.mem_of_find?_eq_some hr)
  have htc : t < cut := by
    by_contra hn
    have hc := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho hs hnr
      hj hpub hzero (le_of_not_gt hn)
    rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)] at hc
    have hh : row.2.2 < cut := he ▸ hlt
    rw [ht] at hh
    exact (not_lt.mpr hc) hh
  have hji : j + 1 ≤ V2.D.Run.idxBefore rho cut := by
    exact Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj cut).mpr htc)
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho cut hs]
  exact ⟨D, recovery_pcs_mono E rho hnr hF x hx hji hD,
    hdslot.trans hslot, hdroot.trans hroot⟩

/-- The nonempty gate rank was held before the early cutoff, with the same body. -/
theorem recovery_gate_rank_before_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hF : StageOneFrame p c E rho) (hΔ : E.Δ = p.Δ)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (s : Slot) (rank : PCRank)
    (hrank : gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)) s = some rank) :
    ∃ D ∈ (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) x).st.pcs,
      D.rank = rank := by
  obtain ⟨C, hC, hCr, _, stamp, hstamp, hst⟩ := recovery_gate_rank_witness p _ s rank hrank
  rw [clockPre_pcs] at hC
  have hst' : pcStamp? (V2.D.Run.stateBefore E rho k x).st C = some stamp := by
    simpa only [pcStamp?_def, clockPre_pcStamps] using hst
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [hΔ]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = ((4 * s + 2 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hzero : 0 ≤ SA.earlyTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  obtain ⟨D, hD, hDs, hDr⟩ := recovery_pc_stamp_before_cut E rho hs hnr hF
    k x hx C _ stamp hpub hzero hst' hstamp
  have hD' := hD
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hD'
  have he := transport.rootResolution x hx x hx (V2.D.Run.idxBefore rho _) k D.target C.target
    ((pcsa_outageStore_stateBefore E rho _ x hx).pcBlocks D hD')
    ((pcsa_outageStore_stateBefore E rho k x hx).pcBlocks C hC) hDr
  refine ⟨D, hD, ?_⟩
  rw [← hCr]
  simp only [PC.rank_def, hDs, he]

/-- The gate rank's key reaches every honest node strictly before the freeze. -/
theorem recovery_gate_rank_disseminated (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hF : StageOneFrame p c E rho) (hΔ : E.Δ = p.Δ)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (rank : PCRank) (hg : E.t_GST ≤ SA.earlyTime p.toParams s)
    (horizon : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hrank : gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)) s = some rank) :
    ∃ D ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.pcs,
      D.rank = rank := by
  obtain ⟨C, hC, hr⟩ := recovery_gate_rank_before_early E rho hs hnr hF hΔ
    g transport k x hx s rank hrank
  have he : SA.earlyTime p.toParams s + p.Δ = SA.freezeTime p.toParams s := by
    change (4 * p.Δ * (s : Int) + 2 * p.Δ) + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hk := transport.pcReceipt _ ⟨s, Or.inl rfl⟩ hg (by rwa [he]) x hx y hy C hC
  rw [he] at hk
  obtain ⟨D, hD, hDs, hDt⟩ := (KeyHeld_def _ _ _).mp hk
  exact ⟨D, hD, by simpa only [PC.rank_def, hDs, hDt] using hr⟩

end AvailableChain.PCSA.Run
end
