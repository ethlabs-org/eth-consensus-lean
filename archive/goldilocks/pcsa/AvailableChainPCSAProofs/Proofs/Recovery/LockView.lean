module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockStamp
public import AvailableChainPCSAProofs.Proofs.Shared.VoterView

public section

/-! The rank lower bound in later voter views. -/
namespace AvailableChain.PCSA

/-- A best-PC choice is at least the rank of each candidate. -/
theorem recovery_bestPC_rank_bound {n : Nat} (cs : List (PC n)) (C D : PC n)
    (hC : C ∈ cs) (hD : bestPC cs = some D) : rankAtLeast D (some C.rank) = true := by
  have h := pcsa_bestPC_rank_max cs C D hC hD
  rw [rankAtLeast_def, Option.all_some, PC.rank_def]
  change (!pcBelow D C) = true
  simpa only [Bool.not_eq_true'] using h

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A post-clock store is the store after its actual local tick event. -/
theorem recovery_postClock_index (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) :
    ∃ i, rho.events[i]? = some (.tick x t) ∧
      nd.st = (V2.D.Run.stateBefore E rho (i + 1) x).st := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hn
  obtain ⟨nd0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hn0
  have he := V2.D.Run.tickIdx?_spec hi
  refine ⟨i, he, ?_⟩
  rw [V2.D.Run.stateBefore_succ E rho he]
  change (clock p (V2.D.Run.stateBefore E rho i x).st t) =
    (Function.update (V2.D.Run.stateBefore E rho i) x _ x).st
  rw [Function.update_self]
  exact (pcsa_tick_st E rho (V2.D.Run.stateBefore E rho i x) x t).symm

omit [DecidableEq V] in
private theorem lock_view_idx_mono (rho : V2.D.Run V (pcsaWith m p c)) {a b : Time}
    (hab : a ≤ b) : V2.D.Run.idxBefore rho a ≤ V2.D.Run.idxBefore rho b := by
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (lt_of_lt_of_le (of_decide_eq_true he) hab))

/-- A PC held before a freeze is in that snapshot at every later honest read. -/
theorem recovery_frozen_pc_at_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hF : StageOneFrame p c E rho) (hΔ : E.Δ = p.Δ)
    (x : V) (hx : x ∈ rho.honest) (s : Slot) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) (ht : SA.freezeTime p.toParams s < t)
    (C : PC p.n)
    (hC : C ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) x).st.pcs) :
    C ∈ pcSnapshotAt nd.st s := by
  obtain ⟨q, hq, hnd⟩ := recovery_postClock_index E rho x t nd hn
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [hΔ]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = ((4 * s + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hzero : 0 ≤ SA.freezeTime p.toParams s := by
    have hd := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    positivity
  have hh := (hs.in_horizon _ (List.mem_of_getElem? hq)).2
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
    (hs.tick_total x hx _ hpub hzero (ht.le.trans hh))
  have hji : j < V2.D.Run.idxBefore rho t :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hj t).mpr ht
  have hiq : V2.D.Run.idxBefore rho t ≤ q := by
    apply Nat.le_of_not_lt
    intro hlt
    exact lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hs hq t).mp hlt)
  have hstep : (V2.D.Run.stateBefore E rho (j + 1) x).st =
      clock p (V2.D.Run.stateBefore E rho j x).st (SA.freezeTime p.toParams s) := by
    rw [V2.D.Run.stateBefore_succ E rho hj]
    change (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st = _
    rw [Function.update_self]
    exact pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x _
  have hm : C ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho (j + 1) x).st s := by
    rw [hstep, clock_freeze_snapshot p _ s (snapshot_absent_before_tick E rho hs.nodup j x s hj),
      clock_pcs_eq, V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs hnr hj]
    exact hC
  have hp : ((V2.D.Run.stateBefore E rho (j + 1) x).st.pcSnapshot.find?
      (fun row => row.1 == s)).isSome := by
    cases he : (V2.D.Run.stateBefore E rho (j + 1) x).st.pcSnapshot.find?
        (fun row => row.1 == s) with
    | none => rw [pcSnapshotAt_absent _ _ he] at hm; exact (List.not_mem_nil hm).elim
    | some row => rfl
  have he := (pcsa_stageOne_mono E rho hnr hF x hx
    (show j + 1 ≤ q + 1 by omega)).2 s hp
  rwa [hnd, he.1]

/-- A nonempty gate rank occurs in every later voter's active frozen candidates. -/
theorem recovery_gate_rank_voter_candidate (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hF : StageOneFrame p c E rho) (hΔ : E.Δ = p.Δ)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s r : Slot) (hsr : s < r) (rank : PCRank)
    (hg : E.t_GST ≤ SA.earlyTime p.toParams s) (nd : Node p)
    (hn : pcsa_postClock E rho y (SA.voteTime p.toParams r) = some nd)
    (hrank : gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)) s = some rank) :
    ∃ C ∈ (pcSnapshotAt nd.st (r - 1) ++ carriedPCs nd.st r).filter (frameActive p nd.st),
      C.rank = rank := by
  try delta Slot at *
  have hd := p.deltaPos
  have hsr' : (s : Int) ≤ ((r - 1 : Nat) : Int) := by omega
  have hr' : ((r - 1 : Nat) : Int) + 1 = (r : Int) := by omega
  have hzz : SA.freezeTime p.toParams s ≤ SA.freezeTime p.toParams (r - 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((r - 1 : Nat) : Int) + 3 * p.Δ
    nlinarith
  have hzv : SA.freezeTime p.toParams (r - 1) < SA.voteTime p.toParams r := by
    change 4 * p.Δ * ((r - 1 : Nat) : Int) + 3 * p.Δ < 4 * p.Δ * (r : Int) + p.Δ
    nlinarith
  obtain ⟨q, hq, hnd⟩ := recovery_postClock_index E rho y _ nd hn
  have horizon := (hzz.trans hzv.le).trans (hs.in_horizon _ (List.mem_of_getElem? hq)).2
  obtain ⟨C, hC, hCr⟩ := recovery_gate_rank_disseminated E rho hs hnr hF hΔ
    g transport k x y hx hy s rank hg horizon hrank
  have hC' : C ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r - 1)) y).st.pcs := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hC ⊢
    exact recovery_pcs_mono E rho hnr hF y hy (lock_view_idx_mono rho hzz) hC
  have hmem := recovery_frozen_pc_at_read E rho hs hnr hF hΔ y hy (r - 1) _ nd hn hzv C hC'
  have hO := pcsa_outageStore_stateBefore E rho (q + 1) y hy
  have hheld : C ∈ (V2.D.Run.stateBefore E rho (q + 1) y).st.pcs := by
    rw [hnd] at hmem
    delta pcSnapshotAt at hmem
    cases he : (V2.D.Run.stateBefore E rho (q + 1) y).st.pcSnapshot.find?
        (fun row => row.1 == r - 1) with
    | none => rw [he] at hmem; exact (List.not_mem_nil hmem).elim
    | some row =>
      rw [he] at hmem
      exact hO.snapSub row (List.mem_of_find?_eq_some he) C hmem
  refine ⟨C, List.mem_filter.mpr ⟨List.mem_append_left _ hmem, ?_⟩, hCr⟩
  rw [hnd]
  exact (pcsa_frameActive_vacuous p _ (hF y hy (q + 1)) C).mpr
    (hO.lift C.target (hO.pcBlocks C hheld))

/-- Every selected later voter PC is at least the pending or surviving write rank. -/
theorem recovery_voter_rank_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hF : StageOneFrame p c E rho) (hΔ : E.Δ = p.Δ)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s r : Slot) (hsr : s < r) (hg : E.t_GST ≤ SA.earlyTime p.toParams s)
    (nd : Node p) (hn : pcsa_postClock E rho y (SA.voteTime p.toParams r) = some nd)
    (D : PC p.n) (hD : voterPC p nd.st r = some D) :
    rankAtLeast D (gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)) s) = true := by
  cases hr : gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)) s with
  | none => rw [rankAtLeast_def]; rfl
  | some rank =>
    obtain ⟨C, hC, hCr⟩ := recovery_gate_rank_voter_candidate E rho hs hnr hF hΔ
      g transport k x y hx hy s r hsr rank hg nd hn hr
    rw [← hCr]
    exact recovery_bestPC_rank_bound _ C D hC hD


/-- A selected voter PC has its key in the pre-vote store, including carried PCs. -/
theorem recovery_voter_key_before_vote (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (x : V) (hx : x ∈ rho.honest) (s : Slot) (nd : Node p)
    (hn : pcsa_postClock E rho x (SA.voteTime p.toParams s) = some nd)
    (C : PC p.n) (hC : voterPC p nd.st s = some C) :
    KeyHeld (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s) x).st C.slot C.target := by
  obtain ⟨q, hq, hnd⟩ := recovery_postClock_index E rho x _ nd hn
  have hO := pcsa_outageStore_stateBefore E rho (q + 1) x hx
  have hclosed := pcsa_collectClosed_stateBefore E rho h x hx (q + 1)
  have hcands := (List.mem_filter.mp (bestPC_mem _ C hC)).1
  rw [hnd] at hcands
  have hk : KeyHeld (V2.D.Run.stateBefore E rho (q + 1) x).st C.slot C.target := by
    rcases List.mem_append.mp hcands with hf | hc
    · delta pcSnapshotAt at hf
      cases he : (V2.D.Run.stateBefore E rho (q + 1) x).st.pcSnapshot.find?
          (fun row => row.1 == s - 1) with
      | none => rw [he] at hf; exact (List.not_mem_nil hf).elim
      | some row =>
        rw [he] at hf
        exact (KeyHeld_def _ _ _).mpr
          ⟨C, hO.snapSub row (List.mem_of_find?_eq_some he) C hf, rfl, rfl⟩
    · obtain ⟨hmem, hv⟩ := List.mem_filter.mp hc
      obtain ⟨hwfB, hactive⟩ := Bool.and_eq_true_iff.mp hv
      obtain ⟨hwf, hbody⟩ := Bool.and_eq_true_iff.mp hwfB
      apply pcsa_keyHeld_of_collectClosed _ hclosed C hwf ?_
        (of_decide_eq_true hbody) hactive
      obtain ⟨w, hw, hf⟩ := List.mem_filterMap.mp hmem
      cases hd : w.decode with
      | none => rw [hd] at hf; cases hf
      | some msg =>
        rw [hd] at hf
        cases msg with
        | vote r i root => cases hf
        | row i body => cases hf
        | ack r i root => cases hf
        | pc D => cases hf
        | block r N =>
          dsimp only at hf
          split at hf
          · intro a ha
            apply hO.carried w hw r N hd a
            · change a ∈ (N.pc.map PC.acks).getD []
              simpa only [hf, Option.map_some, Option.getD_some] using ha
            · obtain ⟨i, hi⟩ := (pcsa_pc_wellFormed_parts C hwf).2.2.2.2.2 a ha
              rw [hi]
              rfl
          · cases hf
  rw [KeyHeld_def] at hk ⊢
  obtain ⟨D, hD, hDs, hDt⟩ := hk
  rw [V2.D.Run.stateBefore_succ E rho hq] at hD
  change D ∈ (Function.update (V2.D.Run.stateBefore E rho q) x _ x).st.pcs at hD
  rw [Function.update_self, pcsa_tick_st E rho (V2.D.Run.stateBefore E rho q x) x _,
    clock_pcs_eq, V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
      h.valid.toScheduleWellFormed h.noRestart hq] at hD
  exact ⟨D, hD, hDs, hDt⟩

/-- K at the first later HEAD: the selected voter view cannot block the write. -/
theorem recovery_write_voter_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (g s : Slot)
    (transport : RecoveryLockTransport p c E rho g)
    (k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s)))
    (hg : E.t_GST ≤ SA.earlyTime p.toParams s) (B : Block)
    (hwrite : leaseWriteOK
      (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams s)).pcs
      (gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams s)) s) B = true)
    (nd : Node p) (hn : pcsa_postClock E rho y (SA.voteTime p.toParams (s + 1)) = some nd)
    (C : PC p.n) (hC : voterPC p nd.st (s + 1) = some C) : Block.Compatible C.target B := by
  have hr := recovery_voter_rank_bound E rho h.valid.toScheduleWellFormed h.noRestart hF h.delta
    g transport k x y hx hy s (s + 1) (Nat.lt_succ_self s) hg nd hn C hC
  obtain ⟨D, hD, hDs, hDt⟩ := (KeyHeld_def _ _ _).mp
    (recovery_voter_key_before_vote E rho h y hy (s + 1) nd hn C hC)
  have ht : E.t_GST ≤ SA.voteTime p.toParams (s + 1) := by
    have hd := p.deltaPos
    apply hg.trans
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    nlinarith
  have hc := recovery_write_relay_pc_compatible E rho h.valid.toScheduleWellFormed h.noRestart
    g s transport x y hx hy k hk ht B _ hwrite D hD
    (by simpa only [rankAtLeast_def, hDs, hDt] using hr)
  simpa only [hDt] using hc

/-- K during survival: relay of the selected voter view is inside the exact-row interval. -/
theorem recovery_survivor_voter_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (g s r : Slot) (hsr : s < r)
    (transport : RecoveryLockTransport p c E rho g)
    (i k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (row : Block × Nat × Time)
    (hsurv : ∀ a, k < a → a ≤ i →
      row ∈ (V2.D.Run.stateBefore E rho a x).st.base.obligations ∧
      leaseRank (V2.D.Run.stateBefore E rho a x).st row.1 =
        leaseRank (V2.D.Run.stateBefore E rho i x).st row.1)
    (hrank : leaseRank (V2.D.Run.stateBefore E rho i x).st row.1 =
      gateRank p (clockPre p (V2.D.Run.stateBefore E rho k x).st
        (SA.gateTime p.toParams s)) s)
    (hg : E.t_GST ≤ SA.earlyTime p.toParams s)
    (horizon : SA.voteTime p.toParams r + p.Δ ≤ rho.horizon)
    (hlo : k < V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ))
    (hhi : V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ) ≤ i)
    (nd : Node p) (hn : pcsa_postClock E rho y (SA.voteTime p.toParams r) = some nd)
    (C : PC p.n) (hC : voterPC p nd.st r = some C) : Block.Compatible C.target row.1 := by
  have hr := recovery_voter_rank_bound E rho h.valid.toScheduleWellFormed h.noRestart hF h.delta
    g transport k x y hx hy s r hsr hg nd hn C hC
  obtain ⟨D, hD, hDs, hDt⟩ := (KeyHeld_def _ _ _).mp
    (recovery_voter_key_before_vote E rho h y hy r nd hn C hC)
  have ht : E.t_GST ≤ SA.voteTime p.toParams r := by
    have hd := p.deltaPos
    have hi : (s : Int) + 1 ≤ (r : Int) := by exact_mod_cast hsr
    apply hg.trans
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (r : Int) + p.Δ
    nlinarith
  have hc := recovery_survivor_relay_pc_compatible E rho h.valid.toScheduleWellFormed
    g transport i k x y hx hy row hsurv _ ⟨r, Or.inr rfl⟩ ht horizon hlo hhi D hD
    (by rw [hrank]; simpa only [rankAtLeast_def, hDs, hDt] using hr)
  simpa only [hDt] using hc

end AvailableChain.PCSA.Run
end
