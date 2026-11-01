module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingBatch
public import Mathlib.Tactic.IntervalCases -- shake: keep (interval_cases tests)
public import Mathlib.Tactic.FinCases -- shake: keep (fin_cases tests)



-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingMain -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingDutySleep
public import AvailableChainFGSAProofs.Proofs.Clean.EpochSaved
public import AvailableChainFGSAProofs.Proofs.Clean.GateOutput

public section

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.OutageArming

open AvailableChain.SimplexFG
open Gen.Pure

/-! Plan O-ARM §10 boundary examples. -/

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Plan O-ARM §2, §10. Class (iii). DC: INTENTIONAL.
A cut at a gate time, b₀ = d(l): the cut label is `l` itself, the batch
receipt deadline e(l + 1) equals the cut, and the pending gate is strictly
later. -/
theorem cut_at_gate (p : Params) (l : Slot) :
    let b₀ := SA.gateTime p.toParams l
    ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat = l ∧
      SA.earlyTime p.toParams (l + 1) = b₀ ∧ b₀ < SA.gateTime p.toParams (l + 1) := by
  intro b₀
  have h6 : 6 * p.Δ ≤ b₀ := by
    change 6 * p.Δ ≤ 4 * p.Δ * (l : Time) + 6 * p.Δ
    have := p.deltaPos
    have : (0 : Time) ≤ 4 * p.Δ * (l : Time) := by positivity
    linarith
  have hle := (arming_le_label p b₀ h6 l).mp le_rfl
  have hlt : ¬ l + 1 ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat := fun h =>
    absurd ((arming_le_label p b₀ h6 (l + 1)).mpr h)
      (not_le.mpr ((arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l)))
  refine ⟨le_antisymm (Nat.le_of_lt_succ (not_le.mp hlt)) hle, arming_early_next p l,
    (arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l)⟩

/-- Plan O-ARM §10. Class (iii). DC: INTENTIONAL.
Δ = 1 and b₀ = d(2) = 14: the cut label is 2. -/
example : (((14 : Int) - 6 * 1) / (4 * 1)).toNat = 2 := by decide

/-- Plan O-ARM §2, §10. Class (iii). DC: INTENTIONAL.
The first possible origin s = 1. The fast lag puts the pending label at
least at 3; the slow window labels are between 2 and `l`. -/
example (p : Params) (T b₀ : Time) (hs : SA.gateTime p.toParams 1 ≤ T)
    (hlag : T + 4 * p.Δ ≤ b₀) : 3 ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 :=
  arming_fast_gap p 1 T b₀ hs hlag

example (p : Params) (l a : Nat) (hgap : 1 + p.k ≤ l + 1) (ha : a < p.k - 1) :
    2 ≤ l + 1 - (a + 1) ∧ l + 1 - (a + 1) ≤ l :=
  let h := arming_slow_window_label p 1 l a le_rfl hgap ha
  ⟨h.2.2, h.2.1⟩

/-- Plan O-ARM §10. Class (iii). DC: INTENTIONAL.
A pending gate after the horizon: no actual gate tick exists, so field 9 is
vacuous, and the pre-pending fields alone cover every read up to the horizon. -/
theorem pending_after_horizon {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {T b₀ b₁ : Time} {B : Block}
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hhor : rho.horizon < SA.gateTime p.toParams (l + 1)) :
    (∀ i y, ¬ IsGateTick p c rho i y (l + 1)) ∧
    ∀ y t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t → t ≤ rho.horizon →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y) := by
  refine ⟨fun i y hi => ?_, fun y t hy hlt ht => ?_⟩
  · have h := (hs.in_horizon _ (List.mem_of_getElem? hi)).2
    exact absurd (lt_of_le_of_lt h hhor) (lt_irrefl _)
  · have htd := lt_of_le_of_lt ht hhor
    have h0 : 0 ≤ t := le_trans (by
      rw [arming_gate_eq]
      have := p.deltaPos
      positivity) hlt
    exact ⟨hc.pending_cover y t hy hlt htd ht, hc.pending_compat y t hy h0 htd ht⟩

/-- Plan O-ARM §6.4, §10. Class (iii). DC: INTENTIONAL.
Slow mode below τ: the slow test alone admits the release level. -/
example (p : Params) {n : Nat} (v : GridCO.State n .root) (r : Slot) (B : Block)
    (_hbelow : SA.Root.prefixSupport p.toParams v r B < SA.releaseThreshold p.toParams)
    (hslow : GridCO.slowEligible p.toParams.engine v r B = true) :
    SA.releaseThreshold p.toParams ∈
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine n .root v r B :=
  by
    simp only [GridCO.admissionLevels]
    change SA.releaseThreshold p.toParams ∈
      (if decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v r B) ||
        GridCO.slowEligible p.toParams.engine v r B then [SA.releaseThreshold p.toParams] else [])
    simp [hslow]

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.cut_at_gate
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.pending_after_horizon
#print axioms AvailableChain.FGSA.Run.ArmingData_def
/-- Restart clears saved rows. A prior epoch cannot supply the slow window. -/
theorem saved_rows_erased_at_restart (p : Params) (st : State p.n) (w : Time) (s : Slot) :
    GridCO.savedGenuine (acRestart p st w).base s = none := by
  unfold GridCO.savedGenuine
  rw [acRestart_genuine]
  rfl

/-- Same-time wake precedes the gate's read. The strict-before read is insufficient. -/
theorem gate_reads_after_wake {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : IsGateTick p c rho i x s) :
    storeAt p c E rho i x = (V2.D.Run.stateAfterRestartsAt E rho
      (SA.gateTime p.toParams s) x).st := by
  exact congrArg Node.st (V2.D.Engine.stateBefore_tick_eq_stateAfterRestartsAt hs hi)

/-- Full sleep excludes the old all-honest tick conclusion. -/
theorem asleep_has_no_tick {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) {x : V} {t : Time} (ha : E.awake x t = false) :
    V2.Event.tick x t ∉ rho.events := by
  intro ht
  have hw := hE.tick_awake x t ht
  rw [ha] at hw
  cases hw

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.saved_rows_erased_at_restart
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.gate_reads_after_wake
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.asleep_has_no_tick
#print axioms AvailableChain.FGSA.Run.arming_tick_exists
#print axioms AvailableChain.FGSA.Run.arming_block_early
#print axioms AvailableChain.FGSA.Run.arming_head_ge
#print axioms AvailableChain.FGSA.Run.arming_head_ge_on
#print axioms AvailableChain.FGSA.Run.arming_healthy_batch
#print axioms AvailableChain.FGSA.Run.arming_enabled_of_pass
#print axioms AvailableChain.FGSA.Run.arming_clean_mem
#print axioms AvailableChain.FGSA.Run.arming_clean_of_tick
#print axioms AvailableChain.FGSA.Run.arming_max_label
#print axioms AvailableChain.FGSA.Run.arming_origin_of_clean
#print axioms AvailableChain.FGSA.Run.arming_origin
#print axioms AvailableChain.FGSA.Run.arming_store_succ_on
#print axioms AvailableChain.FGSA.Run.arming_store_succ
#print axioms AvailableChain.FGSA.Run.arming_clock_offGate_fields
#print axioms AvailableChain.FGSA.Run.arming_saved_interval_on
#print axioms AvailableChain.FGSA.Run.arming_saved_interval
#print axioms AvailableChain.FGSA.Run.arming_slow_saved_on
#print axioms AvailableChain.FGSA.Run.arming_slow_eligible_on
#print axioms AvailableChain.FGSA.Run.arming_slow_saved
#print axioms AvailableChain.FGSA.Run.arming_fast_awake
#print axioms AvailableChain.FGSA.Run.arming_fast_restart_free
#print axioms AvailableChain.FGSA.Run.arming_receiver_window
#print axioms AvailableChain.FGSA.Run.arming_receiver_times
#print axioms AvailableChain.FGSA.Run.arming_receiver_start_epoch
#print axioms AvailableChain.FGSA.Run.arming_receiver_epoch
#print axioms AvailableChain.FGSA.Run.arming_receiver_enabled
#print axioms AvailableChain.FGSA.Run.arming_receiver_gate_epoch
#print axioms AvailableChain.FGSA.Run.arming_tick_store_on
#print axioms AvailableChain.FGSA.Run.arming_emitted_head_fields
#print axioms AvailableChain.FGSA.Run.arming_proposal_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_head_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_batch_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_prefix_batch_receipt_on

#print axioms AvailableChain.FGSA.Run.arming_enabled_of_result
#print axioms AvailableChain.FGSA.Run.arming_source_below
#print axioms AvailableChain.FGSA.Run.arming_entry_below
#print axioms AvailableChain.FGSA.Run.arming_frame_below
#print axioms AvailableChain.FGSA.Run.arming_leases_cut
#print axioms AvailableChain.FGSA.Run.arming_leases_interval
#print axioms AvailableChain.FGSA.Run.arming_leases_interval_on
#print axioms AvailableChain.FGSA.Run.arming_prefix_state
#print axioms AvailableChain.FGSA.Run.arming_S_cut
#print axioms AvailableChain.FGSA.Run.arming_S_interval
#print axioms AvailableChain.FGSA.Run.arming_S_interval_on
#print axioms AvailableChain.FGSA.Run.arming_cover
#print axioms AvailableChain.FGSA.Run.arming_compat
#print axioms AvailableChain.FGSA.Run.arming_nonrow_delivery
#print axioms AvailableChain.FGSA.Run.arming_head_ready
#print axioms AvailableChain.FGSA.Run.arming_fresh_head_service
#print axioms AvailableChain.FGSA.Run.arming_proposal_service
#print axioms AvailableChain.FGSA.Run.arming_pending_rows_on

end AvailableChain.FGSA.Run.Tests.OutageArming

namespace AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut

open AvailableChain.SimplexFG
/-! DECISION P15-CUT excludes a batch after an early healthy cut. -/

abbrev p : Params :=
  { Δ := 2, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }
abbrev P := fgsa p unitCodec
def env : Generic.Env (Fin 1) := ⟨2, by decide, 0, by decide, fun _ _ => true⟩
def head0 : Obj p := ⟨.seat (.base (.head 0)) ⟨0, by decide⟩, .head genesisRoot⟩
def wire0 : HeadWire p.n := ⟨.seat (.head 0) ⟨0, by decide⟩, genesisRoot⟩
def body : NamedProposal p.n := namedProposal p .genesis 1 0 [wire0] [wire0] []
def proposal : Obj p := ⟨.seat (.prop 1) ⟨0, by decide⟩, .proposal body⟩
def run : V2.D.Run (Fin 1) P where
  honest := {0}
  horizon := 8
  events := [.tick 0 0, .tick 0 2, .deliver 0 head0 2, .tick 0 4, .tick 0 6, .tick 0 8]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

theorem fgp_emitted_cases {v : Fin 1} {o : Obj p} {t : Time}
    (h : V2.D.Run.emits env run v o t) :
    (o = head0 ∧ t = 2) ∨ (o = proposal ∧ t = 8) := by
  obtain ⟨i, hi, ho⟩ := h
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change i < 6 at hb
  interval_cases i <;> simp [run] at hi
  all_goals obtain ⟨rfl, rfl⟩ := hi
  all_goals first
    | (change o ∈ [] at ho; exact (List.not_mem_nil ho).elim)
    | (change o ∈ [head0] at ho; exact Or.inl ⟨List.mem_singleton.mp ho, rfl⟩)
    | (change o ∈ [proposal] at ho; exact Or.inr ⟨List.mem_singleton.mp ho, rfl⟩)

theorem fgp_valid : V2.D.ExecutionValid env run := by
  refine {
    toScheduleWellFormed := ?_
    toSleepWellFormed := ?_
    toDeliveryWellFormed := ?_
    toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp [run] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro e he
      simp [run] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro v t he
      simp [run] at he
      refine ⟨(t / 2).toNat, ?_⟩
      simp [env]; dsimp [Time] at *; omega
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      change t = (k : Time) * 2 at hk
      change t ≤ 8 at hh
      have hkbound : k ≤ 4 := by dsimp [Time] at *; omega
      interval_cases k <;> simp [run] <;> dsimp [Time] at * <;> omega
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp [run] at he
    all_goals obtain ⟨rfl, rfl, rfl⟩ := he
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals change i < 6 at hib
    all_goals interval_cases i <;> first
      | decide +kernel
      | exact False.elim ((by decide +kernel : ¬ (type_of% hi)) hi)
  · refine ⟨?_, ?_⟩
    · intro v o t hp u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [run] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hu0 : u = 0 := Subsingleton.elim _ _
      subst u
      exact ⟨2, le_rfl, 1, rfl, by change head0 ∈ [head0]; exact List.mem_singleton_self _⟩
    · intro v o t hp o' hc u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [run] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hn : ¬ P.carries head0 o' := by intro h; cases h
      exact (hn hc).elim
  · refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, ?_⟩
    intro v hv t ht hh hw
    have hf := hw.2
    change true = false at hf
    cases hf

theorem fgp_roots : NamedReceiptRootCollisionFree p unitCodec env run := by
  have old {A : NamedProposal p.n} (hA : NamedProposalInRun p unitCodec env run A) :
      A = .genesis := by
    rcases namedProposalInRun_genesis_or_delivered env run (by
      intro x o t N hd ho
      simp [run] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases ho) hA with hg | ⟨x, o, t, hd, ho⟩
    · exact hg
    · simp [run] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases ho
  have scope {A : NamedProposal p.n} (hA : NamedProposalReceiptScope p unitCodec env run A) :
      A = .genesis ∨ A = body := by
    rcases hA with hA | ⟨v, hv, o, t, N, he, ho, hAN⟩
    · exact Or.inl (old hA)
    · rcases fgp_emitted_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases ho
      · change Msg.proposal body = Msg.proposal N at ho
        cases Msg.proposal.inj ho
        change (decide (A = body) || NamedProposal.preceq A .genesis) = true at hAN
        have hh : A = body ∨ A = .genesis := by
          simpa only [Bool.or_eq_true, decide_eq_true_eq, NamedProposal.preceq] using hAN
        exact hh.symm
  intro A B hA hB he
  rcases scope hA with rfl | rfl
  all_goals rcases scope hB with rfl | rfl
  all_goals first
    | rfl
    | exact False.elim ((by decide +kernel : ¬ (type_of% he)) he)

theorem fgp_healthy : Gen.V2.Duty.HealthyPrefixDeliveryBy env run (fgsaDelay env.Δ 2) 8 := by
  have demand : V2.D.DeliveryDemand env run 0 0 head0 2 (fun a => a + 2) 8 := by
    intro a ha hn hl hc hh hr hx
    change a + 2 ≤ 8 at hc
    have hb : a ≤ 6 := by dsimp [Time] at *; omega
    interval_cases a
    all_goals first
      | (right; exact ⟨2, le_rfl, by decide, 2, head0, rfl, Or.inl rfl⟩)
      | (left; exact ⟨3, by decide, by decide +kernel⟩)
  constructor
  · intro v hv o t he w hw
    have hv0 : v = 0 := Subsingleton.elim _ _
    have hw0 : w = 0 := Subsingleton.elim _ _
    subst v; subst w
    rcases fgp_emitted_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact demand
    · intro a ha hn hl hc
      change a + 2 ≤ 8 at hc
      dsimp [Time] at *
      omega
  · intro v hv i o t ha w hw
    obtain ⟨parent, hi, hc⟩ := ha.1
    have hm := List.mem_of_getElem? hi
    simp [run] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    rcases (fgsaHooks p unitCodec).handles_carries _ _ _ hc with h | h
    · subst o
      have hw0 : w = 0 := Subsingleton.elim _ _
      subst w
      exact demand
    · have hn : ¬ P.carries head0 o := by intro h; cases h
      exact (hn h).elim


theorem joined_all (v : Fin 1) (s : Slot) (t : Time) : joinedAt p env run v s t := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w hw ht he
    have hf := he.2
    change true = false at hf
    cases hf
  · intro w hw ht he
    simp [run] at he

theorem base : Base₂ p unitCodec env run := by
  have hseats (l : RunLabel) : P.seats l = 1 := by
    cases l with
    | base l => cases l <;> rfl
    | prop s => rfl
  refine ⟨fgp_valid, ?_, ?_, ?_, rfl, fgp_roots⟩
  · refine ⟨1, Equiv.refl _, ?_⟩
    intro l hl
    exact ⟨hseats l, fun i => Subsingleton.elim _ _⟩
  · intro l hl
    have hinj : Function.Injective (run.seatOf l) := by
      intro a b he
      have ha : a.val < 1 := (hseats l) ▸ a.isLt
      have hb : b.val < 1 := (hseats l) ▸ b.isLt
      apply Fin.ext
      omega
    exact ⟨hinj, fun v => ⟨⟨0, by rw [hseats l]; decide⟩, Subsingleton.elim _ _⟩⟩
  · intro v t he
    simp [run] at he

theorem regime : OutageSleep₂ p unitCodec true env run 0 8 8 2 := by
  classical
  have hj (t : Time) : joinedHonest p env run t = run.honest := by
    ext v
    simp [joinedHonest, joined_all]
  have ha (t : Time) : Gen.V2.Duty.awakeHonest env run t = run.honest := by
    ext v
    simp [Gen.V2.Duty.awakeHonest_def, env]
  have hpart (t : Time) :
      (Gen.V2.Duty.faulty run).card < (Gen.V2.Duty.awakeHonest env run t).card := by
    rw [ha]
    decide
  have hpre : HealthyPrefix₂ p unitCodec env run 8 2 :=
    ⟨base, by decide, fgp_healthy, le_rfl, fun t _ _ => hpart t⟩
  have hsleep : ∀ t : Time,
      (awakeHonestIn env run (t - p.η) t ∪ Gen.V2.Duty.faulty run).card <
        2 * (Gen.V2.Duty.awakeHonest env run t).card := by
    intro t
    rw [ha]
    have hex : ∃ u : Time, t ≤ u ∧ u ≤ t := ⟨t, le_rfl, le_rfl⟩
    simp [awakeHonestIn, env, run, Gen.V2.Duty.faulty, hex]
  refine {
    pre := hpre
    sleepy := fun t _ _ => hsleep t
    order := by decide
    lag := by decide
    budget := by decide
    fastPart := ?_
    sleepPre := ⟨hpre, ?_⟩
    joinedSleepy := ?_
    joinedFastPart := ?_
    protection := ?_ }
  · intro _ t _ _
    rw [ha]
    decide
  · intro t _ _
    rw [hj]
    decide
  · intro t _ _
    rw [hj, ← ha]
    exact hsleep t
  · intro _ t _ _
    rw [hj]
    decide
  · refine ⟨1, ?_, ?_⟩
    · intro s
      change 8 ≤ 8 * (s : Time) + 2 ↔ 1 ≤ s
      cases s with
      | zero => decide
      | succ s =>
        constructor
        · intro _; exact Nat.succ_le_succ (Nat.zero_le s)
        · intro _
          have hn : (0 : Time) ≤ (s : Time) := Int.natCast_nonneg s
          push_cast
          linarith
    · have hc : coveredNodes p env run true 8 = run.honest := by
        ext v
        simp [coveredNodes, fastCoveredSchedule, joined_all]
      have hw : outageW p env run true 8 1 = ∅ := by
        ext v
        simp only [outageW, Finset.mem_filter, hc, Finset.notMem_empty]
        exact ⟨fun h => (h.2.1 h.1).elim, False.elim⟩
      rw [hw]
      decide

/-- The corrected prefix receipt claim excludes the batch beyond this early cut. -/
theorem prefix_receipt : OutagePrefixReceipt p unitCodec env run true 0 8 := by
  intro x hx q hq hT hCut
  have hq1 : q = 1 := by simpa [coverLabel, p] using hq
  rw [hq1] at hCut
  exact False.elim ((by decide : ¬ SA.earlyTime p.toParams 1 ≤ 8) hCut)

end AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.fgp_emitted_cases
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.fgp_valid
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.fgp_roots
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.fgp_healthy
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.joined_all
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.base
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.regime
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.prefix_receipt

#print axioms AvailableChain.FGSA.Run.arming_gate_ne_vote

#print axioms AvailableChain.FGSA.Run.arming_gate_ne_proposal

#print axioms AvailableChain.FGSA.Run.arming_F_mono

#print axioms AvailableChain.FGSA.Run.arming_lift_mem

#print axioms AvailableChain.FGSA.Run.arming_emit_awake

#print axioms AvailableChain.FGSA.Run.arming_emit_head

#print axioms AvailableChain.FGSA.Run.arming_emit_proposal

#print axioms AvailableChain.FGSA.Run.arming_emit_head_store

#print axioms AvailableChain.FGSA.Run.arming_ancestor_stamp

#print axioms AvailableChain.FGSA.Run.arming_clock_gate

#print axioms AvailableChain.FGSA.Run.arming_admission

#print axioms AvailableChain.FGSA.Run.arming_gate_write

#print axioms AvailableChain.FGSA.Run.arming_leaseOf

#print axioms AvailableChain.FGSA.Run.arming_rows_compat

#print axioms AvailableChain.FGSA.Run.arming_gate_core

#print axioms AvailableChain.FGSA.Run.pending_gate_lease_or_F

#print axioms AvailableChain.FGSA.Run.arming_proposal_genuine

#print axioms AvailableChain.FGSA.Run.arming_process_lease

#print axioms AvailableChain.FGSA.Run.arming_event_window

#print axioms AvailableChain.FGSA.Run.arming_offGate

#print axioms AvailableChain.FGSA.Run.arming_write_row

#print axioms AvailableChain.FGSA.Run.arming_write_keep

#print axioms AvailableChain.FGSA.Run.arming_writeKeys_keep

#print axioms AvailableChain.FGSA.Run.arming_writeKeys_row

#print axioms AvailableChain.FGSA.Run.arming_writeKeys_stable

#print axioms AvailableChain.FGSA.Run.arming_gateResult_tick

#print axioms AvailableChain.FGSA.Run.ArmingCert

#print axioms AvailableChain.FGSA.Run.ArmingData

#print axioms AvailableChain.FGSA.Run.arming_gate_eq

#print axioms AvailableChain.FGSA.Run.arming_vote_eq

#print axioms AvailableChain.FGSA.Run.arming_early_eq

#print axioms AvailableChain.FGSA.Run.arming_freeze_eq

#print axioms AvailableChain.FGSA.Run.arming_release_eq

#print axioms AvailableChain.FGSA.Run.arming_proposal_eq

#print axioms AvailableChain.FGSA.Run.arming_lifetime_eq

#print axioms AvailableChain.FGSA.Run.arming_gate_le_iff

#print axioms AvailableChain.FGSA.Run.arming_gate_lt_iff

#print axioms AvailableChain.FGSA.Run.arming_early_next

#print axioms AvailableChain.FGSA.Run.arming_vote_add

#print axioms AvailableChain.FGSA.Run.arming_vote_lt_early

#print axioms AvailableChain.FGSA.Run.arming_label

#print axioms AvailableChain.FGSA.Run.arming_le_label

#print axioms AvailableChain.FGSA.Run.arming_lt_pending

#print axioms AvailableChain.FGSA.Run.arming_gate_window

#print axioms AvailableChain.FGSA.Run.arming_vote_window

#print axioms AvailableChain.FGSA.Run.arming_proposal_window

#print axioms AvailableChain.FGSA.Run.arming_inflight

#print axioms AvailableChain.FGSA.Run.arming_inflight_window

#print axioms AvailableChain.FGSA.Run.arming_duty_window

#print axioms AvailableChain.FGSA.Run.arming_action_label

#print axioms AvailableChain.FGSA.Run.arming_fast_gap

#print axioms AvailableChain.FGSA.Run.arming_slow_gap

#print axioms AvailableChain.FGSA.Run.arming_slow_window_label

#print axioms AvailableChain.FGSA.Run.arming_end_lt_deadline

#print axioms AvailableChain.FGSA.Run.arming_L_pos

#print axioms AvailableChain.FGSA.Run.arming_lt_timeIdx_iff

#print axioms AvailableChain.FGSA.Run.arming_timeIdx_mono

#print axioms AvailableChain.FGSA.Run.arming_timeIdx_le_idxBefore

#print axioms AvailableChain.FGSA.Run.arming_idxBefore_le_timeIdx

#print axioms AvailableChain.FGSA.Run.arming_timeIdx_le_length

#print axioms AvailableChain.FGSA.Run.arming_idxBefore_le_length

#print axioms AvailableChain.FGSA.Run.arming_vote_nat

#print axioms AvailableChain.FGSA.Run.arming_early_nat

#print axioms AvailableChain.FGSA.Run.arming_proposal_nat

#print axioms AvailableChain.FGSA.Run.arming_gate_nat

#print axioms AvailableChain.FGSA.Run.arming_prec

#print axioms AvailableChain.FGSA.Run.arming_prec_ne_genesis

#print axioms AvailableChain.FGSA.Run.ArmingPrefixState

#print axioms AvailableChain.FGSA.Run.ArmingBatchState

#print axioms AvailableChain.FGSA.Run.arming_batch_at

#print axioms AvailableChain.FGSA.Run.arming_read_bounds

#print axioms AvailableChain.FGSA.Run.arming_head_covers

#print axioms AvailableChain.FGSA.Run.arming_proposal_covers

#print axioms AvailableChain.FGSA.Run.arming_gate_core_on

#print axioms AvailableChain.FGSA.Run.arming_tick_le

#print axioms AvailableChain.FGSA.Run.arming_lt_of_tick

#print axioms AvailableChain.FGSA.Run.arming_clean_ordered

#print axioms AvailableChain.FGSA.Run.arming_comparison_prefix

#print axioms AvailableChain.FGSA.Run.arming_stable_read

#print axioms AvailableChain.FGSA.Run.arming_pending_input

#print axioms AvailableChain.FGSA.Run.arming_proposal_service_trigger

#print axioms AvailableChain.FGSA.Run.arming_cut_saved_on

#print axioms AvailableChain.FGSA.Run.arming_proposal_anchor_service

#print axioms AvailableChain.FGSA.Run.arming_target_service

#print axioms AvailableChain.FGSA.Run.arming_head_not_excluded

#print axioms AvailableChain.FGSA.Run.arming_head_handlers

#print axioms AvailableChain.FGSA.Run.arming_batch_service

#print axioms AvailableChain.FGSA.Run.arming_prefix_batch_receipt

#print axioms AvailableChain.FGSA.Run.arming_protected_origin_on

#print axioms AvailableChain.FGSA.Run.arming_slow_current_rows_on

#print axioms AvailableChain.FGSA.Run.arming_receiver_read_epoch

#print axioms AvailableChain.FGSA.Run.arming_healthy_batch_protected

namespace AvailableChain.FGSA.Run.Tests.OutageArming

open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The returned P-Cl1 producer fits the current-row arming consumer exactly. -/
theorem current_row_consumer [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {ΔF b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    {x : V} {q l : Slot} {B D : Block} (hx : x ∈ rho.honest) (hql : q ≤ l)
    (hcut : SA.gateTime p.toParams q ≤ b₀)
    (hAw : AwakeClosed E x (slotStartZ p (q : Int)) b₀)
    (hEpoch : RestartFreeTime rho x (slotStartZ p (q : Int)) b₀)
    (hOrigin : B = .genesis ∨ ∃ r C, r < q ∧
      (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C)
    (hmax : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) →
      r ≤ l → Block.Preceq C D) :
    Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
      ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
        some (some C) ∧ Block.Preceq B C ∧ Block.Preceq C D := by
  have hh := clean_invariant p c E rho h hq hf hsrc (timeIdx rho b₀) le_rfl
  have st := cleanState_of_hist h hq hf hsrc (clean_actionStep p c E rho) le_rfl hh
  exact arming_cut_saved_on st (clean_epoch_saved_row h hq hf hsrc) hx hql hcut
    hAw hEpoch hOrigin hmax

end AvailableChain.FGSA.Run.Tests.OutageArming

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.current_row_consumer

#print axioms AvailableChain.FGSA.Run.arming_cert

#print axioms AvailableChain.FGSA.Run.fast_arming

#print axioms AvailableChain.FGSA.Run.slow_arming

#print axioms AvailableChain.FGSA.Run.arming_tick_store

#print axioms AvailableChain.FGSA.Run.arming_head_seats

#print axioms AvailableChain.FGSA.Run.arming_saved_map

#print axioms AvailableChain.FGSA.Run.arming_lift

#print axioms AvailableChain.FGSA.Run.ArmingBatchReceiptService

namespace AvailableChain.FGSA.Run.Tests.OutageArming

open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The general slow producer consumes the actual Clean induction and saved-row theorem. -/
theorem slow_certificate_consumer [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c false E rho T b₀ b₁ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    {y : V} (hyG : y ∈ coveredNodes p E rho false b₀) :
    ∃ D Dh, ArmingSleepCert p c E rho false T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  have hh := clean_invariant p c E rho h.sleepPre hq hf hsrc (timeIdx rho b₀) le_rfl
  have hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i := by
    intro i hi
    exact cleanState_of_hist h.sleepPre hq hf hsrc (clean_actionStep p c E rho) hi
      (clean_invariant p c E rho h.sleepPre hq hf hsrc i hi)
  have htransfer := (cleanHistoryAt_body p c E rho h.sleepPre hq hf hsrc).2.2.1
  exact slow_arming_on h hf hsrc htsrc hState hh
    (fun y z s C H hy hz hJ hcut hRes hHead => htransfer y z s C H hy hz hcut hRes hJ hHead)
    (clean_epoch_saved_row h.sleepPre hq hf hsrc) hread hne hyG

/-- Strict-before-cut participation supplies the fast producer's actual last result. -/
theorem fast_certificate_consumer [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    (hStrict : SA.gateTime p.toParams (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) < b₀) :
    ∃ D Dh, ArmingSleepCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  have hh := clean_invariant p c E rho h.sleepPre hq hf hsrc (timeIdx rho b₀) le_rfl
  have hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i := by
    intro i hi
    exact cleanState_of_hist h.sleepPre hq hf hsrc (clean_actionStep p c E rho) hi
      (clean_invariant p c E rho h.sleepPre hq hf hsrc i hi)
  have htransfer := (cleanHistoryAt_body p c E rho h.sleepPre hq hf hsrc).2.2.1
  let l := ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat
  obtain ⟨z, j, _, hG, _⟩ := clean_joined_gate_witness h.sleepPre l hStrict
  have hji := arming_lt_of_tick h.pre.base.valid.toScheduleWellFormed hG.1 hStrict.le
  obtain ⟨C, hC, _⟩ := hh.nonempty j z l hji hG
  exact fast_arming_on h hf hsrc htsrc hState hh
    (fun y z s C H hy hz hJ hcut hRes hHead => htransfer y z s C H hy hz hcut hRes hJ hHead)
    hread hne
    ⟨C, j, hji, z, hG.1, hG.2, hC⟩

end AvailableChain.FGSA.Run.Tests.OutageArming

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.slow_certificate_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.fast_certificate_consumer

#print axioms AvailableChain.FGSA.Run.ArmingGateInput

#print axioms AvailableChain.FGSA.Run.arming_joined_batch_at

#print axioms AvailableChain.FGSA.Run.arming_sleep_pending_input

#print axioms AvailableChain.FGSA.Run.arming_comparison_prefix_on

#print axioms AvailableChain.FGSA.Run.ArmingSleepCert

#print axioms AvailableChain.FGSA.Run.arming_last_max_on

#print axioms AvailableChain.FGSA.Run.arming_joined_head_card

#print axioms AvailableChain.FGSA.Run.arming_sleep_entry_below

#print axioms AvailableChain.FGSA.Run.arming_pending_epochs

#print axioms AvailableChain.FGSA.Run.arming_sleep_comparison_lift

#print axioms AvailableChain.FGSA.Run.arming_sleep_cert_of_last

#print axioms AvailableChain.FGSA.Run.arming_sleep_gate_core

#print axioms AvailableChain.FGSA.Run.pending_gate_lease_or_F_on

#print axioms AvailableChain.FGSA.Run.fast_arming_on

#print axioms AvailableChain.FGSA.Run.slow_arming_on

namespace AvailableChain.FGSA.Run.Tests.OutageArming

open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The actual slow certificate feeds the executed gate and the scoped frame consumer. -/
theorem slow_gate_consumer [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c false E rho T b₀ b₁ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) {y : V} (hyG : y ∈ coveredNodes p E rho false b₀)
    (hgate : SA.gateTime p.toParams (coverLabel p b₀) ≤ rho.horizon)
    (hRows : ∀ z r (a : RowWire p.n) (e Bh : FGBlock (Fin p.n)), eraseFG Bh = B →
      HonestRowBefore p c E rho (afterTicksIdx rho (SA.gateTime p.toParams
        (coverLabel p b₀))) z r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e) :
    let j := coverLabel p b₀
    let I := afterTicksIdx rho (SA.gateTime p.toParams j)
    let st := storeAt p c E rho I y
    Block.Preceq B (S_at p c E rho I y) ∧
    (Block.Preceq B (F_at p c E rho I y) ∨
      (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
        ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams j < dl ∧
          SA.gateTime p.toParams j + L p ≤ dl ∧
          ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (FGSA.controls p st).Z)))) := by
  obtain ⟨D, Dh, hc⟩ := slow_certificate_consumer h hq hf hsrc htsrc hread hne hyG
  exact pending_gate_lease_or_F_on h.pre.base.valid h.pre.base.delta hf hne hc
    hgate hRows y hyG

end AvailableChain.FGSA.Run.Tests.OutageArming

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.slow_gate_consumer
#print axioms AvailableChain.FGSA.Run.arming_genesis_on

namespace AvailableChain.FGSA.Run.Tests.OutageArming

open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The Clean retained-history proof supplies provenance at each joined HEAD read. -/
theorem joined_provenance_consumer {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hV : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ) :
    ArmingJoinedProvenance (c := c) E rho := by
  intro s i y hy hi hJ
  have hs := hV.toScheduleWellFormed
  have hw := arming_joined_window (c := c) hy hJ
  have ht : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    rw [arming_proposal_eq, arming_vote_eq]; push_cast; linarith [p.deltaPos]
  obtain ⟨it, hit⟩ := arming_tick_exists hs hdelta hy (4 * s) (arming_proposal_nat p s)
    (ht.trans (hs.in_horizon _ (List.mem_of_getElem? hi)).2)
    (hw.awake _ (by rw [arming_proposal_eq]; have := p.deltaPos; positivity) le_rfl ht)
  exact clean_headVotes_provenance E rho hV i y s hi hJ hit

/-- The actual Clean induction constructs the general fast certificate at every cut. -/
theorem fast_general_certificate_consumer [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) :
    ∃ D Dh, ArmingSleepGateCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  have hh := clean_invariant p c E rho h.sleepPre hq hf hsrc (timeIdx rho b₀) le_rfl
  have hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i := by
    intro i hi
    exact cleanState_of_hist h.sleepPre hq hf hsrc (clean_actionStep p c E rho) hi
      (clean_invariant p c E rho h.sleepPre hq hf hsrc i hi)
  have htransfer := (cleanHistoryAt_body p c E rho h.sleepPre hq hf hsrc).2.2.1
  exact fast_arming_scoped_on h hf hsrc htsrc hState hh
    (fun y z s C H hy hz hJ hcut hRes hHead => htransfer y z s C H hy hz hcut hRes hJ hHead)
    (joined_provenance_consumer h.pre.base.valid h.pre.base.delta) hread hne

/-- The general fast producer feeds the same full gate result used by P-Ou. -/
theorem fast_general_gate_consumer [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    (hgate : SA.gateTime p.toParams (coverLabel p b₀) ≤ rho.horizon)
    (hRows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)) (Bh : FGBlock (Fin p.n)),
      eraseFG Bh = B → HonestRowBefore p c E rho
        (afterTicksIdx rho (SA.gateTime p.toParams (coverLabel p b₀))) y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e) :
    ∀ y ∈ coveredNodes p E rho true b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (coverLabel p b₀))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (coverLabel p b₀) < dl ∧
            SA.gateTime p.toParams (coverLabel p b₀) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z)))) := by
  obtain ⟨D, Dh, hc⟩ := fast_general_certificate_consumer h hq hf hsrc htsrc hread hne
  exact pending_gate_lease_or_F_scoped_on h.pre.base.valid h.pre.base.delta hf hne hc hgate hRows

end AvailableChain.FGSA.Run.Tests.OutageArming

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.joined_provenance_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.fast_general_certificate_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.fast_general_gate_consumer

#print axioms AvailableChain.FGSA.Run.arming_rest_bound_joined
#print axioms AvailableChain.FGSA.Run.arming_inclusion_proposer_prior_of_F_prefix_on
#print axioms AvailableChain.FGSA.Run.arming_inclusion_reader_scores_on
#print axioms AvailableChain.FGSA.Run.ArmingReadWindow
#print axioms AvailableChain.FGSA.Run.arming_fresh_head_service_window
#print axioms AvailableChain.FGSA.Run.arming_proposal_service_trigger_window
#print axioms AvailableChain.FGSA.Run.arming_proposal_anchor_service_window
#print axioms AvailableChain.FGSA.Run.arming_target_service_window
#print axioms AvailableChain.FGSA.Run.arming_head_not_excluded_window
#print axioms AvailableChain.FGSA.Run.arming_window_epoch
#print axioms AvailableChain.FGSA.Run.arming_window_read_epoch
#print axioms AvailableChain.FGSA.Run.arming_healthy_batch_window
#print axioms AvailableChain.FGSA.Run.arming_joined_window
#print axioms AvailableChain.FGSA.Run.arming_window_mono
#print axioms AvailableChain.FGSA.Run.arming_joined_gate_before
#print axioms AvailableChain.FGSA.Run.ArmingJoinedProvenance
#print axioms AvailableChain.FGSA.Run.arming_prefix_before_cut
#print axioms AvailableChain.FGSA.Run.arming_joined_head_from_previous
#print axioms AvailableChain.FGSA.Run.ArmingSleepGateCert
#print axioms AvailableChain.FGSA.Run.arming_sleep_gate_cert_of_last
#print axioms AvailableChain.FGSA.Run.arming_sleep_gate_core_scoped
#print axioms AvailableChain.FGSA.Run.pending_gate_lease_or_F_scoped_on
#print axioms AvailableChain.FGSA.Run.arming_fast_cert_of_comparison
#print axioms AvailableChain.FGSA.Run.fast_arming_scoped_on
#print axioms AvailableChain.FGSA.Run.arming_healthy_batch_heads
#print axioms AvailableChain.FGSA.Run.ArmingJoinedBatchState
#print axioms AvailableChain.FGSA.Run.arming_batch_at_on
#print axioms AvailableChain.FGSA.Run.arming_head_covers_on
#print axioms AvailableChain.FGSA.Run.arming_proposal_covers_on

#print axioms AvailableChain.FGSA.Run.slow_arming_scoped_on

namespace AvailableChain.FGSA.Run.Tests.OutageArming

open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The actual fast producer supplies all sleep duty-history consumers. -/
theorem fast_history_consumer [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    : ∃ D Dh, ArmingSleepHistoryCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hh := clean_invariant p c E rho h.sleepPre hq hf hsrc (timeIdx rho b₀) le_rfl
  have hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i := by
    intro i hi
    exact cleanState_of_hist h.sleepPre hq hf hsrc (clean_actionStep p c E rho) hi
      (clean_invariant p c E rho h.sleepPre hq hf hsrc i hi)
  obtain ⟨D, Dh, hc⟩ := fast_general_certificate_consumer h hq hf hsrc htsrc hread hne
  have hOut := clean_gateOutput_body p c E rho b₀ h.sleepPre hq hf hsrc
    (timeIdx rho b₀) le_rfl hh
  refine ⟨D, Dh, arming_sleep_history_on h hf hsrc hState hh ?_
    (joined_provenance_consumer h.pre.base.valid h.pre.base.delta) hc hne⟩
  intro j y s hj hG
  obtain ⟨C, hC, _, hS⟩ := hOut j y s hj
    (hs.honest_only _ (List.mem_of_getElem? hG.1)) hG
  exact ⟨C, hC, hS⟩

/-- The actual slow producer supplies all sleep duty-history consumers. -/
theorem slow_history_consumer [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c false E rho T b₀ b₁ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    {y : V} (hyG : y ∈ coveredNodes p E rho false b₀)
    : ∃ D Dh, ArmingSleepHistoryCert p c E rho false T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hh := clean_invariant p c E rho h.sleepPre hq hf hsrc (timeIdx rho b₀) le_rfl
  have hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i := by
    intro i hi
    exact cleanState_of_hist h.sleepPre hq hf hsrc (clean_actionStep p c E rho) hi
      (clean_invariant p c E rho h.sleepPre hq hf hsrc i hi)
  have htransfer := (cleanHistoryAt_body p c E rho h.sleepPre hq hf hsrc).2.2.1
  obtain ⟨D, Dh, hc⟩ := slow_arming_scoped_on h hf hsrc htsrc hState hh
    (fun y z s C H hy hz hJ hcut hRes hHead => htransfer y z s C H hy hz hcut hRes hJ hHead)
    (clean_epoch_saved_row h.sleepPre hq hf hsrc) hread hne hyG
  have hOut := clean_gateOutput_body p c E rho b₀ h.sleepPre hq hf hsrc
    (timeIdx rho b₀) le_rfl hh
  refine ⟨D, Dh, arming_sleep_history_on h hf hsrc hState hh ?_
    (joined_provenance_consumer h.pre.base.valid h.pre.base.delta) hc hne⟩
  intro j y s hj hG
  obtain ⟨C, hC, _, hS⟩ := hOut j y s hj
    (hs.honest_only _ (List.mem_of_getElem? hG.1)) hG
  exact ⟨C, hC, hS⟩

end AvailableChain.FGSA.Run.Tests.OutageArming

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.fast_history_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.slow_history_consumer

#print axioms AvailableChain.FGSA.Run.arming_leases_interval_sleep
#print axioms AvailableChain.FGSA.Run.arming_prefix_sleep_on
#print axioms AvailableChain.FGSA.Run.arming_duty_epochs
#print axioms AvailableChain.FGSA.Run.arming_duty_batch
#print axioms AvailableChain.FGSA.Run.arming_head_covers_sleep
#print axioms AvailableChain.FGSA.Run.arming_proposal_covers_sleep
#print axioms AvailableChain.FGSA.Run.arming_joined_of_tick_guard
#print axioms AvailableChain.FGSA.Run.arming_emit_proposal_on
#print axioms AvailableChain.FGSA.Run.arming_pending_duties_sleep
#print axioms AvailableChain.FGSA.Run.arming_inflight_heads_sleep
#print axioms AvailableChain.FGSA.Run.arming_S_interval_sleep
#print axioms AvailableChain.FGSA.Run.arming_confirmed_restart_bound
#print axioms AvailableChain.FGSA.Run.arming_confirmed_pre_pending_gate
#print axioms AvailableChain.FGSA.Run.arming_cover_sleep
#print axioms AvailableChain.FGSA.Run.ArmingSleepHistoryCert
#print axioms AvailableChain.FGSA.Run.arming_sleep_history_on

/-! Closed finite certificate witnesses. They test the records and production gate exports.
The fast trace delays a HEAD past its strict early read; it uses no healthy-prefix premise. -/

namespace AvailableChain.FGSA.Run.Tests.OutageArming.Finite
-- The finite state fold needs a deeper reduction stack. Heartbeats stay at the default.
set_option maxRecDepth 2048
abbrev p : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }
abbrev P := fgsa p unitCodec
def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
def head (s : Slot) : Obj p :=
  ⟨.seat (.base (.head s)) ⟨0, p.nPos⟩, .head (if s = 0 then genesisRoot else ⟨2⟩)⟩
def wire0 : HeadWire p.n := ⟨.seat (.head 0) ⟨0, by decide⟩, genesisRoot⟩
def body : NamedProposal p.n := namedProposal p .genesis 1 0 [wire0] [wire0] []
def proposal : Obj p := ⟨.seat (.prop 1) ⟨0, by decide⟩, .proposal body⟩
def run (late : Bool) : V2.D.Run (Fin 1) P where
  honest := {0}
  horizon := 18
  events := [.tick 0 0, .tick 0 1, .deliver 0 (head 0) 1,
    .tick 0 2, .tick 0 3, .tick 0 4, .deliver 0 proposal 4,
    .tick 0 5, .deliver 0 (head 1) 5, .tick 0 6, .tick 0 7, .tick 0 8,
    .tick 0 9] ++
    (if late then [.tick 0 10, .deliver 0 (head 2) 10]
      else [.deliver 0 (head 2) 9, .tick 0 10]) ++
    [.tick 0 11, .tick 0 12, .tick 0 13, .deliver 0 (head 3) 13,
      .tick 0 14, .tick 0 15, .tick 0 16, .tick 0 17,
      .deliver 0 (head 4) 17, .tick 0 18]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()
open AvailableChain.SimplexFG Gen.Pure
abbrev B : Block := body.erase
abbrev Bh : FGBlock (Fin p.n) := .node .genesis 1 ⟨2⟩ 0 []

def originIdx (i : Nat) : Nat :=
  if i = 2 then 1 else if i = 6 then 5 else if i = 8 then 7
  else if i = 13 ∨ i = 14 then 12 else if i = 18 then 17 else 22

def originTime (i : Nat) : Time :=
  if i = 2 then 1 else if i = 6 then 4 else if i = 8 then 5
  else if i = 13 ∨ i = 14 then 9 else if i = 18 then 13 else 17

def delivery_check (late : Bool) (i : Fin 25) : Prop :=
    match (run late).events[i.val]? with
    | some (.deliver v o _) => P.wellFormed o = true ∧
        P.depsPresent (V2.D.Run.stateBefore env (run late) i v) o = true ∧
        P.processed (V2.D.Run.stateBefore env (run late) i v) o = false
    | _ => True

theorem fgp_delivery_checks (late : Bool) : ∀ i : Fin 25, delivery_check late i := by
  unfold delivery_check
  intro i
  fin_cases i <;> cases late <;>
    simp only [run, Bool.false_eq_true, ite_false, ite_true, List.cons_append,
      List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ] <;> decide +kernel

def origin_check (late : Bool) (i : Fin 25) : Prop :=
    match (run late).events[i.val]? with
    | some (.deliver v o t) => originTime i ≤ t ∧
        (run late).events[originIdx i]? = some (.tick v (originTime i)) ∧
        o ∈ V2.D.Run.emitsAt env (run late) (originIdx i)
    | _ => True

theorem origin_checks (late : Bool) : ∀ i : Fin 25, origin_check late i := by
  unfold origin_check
  intro i
  fin_cases i <;> cases late <;>
    simp only [run, Bool.false_eq_true, ite_false, ite_true, List.cons_append,
      List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ]
  all_goals first
    | trivial
    | (refine ⟨by decide, rfl, ?_⟩
       first
         | (change head 0 ∈ [head 0]; exact List.mem_singleton_self _)
         | (change proposal ∈ [proposal]; exact List.mem_singleton_self _)
         | (change head 1 ∈ [head 1]; exact List.mem_singleton_self _)
         | (change head 2 ∈ [head 2]; exact List.mem_singleton_self _)
         | (change head 3 ∈ [head 3]; exact List.mem_singleton_self _)
         | (change head 4 ∈ [head 4]; exact List.mem_singleton_self _))

theorem schedule_valid (late : Bool) : V2.D.ScheduleWellFormed env (run late) := by
  refine ⟨by change 0 ≤ (18 : Time); decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases late <;> decide
  · cases late <;> decide
  · intro e he
    cases late <;> simp [run] at he
    all_goals rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he
    have : e.node = 0 := Subsingleton.elim _ _
    simp [this, run]
  · intro v t _
    refine ⟨t.toNat, ?_⟩
    have ht : 0 ≤ t := by
      have he : V2.Event.tick v t ∈ (run late).events := by assumption
      cases late <;> simp [run] at he
      all_goals rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> decide
    simp [env, Int.toNat_of_nonneg ht]
  · intro v _ t ⟨k, hk⟩ ht hh _
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t = (k : Time) * 1 at hk
    change t ≤ 18 at hh
    have hkb : k ≤ 18 := by dsimp [Time] at *; omega
    interval_cases k <;> cases late <;> simp [run] <;> dsimp [Time] at * <;> omega

theorem delivery_valid (late : Bool) : V2.D.DeliveryWellFormed env (run late) := by
  constructor
  all_goals intro i v o t hi
  all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
  all_goals have hb : i < 25 := by cases late <;> simpa [run] using hib
  all_goals have hc := fgp_delivery_checks late ⟨i, hb⟩
  all_goals dsimp only [delivery_check] at hc
  all_goals rw [hi] at hc
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2

theorem signatures_valid (late : Bool) : V2.D.UnforgeableSignatures env (run late) := by
  constructor
  · intro v o t ⟨i, hi⟩ u _ _
    have hu : u = v := Subsingleton.elim _ _
    subst u
    have hb : i < 25 := by
      cases late <;> simpa [run] using (List.getElem?_eq_some_iff.mp hi).1
    have hc := origin_checks late ⟨i, hb⟩
    dsimp only [origin_check] at hc
    rw [hi] at hc
    exact ⟨originTime i, hc.1, originIdx i, hc.2.1, hc.2.2⟩
  · intro v o t ⟨i, hi⟩ o' hc u _ _
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    have he := List.mem_of_getElem? hi
    cases late <;> simp [run] at he
    all_goals rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals first
      | (change False at hc; exact hc.elim)
      | (have ho : o' = head 0 := by
          change o' ∈ [head 0] ∨ o' ∈ [head 0] ∨ o' ∈ [] at hc
          rcases hc with hh | hh | hh
          · exact List.mem_singleton.mp hh
          · exact List.mem_singleton.mp hh
          · exact (List.not_mem_nil hh).elim
         subst o'
         exact ⟨1, by decide, 1, rfl, by
         change head 0 ∈ [head 0]
         exact List.mem_singleton_self _⟩)

theorem fgp_sleep_valid (late : Bool) : V2.D.SleepWellFormed env (run late) := by
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, ?_⟩
  intro v _ t _ _ hw
  have hf := hw.2
  change true = false at hf
  cases hf

theorem fgp_valid (late : Bool) : V2.D.ExecutionValid env (run late) :=
  { toScheduleWellFormed := schedule_valid late
    toDeliveryWellFormed := delivery_valid late
    toUnforgeableSignatures := signatures_valid late
    toSleepWellFormed := fgp_sleep_valid late }

theorem read (late : Bool) :
    V2.D.outputAt env (run late) (fgsaInterface p unitCodec).stable 0 10 = B := by
  cases late <;> decide +kernel

theorem receiver (late : Bool) : 0 ∈ coveredNodes p env (run late) late 14 := by
  classical
  rw [coveredNodes, Finset.mem_filter]
  refine ⟨by simp [run], ?_⟩
  cases late
  · change 2 ≤ 4 ∧ AwakeClosed env 0 8 18 ∧ RestartFreeTime (run false) 0 8 18
    refine ⟨by decide, ?_, ?_⟩
    · intro t _ _ _; rfl
    · intro u _ _ he
      simp [run] at he
  · change joinedAt p env (run true) 0 4 18
    refine ⟨rfl, ?_, ?_⟩
    · intro u _ _ hw
      have hh := hw.2
      change true = false at hh
      cases hh
    · intro u _ _ he
      simp [run] at he

theorem result_table (late : Bool) : ∀ i : Fin 20,
    gateResultAt p unitCodec env (run late) i ∈
      [none, some none, some (some .genesis), some (some B)] := by
  cases late <;> decide +kernel

theorem maximum (late : Bool) : ∀ r C,
    (r, C) ∈ cleanResults p unitCodec env (run late) (timeIdx (run late) 14) →
    r ≤ 2 → Block.Preceq C B := by
  intro r C ⟨i, hi, y, ht, hJ, hC⟩ _
  have hb : i < 20 := by cases late <;> change i < 20 at hi <;> exact hi
  have hs := result_table late ⟨i, hb⟩
  rw [hC] at hs
  simp only [List.mem_cons, List.not_mem_nil, Option.some.injEq, reduceCtorEq,
    or_false, false_or] at hs
  rcases hs with rfl | rfl
  · exact Gen.Pure.block_genesis_preceq B
  · exact Gen.Pure.block_preceq_refl B

theorem origin (late : Bool) :
    (1, B) ∈ cleanResults p unitCodec env (run late) (timeIdx (run late) 14) := by
  cases late
  · exact ⟨14, by decide, 0, rfl, trivial, by decide +kernel⟩
  · exact ⟨13, by decide, 0, rfl, trivial, by decide +kernel⟩

theorem no_last : ¬ ∃ C,
    (2, C) ∈ cleanResults p unitCodec env (run true) (timeIdx (run true) 14) := by
  rintro ⟨C, i, hi, y, ht, _, hC⟩
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  have hb : i < 20 := by change i < 20 at hi; exact hi
  change (run true).events[i]? = some (.tick 0 14) at ht
  interval_cases i <;> simp [run] at ht
  have hn : gateResultAt p unitCodec env (run true) 19 = some none := by decide +kernel
  rw [hn] at hC
  cases hC

theorem source_bound (late : Bool) : ∀ y r C, y ∈ (run late).honest →
    p.actionTime r < SA.gateTime p.toParams 3 →
    actionSource p unitCodec env (run late) y r = some (some C) → Block.Preceq C B := by
  intro y r C _ hr hC
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  have hb : r ≤ 1 := by change 4 * 1 * ((r * 2 : Nat) : Int) + 6 * 1 < 18 at hr; omega
  interval_cases r <;> cases late
  · have hn : actionSource p unitCodec env (run false) 0 0 = some none := by decide +kernel
    rw [hn] at hC
    cases hC
  · have hn : actionSource p unitCodec env (run true) 0 0 = some none := by decide +kernel
    rw [hn] at hC
    cases hC
  · have hn : actionSource p unitCodec env (run false) 0 1 = some (some B) :=
      by decide +kernel
    rw [hn] at hC
    cases Option.some.inj (Option.some.inj hC)
    exact Gen.Pure.block_preceq_refl B
  · have hn : actionSource p unitCodec env (run true) 0 1 = some none := by decide +kernel
    rw [hn] at hC
    cases hC

theorem finality_table (late : Bool) : ∀ i : Fin 25,
    F_at p unitCodec env (run late) i 0 = .genesis := by
  cases late <;> decide +kernel

theorem finality_bound (late : Bool) : ∀ i y,
    i ≤ (run late).idxBefore (SA.gateTime p.toParams 3) → y ∈ (run late).honest →
    Block.Preceq (F_at p unitCodec env (run late) i y) B := by
  intro i y hi _
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  have hb : i < 25 := by cases late <;> change i ≤ 24 at hi <;> omega
  rw [finality_table late ⟨i, hb⟩]
  exact Gen.Pure.block_genesis_preceq B

theorem pending_input (late : Bool) :
    ArmingGateInput p (clockPre p (storeAt p unitCodec env (run late) 24 0) 18)
      late 3 B B := by
  refine ⟨?_, ⟨B, ?_, Gen.Pure.block_preceq_refl B⟩, ?_, ?_, ?_, ?_, ?_⟩
  · cases late <;> decide +kernel
  · cases late <;> decide +kernel
  · cases late <;> decide +kernel
  · cases late <;> decide +kernel
  · cases late <;> exact Gen.Pure.block_compatible_of_common
      (by decide +kernel : Block.Preceq (eraseFG _) B) (Gen.Pure.block_preceq_refl B)
  · cases late <;> decide +kernel
  · intro hf
    have he : late = false := hf
    subst late
    refine ⟨by decide, ?_⟩
    intro a ha
    have ha0 : a = 0 := by change a < 1 at ha; omega
    subst a
    exact ⟨B, by decide +kernel, Gen.Pure.block_preceq_refl B⟩

theorem pending (late : Bool) : ∀ i y, IsGateTick p unitCodec (run late) i y 3 →
    y ∈ coveredNodes p env (run late) late 14 →
    Block.Preceq B (F_at p unitCodec env (run late) i y) ∨
      ArmingGateInput p (clockPre p (storeAt p unitCodec env (run late) i y)
        (SA.gateTime p.toParams 3)) late 3 B B := by
  intro i y ht _
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  change (run late).events[i]? = some (.tick 0 18) at ht
  have hib := (List.getElem?_eq_some_iff.mp ht).1
  have hb : i < 25 := by cases late <;> simpa [run] using hib
  have hi : i = 24 := by
    cases late <;> interval_cases i <;> simp [run] at ht ⊢
  subst i
  exact Or.inr (pending_input late)

theorem fast_certificate :
    ArmingSleepGateCert p unitCodec env (run true) true 10 14 B 2 B Bh := by
  refine ⟨⟨1, B, by decide, origin true, le_rfl, Gen.Pure.block_preceq_refl B⟩,
    rfl, Gen.Pure.block_preceq_refl B, ⟨1, by decide, origin true⟩, maximum true,
    le_rfl, by decide, rfl, source_bound true, ?_, finality_bound true, pending true⟩
  intro z _ _ i ht
  have hz : z = 0 := Subsingleton.elim _ _
  subst z
  change (run true).events[i]? = some (.tick 0 13) at ht
  have hib := (List.getElem?_eq_some_iff.mp ht).1
  have hb : i < 25 := by simpa [run] using hib
  have hi : i = 17 := by interval_cases i <;> simp [run] at ht ⊢
  subst i
  decide +kernel

theorem slow_certificate :
    ArmingSleepCert p unitCodec env (run false) false 10 14 B 2 B Bh := by
  refine ⟨⟨1, B, by decide, origin false, le_rfl, Gen.Pure.block_preceq_refl B⟩,
    rfl, Gen.Pure.block_preceq_refl B, ?_, maximum false,
    le_rfl, by decide, rfl, source_bound false, finality_bound false, pending false⟩
  exact ⟨19, by decide, 0, rfl, trivial, by decide +kernel⟩

theorem fast_gate :
    Block.Preceq B (S_at p unitCodec env (run true) 25 0) ∧
      ∃ dl, leaseOf (storeAt p unitCodec env (run true) 25 0) B = some dl ∧
        18 < dl ∧ 18 + L p ≤ dl := by
  have hc := arming_sleep_gate_core_scoped (fgp_valid true) rfl (by decide : B ≠ .genesis)
    fast_certificate (by decide) 0 (receiver true)
  have hF : F_at p unitCodec env (run true) 25 0 = .genesis := by decide +kernel
  change Block.Preceq B (S_at p unitCodec env (run true) 25 0) ∧ _ at hc
  refine ⟨hc.1, ?_⟩
  rcases hc.2 with hf | ⟨_, _, dl, hl, ht, hd, _⟩
  · change Block.Preceq B (F_at p unitCodec env (run true) 25 0) at hf
    rw [hF] at hf
    exact (by decide : ¬ Block.Preceq B .genesis) hf |>.elim
  · exact ⟨dl, hl, ht, hd⟩

theorem slow_gate :
    Block.Preceq B (S_at p unitCodec env (run false) 25 0) ∧
      ∃ dl, leaseOf (storeAt p unitCodec env (run false) 25 0) B = some dl ∧
        18 < dl ∧ 18 + L p ≤ dl := by
  have hc := arming_sleep_gate_core (fgp_valid false) rfl (by decide : B ≠ .genesis)
    slow_certificate (by decide) 0 (receiver false)
  have hF : F_at p unitCodec env (run false) 25 0 = .genesis := by decide +kernel
  change Block.Preceq B (S_at p unitCodec env (run false) 25 0) ∧ _ at hc
  refine ⟨hc.1, ?_⟩
  rcases hc.2 with hf | ⟨_, _, dl, hl, ht, hd, _⟩
  · change Block.Preceq B (F_at p unitCodec env (run false) 25 0) at hf
    rw [hF] at hf
    exact (by decide : ¬ Block.Preceq B .genesis) hf |>.elim
  · exact ⟨dl, hl, ht, hd⟩

/-- The fast cut is exactly the label-3 early read, with no label-2 result. -/
theorem equal_cut : coverLabel p 14 = 3 ∧ SA.earlyTime p.toParams 3 = 14 ∧
    (((14 - 6 * p.Δ) / (4 * p.Δ)).toNat : Slot) = 2 := by decide

/-- All positive fast inputs and the executed lease conclusion hold on one finite run. -/
theorem positive_fast :
    V2.D.ExecutionValid env (run true) ∧ B ≠ .genesis ∧
      V2.D.outputAt env (run true) (fgsaInterface p unitCodec).stable 0 10 = B ∧
      0 ∈ coveredNodes p env (run true) true 14 ∧
      ArmingSleepGateCert p unitCodec env (run true) true 10 14 B 2 B Bh ∧
      (¬ ∃ C, (2, C) ∈ cleanResults p unitCodec env (run true) (timeIdx (run true) 14)) ∧
      Block.Preceq B (S_at p unitCodec env (run true) 25 0) ∧
        ∃ dl, leaseOf (storeAt p unitCodec env (run true) 25 0) B = some dl ∧
          18 < dl ∧ 18 + L p ≤ dl := by
  exact ⟨fgp_valid true, by decide, read true, receiver true, fast_certificate, no_last, fast_gate⟩

/-- The slow run has a label-2 result, a current-epoch saved row, and an executed lease. -/
theorem positive_slow :
    V2.D.ExecutionValid env (run false) ∧ B ≠ .genesis ∧
      V2.D.outputAt env (run false) (fgsaInterface p unitCodec).stable 0 10 = B ∧
      0 ∈ coveredNodes p env (run false) false 14 ∧
      ArmingSleepCert p unitCodec env (run false) false 10 14 B 2 B Bh ∧
      Block.Preceq B (S_at p unitCodec env (run false) 25 0) ∧
        ∃ dl, leaseOf (storeAt p unitCodec env (run false) 25 0) B = some dl ∧
          18 < dl ∧ 18 + L p ≤ dl := by
  exact ⟨fgp_valid false, by decide, read false, receiver false, slow_certificate, slow_gate⟩

end AvailableChain.FGSA.Run.Tests.OutageArming.Finite

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.delivery_check
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.fgp_delivery_checks
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.origin_check
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.origin_checks
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.schedule_valid
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.delivery_valid
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.signatures_valid
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.fgp_sleep_valid
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.fgp_valid
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.read
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.receiver
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.result_table
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.maximum
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.origin
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.no_last
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.source_bound
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.finality_table
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.finality_bound
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.pending_input
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.pending
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.fast_certificate
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.slow_certificate
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.fast_gate
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.slow_gate
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.equal_cut
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.positive_fast
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.Finite.positive_slow

namespace AvailableChain.FGSA.Run.Tests.OutageArming

/-- The continuation prefix input needs no outage budget or OutageE1 assumption. -/
theorem continuation_prefix_consumer {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
    OutagePrefixReceipt p c E rho fast T b₀ := by
  exact arming_continuation_prefix_receipt h

end AvailableChain.FGSA.Run.Tests.OutageArming

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.continuation_prefix_consumer

#print axioms AvailableChain.FGSA.Run.arming_nonrow_delivery_of_prefix
#print axioms AvailableChain.FGSA.Run.arming_fresh_head_service_of_prefix
#print axioms AvailableChain.FGSA.Run.arming_proposal_service_trigger_of_prefix
#print axioms AvailableChain.FGSA.Run.arming_proposal_anchor_service_of_prefix
#print axioms AvailableChain.FGSA.Run.arming_target_service_of_prefix
#print axioms AvailableChain.FGSA.Run.arming_head_not_excluded_of_prefix
#print axioms AvailableChain.FGSA.Run.arming_batch_service_of_prefix
#print axioms AvailableChain.FGSA.Run.arming_prefix_receipt_of_healthy_prefix
#print axioms AvailableChain.FGSA.Run.arming_continuation_prefix_receipt
