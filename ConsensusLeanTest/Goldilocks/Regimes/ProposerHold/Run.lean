module
public import ConsensusLean.Lemmas.Model.Retain
public import ConsensusLean.Lemmas.Model.Canonical.Inject
public import ConsensusLean.Lemmas.Model.Adequate
public import ConsensusLean.Lemmas.Model.SysLog
public import ConsensusLean.Lemmas.Shape.Payload
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
import all ConsensusLean.Lemmas.Model.Canonical.Events
import all ConsensusLean.Lemmas.Model.Retain
@[expose] public section

/-! # The proposer-hold counterexample: the run and its premises

The compiled Goldilocks run of the hold-zero counterexample (`ProposerHold.lean`), at every
`Setup`: five validators with the identity PKI, everyone awake, `ΔAC = ΔFG = 3` (slots of `12`),
horizon `41`, no submissions. Key `0` is faulty from the start and silent; key `1` proposes
slot `1` (at time `12`) and is compromised at `13`; key `2` proposes every other slot. The
schedule (`Model.Run.injectEvents`) is the canonical one with two changes: the objects key `1`
releases at time `12` reach the others at `14` (`delay`), and the forged twin `P'` of slot `1`
(parent genesis, empty payload, an input no honest proposal has) is delivered to the honest nodes
at `13` (`inj`), signed by the then compromised key `1`.

This file proves the run-level facts: validity, synchrony (`PSync 0`), no hash collision (the
hash is injective), the sleepy participation of the contract (look-ahead `ahead = 5`), the
hold-`0` recurrence (and the failure of the hold-`1` one), and the payload of honest proposals. -/

namespace Consensus.Goldilocks.Test.ProposerHold
open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

/-- `ΔAC = ΔFG = 3`, everyone awake at every time. -/
def env : Env (Fin 5) := ⟨3, by decide, 3, by decide, fun _ _ => true⟩

/-- Key `0` from the start, key `1` from `13`. -/
def faulty (t : Time) : Finset (Fin 5) := if 13 ≤ t then {0, 1} else {0}

theorem faulty_mono : Monotone faulty := by
  intro a b hab
  unfold faulty
  split_ifs with ha hb
  · exact le_rfl
  · exact absurd (ha.trans hab) hb
  · decide
  · exact le_rfl

theorem faulty_of_lt {t : Time} (ht : t < 13) : faulty t = {0} := by
  simp [faulty, not_le.mpr ht]

theorem faulty_of_ge {t : Time} (ht : 13 ≤ t) : faulty t = {0, 1} := by
  simp [faulty, ht]

theorem one_le_card : 1 ≤ Fintype.card (Fin 5) := by decide

/-- A key of the run. -/
abbrev key (i : Nat) (h : i < 5 := by decide) : Fin (Fintype.card (Fin 5)) := ⟨i, by simpa using h⟩

variable (S : Setup)

/-- The objects of the compiled family in `env`. -/
abbrev Obj := (Model.protoOf (compiled (goldilocks S)) env).Object

/-- The run's event type. -/
abbrev Ev := Model.Event (Fin 5) (Obj S)

/-- Key `1` proposes slot `1`, key `2` every other slot; everyone polls. -/
def sel : (Model.protoOf (compiled (goldilocks S)) env).Role → Finset (Fin (Fintype.card (Fin 5)))
  | .proposer s => if s = 1 then {key 1} else {key 2}
  | .duty _ k => k.elim
  | .poll => Finset.univ

theorem sel_admits : (Model.protoOf (compiled (goldilocks S)) env).SelAdmits (sel S) := by
  intro r
  cases r with
  | proposer s =>
    show (sel S (.proposer s)).card = min 1 (Fintype.card (Fin 5))
    simp only [sel]
    split_ifs <;> simp
  | duty _ k => exact k.elim
  | poll => rfl

/-- The forged header: parent genesis, slot `1`, empty payloads, and an input no honest
proposal writes (`encodeTxs [] + 1`; honest inputs are `encodeTxs []`, nothing is submitted). -/
def hdr : Header Info := ⟨.root, 1, encodeTxs [] + 1, ([], [], [])⟩

/-- The forged twin of slot `1`, signed by key `1` in its proposer role, carrying nothing. -/
def twin : Obj S := .mk (.signed (key 1) (.proposer 1)) (.item hdr) []

/-- An injective code of headers. -/
noncomputable def enc : Header Info → Nat := (Countable.exists_injective_nat (Header Info)).choose

theorem enc_injective : Function.Injective enc :=
  (Countable.exists_injective_nat (Header Info)).choose_spec

open Classical in
/-- The hash: `0` for the forged header, `enc + 1` otherwise (injective). -/
noncomputable def hash (h : Header Info) : Nat := if h = hdr then 0 else enc h + 1

theorem hash_injective : Function.Injective hash := by
  intro a b hab
  unfold hash at hab
  by_cases ha : a = hdr <;> by_cases hb : b = hdr
  · exact ha.trans hb.symm
  · simp [ha, hb] at hab
  · simp [ha, hb] at hab
  · simp only [ha, hb, ↓reduceIte, add_left_inj] at hab
    exact enc_injective hab

/-- The base run: the point, the PKI, the selection and the hash; no events. -/
noncomputable def base : Model.Run (compiled (goldilocks S)) env :=
  ⟨faulty, faulty_mono, 41, [], Equiv.refl _, sel S, fun _ _ => [], fun _ _ => [], hash⟩

/-- Key `1`'s releases at time `12` are held back by `2`. -/
def delay (e : Ev S) : Time := if e.node = 1 ∧ e.time = 12 then 2 else 0

/-- The forged twin goes to every honest node at `13`. -/
def inj (t : Time) (_ : Fin 5) : List (Obj S) := if t = 13 then [twin S] else []

/-- **The run.** -/
noncomputable def rho : Model.Run (compiled (goldilocks S)) env := (base S).injectRun (delay S) (inj S)

theorem rho_faultyAt : (rho S).faultyAt = faulty := Model.Run.withEvents_faultyAt _ _

theorem rho_horizon : (rho S).horizon = 41 := Model.Run.withEvents_horizon _ _

theorem rho_key : (rho S).key = Equiv.refl _ := Model.Run.withEvents_key _ _

theorem rho_sel : (rho S).sel = sel S := Model.Run.withEvents_sel _ _

theorem rho_hash : (rho S).hash = hash := by rfl

theorem rho_point : (rho S).point = ⟨env, faulty, faulty_mono, 41, fun _ _ => []⟩ :=
  Model.Run.withEvents_point _ _

theorem rho_submit : (rho S).submit = fun _ _ => [] := congrArg EnvPoint.submit (rho_point S)

theorem rho_events : (rho S).events = (base S).injectEvents (delay S) (inj S) :=
  Model.Run.withEvents_events _ _

theorem delay_nonneg (e : Ev S) : 0 ≤ delay S e := by
  unfold delay; split_ifs <;> decide

theorem delay_lt (e : Ev S) : delay S e < 3 := by
  unfold delay; split_ifs <;> decide

theorem mem_inj {t : Time} {v : Fin 5} {o : Obj S} : o ∈ inj S t v ↔ t = 13 ∧ o = twin S := by
  unfold inj; split_ifs with h <;> simp [h]

theorem twin_contains {d : Obj S} (h : Model.Obj.Contains (twin S) d) : d = twin S := by
  rcases h.cases with h | ⟨c, hc, -⟩
  · exact h
  · simp [twin, Model.Obj.carried] at hc

/-- **The run is valid**: the twin is signed by key `1`, compromised at `13`, in the role the
selection gives it. -/
theorem rho_valid : (rho S).ExecutionValid := by
  apply (base S).injectEvents_valid (delay S) (inj S) (by simp [base]) (sel_admits S)
    (delay_nonneg S)
  · intro t v o ho d hd u hu
    obtain ⟨rfl, rfl⟩ := (mem_inj S).mp ho
    obtain rfl := twin_contains S hd
    change some ((base S).key (key 1)) = some u at hu
    obtain rfl := Option.some.inj hu
    show (1 : Fin 5) ∈ faulty 13
    decide
  · intro t v o ho d hd k r ha
    obtain ⟨rfl, rfl⟩ := (mem_inj S).mp ho
    obtain rfl := twin_contains S hd
    simp only [twin, Model.Obj.auth] at ha
    obtain ⟨rfl, rfl⟩ := ha
    simp [base, sel]

/-- **The run is synchronous**: every delay is below `ΔAC = ΔFG = 3`. -/
theorem rho_psync : (rho S).log.PSync (rho S).point 0 := by
  apply (base S).injectEvents_psync (delay S) (inj S) (by simp [base]) (by decide) (by decide)
    (fun e => ⟨delay_nonneg S e, delay_lt S e, delay_lt S e⟩)
  rw [Model.Run.eagerTxDelivery_iff]
  intro u x τ _ _ _ hx
  exact absurd hx (by simp [base, Model.Run.injectRun, Model.Run.withEvents])

theorem rho_not_hashCollision : ¬ (rho S).HashCollision := by
  apply Model.Run.not_hashCollision_of_injective
  rw [Model.Run.injectiveHash_iff, rho_hash]
  exact hash_injective

/-! ### The contract at a proposer hold -/

/-- The Goldilocks contract with proposer hold `h`: only `hold` differs from
`goldilocksContract`. -/
abbrev holdContract {S : Setup} (A : ContractAssumptions S) (C : ContractCoefficients) (h : Nat) :
    Contract ProgressReq :=
  { goldilocksContract A C with
    progress := fun cap X => .recur
      { pattern := if cap = .final then finalWindow A else Pattern.single, gap := X, hold := h } }

theorem holdContract_one {S : Setup} (A : ContractAssumptions S) (C : ContractCoefficients) :
    holdContract A C 1 = goldilocksContract A C := rfl

/-- The run as a run of the compiled system. -/
noncomputable abbrev run : (Sys (goldilocks S) (Fin 5)).Run := ⟨env, rho S⟩

theorem run_pt : (Sys (goldilocks S) (Fin 5)).pt (run S) =
    ⟨env, faulty, faulty_mono, 41, fun _ _ => []⟩ := rho_point S

/-- On the view retained through a time `≥ 13`, the ready validators are `2, 3, 4`. -/
theorem retain_readyAt {d : Time} (hd : 13 ≤ d) (c t : Time) :
    ((⟨env, faulty, faulty_mono, 41, fun _ _ => []⟩ : EnvPoint (Fin 5)).retain d).readyAt c t =
      {2, 3, 4} := by
  unfold EnvPoint.readyAt
  ext v
  simp only [EnvPoint.retain, Finset.mem_filter, Finset.mem_univ, true_and, EnvPoint.Ready,
    EnvPoint.HonestAt, EnvPoint.AwakeOnClosed, faulty_of_ge hd, env, implies_true, and_true]
  revert v
  decide

variable {S}

/-- **The sleepy regime of the contract** (`PSync 0`, and `θ = ½` participation on the views
retained through the look-ahead `ahead·ΔAC = 15`: three ready against two compromised). -/
theorem run_sleepy (A : ContractAssumptions S) (C : ContractCoefficients) (h : Nat) :
    (Sys (goldilocks S) (Fin 5)).Sleepy (holdContract A C h) (run S) := by
  refine ⟨(Model.sysOf_delivers_iff (rho S) _ _ _).mpr (rho_psync S), ?_⟩
  intro t ht0 ht
  rw [show (Sys (goldilocks S) (Fin 5)).aheadDur (holdContract A C h) (run S) = 15 from rfl]
  rw [run_pt] at ht ⊢
  have hd : 13 ≤ EnvPoint.lookAhead ⟨env, faulty, faulty_mono, 41, fun _ _ => []⟩ 15 t := by
    change 13 ≤ min (t + 15) 41
    dsimp only [Time] at *
    omega
  unfold EnvPoint.ReadyAbove
  rw [retain_readyAt hd]
  simp only [EnvPoint.faultCount, EnvPoint.retain, faulty_of_ge hd]
  change (1 / 2 : ℚ) * (_ + _) < _
  norm_num [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton]

/-- The slot times of the run: slots of `4·ΔAC = 12`. -/
theorem grid_slotTime (s : Nat) : (goldilocks S (pubOf env)).skel.grid.slotTime s = (s : Time) * 12 :=
  by change (s : Time) * (4 * 3) = _; norm_num

/-- The proposer of slot `s` in the run. -/
theorem rho_sel_proposer (s : Nat) :
    (rho S).sel (.proposer s) = if s = 1 then {key 1} else {key 2} := by
  rw [rho_sel]; rfl

/-- **The hold-`0` recurrence holds on the whole run**, at the available output and index `1`:
every window of one slot holds a slot whose proposer is ready and honest at its slot time
(key `1` at `12`, key `2` at `24` and `36`). -/
theorem run_prog_zero (A : ContractAssumptions S) (C : ContractCoefficients) :
    (Sys (goldilocks S) (Fin 5)).prog (shapeProgress (goldilocks S) (Fin 5))
      (holdContract A C 0) .available 1 0 ((Sys (goldilocks S) (Fin 5)).pt (run S)).horizon
      (run S) := by
  show PatternRecurrence (rho S).point (rho S).key (fun s => (rho S).sel (.proposer s))
    (goldilocks S (pubOf env)).skel.grid ⟨Pattern.single, 1, 0⟩ _ 0 (rho S).point.horizon
  intro t ht0 hte _
  rw [rho_point] at hte
  change 0 ≤ t at ht0
  change t + ((1 + 0 : Nat) : Time) * (4 * 3) ≤ 41 at hte
  let s : Nat := if t < 12 then 1 else if t < 24 then 2 else 3
  refine ⟨s, ?_, ?_, ?_⟩
  · rw [grid_slotTime]
    simp only [s]; split_ifs <;> push_cast <;> dsimp only [Time] at * <;> omega
  · rw [grid_slotTime]
    change _ ≤ t + ((1 : Nat) : Time) * (4 * 3)
    simp only [s]; split_ifs <;> push_cast <;> dsimp only [Time] at * <;> omega
  · intro j hj
    simp [Pattern.single] at hj
    subst hj
    change ((rho S).sel (.proposer (s + 0))).Nonempty ∧ ∀ k ∈ (rho S).sel (.proposer (s + 0)), _
    rw [rho_sel_proposer, grid_slotTime, rho_point]
    by_cases h1 : s + 0 = 1
    · simp only [h1, ↓reduceIte]
      refine ⟨Finset.singleton_nonempty _, fun k hk => ?_⟩
      rw [Finset.mem_singleton.mp hk, rho_key]
      refine ⟨⟨?_, fun _ _ _ => rfl⟩, ?_⟩
      · change (1 : Fin 5) ∉ faulty (((1 : Nat) : Time) * 12)
        rw [faulty_of_lt (by norm_num)]; decide
      · change (1 : Fin 5) ∉ faulty (min (((1 : Nat) : Time) * 12 + ((0 : Nat) : Time) * 3) 41)
        rw [faulty_of_lt (by norm_num)]; decide
    · simp only [h1, ↓reduceIte]
      refine ⟨Finset.singleton_nonempty _, fun k hk => ?_⟩
      rw [Finset.mem_singleton.mp hk, rho_key]
      refine ⟨⟨?_, fun _ _ _ => rfl⟩, ?_⟩
      · change (2 : Fin 5) ∉ faulty _
        unfold faulty; split_ifs <;> decide
      · change (2 : Fin 5) ∉ faulty _
        unfold faulty; split_ifs <;> decide

/-- **The run fails the hold-`1` recurrence**: the window after `0` holds only slot `1`, whose
proposer is compromised at `t_1 + ΔAC = 15`. So the run does not refute hold `1`. -/
theorem run_not_prog_one (A : ContractAssumptions S) (C : ContractCoefficients) :
    ¬ (Sys (goldilocks S) (Fin 5)).prog (shapeProgress (goldilocks S) (Fin 5))
      (goldilocksContract A C) .available 1 0 41 (run S) := by
  intro h
  change PatternRecurrence (rho S).point (rho S).key (fun s => (rho S).sel (.proposer s))
    (goldilocks S (pubOf env)).skel.grid ⟨Pattern.single, 1, 1⟩ _ 0 41 at h
  have h0 := h 0 le_rfl (by show (0 : Time) + ((1 + 0 : Nat) : Time) * (4 * 3) ≤ 41; norm_num)
    (by rw [rho_point]; show (0 : Time) + ((1 + 0 : Nat) : Time) * (4 * 3) ≤ 41; norm_num)
  obtain ⟨s, hs1, hs2, hs⟩ := h0
  rw [grid_slotTime] at hs1 hs2
  change _ ≤ (0 : Time) + ((1 : Nat) : Time) * (4 * 3) at hs2
  have hs1' : s = 1 := by
    have h1 : (0 : Int) < (s : Int) * 12 := hs1
    have h2 : (s : Int) * 12 ≤ 12 := by simpa using hs2
    have key : ∀ n : Nat, (0 : Int) < n * 12 → (n : Int) * 12 ≤ 12 → n = 1 := by intro n; omega
    exact key s h1 h2
  subst hs1'
  obtain ⟨-, hk⟩ := hs 0 (by simp [Pattern.single])
  have hk1 := (hk (key 1) (by show key 1 ∈ (rho S).sel (.proposer (1 + 0)); rw [rho_sel_proposer]; simp)).2
  rw [rho_point, rho_key, grid_slotTime] at hk1
  change (1 : Fin 5) ∉ faulty (min (((1 + 0 : Nat) : Time) * 12 + ((1 : Nat) : Time) * 3) 41) at hk1
  exact hk1 (by rw [faulty_of_ge (by norm_num)]; decide)

/-- **Every honest proposal differs from the forged header**: its input is the empty mempool's. -/
theorem honestProposal_ne_hdr {τ : Time} {k : Fin (Fintype.card (Fin 5))} {h : Header Info}
    (hp : HonestProposal (rho S) τ k h) : h ≠ hdr := by
  intro he
  have hi := honestProposal_payload (rho_valid S) hp
  have hm : Model.mempool (rho S).inbox ((rho S).key k) τ = [] := by
    unfold Model.mempool Model.Run.inbox
    rw [rho_submit]
    split_ifs
    · rfl
    · simp [rho, base, Model.Run.injectRun, Model.Run.withEvents]
  rw [hm, he] at hi
  simp [hdr] at hi

end Consensus.Goldilocks.Test.ProposerHold

end
