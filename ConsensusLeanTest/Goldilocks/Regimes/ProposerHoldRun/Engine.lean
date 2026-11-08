module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import all ConsensusLean.Lemmas.Model.Canonical.Events
import all ConsensusLean.Lemmas.Model.Canonical.Inject
import all ConsensusLean.Lemmas.Model.Truncate
import all ConsensusLean.Lemmas.Model.Retain
@[expose] public section

/-! # The proposer-hold counterexample: engine provenance

Two object-indexed provenance facts of the run (`closed_of_sources` of `Canonical/Inject`):

* `delivered_proposal`: up to time `13`, every object delivered to a node carries no proposer-signed
  object but the forged twin. Before `14` the only proposal is key `1`'s at `12`, and its batch is
  held back until `14`.
* `delivered_vote`: no object delivered in the run carries a vote of key `0` or `1` of a slot after
  `1`. Key `0` releases nothing, and key `1` releases only while honest (until `12`), its own
  votes of the slots of its release times. -/

namespace Consensus.Goldilocks.Test.ProposerHold
open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {S : Setup}

/-! ### Duties and released roots -/

/-- The duty of a tick signed in a proposer role is the proposal of a positive slot at its slot
time. -/
theorem duty_proposer {t : Time} {d : (Model.protoOf (compiled (goldilocks S)) env).Duty}
    (hd : d ∈ (Model.protoOf (compiled (goldilocks S)) env).duties t) {s : Nat}
    (hr : (Model.protoOf (compiled (goldilocks S)) env).role d = .proposer s) :
    t = (s : Time) * 12 ∧ 0 < s := by
  by_cases ht : 0 ≤ t
  swap
  · rw [Simulation.duties_eq_nil S t (not_le.mp ht)] at hd; cases hd
  rw [Simulation.duties_eq S t ht] at hd
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · rcases hd with _ | ⟨_, _ | ⟨_, _ | ⟨_, hd⟩⟩⟩
        · cases hr
        · cases hr
        · cases hr
        · cases hd
      · rcases Simulation.Skeleton.proposeAt_cases (skeleton (pubOf env)) t with
          ⟨hnil, -⟩ | ⟨s', h, heq, hts⟩
        · rw [hnil] at hd; cases hd
        · rw [heq] at hd
          rcases hd with _ | ⟨_, hd⟩
          · cases hr
            refine ⟨hts.trans ?_, h⟩
            change (s : Time) * (4 * 3) = _
            norm_num
          · cases hd
    · rcases hd with _ | ⟨_, hd⟩
      · cases hr
      · cases hd
  · rcases hd with _ | ⟨_, hd⟩
    · cases hr
    · cases hd

/-- The duties of a delivery are poll steps. -/
theorem deliverDuty_poll {t : Time} {d : (Model.protoOf (compiled (goldilocks S)) env).Duty}
    (hd : d ∈ (Model.protoOf (compiled (goldilocks S)) env).deliverDuties t) :
    (Model.protoOf (compiled (goldilocks S)) env).role d = .poll := by
  by_cases ht : 0 ≤ t
  · rw [Simulation.deliverDuties_eq S t ht] at hd
    rcases hd with _ | ⟨_, hd⟩
    · rfl
    · cases hd
  · rw [Simulation.deliverDuties_eq_nil S t (not_le.mp ht)] at hd; cases hd

/-- **A released root signed in a proposer role** is the proposal of a tick at the slot time, by a
node selected for the slot. -/
theorem root_proposer {i : Nat} {o : Obj S} (ho : o ∈ (rho S).releasesAt i)
    {k : Fin (Fintype.card (Fin 5))} {s : Nat} (ha : o.auth = .signed k (.proposer s)) :
    ∃ v t, (rho S).events[i]? = some (.tick v t) ∧ t = (s : Time) * 12 ∧ 0 < s ∧
      (rho S).ownKey v ∈ (rho S).sel (.proposer s) := by
  cases he : (rho S).events[i]? with
  | none => simp [Model.Run.releasesAt, he] at ho
  | some e =>
    cases e with
    | tick v t =>
      simp only [Model.Run.releasesAt, he] at ho
      obtain ⟨cs, hcs, h2, -⟩ := (rho S).tick_flat ((rho S).stateBefore i v) v t
      rw [h2] at ho
      rcases hcs o (Model.releaseAll_subset _ _ _ _ o ho) with hc | hc
      · obtain ⟨d, hd, st, -, hc⟩ := (rho S).dutyCandidate_iff.mp hc
        obtain ⟨m, cs', -, hk, rfl⟩ := (rho S).mem_signedCandidate.mp hc
        injection ha with _ hr
        obtain ⟨ht, hs⟩ := duty_proposer hd hr
        exact ⟨v, t, rfl, ht, hs, hr ▸ hk⟩
      · obtain ⟨mc, -, rfl⟩ := Model.mem_gossipCandidates.mp hc
        cases ha
    | deliver v p t =>
      simp only [Model.Run.releasesAt, he] at ho
      obtain ⟨cs, hcs, h2, -⟩ := (rho S).deliver_flat ((rho S).stateBefore i v) v p t
      rw [h2] at ho
      rcases hcs o (Model.releaseAll_subset _ _ _ _ o ho) with hc | hc
      · obtain ⟨d, hd, st, -, hc⟩ := (rho S).deliverCandidate_iff.mp hc
        obtain ⟨m, cs', -, -, rfl⟩ := (rho S).mem_signedCandidate.mp hc
        injection ha with _ hr
        rw [deliverDuty_poll hd] at hr
        cases hr
      · obtain ⟨mc, -, rfl⟩ := Model.mem_gossipCandidates.mp hc
        cases ha
    | restart v t => simp [Model.Run.releasesAt, he] at ho

/-! ### Basic schedule facts -/

theorem rho_sorted : (rho S).events.Pairwise Model.Event.keyLe := (rho_valid S).sorted

/-- Key `0` has no event. -/
theorem node_ne_zero {e : Ev S} (he : e ∈ (rho S).events) : e.node ≠ 0 := by
  intro h0
  have := (rho_valid S).honest_only e he
  rw [rho_faultyAt, h0] at this
  apply this
  unfold faulty
  split_ifs <;> decide

/-- Key `1`'s events are before `13`. -/
theorem key1_time {e : Ev S} (he : e ∈ (rho S).events) (h1 : e.node = 1) : e.time < 13 := by
  have := (rho_valid S).honest_only e he
  rw [rho_faultyAt, h1] at this
  by_contra hc
  exact this (by rw [faulty_of_ge (not_lt.mp hc)]; decide)

theorem ownKey_eq (v : Fin 5) : (rho S).ownKey v = ⟨v.val, by simp⟩ := by
  simp only [Model.Run.ownKey, rho_key]
  rfl

/-! ### No proposal but the twin before `14` -/

variable (S) in
/-- `d` is the twin or signed in no proposer role. -/
def NoProposal (d : Obj S) : Prop := ∀ k s, d.auth = .signed k (.proposer s) → d = twin S

variable (S) in
/-- The events at times `≤ 13` whose batch is not held back. -/
def Early (i : Nat) : Prop := ∃ e, (rho S).events[i]? = some e ∧ e.time ≤ 13 ∧ delay S e = 0

theorem delay_eq_zero {e : Ev S} (h : ¬ (e.node = 1 ∧ e.time = 12)) : delay S e = 0 := by
  simp [delay, h]

theorem delay_ne_zero {e : Ev S} (h : delay S e ≠ 0) : e.node = 1 ∧ e.time = 12 := by
  by_contra hc; exact h (delay_eq_zero hc)

/-- **Before `14`, released objects carry no proposal but the twin.** -/
theorem early_closed : ∀ i, Early S i → ∀ o ∈ (rho S).releasesAt i, ∀ d,
    Model.Obj.Contains o d → NoProposal S d := by
  refine (rho S).closed_of_sources (fun _ d => NoProposal S d) (Early S) (fun _ h => h)
    ?_ ?_ ?_
  · rintro i j ei ej ⟨e, he, het, hed⟩ hji hi hj hn
    rw [hi] at he; cases he
    have hle := (rho S).time_le_of_lt (rho_sorted (S := S)) hji hi hj
    refine ⟨ej, hj, hle.trans het, ?_⟩
    by_contra hd
    obtain ⟨h1, h12⟩ := delay_ne_zero hd
    have hi1 : ei.node = 1 := hn ▸ h1
    have hlt := key1_time (List.mem_of_getElem? hi) hi1
    have h12' : ei.time ≠ 12 := fun h => by simp [delay, hi1, h] at hed
    dsimp only [Time] at *
    omega
  · rintro i ⟨e, he, het, hed⟩ o ho k s ha
    obtain ⟨v, t, hev, hts, hs, hsel⟩ := root_proposer ho ha
    rw [hev] at he; cases he
    have hs1 : s = 1 := by
      change t ≤ 13 at het
      rw [hts] at het
      have key : ∀ n : Nat, 0 < n → (n : Int) * 12 ≤ 13 → n = 1 := by intro n; omega
      exact key s hs het
    subst hs1
    simp only [rho_sel_proposer, ↓reduceIte, Finset.mem_singleton, ownKey_eq] at hsel
    have hv : v = 1 := by
      have := congrArg Fin.val hsel
      exact Fin.ext this
    subst hv
    rw [hts] at hed
    simp [delay, Model.Event.node, Model.Event.time] at hed
  · rintro i w o t ⟨e, he, het, hed⟩ hi
    rw [hi] at he; cases he
    rcases (base S).injectEvents_source (delay S) (inj S)
        (fun _ _ _ _ => true) hi with hp | ⟨j, hj, ej, hje, hjt, hjr⟩
    · left
      intro d hd
      obtain ⟨-, rfl⟩ := (mem_inj S).mp hp
      rw [twin_contains S hd]
      intro _ _ _; rfl
    · refine Or.inr ⟨j, hj, ⟨ej, hje, ((le_add_of_nonneg_right (delay_nonneg S ej)).trans
        hjt).trans het, ?_⟩, hjr⟩
      by_contra hd
      have h12 := (delay_ne_zero hd).2
      rw [show delay S ej = 2 by simp [delay, delay_ne_zero hd]] at hjt
      change t ≤ 13 at het
      dsimp only [Time] at *
      omega

/-- **Up to `13`, a delivered object carries no proposal but the twin.** -/
theorem delivered_proposal {i : Nat} {w : Fin 5} {o : Obj S} {t : Time}
    (hi : (rho S).events[i]? = some (.deliver w o t)) (ht : t ≤ 13) :
    ∀ d, Model.Obj.Contains o d → NoProposal S d := by
  rcases (base S).injectEvents_source (delay S) (inj S)
      (fun _ _ _ _ => true) hi with hp | ⟨j, -, ej, hje, hjt, hjr⟩
  · intro d hd
    obtain ⟨-, rfl⟩ := (mem_inj S).mp hp
    rw [twin_contains S hd]
    intro _ _ _; rfl
  · refine early_closed j ⟨ej, hje, ((le_add_of_nonneg_right (delay_nonneg S ej)).trans hjt).trans
      ht, ?_⟩ o hjr
    by_contra hd
    have h12 := (delay_ne_zero hd).2
    rw [show delay S ej = 2 by simp [delay, delay_ne_zero hd]] at hjt
    dsimp only [Time] at *
    omega

/-! ### Key `1`'s votes -/

variable (S) in
/-- The run up to `12` with the faults of `12` constant: key `1` is honest there. -/
noncomputable def rho12 : Model.Run (compiled (goldilocks S)) env := ((rho S).truncate 12).retain 12

theorem rho12_valid : (rho12 S).ExecutionValid :=
  Model.Run.retain_valid (Model.Run.truncate_valid (rho_valid S) (by norm_num)
    (by rw [rho_horizon]; norm_num)) le_rfl

theorem rho12_faultyAt (t : Time) : (rho12 S).faultyAt t = {0} := by
  change (rho S).faultyAt 12 = _
  rw [rho_faultyAt, faulty_of_lt (by norm_num)]

theorem rho12_not_hashCollision : ¬ (rho12 S).HashCollision := by
  refine Model.Run.retain_not_hashCollision (Model.Run.truncate_valid (rho_valid S) (by norm_num)
    (by rw [rho_horizon]; norm_num)) le_rfl ?_
  intro h
  exact rho_not_hashCollision S ((Model.Run.truncate_prefix (rho_valid S) 12).2.2.2 h)

/-- **Key `1` releases only votes of slots up to `1`**: it is honest until `12`, and an honest
node's released vote is its emission, of the slot of its time. -/
theorem key1_vote_slot {i : Nat} {e : Ev S} (he : (rho S).events[i]? = some e) (h1 : e.node = 1)
    {v : SA.Vote (Fintype.card (Fin 5))} (hv : voteObj v ∈ (rho S).releasesAt i) :
    v.slot ≤ 1 := by
  obtain ⟨ys, hsplit, hys⟩ := (rho S).truncate_split rho_sorted 12
  have ht : e.time ≤ 12 := by
    have := key1_time (List.mem_of_getElem? he) h1
    dsimp only [Time] at *; omega
  have hiT := Model.Run.truncate_index_lt hsplit hys he ht
  have heT : ((rho S).truncate 12).events[i]? = some e :=
    (Model.Run.truncate_getElem? hsplit hiT).trans he
  have hrT := Model.Run.truncate_releasesAt hsplit hiT
  have hk : e.node ∉ ((rho S).truncate 12).faultyAt 12 := by
    change e.node ∉ (rho S).faultyAt 12
    rw [rho_faultyAt, faulty_of_lt (by norm_num), h1]; decide
  have he12 : (rho12 S).events[((rho S).truncate 12).retainIdx 12 i]? = some e :=
    Model.Run.retain_getElem? heT hk
  have hr12 : (rho12 S).releasesAt (((rho S).truncate 12).retainIdx 12 i) = (rho S).releasesAt i :=
    (Model.Run.retain_releasesAt heT hk).trans hrT
  rw [← hr12] at hv
  have hs : (rho12 S).SendsAt 1 (((rho S).truncate 12).retainIdx 12 i) e.time := by
    cases e with
    | tick w t => simp only [Model.Event.node] at h1; subst h1; exact Or.inl he12
    | deliver w o t => simp only [Model.Event.node] at h1; subst h1; exact Or.inr ⟨o, he12⟩
    | restart w t => simp only [Model.Run.releasesAt, he12] at hv; cases hv
  have hconst : (rho12 S).point.ConstantFaults := Model.Run.retain_constant
  have hv' : (1 : Fin 5) ∉ (rho12 S).faultyAt 0 := by rw [rho12_faultyAt]; decide
  obtain ⟨k, -, ℓ, hc, em, hem, rfl⟩ :=
    Simulation.released_vote_cut S (rho12 S) one_le_card hconst rho12_valid hs hv' hv
  have hrun := Simulation.simTrace_goldilocksRun S (rho12 S) one_le_card hconst rho12_valid
  have hnc := Simulation.noCollRun_simTrace S (rho12 S) one_le_card hconst rho12_valid
    rho12_not_hashCollision
  have hac := (Compose.goldilocks_ac_projection _ _ _ _ _ _ hrun hnc).localRun
  have hy : (rho12 S).ownKey 1 ∈ Simulation.honestKeys S (rho12 S) := by
    rw [Simulation.mem_honestKeys_iff]
    rw [show (rho12 S).key ((rho12 S).ownKey 1) = 1 from (rho12 S).key.apply_symm_apply 1]
    exact hv'
  have hspec := SA.castAt_spec hac hy ⟨Compose.projAC_callAt.mpr hc, hem⟩
  rw [hspec.2.1]
  have hl : (Simulation.simTrace S (rho12 S) one_le_card).label k ≠ none := by
    rw [hc.2]; simp
  have hth := Simulation.simTrace_labelled_time_le S (rho12 S) one_le_card rho12_valid hl
  change _ ≤ (12 : Time) at hth
  have h0 := hrun.time_nonneg k
  have hsl := SA.slot_eq (sp := S.params (pubOf env) one_le_card) h0
  have hle : ((S.params (pubOf env) one_le_card).slot
      ((Simulation.simTrace S (rho12 S) one_le_card).time k) : Int) ≤ 1 := by
    rw [hsl]
    exact Int.ediv_le_of_le_mul (by change (0 : Int) < 4 * 3; norm_num)
      (by change _ ≤ (1 : Int) * (4 * 3); linarith)
  exact_mod_cast hle

/-! ### No late vote of the faulty keys -/

variable (S) in
/-- `d` is not a vote of key `0` or `1` of a slot after `1`. -/
def NoLateVote (d : Obj S) : Prop :=
  ∀ v : SA.Vote (Fintype.card (Fin 5)), d = voteObj v → (v.val = key 0 ∨ v.val = key 1) → v.slot ≤ 1

/-- **No released object carries a vote of key `0` or `1` of a slot after `1`.** -/
theorem released_vote : ∀ i, ∀ o ∈ (rho S).releasesAt i, ∀ d, Model.Obj.Contains o d →
    NoLateVote S d := by
  intro i
  refine (rho S).closed_of_sources (fun _ d => NoLateVote S d) (fun _ => True) (fun _ h => h)
    (fun _ _ _ _ _ => trivial) ?_ ?_ i trivial
  · rintro i - o ho v rfl hval
    cases he : (rho S).events[i]? with
    | none => simp only [Model.Run.releasesAt, he] at ho; cases ho
    | some e =>
      have hsig : (rho S).signerOf (voteObj v) = some e.node := by
        cases e with
        | tick w t =>
          simp only [Model.Run.releasesAt, he] at ho
          rcases (rho S).tick_signerOf _ w t ho with h | h
          · cases h
          · exact h
        | deliver w p t =>
          simp only [Model.Run.releasesAt, he] at ho
          rcases (rho S).deliver_signerOf _ w p t ho with h | h
          · cases h
          · exact h
        | restart w t => simp only [Model.Run.releasesAt, he] at ho; cases ho
      change some ((rho S).key v.val) = _ at hsig
      have hn : e.node = (rho S).key v.val := (Option.some.inj hsig).symm
      have hval' : ((rho S).key v.val).val = v.val.val := by rw [rho_key]; rfl
      rcases hval with hval | hval
      · exact absurd (Fin.ext (by rw [hn, hval', hval]; rfl))
          (node_ne_zero (List.mem_of_getElem? he))
      · exact key1_vote_slot he (Fin.ext (by rw [hn, hval', hval]; rfl)) ho
  · rintro i w o t - hi
    rcases (base S).injectEvents_source (delay S) (inj S)
        (fun _ _ _ _ => true) hi with hp | ⟨j, hj, -, -, -, hjr⟩
    · left
      intro d hd
      obtain ⟨-, rfl⟩ := (mem_inj S).mp hp
      rw [twin_contains S hd]
      intro v hv
      injection hv with _ h2
      cases h2
    · exact Or.inr ⟨j, hj, trivial, hjr⟩

/-- **No delivered object carries a vote of key `0` or `1` of a slot after `1`.** -/
theorem delivered_vote {i : Nat} {w : Fin 5} {o : Obj S} {t : Time}
    (hi : (rho S).events[i]? = some (.deliver w o t)) :
    ∀ d, Model.Obj.Contains o d → NoLateVote S d := by
  rcases (base S).injectEvents_source (delay S) (inj S)
      (fun _ _ _ _ => true) hi with hp | ⟨j, -, -, -, -, hjr⟩
  · intro d hd
    obtain ⟨-, rfl⟩ := (mem_inj S).mp hp
    rw [twin_contains S hd]
    intro v hv
    injection hv with _ h2
    cases h2
  · exact released_vote j o hjr

end Consensus.Goldilocks.Test.ProposerHold

end
