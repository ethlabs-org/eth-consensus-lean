module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RestartStamp
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RelTrace

public section

/-! # Lawful traces are unchanged by restart stamping

The trace carrier is shared: labels (including emissions and their internal read points),
post-states and hence every recursively computed pre-state are literally the same in both
directions. Only the execution law changes. The frame law and nonnegative times, not arbitrary
raw inputs, justify replacing the restart branch. The result applies to every write mode and
unlock oracle, and in particular to admitted parent executions via `ACLocalRun.toU`.
-/

namespace Consensus.Goldilocks.AC

variable {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- The call with the given unlock and write mode, replacing only restart by its bulk stamp. -/
noncomputable def stepWithStamp (m : WriteMode) (self : Fin sp.n) (L : Set Lock)
    (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksAC sp FGP ro).Call) : ACState sp.n × List (Em sp FGP) :=
  match c with
  | .restart => (restartStamp sp A Φ t, [])
  | _ => stepWithM sp ro m self L A Φ t c

/-- Equality includes emissions and their internal read points, not just the post-state. -/
theorem stepWithStamp_eq (m : WriteMode) (self : Fin sp.n) (L : Set Lock)
    (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksAC sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t) :
    stepWithStamp m self L A Φ t c = stepWithM sp ro m self L A Φ t c := by
  cases c <;> try rfl
  exact (acRestart_eq_stamp sp ro self A Φ t hΦ ht).symm

/-- Two-way trace equivalence at lawful restarts. No trace translation loses reads or
emissions: precisely the same carrier satisfies either execution contract, from any starts. -/
theorem localRunStep_stamp_iff (m : WriteMode) (u : Nat → Set Lock)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : GTrace sp FGP ro)
    (ini : Fin sp.n → ACState sp.n) :
    ACLocalRunStep m u (fun _ => stepWithStamp m) H U tr ini ↔
      ACLocalRunU m u H U tr ini := by
  have transfer (step₁ step₂ : Nat → Fin sp.n → Set Lock → ACState sp.n →
      Frm sp.n FGP → Time → (goldilocksAC sp FGP ro).Call →
      ACState sp.n × List (Em sp FGP))
      (heq : ∀ i self L A Φ t c, FrameOK Φ → 0 ≤ t →
        step₁ i self L A Φ t c = step₂ i self L A Φ t c)
      (h : ACLocalRunStep m u step₁ H U tr ini) : ACLocalRunStep m u step₂ H U tr ini := by
    refine { h with exec := ?_ }
    intro i ℓ hl hy
    have hΦ : FrameOK ℓ.frame := by
      rcases h.frameLaw (tr.node i) hy i ℓ ⟨rfl, hl⟩ with
        ⟨_, _, _, _, hc⟩ | ⟨_, _, _, _, _, hc⟩
      · exact hc.1.1
      · exact hc.1.1
    rw [← heq i _ _ _ _ _ _ hΦ (h.time_nonneg i)]
    exact h.exec i ℓ hl hy
  constructor
  · exact transfer _ _ (fun _ self L A Φ t c => stepWithStamp_eq m self L A Φ t c)
  · exact transfer _ _ (fun _ self L A Φ t c hΦ ht =>
      (stepWithStamp_eq m self L A Φ t c hΦ ht).symm)

/-- Every admitted parent contract execution also executes the bulk-stamp rule, on the
identical trace with its states, all state reads and emission read points unchanged. -/
theorem localRun_stamp {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    {tr : GTrace sp FGP ro} {ini : Fin sp.n → ACState sp.n}
    (h : ACLocalRun (goldilocksAC sp FGP ro) H U tr ini) :
    ACLocalRunStep (WriteMode.parent sp) (parentOracle sp tr)
      (fun _ => stepWithStamp (WriteMode.parent sp)) H U tr ini :=
  (localRunStep_stamp_iff _ _ _ _ _ _).mpr h.toU

/-- In both directions the parent execution contract has exactly the same traces as the
bulk-stamp contract with the parent's own unlock. -/
theorem localRun_stamp_iff (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : GTrace sp FGP ro) (ini : Fin sp.n → ACState sp.n) :
    ACLocalRunStep (WriteMode.parent sp) (parentOracle sp tr)
        (fun _ => stepWithStamp (WriteMode.parent sp)) H U tr ini ↔
      ACLocalRun (goldilocksAC sp FGP ro) H U tr ini := by
  constructor
  · intro hs
    have h := (localRunStep_stamp_iff _ _ _ _ _ _).mp hs
    refine {
      coherent := h.coherent
      init := h.init
      exec := ?_
      frameLaw := h.frameLaw
      time_nonneg := h.time_nonneg
      time_mono := h.time_mono
      awake_of_call := h.awake_of_call
      restart_of_sleep := h.restart_of_sleep
      restart_at_wake := h.restart_at_wake
      sleep_of_restart := h.sleep_of_restart }
    intro i ℓ hl hy
    have he := h.exec i ℓ hl hy
    rw [stepWithM_parent] at he
    rw [step_eq_stepWith]
    simpa only [parentOracle, hl] using he
  · exact localRun_stamp

/-- The former execution rule, replaying restart and leaving all other calls unchanged. -/
noncomputable def stepWithReplay (m : WriteMode) (self : Fin sp.n) (L : Set Lock)
    (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksAC sp FGP ro).Call) : ACState sp.n × List (Em sp FGP) :=
  match c with
  | .restart => restartReplay sp ro self A Φ t
  | _ => stepWithM sp ro m self L A Φ t c

/-- The old replay execution and the new stamp execution have exactly the same lawful
traces. Their shared carrier preserves every read and emission, in both directions. -/
theorem localRunStep_replay_iff (m : WriteMode) (u : Nat → Set Lock)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : GTrace sp FGP ro)
    (ini : Fin sp.n → ACState sp.n) :
    ACLocalRunStep m u (fun _ => stepWithReplay m) H U tr ini ↔
      ACLocalRunStep m u (fun _ => stepWithStamp m) H U tr ini := by
  have eqstep (self : Fin sp.n) (L : Set Lock) (A : ACState sp.n)
      (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksAC sp FGP ro).Call)
      (hΦ : FrameOK Φ) (ht : 0 ≤ t) :
      stepWithReplay m self L A Φ t c = stepWithStamp m self L A Φ t c := by
    cases c <;> try rfl
    exact restartReplay_eq_stamp sp ro self A Φ t hΦ ht
  constructor <;> intro h <;> refine { h with exec := ?_ } <;> intro i ℓ hl hy
  all_goals
    have hΦ : FrameOK ℓ.frame := by
      rcases h.frameLaw (tr.node i) hy i ℓ ⟨rfl, hl⟩ with
        ⟨_, _, _, _, hc⟩ | ⟨_, _, _, _, _, hc⟩
      · exact hc.1.1
      · exact hc.1.1
    have he := h.exec i ℓ hl hy
    first
    | rwa [eqstep _ _ _ _ _ _ hΦ (h.time_nonneg i)] at he
    | rwa [← eqstep _ _ _ _ _ _ hΦ (h.time_nonneg i)] at he

/-- A lawful next call from any reachable state can be executed with the bulk stamp.
This is the `AtReachable`/`CallOK` entry point, with no raw-input equality asserted. -/
theorem stamp_atReachable : (goldilocksAC sp FGP ro).AtReachable
    (fun self U A Φ t₀ => ∀ t, t₀ ≤ t → ∀ c Φ',
      (goldilocksAC sp FGP ro).CallOK U Φ t c Φ' →
      stepWithStamp (WriteMode.parent sp) self (parentUnlock sp A Φ' t c) A Φ' t c =
        (goldilocksAC sp FGP ro).step self A Φ' t c) := by
  intro self U _ A Φ t₀ hr t ht c Φ' hc
  have h0 : 0 ≤ t₀ := by
    clear ht hc
    induction hr with
    | init => exact le_rfl
    | step _ _ hle _ ih => exact ih.trans hle
  rw [stepWithStamp_eq _ _ _ _ _ _ _ hc.1.1 (h0.trans ht), stepWithM_parent,
    step_eq_stepWith]

end Consensus.Goldilocks.AC

end
