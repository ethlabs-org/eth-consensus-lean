module
public import AvailableChainPCSAProofs

public section

/-! C3 counterexample: the label-zero ack is allowed, but a label-zero PC
is not. This finite run satisfies the old C3 premises, but not `0 < s`.
All computations use the Lean kernel. See Proofs/Clean/OPEN.md. -/
open AvailableChain AvailableChain.PCSA AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run.Tests.ZeroSlot
/-- One seat, no faults, and Δ = 1. The digest is unused in this run. -/
abbrev p : Params :=
  { Δ := 1, n := 1, k := 2, η := 7, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun _ => ⟨1⟩ }
def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
def hd : Obj p := ⟨.seat (.base (.head 0)) ⟨0, by decide⟩, .head genesisRoot⟩
def ak : Obj p := ackObj p 0 0 genesisRoot
/-- All public ticks through the cut; immediate self-delivery of HEAD and ack. -/
def run : V2.D.Run (Fin 1) (pcsaWith .idle p unitCodec) where
  honest := {0}
  horizon := 3
  events := [.tick 0 0, .tick 0 1, .deliver 0 hd 1, .tick 0 2, .deliver 0 ak 2, .tick 0 3]
  seatOf _ _ := 0
  input _ _ := ()
set_option maxRecDepth 4096
example : (V2.D.Run.emittedAt env run 0 1).map (toWire p) = [toWire p hd] := by decide +kernel
example : (V2.D.Run.emittedAt env run 0 2).map (toWire p) = [toWire p ak] := by decide +kernel
example : (storeAfterTicks p unitCodec env run 0 3).pcs = [] := by decide +kernel
example : (storeAfterTicks p unitCodec env run 0 3).ackPool =
    [⟨.seat (.ack 0) 0, genesisRoot⟩] := by decide +kernel
theorem emitted (o : Obj p) (t : Time) :
    V2.D.Run.emits env run 0 o t ↔ (o = hd ∧ t = 1) ∨ (o = ak ∧ t = 2) := by
  constructor
  · rintro ⟨i, hi, ho⟩
    have hb : i < 6 := by
      have := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hlt, _⟩ := this
      exact hlt
    interval_cases i <;> simp only [run, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq, V2.Event.tick.injEq,
      reduceCtorEq] at hi
    all_goals first | contradiction | skip
    all_goals obtain ⟨_, rfl⟩ := hi
    all_goals change o ∈ _ at ho
    all_goals norm_num [V2.D.Run.emitsAt, run] at ho
    · change o ∈ [hd] at ho
      exact Or.inl ⟨List.mem_singleton.mp ho, rfl⟩
    · change o ∈ [ak] at ho
      exact Or.inr ⟨List.mem_singleton.mp ho, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨1, rfl, by change hd ∈ [hd]; simp⟩
    · exact ⟨3, rfl, by change ak ∈ [ak]; simp⟩
theorem zeroSlot_delivery {i : Nat} {v : Fin 1} {o : Obj p} {t : Time}
    (h : run.events[i]? = some (.deliver v o t)) :
    (i = 2 ∧ v = 0 ∧ o = hd ∧ t = 1) ∨ (i = 4 ∧ v = 0 ∧ o = ak ∧ t = 2) := by
  have hb : i < 6 := (List.getElem?_eq_some_iff.mp h).1
  interval_cases i <;> simp only [run, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq,
    reduceCtorEq] at h
  all_goals first | contradiction | (cases h; simp)

theorem zero_slot_valid : V2.D.ExecutionValid env run := by
  constructor
  · constructor
    · decide
    · decide +kernel
    · change List.Nodup [V2.Event.tick (0 : Fin 1) (0 : Time), .tick 0 1,
        .deliver 0 hd 1, .tick 0 2, .deliver 0 ak 2, .tick 0 3]
      simp [List.nodup_cons, hd, ak, ackObj]
    · intro e he
      simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro e he
      have : e.node = 0 := Subsingleton.elim _ _
      simp [run, this]
    · intro v t ht
      simp only [run, List.mem_cons, List.not_mem_nil, or_false, V2.Event.tick.injEq,
        reduceCtorEq, false_or] at ht
      rcases ht with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · intro v hv t _ h0 h3
      have hv0 : v = 0 := Subsingleton.elim _ _
      subst v
      change t ≤ 3 at h3
      interval_cases t <;> simp [run]
  · constructor
    · intro i v o t h
      rcases zeroSlot_delivery h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
        decide +kernel
    · intro i v o t h
      rcases zeroSlot_delivery h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
        decide +kernel
    · intro i v o t h
      rcases zeroSlot_delivery h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
        decide +kernel
  · constructor
    · rintro v o t ⟨i, h⟩ u _ _
      have hu : u = 0 := Subsingleton.elim _ _
      subst u
      rcases zeroSlot_delivery h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨1, le_refl _, (emitted _ _).mpr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨2, le_refl _, (emitted _ _).mpr (Or.inr ⟨rfl, rfl⟩)⟩
    · rintro v o t ⟨i, h⟩ a ha
      rcases zeroSlot_delivery h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
        rcases ha with ha | ⟨C, rfl, _⟩
      all_goals first | exact ha.elim | (intro u _ hh; cases hh)
theorem bodies (i : Nat) : (V2.D.Run.stateBefore env run i 0).st.namedBodies = [.genesis] := by
  by_cases hi : i < 6
  · interval_cases i <;> decide +kernel
  · have ht : run.events.take i = run.events := List.take_of_length_le (Nat.le_of_not_gt hi)
    change ((run.events.take i).foldl (V2.D.World.step env run)
      V2.D.World.init 0).st.namedBodies = _
    rw [ht]
    decide +kernel

theorem direct (N : NamedProposal p.n) (h : DirectNamedProposalInRun p unitCodec env run N) :
    N = .genesis := by
  rcases h with ⟨x, o, t, he, hp⟩ | ⟨x, _, i, hm⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    rcases zeroSlot_delivery hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      cases hp
  · have hx : x = 0 := Subsingleton.elim _ _
    subst x
    rw [bodies] at hm
    exact List.mem_singleton.mp hm

theorem in_scope (N : NamedProposal p.n) (h : NamedProposalInRun p unitCodec env run N) :
    N = .genesis := by
  obtain ⟨B, hb, hn⟩ := h
  rw [direct B hb] at hn
  exact of_decide_eq_true hn

theorem zeroSlot_base : Base₂ p unitCodec env run := by
  refine ⟨zero_slot_valid, ?_, ?_, ?_, rfl, ?_⟩
  · refine ⟨1, Equiv.refl _, ?_⟩
    intro l hl
    cases l with
    | prop s => exact hl.elim
    | base l => cases l with
      | head s => exact hl.elim
      | ack s => exact hl.elim
      | fg => exact ⟨rfl, fun i => Subsingleton.elim _ _⟩
  · intro l hl
    cases l with
    | prop s => exact hl.elim
    | base l => cases l with
      | fg => exact hl.elim
      | head s | ack s =>
        change Function.Bijective (fun _ : Fin 1 => (0 : Fin 1))
        exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  · intro i v t hi
    have hb : i < 6 := (List.getElem?_eq_some_iff.mp hi).1
    interval_cases i <;> cases hi
  · constructor
    intro B C hB hC A D hA hD _
    rw [in_scope B hB, in_scope C hC] at hA hD
    have ha : A = .genesis := of_decide_eq_true (hA.elim id id)
    have hd : D = .genesis := of_decide_eq_true (hD.elim id id)
    exact ha.trans hd.symm

theorem faults : FaultsBelowQA p unitCodec run := by
  rw [FaultsBelowQA_def]
  decide +kernel

theorem healthy : Gen.V2.Duty.HealthyPrefixDeliveryBy env run (pcsaDelay p env.Δ 1) 3 := by
  constructor
  · intro v hv o t he w hw _ _
    have hv0 : v = 0 := Subsingleton.elim _ _
    have hw0 : w = 0 := Subsingleton.elim _ _
    subst v; subst w
    rcases (emitted o t).mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨1, le_refl _, by decide, 2, hd, rfl, Or.inl rfl⟩
    · exact ⟨2, le_refl _, by decide, 4, ak, rfl, Or.inl rfl⟩
  · intro v _ i o t ha w _ hn
    have hw : w = v := Subsingleton.elim _ _
    subst w
    rw [ha.2.2] at hn
    contradiction

theorem clean : Clean₂ p unitCodec env run 3 1 := by
  refine ⟨zeroSlot_base, by decide, healthy, le_refl _, ?_⟩
  intro j hj
  have hj0 : j = 0 := by
    change 4 * (j : Int) + 2 ≤ 3 at hj
    exact_mod_cast (show (j : Int) = 0 by have := Int.natCast_nonneg j; omega)
  subst j
  decide +kernel

theorem stageOne : StageOneFrame p unitCodec env run := pcsa_ac_frame env run zeroSlot_base faults

/-- The former C3 statement, retained only for this regression test. -/
def UnrestrictedPCDisseminationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (s : Slot) (r : BlockId), SA.freezeTime p.toParams s ≤ b₀ →
      (∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧ ∀ i ∈ Q,
        rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
          (SA.earlyTime p.toParams s)) →
      ∀ y ∈ rho.honest, ∃ c' ∈ (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs,
        c'.slot = s ∧ c'.target.root = r

/-- The former C3 statement is false at slot zero, with all premises proved. -/
theorem refutes_unrestricted_C3 : ¬ UnrestrictedPCDisseminationClaim p := by
  intro h
  have hQ : ∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧ ∀ i ∈ Q,
      run.seatOf (.base (.ack 0)) i ∈ run.honest ∧
      V2.D.Run.emits env run (run.seatOf (.base (.ack 0)) i) (ackObj p 0 i genesisRoot) 2 := by
    refine ⟨{0}, by decide, ?_⟩
    intro i hi
    have hi0 : i = 0 := Finset.mem_singleton.mp hi
    subst i
    exact ⟨by decide, (emitted _ _).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  obtain ⟨C, hC, _⟩ := h unitCodec .idle env run 3 1 clean faults stageOne
    0 genesisRoot (by decide) hQ 0 (by decide)
  have hempty : (storeAfterTicks p unitCodec env run 0 3).pcs = [] := by decide +kernel
  change C ∈ (storeAfterTicks p unitCodec env run 0 3).pcs at hC
  rw [hempty] at hC
  exact List.not_mem_nil hC
/-- The new premise excludes the counterexample slot. -/
theorem positive_slot_excludes : ¬ (0 < (0 : Slot)) := Nat.lt_irrefl 0

#print axioms refutes_unrestricted_C3
#print axioms positive_slot_excludes

end AvailableChain.PCSA.Run.Tests.ZeroSlot
end
