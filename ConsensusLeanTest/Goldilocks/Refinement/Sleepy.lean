module
public import ConsensusLeanTest.Goldilocks.Refinement.Simulation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Witnesses: the Sleepy leaves' and vote forwarding's hypotheses are satisfiable

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), for a valid, collision-free Sleepy
run and for the fields of `ConfirmedQuery` (Sleepy branch). The query fixes the contract to
`K S A`. The theorems below state the same fields over `goldilocksContract A C` for every
coefficient record `C`; at `C = contract_coefficients S A` they are the query's fields, since
`K S A` is that abbreviation.

* `sleepySafety_fields`: a valid, collision-free Sleepy run of `goldilocks S` on two validators,
  with any horizon `H ≥ 0`.
* `sleepyQuery_fields`: the same run with Sleepy progress at `.available`, index 1, on
  `[0, H]`, query time 0, the latency deadline inside the horizon, and a ready reader at the
  deadline, for every `H ≥ 2·latency` (engine `Δ = 2`).
* `vote_emitted_forwarded`: on that run (horizon `H ≥ 2`), validator `0` emits a slot-0 vote
  (`EmitAt` on `simTrace`), the premise of `simTrace_vote_forwarded`, which then yields a
  released forwarding envelope. -/

namespace Consensus.Goldilocks.Obligations.Test.SleepyWitness
open AsChainShape Simulation

open Shape Blocks
open Consensus.Model (pubOf)

/-- Two validators, always awake and honest, engine `Δ = ΔF = 2` (so protocol `Δ_p = 2`),
horizon `H`, no submissions. -/
def point (H : Time) : EnvPoint (Fin 2) :=
  ⟨⟨2, by decide, 2, by decide, fun _ _ => true⟩, fun _ => ∅, monotone_const,
    H, fun _ _ => []⟩

theorem one_le_card : 1 ≤ Fintype.card (Fin 2) := by decide

variable (S : Setup)

/-- Validator `0` proposes every slot; everyone polls. -/
def sel (H : Time) :
    (Model.protoOf (compiled (goldilocks S)) (point H).env).Role →
        Finset (Fin (Fintype.card (Fin 2)))
  | .proposer _ => {⟨0, one_le_card⟩}
  | .duty _ k => k.elim
  | .poll => Finset.univ

theorem sel_admits (H : Time) :
    (Model.protoOf (compiled (goldilocks S)) (point H).env).SelAdmits (sel S H) := by
  intro r
  cases r with
  | proposer s =>
    change ((goldilocks S (pubOf (point H).env)).skel.proposerSel s).Admits _
    rw [Test.skeleton_proposerSel S s]
    change ({(⟨0, one_le_card⟩ : Fin (Fintype.card (Fin 2)))} : Finset _).card =
      min 1 (Fintype.card (Fin 2))
    simp
  | duty _ k => exact k.elim
  | poll => rfl

/-- Every validator is ready at every time and duration. -/
theorem point_ready (H c t : Time) (v : Fin 2) : (point H).Ready c v t :=
  ⟨by simp [EnvPoint.HonestAt, point], fun _ _ _ => rfl⟩

theorem point_readyAt (H c t : Time) : (point H).readyAt c t = Finset.univ := by
  ext v
  simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, iff_true]
  exact ⟨trivial, point_ready H c t v⟩

theorem point_faulty (H t : Time) : (point H).faultyAt t = ∅ := rfl

/-- The run of `Shape.coverage` at `point H`: valid, collision-free and Sleepy for every contract
`goldilocksContract A C`. -/
theorem sleepy_run (A : ContractAssumptions S) (C : ContractCoefficients) (H : Time)
    (hH : 0 ≤ H) :
    ∃ r : (Sys (goldilocks S) (Fin 2)).Run, r.1 = (point H).env ∧ r.2.point = point H ∧
      r.2.sel = sel S H ∧ r.2.key = Equiv.refl _ ∧
      (Sys (goldilocks S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (goldilocks S) (Fin 2)).Sleepy (goldilocksContract A C) r := by
  obtain ⟨rho, hp, hk, hs, hv, hc, -, he⟩ := Shape.coverage (goldilocks S) (point H) hH
    (by exact Equiv.refl _) (sel S H) (sel_admits S H) 0
  refine ⟨⟨(point H).env, rho⟩, rfl, hp, hs, hk, hv, hc, ?_, ?_⟩
  · exact (Model.sysOf_delivers_iff rho _ _ _).mpr
      (he.psync le_rfl (show (1 : Time) < 2 by decide) (show (1 : Time) < 2 by decide))
  · intro t _ _
    change (rho.point.retain _).ReadyAbove (1 / 2) _ t
    rw [hp]
    have hr (d : Time) : (point H).retain d = point H := rfl
    rw [hr]
    unfold EnvPoint.ReadyAbove EnvPoint.faultCount
    rw [point_readyAt, point_faulty]
    norm_num

/-- (a) A valid, collision-free Sleepy run, over `goldilocksContract A C`, exists at
every horizon `H ≥ 0`. -/
theorem sleepySafety_fields (A : ContractAssumptions S) (C : ContractCoefficients)
    (H : Time) (hH : 0 ≤ H) :
    ∃ r : (Sys (goldilocks S) (Fin 2)).Run, 1 ≤ Fintype.card (Fin 2) ∧ r.2.horizon = H ∧
      (Sys (goldilocks S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (goldilocks S) (Fin 2)).Sleepy (goldilocksContract A C) r := by
  obtain ⟨r, -, hp, -, -, hv, hc, hs⟩ := sleepy_run S A C H hH
  exact ⟨r, one_le_card, congrArg EnvPoint.horizon hp, hv, hc, hs⟩

/-- (a) The `ConfirmedQuery` fields on the Sleepy branch, over `goldilocksContract A C`, are jointly
satisfiable: capability `.available`, index 1, query time 0, at every horizon covering the latency
deadline (`Δ = 2`: `2·latency ≤ H`). -/
theorem sleepyQuery_fields (A : ContractAssumptions S) (C : ContractCoefficients)
    (H : Time) (hH : 2 * (C.latency .available 1 : Time) ≤ H) :
    ∃ r : (Sys (goldilocks S) (Fin 2)).Run, 1 ≤ Fintype.card (Fin 2) ∧ r.2.horizon = H ∧
      (Sys (goldilocks S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      ((Sys (goldilocks S) (Fin 2)).Sleepy (goldilocksContract A C) r ∧
        (Sys (goldilocks S) (Fin 2)).prog (shapeProgress (goldilocks S) (Fin 2))
            (goldilocksContract A C)
          .available (1 : ℕ+) 0 r.2.horizon r ∧ (0 : Time) ≤ 0) ∧
      (0 : Time) + ((goldilocksContract A C).params.latency .available (1 : ℕ+) : Time) * r.1.ΔAC ≤
        r.2.horizon ∧
      ∃ v, r.2.point.Ready ((Sys (goldilocks S) (Fin 2)).cDur (goldilocksContract A C) r) v
        ((0 : Time) + ((goldilocksContract A C).params.latency .available (1 : ℕ+) : Time) *
          r.1.ΔAC) := by
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  obtain ⟨⟨E, rho⟩, hE, hp, hs, hk, hv, hc, hsl⟩ := sleepy_run S A C H hH0
  subst hE
  have hhor : rho.horizon = H := congrArg EnvPoint.horizon hp
  refine ⟨⟨_, rho⟩, one_le_card, hhor, hv, hc, ⟨hsl, ?_, le_rfl⟩, ?_, 0, ?_⟩
  · change PatternRecurrence rho.point rho.key (fun s => rho.sel (ShapeRole.proposer s)) _ _ _ _ _
    apply patternRecurrence_of_all
    intro s j _
    rw [hs, hp]
    exact ⟨⟨_, Finset.mem_singleton_self _⟩, fun _ _ =>
      ⟨point_ready H _ _ _, by simp [EnvPoint.HonestAt, point]⟩⟩
  · rw [hhor]
    change (0 : Time) + (C.latency .available 1 : Time) * 2 ≤ H
    linarith
  · rw [hp]
    exact point_ready H _ _ _

/-- (b) The premise of `simTrace_vote_forwarded` is satisfiable on an engine run: on the
two-validator run with horizon `H ≥ 2`, validator `0` emits a slot-0 vote by its first vote
deadline `t₀ + Δp = 2`, and the theorem's conclusion then gives its first released forwarding
envelope. -/
theorem vote_emitted_forwarded (H : Time) (hH : 2 ≤ H) :
    ∃ rho : Model.Run (compiled (goldilocks S)) (point H).env, rho.ExecutionValid ∧
      ∃ y ∈ honestKeys ⟨S, stock⟩ rho, ∃ (k : Nat) (m : SA.Vote (Fintype.card (Fin 2))),
        (simTrace ⟨S, stock⟩ rho one_le_card).EmitAt y k m ∧ m.slot = 0 ∧
        (simTrace ⟨S, stock⟩ rho one_le_card).time k ≤ 2 ∧
        ∃ i, rho.SendsAt (rho.key y) i ((simTrace ⟨S, stock⟩ rho one_le_card).time k) ∧
          .mk (.signed y .poll) (.data (.voteForward ((simTrace ⟨S, stock⟩ rho one_le_card).time k)
            (encodeVote m))) [voteObj m] ∈ rho.releasesAt i := by
  obtain ⟨rho, hp, -, -, hv, hc, -, -⟩ := Shape.coverage (goldilocks S) (point H)
    (le_trans (by decide) hH)
    (by exact Equiv.refl _) (sel S H) (sel_admits S H) 0
  have hn := one_le_card
  have hhon (t : Time) : rho.faultyAt t = ∅ := congrArg (fun p => p.faultyAt t) hp
  have hf : rho.point.ConstantFaults := fun t => by
    change rho.faultyAt t = rho.faultyAt 0
    rw [hhon, hhon]
  have hhor : rho.horizon = H := congrArg EnvPoint.horizon hp
  have hrun := simTrace_goldilocksRun S rho hn hf hv
  have hnc := noCollRun_simTrace S rho hn hf hv hc
  let y : Fin (Fintype.card (Fin 2)) := ⟨0, hn⟩
  have hy : y ∈ honestKeys ⟨S, stock⟩ rho := by
    rw [mem_honestKeys_iff ⟨S, stock⟩ rho]
    rw [hhon]
    exact Finset.notMem_empty _
  let sp := S.params (pubOf (point H).env) hn
  have ht : sp.ts 0 + sp.Δ = 2 := by rfl
  have hawake : ∀ u : Time, 0 ≤ u → u ≤ 2 → (simTrace ⟨S, stock⟩ rho hn).awake y u := by
    intro u h0 h2
    rw [simTrace_awake_iff ⟨S, stock⟩ rho one_le_card, awakeAt_iff ⟨S, stock⟩ rho one_le_card]
    exact ⟨rfl, h0, by rw [hhor]; exact h2.trans hH⟩
  have h0 : (0 : Time) ≤ sp.ts 0 + sp.Δ := by rw [ht]; decide
  have hc8 : 8 * sp.Δ ≤ 8 * sp.Δ + 1 := Int.le_add_one le_rfl
  obtain ⟨hw, hj⟩ := Compose.ready_implies_joined sp _ _ _ _ _ hrun y hy (sp.ts 0 + sp.Δ)
    (8 * sp.Δ) h0 hc8 (fun u hu hu' =>
      hawake u ((le_max_left _ _).trans hu) (hu'.trans ht.le))
  obtain ⟨k, e, ⟨ℓ, hcall, he⟩, hslot, htime⟩ :=
    Compose.vote_of_awake_joined hrun hnc hy (s := 0) (Compose.mayVote_stock hrun hnc hy 0) hw hj
  have hem : (simTrace ⟨S, stock⟩ rho hn).EmitAt y k e.msg :=
      ⟨ℓ, Compose.projAC_callAt.mp hcall, e, he, rfl⟩
  obtain ⟨i, -, -, hsend, hrel, -⟩ :=
    simTrace_vote_forwarded S rho hn hf hv y hy k e.msg (Or.inl hem)
  exact ⟨rho, hv, y, hy, k, e.msg, hem, hslot, htime.trans ht.le, i, hsend, hrel⟩

end Consensus.Goldilocks.Obligations.Test.SleepyWitness
