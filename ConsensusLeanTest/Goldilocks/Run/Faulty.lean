module
public import ConsensusLeanTest.Goldilocks.Refinement.Simulation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
@[expose] public section

/-! # Witness: a Goldilocks run with one faulty validator meets the run-level fault premises

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), with `f = 1`: four validators, key
`0` faulty and the keys `1, 2, 3` honest, engine `Δ = ΔF = 2`, horizon `40`, identity PKI,
honest proposer `1` at every slot, everyone awake, no submissions, at every `Setup` (so every
lock window `S.k ≥ 2`; no lock-rule value is chosen or used). The run is `Shape.coverage` of
`goldilocks S` at that point, carried to the node level by `simTrace_goldilocksRun` and
`noCollRun_simTrace`.

* `faulty_run`: a valid engine run whose `simTrace` is a `GoldilocksRun` with `NoCollRun`, with
  `f = (honestKeys S rho)ᶜ.ncard = 1`, `q = 3` and `f < 2q − n` (`1 < 2`).
* `faulty_run_safe`: on that run the proved R.7 rows apply: `Regimes.finalized_safe` (finalized
  tips of honest nodes never conflict) and `Regimes.non_framing` (no honest slashable pair).
* `honestAwakeJoined_eq`, `faultBound`, `slot_faultBound`: `h_t = 3` at every `t ∈ [0, 40]`,
  so `f = 1 < h_t`; in particular at `t_s`, `t_s + Δ`, `t_s + 2Δ` up to `40` (the premise of
  `sleepy_safe_finite`, through `sleepy_faultBound`).
* `faulty_silent`: the faulty key has no engine event and makes no call in `simTrace` (so it
  signs and emits nothing there).

Limitations. Whole-run `SleepyRun` is not met: the engine horizon is finite and `simTrace`
clamps awake status to `[0, horizon]`, while `SleepyRun` quantifies over every slot. The full
`PersistPremises` bundle is not attempted (its lock, carry and committee fields are
lock-sensitive). Silence is stated for the faulty key's own events and calls only; that no
delivered object carries the faulty key's signature (causality of the canonical run) is not
stated, since `Shape.coverage` does not export `rho.Causal`. The run and digest are
noncomputable: a proof-level existential witness, not an evaluated trace. -/

namespace Consensus.Goldilocks.Obligations.Test.FaultyRunWitness
open AsChainShape Simulation

open Shape
open Consensus.Model (pubOf)

/-- Four validators, always awake, key `0` faulty, engine `Δ = ΔF = 2`, horizon `40`, no
submissions. -/
def point : EnvPoint (Fin 4) :=
  ⟨⟨2, by decide, 2, by decide, fun _ _ => true⟩, {1, 2, 3}, 40, fun _ _ => []⟩

theorem one_le_card : 1 ≤ Fintype.card (Fin 4) := by decide

/-- The faulty key. -/
def faultyKey : Fin (Fintype.card (Fin 4)) := ⟨0, one_le_card⟩

theorem point_faulty : point.faulty = {0} := by decide

theorem point_ready (c t : Time) (v : Fin 4) (hv : v ∈ point.honest) : point.Ready c v t :=
  ⟨hv, fun _ _ _ => rfl⟩

theorem point_readyAt (c t : Time) : point.readyAt c t = point.honest := by
  ext v
  simp only [EnvPoint.readyAt, Finset.mem_filter, and_iff_left_iff_imp]
  exact point_ready c t v

variable (S : Setup)

/-- Honest key `1` proposes every slot; everyone polls. -/
def sel :
    (Model.protoOf (compiled (goldilocks S)) point.env).Role → Finset (Fin (Fintype.card (Fin 4)))
  | .proposer _ => {⟨1, by decide⟩}
  | .duty _ k => k.elim
  | .poll => Finset.univ

theorem sel_admits : (Model.protoOf (compiled (goldilocks S)) point.env).SelAdmits (sel S) := by
  intro r
  cases r with
  | proposer s =>
    change ((goldilocks S (pubOf point.env)).skel.proposerSel s).Admits _
    rw [Test.skeleton_proposerSel S s]
    change ({(⟨1, by decide⟩ : Fin (Fintype.card (Fin 4)))} : Finset _).card =
      min 1 (Fintype.card (Fin 4))
    simp
  | duty _ k => exact k.elim
  | poll => rfl

/-- The quorum at four validators is `q = 3`. -/
theorem quorum_eq : (S.params (pubOf point.env) one_le_card).toParams.q = 3 := by
  change (2 * Fintype.card (Fin 4) + 2) / 3 = 3
  simp

/-- The FG safety threshold at four validators: `1 < 2q − n = 2`. -/
theorem one_lt_threshold :
    1 < 2 * (S.params (pubOf point.env) one_le_card).toParams.q -
      (S.params (pubOf point.env) one_le_card).n := by
  rw [quorum_eq]
  change 1 < 2 * 3 - Fintype.card (Fin 4)
  simp

variable {S} {rho : Model.Run (compiled (goldilocks S)) point.env}

/-- The faulty keys of a run at `point` are one: `f = 1`. -/
theorem faulty_ncard (hp : rho.point = point) : (honestKeys S rho)ᶜ.ncard = 1 := by
  have heq : (honestKeys S rho)ᶜ = rho.key ⁻¹' (↑rho.point.faulty : Set (Fin 4)) := by
    ext k
    simp [mem_honestKeys_iff, EnvPoint.faulty, Model.Run.point]
  rw [heq, Set.ncard_preimage_of_injective_subset_range rho.key.injective
    (by simp [rho.key.surjective.range_eq]), Set.ncard_coe_finset, hp, point_faulty]
  rfl

/-- The honest keys of a run at `point` are three. -/
theorem honest_ncard (hp : rho.point = point) : (honestKeys S rho).ncard = 3 := by
  have h := Set.ncard_add_ncard_compl (honestKeys S rho)
  rw [faulty_ncard hp, Nat.card_eq_fintype_card] at h
  change _ + 1 = 4 at h
  omega

/-- The honest keys are awake and joined at every `t ∈ [0, 40]`: `h_t = 3`. -/
theorem honestAwakeJoined_eq (hp : rho.point = point) (hv : rho.ExecutionValid) {t : Time}
    (ht : 0 ≤ t) (htb : t ≤ 40) :
    (simTrace S rho one_le_card).honestAwakeJoined (honestKeys S rho) t = 3 := by
  have hhor : rho.horizon = 40 := congrArg EnvPoint.horizon hp
  have hawake : ∀ y u, 0 ≤ u → u ≤ 40 → (simTrace S rho one_le_card).awake y u := by
    intro y u h0 h1
    rw [simTrace_awake_iff, awakeAt_iff]
    exact ⟨rfl, h0, hhor ▸ h1⟩
  have hset : {y | y ∈ honestKeys S rho ∧ (simTrace S rho one_le_card).awake y t ∧
      (simTrace S rho one_le_card).JoinedAt y t} = honestKeys S rho := by
    ext y
    refine ⟨fun h => h.1, fun hy => ⟨hy, ?_⟩⟩
    exact Compose.ready_implies_joined _ _ _ _ _ _
      (simTrace_goldilocksRun S rho one_le_card hv) y hy t
      (8 * (S.params (pubOf point.env) one_le_card).Δ) ht (Int.le_add_one le_rfl)
      (fun u hu hu' => hawake y u ((le_max_left _ _).trans hu) (hu'.trans htb))
  change {y | _}.ncard = 3
  rw [hset, honest_ncard hp]

/-- `f = 1 < h_t` at every `t ∈ [0, 40]`. -/
theorem faultBound (hp : rho.point = point) (hv : rho.ExecutionValid) {t : Time}
    (ht : 0 ≤ t) (htb : t ≤ 40) :
    (simTrace S rho one_le_card).FaultBound (honestKeys S rho) t := by
  change (honestKeys S rho)ᶜ.ncard < _
  rw [faulty_ncard hp, honestAwakeJoined_eq hp hv ht htb]
  decide

/-- The slot-point fault bound premise of `sleepy_safe_finite` through the horizon, from
`sleepy_faultBound`: `f < h_t` at `t_s`, `t_s + Δ`, `t_s + 2Δ` whenever they are `≤ 40`. -/
theorem slot_faultBound (hp : rho.point = point) (hv : rho.ExecutionValid) :
    ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf point.env) one_le_card).Δ,
      2 * (S.params (pubOf point.env) one_le_card).Δ} : Set Time),
      (S.params (pubOf point.env) one_le_card).ts s + d ≤ 40 →
      (simTrace S rho one_le_card).FaultBound (honestKeys S rho)
        ((S.params (pubOf point.env) one_le_card).ts s + d) := by
  have hhor : rho.horizon = 40 := congrArg EnvPoint.horizon hp
  refine sleepy_faultBound S rho one_le_card hv hhor.ge ?_
  intro t _ _
  unfold EnvPoint.ReadyAbove
  rw [hp, point_readyAt, point_faulty]
  norm_num [point]

/-- A key outside the honest keys makes no call in `simTrace`. -/
theorem not_callAt_of_not_honest (hv : rho.ExecutionValid) {y : Fin (Fintype.card (Fin 4))}
    (hy : y ∉ honestKeys S rho) (k : Nat) (ℓ) : ¬ (simTrace S rho one_le_card).CallAt y k ℓ := by
  rintro ⟨hnode, hl⟩
  obtain ⟨_, _, ev, _, he, -, -, -, hn, -⟩ :=
    simTrace_cut S rho one_le_card (hl ▸ Option.some_ne_none ℓ)
  apply hy
  rw [mem_honestKeys_iff]
  rw [← hnode, hn, show rho.key (rho.ownKey ev.node) = ev.node from rho.key.apply_symm_apply _]
  exact hv.honest_only ev (List.mem_of_getElem? he)

/-- The faulty key is silent: it has no engine event, and it makes no call in `simTrace`, so
it signs no attestation and emits no AC message there. -/
theorem faulty_silent (hp : rho.point = point) (hk : rho.key = Equiv.refl _)
    (hv : rho.ExecutionValid) :
    faultyKey ∉ honestKeys S rho ∧ (∀ e ∈ rho.events, e.node ≠ rho.key faultyKey) ∧
      (∀ k ℓ, ¬ (simTrace S rho one_le_card).CallAt faultyKey k ℓ) ∧
      (∀ k a, ¬ (simTrace S rho one_le_card).SignAt faultyKey k a) ∧
      ∀ k m, ¬ (simTrace S rho one_le_card).EmitAt faultyKey k m := by
  have hhon : rho.honest = {1, 2, 3} := congrArg EnvPoint.honest hp
  have hf : faultyKey ∉ honestKeys S rho := by
    rw [mem_honestKeys_iff]
    rw [hk, hhon]
    decide
  have hc := not_callAt_of_not_honest hv hf
  refine ⟨hf, fun e he h => hf ?_, hc, fun k a ⟨_, h⟩ => hc k _ h,
    fun k m ⟨_, h, _⟩ => hc k _ h⟩
  rw [mem_honestKeys_iff]
  exact h ▸ hv.honest_only e he

variable (S)

/-- (a) A valid engine run of `goldilocks S` at `point` whose canonical trace is a `GoldilocksRun`
with `NoCollRun`, one faulty key (`f = 1`), and `f < 2q − n`. -/
theorem faulty_run :
    ∃ rho : Model.Run (compiled (goldilocks S)) point.env, rho.point = point ∧
      rho.key = Equiv.refl _ ∧ rho.sel = sel S ∧ rho.ExecutionValid ∧
      GoldilocksRun (runProposer S rho one_le_card) (digestOf S rho) (honestKeys S rho)
        (simTrace S rho one_le_card) ∧
      Compose.NoCollRun (digestOf S rho) (simTrace S rho one_le_card) ∧
      (honestKeys S rho)ᶜ.ncard = 1 ∧
      (honestKeys S rho)ᶜ.ncard < 2 * (S.params (pubOf point.env) one_le_card).toParams.q -
        (S.params (pubOf point.env) one_le_card).n := by
  obtain ⟨rho, hp, hk, hs, hv, hc, -, -⟩ := Shape.coverage (goldilocks S) point (by decide)
    (by exact Equiv.refl _) (sel S) (sel_admits S) 0
  refine ⟨rho, hp, hk, hs, hv, simTrace_goldilocksRun S rho one_le_card hv,
    noCollRun_simTrace S rho one_le_card hv hc, faulty_ncard hp, ?_⟩
  rw [faulty_ncard hp]
  exact one_lt_threshold S

/-- (a) On a run with one faulty key, the proved R.7 rows `Regimes.finalized_safe` and
`Regimes.non_framing` apply: the finalized tips of honest nodes never conflict, and no honest
key signs a slashable pair. -/
theorem faulty_run_safe :
    ∃ rho : Model.Run (compiled (goldilocks S)) point.env, rho.point = point ∧
      rho.ExecutionValid ∧ (honestKeys S rho)ᶜ.ncard = 1 ∧
      (∀ y ∈ honestKeys S rho, ∀ z ∈ honestKeys S rho, ∀ i j,
        Compatible ((simTrace S rho one_le_card).HonestBlocks (honestKeys S rho))
          ((simTrace S rho one_le_card).finalizedAt y i)
          ((simTrace S rho one_le_card).finalizedAt z j)) ∧
      ∀ v ∈ honestKeys S rho, ∀ k k' a b, (simTrace S rho one_le_card).SignAt v k a →
        (simTrace S rho one_le_card).SignAt v k' b → ¬ FG.slashable a b := by
  obtain ⟨rho, hp, -, -, hv, hrun, hnc, hf, hlt⟩ := faulty_run S
  exact ⟨rho, hp, hv, hf, Regimes.finalized_safe _ _ _ _ _ _ hrun hnc hlt,
    Regimes.non_framing _ _ _ _ _ _ hrun⟩

/-- (a) The run-level fault premises with `f = 1` are jointly satisfiable on one run: the run
and collision freedom, `f = 1 < 2q − n`, `f < h_t` at every `t ∈ [0, 40]` (`h_t = 3`), and a
silent faulty key. -/
theorem faulty_run_premises :
    ∃ rho : Model.Run (compiled (goldilocks S)) point.env, rho.ExecutionValid ∧
      GoldilocksRun (runProposer S rho one_le_card) (digestOf S rho) (honestKeys S rho)
        (simTrace S rho one_le_card) ∧
      Compose.NoCollRun (digestOf S rho) (simTrace S rho one_le_card) ∧
      (honestKeys S rho)ᶜ.ncard = 1 ∧
      (honestKeys S rho)ᶜ.ncard < 2 * (S.params (pubOf point.env) one_le_card).toParams.q -
        (S.params (pubOf point.env) one_le_card).n ∧
      (∀ t : Time, 0 ≤ t → t ≤ 40 →
        (simTrace S rho one_le_card).honestAwakeJoined (honestKeys S rho) t = 3 ∧
        (simTrace S rho one_le_card).FaultBound (honestKeys S rho) t) ∧
      ∀ k ℓ, ¬ (simTrace S rho one_le_card).CallAt faultyKey k ℓ := by
  obtain ⟨rho, hp, hk, -, hv, hrun, hnc, hf, hlt⟩ := faulty_run S
  exact ⟨rho, hv, hrun, hnc, hf, hlt,
    fun _ ht htb => ⟨honestAwakeJoined_eq hp hv ht htb, faultBound hp hv ht htb⟩,
    (faulty_silent hp hk hv).2.2.1⟩

end Consensus.Goldilocks.Obligations.Test.FaultyRunWitness
