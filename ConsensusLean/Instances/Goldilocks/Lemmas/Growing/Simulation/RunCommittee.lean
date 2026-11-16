module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Binding
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule

public section

/-! # The committee of a run at each time

`runCommittee S rho hn t` is the committee of the slot of `t`: the keys the run selects for that
slot's vote role (`voteK`). For `t ≥ 0` it is the selection the participation premises read at
`t` (`runCommittee_eq`, from `mem_voteK_iff_selected`), and read at each slot's start it is
`voteK` again (`dictOfTime_runCommittee`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Obligations.Growing (voteK mem_voteK_iff_selected)
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : Setup) {E : Env V}
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The committee of a run at time `t`**: the committee of the slot of `t`. -/
noncomputable def runCommittee : Time → Finset (Fin (Fintype.card V)) := by
  classical
  exact fun t => ((voteK S rho).committee ((S.params (pubOf E) hn).slot t)).toFinset

omit [DecidableEq V] in
/-- Times in the same slot select the same committee. -/
theorem runCommittee_eq_of_slot_eq {t u : Time}
    (h : (S.params (pubOf E) hn).slot t = (S.params (pubOf E) hn).slot u) :
    runCommittee S rho hn t = runCommittee S rho hn u := by
  classical
  change ((voteK S rho).committee _).toFinset = ((voteK S rho).committee _).toFinset
  exact congrArg (fun s => ((voteK S rho).committee s).toFinset) h

/-- **The committee at `t ≥ 0` is the selection the participation premises read at `t`.** -/
theorem runCommittee_eq (hv : rho.ExecutionValid) :
    ∀ y t, 0 ≤ t → (y ∈ runCommittee S rho hn t ↔ rho.key y ∈
      (Model.sysExternal _ (compiled (goldilocks S)) V).selected
        E (rho.key, rho.sel) t) := by
  intro y t ht
  classical
  rw [runCommittee, Set.mem_toFinset]
  exact mem_voteK_iff_selected S rho hn hv ht

omit [DecidableEq V] in
/-- **Read at each slot's start, the run committee is `voteK`.** -/
theorem dictOfTime_runCommittee :
    Generic.dictOfTime (S.params (pubOf E) hn) (runCommittee S rho hn) = voteK S rho := by
  classical
  have hslot : ∀ s : Nat, (S.params (pubOf E) hn).slot
      ((S.params (pubOf E) hn).toParams.slotTime s) = s := fun s => by
    have hts : (S.params (pubOf E) hn).toParams.slotTime s = (S.params (pubOf E) hn).ts s := by
      rw [(S.params (pubOf E) hn).slotTime_eq]
      simp [SA.SAParams.ts]
    rw [hts]
    exact SA.slot_of_mem _ s le_rfl ((SA.ts_lt_iff _).2 (by push_cast; omega))
  simp only [Generic.dictOfTime, runCommittee, Set.coe_toFinset, hslot]

end Consensus.Goldilocks.Simulation

end
