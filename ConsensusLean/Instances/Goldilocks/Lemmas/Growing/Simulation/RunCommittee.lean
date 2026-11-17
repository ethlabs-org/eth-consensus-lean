module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Binding
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule

public section

/-! # The committee of a run at each time

`runCommittee S rho hn t` is the committee of the slot of `t`: the keys the run selects for that
slot's vote role (`voteK`). For `t ≥ 0` it is the selection the participation premises read at
`t` (`runCommittee_eq`, from `mem_voteK_iff_selected`), and read at each slot's start it is
`voteK` again (`dictOfTime_runCommittee`). A healthy committee bound over the run's selections,
charged at a bound `b`, bounds every run committee against honesty up to `b`
(`committeeFaultsUpTo_of_healthyOn`). -/

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

/-- **Every run committee has `committeeSize` members**, the slot committee of its time. -/
theorem runCommittee_card (hv : rho.ExecutionValid) (t : Time) :
    (runCommittee S rho hn t).card = (S.params (pubOf E) hn).committeeSize := by
  classical
  simp only [runCommittee]
  rw [← Set.ncard_eq_toFinset_card']
  exact Obligations.Growing.voteK_ncard S rho hn hv _

/-- **Healthy committee counts bound the run committees.** A committee bound over the run's
selections on `[max g 0, b]`, charged at `b`, bounds the faulty members of each run
committee in that window against honesty at any time `d ∈ [0, b]`. -/
theorem committeeFaultsUpTo_of_healthyOn (hv : rho.ExecutionValid) {β : ℚ} {g b : Time}
    (h : rho.point.CommitteeHealthyOn
      ((Model.sysExternal _ (compiled (goldilocks S)) V).selected E (rho.key, rho.sel)) β
      (max g 0) b) :
    Generic.CommitteeFaultsUpTo (P := (S.params (Model.pubOf E) hn).toParams) β
      (runCommittee S rho hn) (honestKeysAt S rho) g b := by
  classical
  intro t d ht htb _ hdb hne
  have ht0 : 0 ≤ t := (le_max_right g 0).trans ht
  have hlt := h t ht htb
  obtain ⟨Ks, hKs⟩ : ∃ Ks, (Model.sysExternal _ (compiled (goldilocks S)) V).selected E
      (rho.key, rho.sel) t = Ks := ⟨_, rfl⟩
  rw [hKs] at hlt
  have hmem : ∀ y, y ∈ runCommittee S rho hn t ↔ rho.key y ∈ Ks := fun y => by
    rw [← hKs]
    exact runCommittee_eq S rho hn hv y t ht0
  have hmap : (runCommittee S rho hn t).map rho.key.toEmbedding = Ks := by
    ext v
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).1 hy
    · intro hvK
      exact ⟨rho.key.symm v, (hmem _).2 (by simpa using hvK), by simp⟩
  have hcard : (runCommittee S rho hn t).card = Ks.card := by
    rw [← hmap, Finset.card_map]
  replace hlt := hlt (by rw [← hmap]; exact hne.map)
  have hle : ((↑(runCommittee S rho hn t) : Set (Fin (Fintype.card V))) ∩
      (honestKeysAt S rho d)ᶜ).ncard ≤ (rho.point.faultyAt b ∩ Ks).card := by
    rw [← Set.ncard_coe_finset (rho.point.faultyAt b ∩ Ks)]
    refine Set.ncard_le_ncard_of_injOn rho.key ?_ rho.key.injective.injOn (Finset.finite_toSet _)
    rintro y ⟨hy, hyd⟩
    rw [Set.mem_compl_iff, mem_honestKeysAt_iff, not_not] at hyd
    rw [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_coe]
    exact ⟨rho.faultyAt_mono ((min_le_left _ _).trans hdb) hyd, (hmem y).1 hy⟩
  calc (((↑(runCommittee S rho hn t) : Set (Fin (Fintype.card V))) ∩
        (honestKeysAt S rho d)ᶜ).ncard : ℚ)
      ≤ ((rho.point.faultyAt b ∩ Ks).card : ℚ) := by exact_mod_cast hle
    _ < β * Ks.card := hlt
    _ = β * (runCommittee S rho hn t).card := by rw [hcard]

end Consensus.Goldilocks.Simulation

end
