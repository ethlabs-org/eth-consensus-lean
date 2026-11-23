module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Binding
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation
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
      simp [AC.ACParams.ts]
    rw [hts]
    exact AC.slot_of_mem _ s le_rfl ((AC.ts_lt_iff _).2 (by push_cast; omega))
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
private theorem committeeFaultsUpTo_of_selection {P : Params} {O : OutputSchema}
    {F : Model.ProtocolFamily O} {rho : Model.Run F E} (key : Fin P.n ≃ V)
    {cm : Time → Finset (Fin P.n)} {H : Time → Set (Fin P.n)} {Sel : Time → Finset V}
    (hcm : ∀ y t, 0 ≤ t → (y ∈ cm t ↔ key y ∈ Sel t))
    (hH : ∀ y d, y ∈ H d ↔ key y ∉ rho.faultyAt (min d rho.horizon))
    {β : ℚ} {g b : Time} (h : rho.point.CommitteeHealthyOn Sel β (max g 0) b) :
    Generic.CommitteeFaultsUpTo (P := P) β cm H g b := by
  classical
  intro t d ht htb _ hdb hne
  have ht0 : 0 ≤ t := (le_max_right g 0).trans ht
  have hlt := h t ht htb
  have hmem := fun y => hcm y t ht0
  have hmap : (cm t).map key.toEmbedding = Sel t := by
    ext v
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).1 hy
    · intro hvK
      exact ⟨key.symm v, (hmem _).2 (by simpa using hvK), by simp⟩
  have hcard : (cm t).card = (Sel t).card := by
    rw [← hmap, Finset.card_map]
  replace hlt := hlt (by rw [← hmap]; exact hne.map)
  have hle : ((↑(cm t) : Set (Fin P.n)) ∩ (H d)ᶜ).ncard ≤
      (rho.point.faultyAt b ∩ Sel t).card := by
    rw [← Set.ncard_coe_finset (rho.point.faultyAt b ∩ Sel t)]
    refine Set.ncard_le_ncard_of_injOn key ?_ key.injective.injOn (Finset.finite_toSet _)
    rintro y ⟨hy, hyd⟩
    rw [Set.mem_compl_iff, hH, not_not] at hyd
    rw [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_coe]
    exact ⟨rho.faultyAt_mono ((min_le_left _ _).trans hdb) hyd, (hmem y).1 hy⟩
  calc (((↑(cm t) : Set (Fin P.n)) ∩ (H d)ᶜ).ncard : ℚ)
      ≤ ((rho.point.faultyAt b ∩ Sel t).card : ℚ) := by exact_mod_cast hle
    _ < β * (Sel t).card := hlt
    _ = β * (cm t).card := by rw [hcard]

/-- Healthy committee counts bound the Goldilocks selection at each time. -/
theorem committeeFaultsUpTo_of_healthyOn (hv : rho.ExecutionValid) {β : ℚ} {g b : Time}
    (h : rho.point.CommitteeHealthyOn
      ((Model.sysExternal _ (compiled (goldilocks S)) V).selected E (rho.key, rho.sel)) β
      (max g 0) b) :
    Generic.CommitteeFaultsUpTo (P := (S.params (Model.pubOf E) hn).toParams) β
      (runCommittee S rho hn) (honestKeysAt S rho) g b :=
  committeeFaultsUpTo_of_selection rho.key (runCommittee_eq S rho hn hv)
    (fun y d => mem_honestKeysAt_iff S rho d y) h

/-- Healthy committee counts transport through the map's committee and honesty equations. -/
theorem _root_.Consensus.Goldilocks.Generic.RunMap.committeeFaultsUpTo
    {P : Params} {A : NodeAC P} {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
    {F : ChainShapeFamily O I} {run : Model.Run (compiled F) E}
    {payload : A.Blk → Set Nat} (M : Generic.RunMap run payload) {β : ℚ} {g b : Time}
    (h : run.point.CommitteeHealthyOn
      ((Model.sysExternal O (compiled F) V).selected E (run.key, run.sel)) β (max g 0) b) :
    Generic.CommitteeFaultsUpTo (P := P) β M.committee M.honest g b :=
  committeeFaultsUpTo_of_selection M.validator M.committee_eq (fun y d => M.honest_eq y d) h

end Consensus.Goldilocks.Simulation

end
