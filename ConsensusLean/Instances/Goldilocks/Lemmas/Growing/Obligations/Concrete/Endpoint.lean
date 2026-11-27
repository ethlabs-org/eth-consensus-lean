module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ClaimReductionEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksClaimSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Supply.Fields
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.EngineBinding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GuardIdle
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap

public section

/-! # The growing-fault endpoint at every vote binding

`meetsObligations_growing`: the shape obligations of `goldilocks S` at `K S A`, for every setup
`S`, from the capstone (`meetsObligations_of_local_proof`) at the Goldilocks engine binding, the
local supplier built from the healing witness (`goldilocksACCorrectLocal_of_healing`,
`goldilocks_ac_healing`) and the local claim suppliers of the canonical run map
(`goldilocks_localClaimSuppliers`), and the idle slashing guard (`Simulation.guardIdle`). The
binding's payload and run interface are the supplier's by its data equations. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Obligations Generic Simulation
open Blocks Shape
open Consensus.Model (pubOf)

variable (S : Setup) (A : ContractAssumptions S)

/-- Run interfaces with the same run predicate and committee start are equal. -/
private theorem acRun_ext {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {R R' : ACRun A sg}
    (hrun : R.Run = R'.Run) (hstart : R.start = R'.start) : R = R' := by
  cases R
  cases R'
  cases hrun
  cases hstart
  rfl

/-- At each public parameter, a local supplier at the data equations has an engine binding with
its payload and run interface, an outage policy and a stored read context, and the local claim
suppliers at every valid run. -/
private theorem local_binding (V : Type) [Fintype V] [DecidableEq V]
    (pub : Model.Public) (hn : 1 ≤ pub.n)
    {fgHold : Time} (C : ACCorrectLocal (goldilocksNode (S.params pub hn))
      (fun v => v.val) fgHold)
    (hC : GoldilocksLocalData (S.params pub hn) C (S.sign pub) A.signGap
      A.releaseGap) :
    ∃ B : EngineBinding (F := goldilocks S) (V := V) pub C.payload (fun v => v.val) C.run,
      ∃ D : ∀ E hE rho hv, OutagePolicy (B.map E hE rho hv),
      ∃ R : ∀ E hE rho hv, StoredReadContext (B.map E hE rho hv),
        ∀ E hE rho hv, LocalClaimSuppliers (B.map E hE rho hv) (B.signer_eq E hE rho hv ▸ C)
          (K S A) (D E hE rho hv) (R E hE rho hv) (SleepyLayer1.goldilocksEvents _) := by
  have hpl : payloadOf S = C.payload := by
    rw [hC.payload]
    funext B
    exact payloadOf_eq S B
  have hd := goldilocksRunInterface_data (sp := S.params pub hn)
    (sign := S.sign pub) (G := A.signGap)
  rw [← hpl, ← acRun_ext (hd.1.trans hC.healing.1.1.symm) (hd.2.trans hC.healing.1.2.symm)]
  refine ⟨goldilocksEngineBinding S A pub hn,
    fun E hE rho hv => by
      subst hE
      exact (goldilocksEngineBinding_map S A E hn rho hv).symm ▸
        goldilocksOutagePolicy S rho hn hv,
    fun E hE rho hv => by
      subst hE
      exact (goldilocksEngineBinding_map S A E hn rho hv).symm ▸
        goldilocksStoredReadContext S rho hn hv,
    fun E hE rho hv => ?_⟩
  subst hE
  have aux : ∀ M (hM : M = goldilocksRunMap S rho hn hv)
      (hsg : (fun v => v.val : (goldilocksNode (S.params (pubOf E) hn)).Msg →
        Fin (Fintype.card V)) = M.signer),
      LocalClaimSuppliers M (hsg ▸ C) (K S A) (hM.symm ▸ goldilocksOutagePolicy S rho hn hv)
        (hM.symm ▸ goldilocksStoredReadContext S rho hn hv)
        (SleepyLayer1.goldilocksEvents _) := by
    rintro M rfl hsg
    exact goldilocks_localClaimSuppliers S A rho hn hv C hC
  exact aux _ (goldilocksEngineBinding_map S A E hn rho hv) _

/-- **The growing-fault endpoint** of `goldilocks S` at the coefficients `contract_coefficients
S A`, at every vote binding. -/
theorem meetsObligations_growing : ShapeObligations (goldilocks S) (K S A) := by
  have hδ : ∀ pub : {pub : Model.Public // 1 ≤ pub.n},
      3 + (A.signGap + 3) / 4 ≤ (S.params pub.1 pub.2).toParams.δt := fun _ =>
    signGap_δt A
  choose C hC using fun pub : {pub : Model.Public // 1 ≤ pub.n} =>
    goldilocksACCorrectLocal_of_healing
      (goldilocks_ac_healing (sign := S.sign pub.1) (G := A.signGap)
        (Rg := A.releaseGap) (hδ pub))
  choose B D R hL using fun (V : Type) (_ : Fintype V) (_ : DecidableEq V) pub =>
    local_binding S A V pub.1 pub.2 (C pub) (hC pub)
  exact (meetsObligations_of_local_iff _ _).1 (meetsObligations_of_local_proof _ _) _ _ _ C
    (fun _ => SleepyLayer1.goldilocksEvents _) (fun V _ _ pub => B V _ _ pub)
    (fun V _ _ pub => D V _ _ pub)
    (fun V _ _ pub => R V _ _ pub) (fun V _ _ pub => hL V _ _ pub)
    (meetsObligations_admissible S A) (by simp [OutputSchema.Serves, schema])
    (meetsObligations_progressFits S A) (meetsObligations_progressTolerant S A)
    (fun _ _ _ r hv => Simulation.guardIdle S r.2 hv)
    (by norm_num [HealthyBetaFit, Params.standard])
    (by norm_num [CommitteeHalfFit, Params.standard])

end Consensus.Goldilocks.Obligations.Growing

end
