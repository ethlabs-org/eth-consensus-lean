module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ClaimReductionEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksClaimSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Supply.Fields
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.EngineBinding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs

public section

/-! # The growing-fault endpoint at every vote binding

`meetsObligations_growing`: the shape obligations of `goldilocks S` at `K S A`, for every setup
`S`, from the capstone (`meetsObligations_of_local_proof`) at the Goldilocks engine binding, the
local supplier built from the healing witness (`goldilocksACCorrectLocal_of_healing`,
`goldilocks_ac_healing`) and the local claim suppliers of the canonical run map
(`goldilocks_localClaimSuppliers`). The binding's payload and run interface are the supplier's by
its data equations. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Obligations Generic Simulation
open Blocks Shape
open Consensus.Model (pubOf)

variable (S : Setup) (A : ContractAssumptions S)

/-- At each public parameter, a local supplier at the data equations has an engine binding with
its payload and run interface, an outage policy and a stored read context, and the local claim
suppliers at every valid run. -/
private theorem local_binding (V : Type) [Fintype V] [DecidableEq V]
    (pub : Model.Public) (hn : 1 ≤ pub.n)
    (C : ACCorrectLocal (goldilocksNode (S.params pub hn) (S.ro _)) (fun v => v.val))
    (hC : GoldilocksLocalData (S.params pub hn) (S.ro _) C) :
    ∃ B : EngineBinding (F := goldilocks S) (V := V) pub C.payload (fun v => v.val) C.run,
      ∃ D : ∀ E hE rho hv, OutagePolicy (B.map E hE rho hv),
      ∃ R : ∀ E hE rho hv, StoredReadContext (B.map E hE rho hv),
        ∀ E hE rho hv, LocalClaimSuppliers (B.map E hE rho hv) (B.signer_eq E hE rho hv ▸ C)
          (K S A) (D E hE rho hv) (R E hE rho hv) (SleepyLayer1.goldilocksEvents _ _) := by
  have hpl : payloadOf S = C.payload := by
    rw [hC.payload]
    funext B
    exact payloadOf_eq S B
  have hR : goldilocksRunInterface (S.params pub hn) (S.ro _) = C.run := by
    obtain ⟨⟨hrun, hstart⟩, -⟩ := hC.healing
    obtain ⟨hrun', hstart'⟩ :=
      goldilocksRunInterface_data (sp := S.params pub hn) (ro := S.ro _)
    revert hrun hstart hrun' hstart'
    generalize C.run = R
    generalize goldilocksRunInterface (S.params pub hn) (S.ro _) = R'
    rcases R with ⟨Run, start⟩
    rcases R' with ⟨Run', start'⟩
    intro hrun hstart hrun' hstart'
    dsimp only at hrun hstart hrun' hstart'
    subst hrun hstart hrun' hstart'
    rfl
  have key : ∀ (pl : (goldilocksNode (S.params pub hn) (S.ro _)).Blk → Set Nat)
      (R' : ACRun (goldilocksNode (S.params pub hn) (S.ro _)) (fun v => v.val)),
      payloadOf S = pl → goldilocksRunInterface _ _ = R' →
      ∃ B : EngineBinding (F := goldilocks S) (V := V) pub pl (fun v => v.val) R',
      ∃ D : ∀ E hE rho hv, OutagePolicy (B.map E hE rho hv),
      ∃ R : ∀ E hE rho hv, StoredReadContext (B.map E hE rho hv),
        ∀ E hE rho hv, LocalClaimSuppliers (B.map E hE rho hv) (B.signer_eq E hE rho hv ▸ C)
          (K S A) (D E hE rho hv) (R E hE rho hv) (SleepyLayer1.goldilocksEvents _ _) := by
    rintro pl R' rfl rfl
    refine ⟨goldilocksEngineBinding S pub hn,
      fun E hE rho hv => by
        subst hE
        exact (goldilocksEngineBinding_map S E hn rho hv).symm ▸ goldilocksOutagePolicy S rho hn hv,
      fun E hE rho hv => by
        subst hE
        exact (goldilocksEngineBinding_map S E hn rho hv).symm ▸
          goldilocksStoredReadContext S rho hn hv,
      fun E hE rho hv => ?_⟩
    subst hE
    have aux : ∀ (M : RunMap (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) rho
          (payloadOf S)) (hM : M = goldilocksRunMap S rho hn hv)
        (hsg : (fun v : (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).Msg => v.val) =
          M.signer),
        LocalClaimSuppliers M (hsg ▸ C) (K S A) (hM.symm ▸ goldilocksOutagePolicy S rho hn hv)
          (hM.symm ▸ goldilocksStoredReadContext S rho hn hv)
          (SleepyLayer1.goldilocksEvents _ _) := by
      rintro M rfl hsg
      exact goldilocks_localClaimSuppliers S A rho hn hv C hC
    exact aux _ (goldilocksEngineBinding_map S E hn rho hv) _
  exact key _ _ hpl hR

/-- **The growing-fault endpoint** of `goldilocks S` at the coefficients `contract_coefficients
S A`, at every vote binding. -/
theorem meetsObligations_growing : ShapeObligations (goldilocks S) (K S A) := by
  have hδ : ∀ pub : {pub : Model.Public // 1 ≤ pub.n},
      3 ≤ (S.params pub.1 pub.2).toParams.δt := fun _ => by
    have := A.timeout
    have := A.two_le_fgSlots
    change 3 ≤ S.δt
    omega
  choose C hC using fun pub : {pub : Model.Public // 1 ≤ pub.n} =>
    goldilocksACCorrectLocal_of_healing (goldilocks_ac_healing (ro := S.ro _) (hδ pub))
  choose B D R hL using fun (V : Type) (_ : Fintype V) (_ : DecidableEq V) pub =>
    local_binding S A V pub.1 pub.2 (C pub) (hC pub)
  exact (meetsObligations_of_local_iff _ _).1 (meetsObligations_of_local_proof _ _) _ _ _ C
    (fun _ => SleepyLayer1.goldilocksEvents _ _) (fun V _ _ pub => B V _ _ pub)
    (fun V _ _ pub => D V _ _ pub)
    (fun V _ _ pub => R V _ _ pub) (fun V _ _ pub => hL V _ _ pub)
    (meetsObligations_admissible S A) (by simp [OutputSchema.Serves, schema])
    (meetsObligations_progressFits S A) (meetsObligations_progressTolerant S A)
    (by norm_num [HealthyBetaFit, Params.standard])
    (by norm_num [CommitteeHalfFit, Params.standard])

end Consensus.Goldilocks.Obligations.Growing

end
