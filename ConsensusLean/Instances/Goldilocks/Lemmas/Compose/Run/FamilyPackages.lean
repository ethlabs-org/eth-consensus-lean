module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.Identity
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.ServiceEquivalence
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Votes
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Records
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutagePostStop

/-! # Goldilocks supplies for packages requiring node-level provenance -/

public section

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload goldilocksFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {R : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

theorem goldilocksLockOrigin_node (hr : GoldilocksRun proposer dg H R) (hnc : NoCollRun dg R) :
    SA.FamilyFacts.LockOrigin (goldilocksFamily sp (List (FG.Att sp.n)) ro)
      R.projAC H (R.HonestBlocks H) := by
  simp only [SA.FamilyFacts.LockOrigin, SA.proj_goldilocks]
  intro y hy i l hl
  rw [projAC_state hr.toLocalRun hy i] at hl
  obtain ⟨L, hL, hLr, C, ho, hLC⟩ := lock_origin hr hnc hy i l hl
  obtain ⟨z, hz, j, hj, CV, he⟩ := originBefore_iff.mp ho
  refine ⟨L, ⟨y, hy, i, hL⟩, hLr, z, hz, j, hj, C, CV, ?_, hLC⟩
  exact he.imp_right fun h => ⟨rfl, h⟩

theorem goldilocksSlowCompatibility_node (hr : GoldilocksRun proposer dg H R)
    (hnc : NoCollRun dg R) :
    SA.FamilyFacts.SlowCompatibility (goldilocksFamily sp (List (FG.Att sp.n)) ro)
      R.projAC H (R.HonestBlocks H) := by
  simp only [SA.FamilyFacts.SlowCompatibility, SA.proj_goldilocks]
  intro y hy i l hl hf B hg
  rw [projAC_state hr.toLocalRun hy i] at hl
  exact slow_lock_compatible hr hnc hy hl hf hg

theorem goldilocksParticipants_node (hr : GoldilocksRun proposer dg H R) (hnc : NoCollRun dg R) :
    SA.FamilyFacts.Participants (goldilocksFamily sp (List (FG.Att sp.n)) ro)
      R.projAC H (R.HonestBlocks H) := by
  have hlocal := (goldilocks_ac_projection sp ro dg H R proposer hr hnc).localRun
  constructor
  · simp only [SA.proj_goldilocks]
    intro x hx s hw hj
    have hj' := (joined_projection sp ro dg H R proposer hr x hx _).1.mpr hj
    obtain ⟨i, e, he, hs, _⟩ := vote_of_awake_joined hr hnc hx (mayVote_stock hr hnc hx _) hw hj'
    exact ⟨i, e, he, (SA.vote_signer_slot hlocal hx he).1, hs⟩
  · simp only [SA.proj_goldilocks]
    intro s b hserv hb X hX i ℓ hu x hx hw hj
    have hj' := (joined_projection sp ro dg H R proposer hr x hx _).1.mpr hj
    exact awake_participant_early hr hnc
      ((SA.FamilyFacts.serviceBefore_iff_old ..).mp hserv) hb hX hu hx
      (mayVote_stock hr hnc hx _) hw hj'

variable {FGP : Type} {ro : ReplayOrder sp FGP} {U : Set (SA.Blk sp.n FGP)}
  {o : SA.SATrace sp FGP ro}

theorem goldilocksWrites_iff (y : Fin sp.n) (i : Nat)
    (ℓ : ACLabel (SA.goldilocksSA sp FGP ro)) (r r' : Nat) :
    Writes ℓ.frame (fun C => ∃ s CV, SA.ResultAt o y i s C CV ∨
      SA.OptimisticLockAt o y i s C CV) r r' ↔
    Relation.ReflTransGen (fun r r' => ∃ C ∈ ℓ.frame.tree,
      (∃ s CV, SA.ResultAt o y i s C CV ∨
        SA.FamilyFacts.OptimisticEvent (goldilocksFamily sp FGP ro).mode o y i s C CV) ∧
      ((SA.AncR ℓ.frame C r ∧ r' = r) ∨ (¬ SA.AncR ℓ.frame C r ∧ r' = C.root))) r r' := by
  rw [writes_iff]
  have hm : (goldilocksFamily sp FGP ro).mode.optimistic = true := rfl
  simp only [SA.FamilyFacts.OptimisticEvent, hm, true_and]

theorem goldilocksRecordWrites (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U o) :
    SA.FamilyFacts.RecordWrites (goldilocksFamily sp FGP ro) o H := by
  simp only [SA.FamilyFacts.RecordWrites, SA.proj_goldilocks]
  intro y hy i ℓ hc
  exact (goldilocksWrites_iff y i ℓ _ _).mp (call_writes hr hy hc)

end Consensus.Goldilocks.Compose

end
