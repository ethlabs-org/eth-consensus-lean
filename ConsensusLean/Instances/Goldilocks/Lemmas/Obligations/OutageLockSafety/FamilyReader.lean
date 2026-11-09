module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyCount
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Readers of the family outage invariant

Lock compatibility is a consumer of the outage invariant. The stronger record-above-lock
invariant is a separate step-law fact; it is not inferred from the unlock relation alone.
-/

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

/-- Ancestor transfer in any coherent block universe. -/
theorem compatible_of_anc_right_family {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {X B P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc U B P) (hX : Compatible U X P) : Compatible U X B := by
  rcases hX with h | h
  · exact Anc.total hU h hBP
  · exact Or.inr (hBP.trans h)

/-- Live projected locks remain compatible with every ancestor of the protected block. -/
theorem liveLockBlocks_compatible_family {D : OutageLockPremises F tr H proposer dg sg}
    (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    (m : Nat) (τ : Time) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocks H) B D.P) :
    ∀ X ∈ SA.liveLockBlocks sp ((F.proj tr.projAC).state y m).locks
      (Node.frame (tr.state y m)) τ, Compatible (tr.HonestBlocks H) X B := by
  intro X hX
  have hU := D.coherent
  have hΦ := Compose.frameOK_state D.hrun.toLocalRun hy m
  have hΦU : (Node.frame (tr.state y m)).tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨y, hy, m, hZ.1⟩
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hX
  obtain ⟨L, hL, hLr, hLP⟩ := (hinv m).locks y hy m le_rfl l hl
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) ⟨y, hy, m, hL⟩ (hB₀r.trans hLr.symm)
  apply compatible_of_anc_right_family hU hBP
  have hanc := (SA.viableAncestor_anc hΦ hB₀).2.mono hΦU
  rcases hLP with h | h
  · exact Or.inl (hanc.trans h)
  · exact Anc.total hU hanc h

/-- The record/lock invariant required by the chain reader, over observations only. -/
def LockInvariant (F : SAFamily sp (List (FG.Att sp.n)) ro A) (tr : RunTrace A.toAC)
    (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ m, SA.LockInv (tr.HonestBlocks H) ((F.proj tr.projAC).state y m)
    (Node.frame (tr.state y m))

/-- Supply the existing record/lock invariant for Goldilocks, without exporting reachability. -/
theorem lockInvariant_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    LockInvariant (SA.goldilocksFamily sp _ ro) tr H := by
  intro y hy m
  dsimp only [SA.goldilocksFamily, SA.goldilocksOperations, SA.SAOperations.toAC]
  change SA.LockInv (tr.HonestBlocks H) (tr.projAC.state y m) (Node.frame (tr.state y m))
  have hac := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc).localRun
  have hst := Compose.projAC_state hr.toLocalRun hy m
  obtain ⟨E, hEt, hEr, -⟩ := Compose.record_origin hr hnc hy m
  have hEU : E ∈ tr.HonestBlocks H := ⟨y, hy, m, hEt⟩
  refine SA.lockInv_iff.2 ⟨E, hEU, by rw [hst]; exact hEr,
    fun hFE => ⟨hEt, Compose.honest_held_anc hr hnc hy hFE hEt⟩,
    fun l hl X hX hXr => ?_⟩
  rcases SA.state_reachable sp hac hy m with h0 | ⟨Φ, t, hreach, -⟩
  · rw [h0] at hl
    exact absurd hl (Set.notMem_empty l)
  · obtain ⟨-, -, hli⟩ := SA.lockInv_of_reachable hac.coherent hreach
    obtain ⟨E', hE'U, hE'r, -, hlE⟩ := SA.lockInv_iff.1 hli
    obtain rfl : E' = E := hac.coherent.1 hE'U hEU (hE'r.trans (by rw [hst]; exact hEr.symm))
    exact hlE l hl X hX hXr

/-- The reader requests the lock invariant, not reachability under a concrete handler. -/
theorem lockInv_state_family (h : LockInvariant F tr H) {y : Fin sp.n} (hy : y ∈ H) (m : Nat) :
    SA.LockInv (tr.HonestBlocks H) ((F.proj tr.projAC).state y m)
      (Node.frame (tr.state y m)) := h y hy m

/-- The chain consequence is independent of the candidate's execution rule. -/
theorem liveBlocks_chain_at_family (hr : FamilyRun F proposer dg H sg tr)
    (h : LockInvariant F tr H) {y : Fin sp.n} (hy : y ∈ H) (m : Nat) (τ : Time) :
    ∀ X ∈ SA.liveLockBlocks sp ((F.proj tr.projAC).state y m).locks (Node.frame (tr.state y m)) τ,
      ∀ Y ∈ SA.liveLockBlocks sp ((F.proj tr.projAC).state y m).locks (Node.frame (tr.state y m)) τ,
        Compatible (Node.frame (tr.state y m)).tree X Y :=
  (lockInv_state_family h hy m).liveBlocks_chain hr.observation.coherent
    (Compose.frameOK_state hr.toLocalRun hy m) fun _ hX => ⟨y, hy, m, hX.1⟩

end Consensus.Goldilocks.FamilySafety

end
