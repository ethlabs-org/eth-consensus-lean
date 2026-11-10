module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Inv

public section

/-! # External use of the lock invariant's record update -/

namespace Consensus.Goldilocks.SA.Test

open Classical in
/-- The exported update theorem also applies when the new-lock set is empty. -/
theorem lockInv_addLocks_empty {sp : SAParams} {FGP : Type}
    {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A A' : SAState sp.n} (h : LockInv U A Φ) {t : Time} {s : Nat}
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hconf : ¬ conflictsWithLock sp A.locks Φ t B)
    (hlocks : A'.locks = SA.addLocks sp A.locks Φ t s ∅)
    (hrec : A'.latestConfirmed =
      if AncR Φ B A.latestConfirmed then A.latestConfirmed else B.root) :
    LockInv U A' Φ := by
  exact LockInv.addLocks hU hΦ hΦU h (C := B) (N := ∅) hB hconf hlocks
    (by simp) hrec

end Consensus.Goldilocks.SA.Test
