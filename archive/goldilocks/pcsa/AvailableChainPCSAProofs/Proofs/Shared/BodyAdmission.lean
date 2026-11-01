module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Shared.Roots
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.Admission
public import AvailableChainFGSA.Proofs.WindowStore

public section

/-! C3 immutable-parent exclusions and receiver admission. -/

namespace AvailableChain.PCSA
open SimplexFG Gen.Pure Run
private theorem pcsa_receiver_parent_eq {n : Nat} (st : State n) (N : NamedProposal n)
    (P Q : FGBlock (Fin n)) (hP : eraseFG P = N.erase.parent)
    (hQ : parentFG st N.erase = some Q) : Q = P := by
  have hl := FGSA.pickPair_some_spec st.fg.TF
    (fun B => decide (eraseFG B = N.erase.parent)) hQ
  apply FGSA.eraseFG_injective
  rw [← pcsa_eraseFG_eq, ← pcsa_eraseFG_eq]
  exact (of_decide_eq_true hl.2).trans hP.symm
/-- A body already valid at its immutable parent is never excluded in stage 1. -/
theorem pcsa_body_not_excluded (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n)) (hF : st.fg.F = .genesis)
    (hP : eraseFG P = N.erase.parent)
    (hrows : rowsValidForParent p P N.slot N.rows = true) :
    excludesS p st (ofWire p ⟨.proposer s, .proposal N⟩) = false := by
  change (blockExcluded st N.erase || invalidForParent p st N) = false
  have hb : blockExcluded st N.erase = false := by
    delta blockExcluded activeCompatible
    rw [hF]
    have hc : Block.compatible N.erase (eraseFG (FGBlock.genesis : FGBlock (Fin p.n))) = true :=
      block_compatible_of_common (block_preceq_refl _) (block_genesis_preceq _)
    rw [hc]
    rfl
  rw [hb, Bool.false_or]
  delta invalidForParent
  split
  · rfl
  · cases hq : parentFG st N.erase with
    | none => rfl
    | some Q =>
      dsimp only
      rw [pcsa_receiver_parent_eq st N P Q hP hq, hrows]
      rfl

/-- A fresh dependency-ready body passes the receiver checks in stage 1. -/
theorem pcsa_body_accepted (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hF : st.fg.F = .genesis) (hP : eraseFG P = N.erase.parent)
    (hrows : rowsValidForParent p P N.slot N.rows = true)
    (hw : wellFormed p ⟨.proposer s, .proposal N⟩ = true)
    (hd : depsS p st (ofWire p ⟨.proposer s, .proposal N⟩) = true)
    (hf : processedS p st (ofWire p ⟨.proposer s, .proposal N⟩) = false)
    (hs : N.erase.slot ≤ st.slot p) :
    namedParentHeld st N = true ∧ ∃ Q, parentFG st N.erase = some Q ∧
      blockAccepted p st s N Q = true := by
  change (namedParentHeld st N && (parentFG st N.erase).isSome) = true at hd
  obtain ⟨hn, hq⟩ := Bool.and_eq_true_iff.mp hd
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hq
  have heq := pcsa_receiver_parent_eq st N P Q hP hQ
  refine ⟨hn, Q, hQ, ?_⟩
  change decide (∃ Y ∈ st.fg.TF, Y.root = N.root) = false at hf
  have hroot : N.erase.root = N.root := by cases N <;> rfl
  have hnot : ¬∃ Y ∈ st.fg.TF, Y.root = N.erase.root := by
    simpa only [hroot] using (of_decide_eq_false hf)
  change (N.erase != .genesis && s == N.erase.slot &&
    decide (N.erase.parent.slot < N.erase.slot) && _ && _ && _ && _ &&
    contentOk p N.erase N.raw N.support N.rows N.pc) = true at hw
  have h8 := Bool.and_eq_true_iff.mp hw
  have h7 := Bool.and_eq_true_iff.mp h8.1
  have h6 := Bool.and_eq_true_iff.mp h7.1
  have h5 := Bool.and_eq_true_iff.mp h6.1
  have h4 := Bool.and_eq_true_iff.mp h5.1
  have h3 := Bool.and_eq_true_iff.mp h4.1
  have h2 := Bool.and_eq_true_iff.mp h3.1
  delta blockAccepted
  dsimp only
  rw [hF]
  have hNslot : N.slot = N.erase.slot := by cases N <;> rfl
  have hRowsErase : rowsValidForParent p P N.erase.slot N.rows = true := by
    simpa only [hNslot] using hrows
  simp only [Bool.and_true, heq, hRowsErase]
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨bne_iff_ne.mp h2.1, hs⟩, hnot⟩, KitFG.genesis_preceq _⟩,
    of_decide_eq_true h3.2⟩, beq_iff_eq.mp h2.2⟩, h7.2⟩, h8.2⟩

end AvailableChain.PCSA

end
