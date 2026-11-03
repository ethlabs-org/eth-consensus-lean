module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks SA: a voter's walk stops at the honest proposal (the regime-free core)

At an honest slot-`s` vote, with `P` a block of slot `s` and parent `Q` of an honest proposer:
when `P` is in the voter's viable voter block tree and no old child of `Q` (slot below `s`) is
eligible there, `P` is the voter's only eligible child of `Q` (a second slot-`s` child would be a
second block of the honest proposer in the slot, `HonestObjects.one_block`; `P` itself is eligible
as a block of the current slot), and the voter's walk has no best child at `P` (no block of the
frame is of a later slot than the vote, `frame_slot_le`). Shared by A1.7 (`stop_at_parent_before`,
under `Sleepy`) and HS.3 (`proposal_only_child`, in a settled phase), which supply the two leaves.
-/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- **The stop at `Q`, from its two leaves.** -/
theorem stop_core (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y j ℓ e) {s : Nat}
    (hes : e.msg.slot = s) {Q P : Blk sp.n FGP} (hPs : P.slot = s)
    (hPQ : P.parent = some Q.root) (hpH : P.proposer ∈ H)
    (hng : ∀ B ∈ ℓ.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot)
    (hPv : P ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame s))
    (hold : ∀ B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame s),
      B.parent = some Q.root → B.slot < s →
      ¬ goldfishEligible sp ℓ.frame (tr.time j) (mergedVoteView sp e.readPoint ℓ.frame s)
        ((s : Int) - 1) B) :
    (P ∈ {B | B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame s) ∧
        B.parent = some Q.root ∧ goldfishEligible sp ℓ.frame (tr.time j)
          (mergedVoteView sp e.readPoint ℓ.frame s) ((s : Int) - 1) B} ∧
      ∀ B ∈ {B | B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame s) ∧
          B.parent = some Q.root ∧ goldfishEligible sp ℓ.frame (tr.time j)
            (mergedVoteView sp e.readPoint ℓ.frame s) ((s : Int) - 1) B}, B = P) ∧
    ¬ ∃ C, IsBest sp
      (goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame s) ((s : Int) - 1))
      {B | B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame s) ∧
        B.parent = some P.root ∧ goldfishEligible sp ℓ.frame (tr.time j)
          (mergedVoteView sp e.readPoint ℓ.frame s) ((s : Int) - 1) B} C := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΦU := (frameIn_of_callAt hr hy hc.1).2
  have hsj : sp.slot (tr.time j) = s := (castAt_spec hr hy hc).2.1.symm.trans hes
  have hslot := frame_slot_le sp hr hy hc.1
  have hPt : P ∈ ℓ.frame.tree := hPv.1.1
  have hfb : ∀ B ∈ ℓ.frame.tree, HonestFrameBlock tr H B := fun B hB => ⟨y, hy, j, ℓ, hc.1, hB⟩
  have hpp : P.proposer = proposer s :=
    hPs ▸ hrun.honest.proposer P (hfb P hPt) (hng P hPt (by rw [hPQ]; simp))
  refine ⟨⟨⟨hPv, hPQ, Or.inr (Or.inl (hPs.trans hsj.symm))⟩, fun B ⟨hBv, hBQ, hBe⟩ => ?_⟩, ?_⟩
  · have hBt : B ∈ ℓ.frame.tree := hBv.1.1
    rcases Nat.lt_or_ge B.slot s with hlt | hge
    · exact absurd hBe (hold B hBv hBQ hlt)
    have hBs : B.slot = s := le_antisymm (hsj ▸ hslot B hBt) hge
    have hBp : B.proposer = proposer s :=
      hBs ▸ hrun.honest.proposer B (hfb B hBt) (hng B hBt (by rw [hBQ]; simp))
    exact (hrun.honest.one_block P B (hfb P hPt) (hfb B hBt) hpH (hpp.trans hBp.symm)
      (hPs.trans hBs.symm)).symm
  · rintro ⟨C, ⟨⟨hCv, hCP, -⟩, -⟩⟩
    have hCt : C ∈ ℓ.frame.tree := hCv.1.1
    have h1 := hU.2 P (hΦU hPt) C (hΦU hCt) hCP
    have h2 : C.slot ≤ sp.slot (tr.time j) := hslot C hCt
    omega

end Consensus.Goldilocks.SA

end
