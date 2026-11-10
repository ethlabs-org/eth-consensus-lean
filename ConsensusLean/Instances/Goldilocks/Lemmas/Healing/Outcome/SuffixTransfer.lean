module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild

public section

/-! # Goldilocks Healing: a best child below the proposal parent stays best at the voter

One step of a voter's walk towards the parent of an actual proposal (`suffix_best_of_views`). It
reads the two frames and the agreement of the two vote views; the winner's place in the voter's
tree and the reflection of the competitors are premises, not the run or its fault model. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams Payload)

variable {sp : SAParams}

/-- **A best child below the proposal parent stays best at the voter.** The frames `Φp`
(proposer, at `t_{s+1}`) and `Φy` lie in a coherent `U`, the view `V` agrees with `pay`, and `P`
(slot `s + 1`, in `Φy.tree`) is a child of `Q ∈ Φp.tree`. The best eligible child `C` below `Q` of
a viable head `X ≠ Q` of `Φp` is the best eligible child of `X` in `Ty`, when `C` is in `Ty`
(`hwin`) and every other child of `X` in `Ty` is in `Φp`'s viable tree (`hrefl`): `C` is older
than slot `s + 1`, so it is eligible by its strict majority (`SA.isBest_transfer`). -/
theorem suffix_best_of_views {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {Φp Φy : SA.Frm sp.n (List (FG.Att sp.n))} (hΦp : FrameOK Φp) (hΦpU : Φp.tree ⊆ U)
    (hΦyU : Φy.tree ⊆ U) {Ty : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hTy : Ty ⊆ Φy.tree)
    {ti tj : Time} {s : Nat} (hti : ti = sp.ts (s + 1 : Nat)) {pay : Payload sp.n}
    {V : SA.View sp.n}
    (hv : SA.equivocators (SA.View.ofLists pay).votes = SA.equivocators V.votes ∧
      SA.voters (SA.View.ofLists pay).votes = SA.voters V.votes ∧
      ∀ X ∈ Φp.tree, X ∈ Φy.tree →
        SA.supporters Φp (SA.View.ofLists pay) s X = SA.supporters Φy V s X)
    {Q P X C : SA.Blk sp.n (List (FG.Att sp.n))} (hQt : Q ∈ Φp.tree)
    (hPQ : P.parent = some Q.root) (hPs : P.slot = s + 1) (hPy : P ∈ Φy.tree)
    (hXQ : Φp.Anc X Q) (hne : X ≠ Q) (hXv : X ∈ Φp.viableHeads) (hCQ : Φp.Anc C Q)
    (hwin : Anc U C P → Anc U X C → C ∈ Ty)
    (hrefl : ∀ B ∈ Ty, B ≠ P → B.parent = some X.root → B ∈ Φp.viableTree Φp.tree)
    (hC : SA.IsBest sp (SA.goldfishScore sp Φp (SA.View.ofLists pay) s)
      {B | B ∈ Φp.viableTree Φp.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) s B} C) :
    SA.IsBest sp (SA.goldfishScore sp Φy V s)
      {B | B ∈ Ty ∧ B.parent = some X.root ∧ SA.goldfishEligible sp Φy tj V s B} C := by
  have hXt := SA.mem_of_anc hXQ hQt
  have hQP : Anc U Q P := .single ⟨hΦpU hQt, hΦyU hPy, hPQ⟩
  have hXC : Anc U X C := .single ⟨hΦpU hXt, hΦpU hC.1.1.1, hC.1.2.1⟩
  have hCs : C.slot < s + 1 := by
    have h1 := (Anc.slot_le hΦp.coherent hCQ).1
    have h2 := hU.2 Q (hΦpU hQt) P (hΦyU hPy) hPQ
    omega
  have hslot : sp.slot ti = s + 1 := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  apply SA.isBest_transfer hXv (by omega) hv.2.1 ?_ (fun B hB => hB.1) hTy
    (hwin ((hCQ.mono hΦpU).trans hQP) hXC) ?_ hC
  · intro B hBp hBy
    simp only [SA.goldfishScore, hv.1, hv.2.2 B hBp hBy]
  · intro B hB hBX
    refine hrefl B hB ?_ hBX
    rintro rfl
    exact hne (hU.1 (hΦpU hXt) (hΦpU hQt) (Option.some_injective _ (hBX.symm.trans hPQ)))

end Consensus.Goldilocks.Healing

end
