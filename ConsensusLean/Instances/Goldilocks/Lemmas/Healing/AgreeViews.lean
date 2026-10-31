module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeFrozen

public section

/-! # Goldilocks Healing, HS.3: the proposal's view and a voter's merged view agree

`hs234-exact-interface.md` §4 (workbench#12 §3, first paragraph; as A1.7's view agreement in
`Compose/Service/Suffix`): in the settled phase of `AgreeSetting`, the proposal's view
(`View.ofLists pay`, the proposer's slot-`(s−1)` pool) and an honest slot-`s` voter's merged view
have the same equivocators and voters, and the same supporters for every block of both trees
(`SA.view_agree`: the voter's pre-freeze votes and blocks reach the proposer by `t_s`, the support
heads of `P` reach the voter by its vote). Used by `AgreeSuffix`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ i m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {p : Fin sp.n} {kP s : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}

/-- **The views agree**: the proposal's view and the voter's merged view have the same
equivocators and voters, and the same supporters for every block of both trees (open). -/
theorem proposal_views_agree (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓy.frame.tree →
        SA.supporters ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) X =
          SA.supporters ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)
            X := by
  sorry

end Consensus.Goldilocks.Healing

end
