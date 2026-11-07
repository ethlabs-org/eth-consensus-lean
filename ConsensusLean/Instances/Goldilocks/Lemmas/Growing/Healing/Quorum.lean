module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Entries

public section

/-! # Historical entry namers charged at consumption

The signing cutoff and consumption horizon are distinct. A validator honest at consumption
cannot have named the entry by the cutoff when the historical honest-signing bound excludes it.
Validators compromised in between are counted as faulty at consumption, not discarded.
-/

namespace Consensus.Goldilocks.Healing.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- If no honest signing event names `E` before `T₀`, its consumption-horizon namers are
exactly the validators faulty at `d`. No compromise-free interval is assumed. -/
theorem namers_eq_faulty (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {T₀ d : Time} (hTd : T₀ ≤ d) {E : NodeBlock P ACP}
    (hquiet : ∀ v j a, v ∈ H (tr.time j) → tr.SignAt v j a → tr.time j ≤ T₀ →
      a.T ≠ E.root) :
    Store.Growing.namers P ACP H tr T₀ d E = (H d)ᶜ := by
  ext v
  constructor
  · intro hv
    rcases hv with hv | ⟨j, a, hs, hj, hE⟩
    · exact hv
    · intro hv
      exact hquiet v j a (hr.antitone (hj.trans hTd) hv) hs hj hE
  · exact Or.inl

/-- The HR.1 namer count follows from the healthy bound at the consumption horizon. -/
theorem namers_lt_quorum (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {T₀ d : Time} (hTd : T₀ ≤ d) (hq : (H d)ᶜ.ncard < P.fg.q)
    {E : NodeBlock P ACP}
    (hquiet : ∀ v j a, v ∈ H (tr.time j) → tr.SignAt v j a → tr.time j ≤ T₀ →
      a.T ≠ E.root) :
    (Store.Growing.namers P ACP H tr T₀ d E).ncard < P.fg.q := by
  rw [namers_eq_faulty hr hTd hquiet]
  exact hq

end Consensus.Goldilocks.Healing.Growing

end
