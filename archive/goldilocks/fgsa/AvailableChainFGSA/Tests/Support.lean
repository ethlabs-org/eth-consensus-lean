module
public import AvailableChainFGSA.Model.Handlers

@[expose] public section

namespace AvailableChain.FGSA.Tests

open AvailableChain.SimplexFG

/-! Test support: a proved rewrite of a proposal delivery with an explicit FG
block, for fixtures whose `decide +kernel` checks would otherwise reduce
`fgBlock` again at each use. -/

/-- [test helper; ROOT-DIGEST W3] The accepted branch of `admitBlock`, with an explicit FG block
`B` in place of `fgBlock P N.erase N.rows`. The kernel reduces `fgBlock P N.erase N.rows` again
at each use, and each reduction decodes the body (`appOf`). On a large store
this makes a `decide +kernel` check too slow, so such a test first rewrites
with `process_eq_admitWith` (for the `B` with `fgBlock P N.erase N.rows = B`). -/
def admitWith (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (P B : FGBlock (Fin p.n)) : State p.n :=
  if !namedParentHeld st N then st else
  if blockAccepted p st s N P then
    let st1 : State p.n := { st with
      base := GridCO.admitProposal p.toParams.engine st.base
        (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
      fg := Window.on_block p p.K_W st.fg B
      proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
    let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
    N.rows.foldl (admitRow p) st2
  else st

/-- [test helper; ROOT-DIGEST W3] A proposal delivery, with its FG parent `P` and its FG block
`B` explicit. -/
theorem process_eq_admitWith (p : Params) (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (P B : FGBlock (Fin p.n)) (hP : parentFG st N.erase = some P)
    (hB : fgBlock P N.erase N.rows = B) :
    process p st ⟨.proposer s, .proposal N⟩ =
      admitWith p st s N P B := by
  subst hB
  change admitBlock p st s N = _
  unfold admitBlock admitWith
  by_cases hn : namedParentHeld st N = true
  · simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [hP]
  · have hf : namedParentHeld st N = false := Bool.eq_false_iff.mpr hn
    simp only [hf, Bool.not_false, ite_true]

end AvailableChain.FGSA.Tests
end
