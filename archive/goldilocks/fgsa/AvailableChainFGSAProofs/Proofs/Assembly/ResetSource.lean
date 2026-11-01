module
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (source)
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (core types)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- The prepared reset source keeps the source, height, root, gate result, and fast key. -/
theorem assembly_reset_emittedName (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hb : BaseSet p c E rho)
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId}
    (ha : HonestRowAt p c E rho j x r a) (he : namedEntry a.payload.height_pair = some e) :
    ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
      e = ((heightView p C).h, (heightView p C).T_h.root) ∧
      gateResult p c E rho x (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C) := by
  have hsd : SourceDisciplineBaseAt p c E rho :=
    sourceDiscipline_base p c E rho (pt := ()) ⟨hb⟩
  delta SourceDisciplineBaseAt at hsd
  obtain ⟨e', C, G, he', hC, hh, _, hG, hCG, hf⟩ := hsd.2.2 j x r a ha
  obtain rfl : e = e' := Option.some.inj (he.symm.trans he')
  exact ⟨C, G, hC, hh, hG, hCG, hf⟩

end AvailableChain.FGSA.Run
end
