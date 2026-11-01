module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateBody
public import AvailableChainFGSAProofs.Proofs.Outage.ReceiverInputs

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Closed Clean history and public reads produce both growth callbacks.
The receiver and gate services are produced here, with their exact GST and floor guards. -/
theorem clean_growth_suppliers [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hOutputs : ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedCompat (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
        (fun t => 0 ≤ t ∧ t ≤ rho.horizon))
    (hOrigins : ∀ t x, SA.gateTime p.toParams pt.s ≤ t → t ≤ rho.horizon →
      confirmedReader p c E rho x t →
      ∃ q i B, pt.s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
        enabledGateAt p c E rho i x q ∧ gateResultAt p c E rho i = some (some B) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho t) x))
    (hstrat : RStrat p c E rho) :
    (∃ y, confirmedReader p c E rho y (SA.gateTime p.toParams pt.s) ∧
      Block.Preceq pt.P (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams pt.s)) y)) ∧
    (∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) pt.s →
      confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Compatible (V2.D.outputAt E rho g x u) pt.P) ∧
    (∀ u x g, SA.gateTime p.toParams pt.s ≤ u → u ≤ rho.horizon →
      confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Preceq pt.P (V2.D.outputAt E rho g x u)) := by
  have hInputs := inclusion_receiver_inputs_of_clean hset
  have hWitness := clean_inclusion_gate_witness E rho ΔF hset hInputs hHistory hstore hframe
    hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hstrat
  have hInclusion := clean_inclusion_body E rho ΔF hset hInputs hHistory hstore hframe
    hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hOrigins hstrat
  refine ⟨hWitness, ?_, ?_⟩
  · intro u x g hu hup hx hg
    exact clean_growth_compatible_of_outputs E rho hset hOutputs hhor hWitness hu hup hx hg
  · intro u x g hgu hhoru hx hg
    exact hInclusion g hg u x ⟨hgu, hhoru⟩ hx

end AvailableChain.FGSA.Run
end
