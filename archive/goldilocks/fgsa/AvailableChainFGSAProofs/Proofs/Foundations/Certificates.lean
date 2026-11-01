module
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainFGSAClaims.Statements.ChannelProps

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- ROOT-DIGEST W2b. Stored-chain geometry from KitFG; these facts hold for every FG block. -/
theorem fgsa_rGeo : RGeo p c E rho := by
  simp only [RGeo_def, heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
  intro i x W _ _
  refine ⟨rfl, fun _ _ h _ => KitFG.h_mono p.E p.cfg h, ?_,
    fun B _ => ⟨KitFG.entry_preceq p.E p.cfg B, KitFG.entry_same_height p.E p.cfg B⟩,
    fun _ _ h _ hh => KitFG.entry_eq_on_plateau p.E p.cfg h hh⟩
  intro B _
  cases B with
  | genesis => exact Nat.le_succ _
  | node P s root r rows =>
    change (derive p.E p.cfg (.node P s root r rows)).h ≤ (derive p.E p.cfg P).h + 1
    rcases KitFG.derive_node_height_cases p.E p.cfg P s root r rows with h | h <;> rw [h]
    · exact Nat.le_succ _

/-- L49 certificate clauses, using the designated KitFG producers directly. -/
theorem fgsa_rCert : RCert p c E rho := by
  simp only [RCert_def, heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
  intro i x W _ _
  refine ⟨KitFG.height_crossing p.E p.cfg W, ?_, ?_, ?_⟩
  · simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def] using
    (fgCertificateLaws p).height.justification_certificate W
  · exact
    KitFG.finality_certificate_of_certificate
      p.E (heightView p) (finalityView p) (fgCertificateLaws p) W
  · simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def] using
    KitFG.provenance_finality_of_certificate
      p.E (heightView p) (finalityView p) (fgCertificateLaws p) W

end AvailableChain.FGSA.Run
end
