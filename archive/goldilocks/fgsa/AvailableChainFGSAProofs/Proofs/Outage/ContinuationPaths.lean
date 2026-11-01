module
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationFrame

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; a received compatible HEAD path
is active even when its target is a strict ancestor of the receiver's F.
ANCHOR-DL: readiness, history, handlers and survival use the same anchor. -/
theorem outageV_active_path_of_coverage (hE : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (K : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (anchor : Obj p → Time → Time)
    (hx : x ∈ rho.honest)
    (hcov : ReceiptCoverageAnchorPremises E rho dl cut D first x K required paths anchor)
    (hpath : paths K D)
    (hKF : Block.Compatible K (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F))
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ X, Block.Preceq X K → X ∈ (actView (V2.D.Run.stateBeforeTime E rho D x).st).blocks := by
  let st := (V2.D.Run.stateBeforeTime E rho D x).st
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  by_cases hbelow : Block.Preceq K (eraseFG st.fg.F)
  · intro X hX
    exact actView_ancestor_closed p st hb ((actView_genesis_F p st hb).2)
      (block_preceq_trans hX hbelow)
  · have hFK : Block.Preceq (eraseFG st.fg.F) K := by
      rcases Bool.or_eq_true_iff.mp hKF with h | h
      · exact (hbelow h).elim
      · exact h
    exact fgsa_active_path_of_coverage_anchor E rho hE hDelta dl cut D first x K
      required paths anchor hx hcov hpath hFK hroots

/-- OUTPUT-DIRECT §6. Exact carrier receipt uses ANCHOR-DL at the
receiver's service anchor. The finality alternative and height witness are
unchanged. Assembly supplies local service from the joint invariant. -/
theorem outageV_exact_carrier_receipt (hE : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ) (hroots : NamedReceiptRootCollisionFree p c E rho)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (anchor : Obj p → Time → Time) {B P : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hBP : FGBlock.Preceq B P)
    (hBJ : FGBlock.Preceq B (heightView p P).J)
    (hcov : ReceiptCoverageAnchorPremises E rho dl cut D first x (eraseFG P)
      required paths anchor) (hpath : paths (eraseFG P) D)
    (hF : Block.Compatible (eraseFG B)
      (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F)) :
    let dst := (V2.D.Run.stateBeforeTime E rho D x).st
    Block.Preceq (eraseFG B) (eraseFG dst.fg.F) ∨
      P ∈ dst.fg.TF ∧ (heightView p P).h_j ≤ dst.fg.h_j := by
  intro dst
  by_cases hBF : Block.Preceq (eraseFG B) (eraseFG dst.fg.F)
  · exact Or.inl hBF
  have hFB : Block.Preceq (eraseFG dst.fg.F) (eraseFG B) := by
    rcases Bool.or_eq_true_iff.mp hF with h | h
    · exact (hBF h).elim
    · exact h
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  have hblocks := fgsa_active_path_of_coverage_anchor E rho hE hDelta dl cut D first x
    (eraseFG P) required paths anchor hx hcov hpath
    (block_preceq_trans hFB (eraseFG_preceq hBP)) hroots
  have hmem : P ∈ dst.fg.TF := by
    have hP := (actView_blocks dst (eraseFG P)).mp (hblocks _ (block_preceq_refl _))
    obtain ⟨Y, hY, heY⟩ := (hb.baseTree _).mp hP.1
    exact eraseFG_injective heY ▸ hY
  exact Or.inr ⟨hmem, outageV_received_height p dst
    (storeBundle_stateBeforeTime E rho D x).cstore hmem
    (eraseFG_preceq_iff.mp (block_preceq_trans hFB (eraseFG_preceq hBJ)))⟩

end AvailableChain.FGSA.Run
end
