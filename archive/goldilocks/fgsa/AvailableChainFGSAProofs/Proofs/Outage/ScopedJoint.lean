module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedCatchUp
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedArming

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

variable [Fintype V] {fast : Bool} {T b₀ b₁ : Time} {ΔF : Time}
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hClean : OutageCleanCutInputs (p := p) (c := c) E rho b₀)

include hf hsrc htsrc hnamed hClean in
/-- Assemble the scoped continuation outputs for every actual initial read.
Each continuation output uses its public repair qualification. -/
theorem outage_continuation_scoped_body
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (origin : RQCOrigin p c E rho) :
    OutageContinuationConcl p c E rho fast T b₀ b₁ := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  intro x B hReader hread
  by_cases he : B = .genesis
  · subst B
    refine ⟨?_, ?_, ?_⟩
    · intro y t _ _ _ _
      exact ⟨block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _),
        block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _),
        block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _),
        fun _ => ⟨block_genesis_preceq _, block_genesis_preceq _, block_genesis_preceq _⟩⟩
    · intro y t o H _ _ _ _ _
      exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)
    · intro y t _ _ _
      exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)
  have hStable : Block.Preceq B
      (V2.D.outputAt E rho (fgsaInterface p c).stable x T) := by
    rwa [arming_stable_read hs]
  obtain ⟨D, Dh, hc⟩ := outage_scoped_arming (outage_continuation_arming_regime h)
    hf hsrc htsrc hClean hStable he
  obtain ⟨β, hβ⟩ := outage_protected_initial_lift h.pre.base.valid hc
  have hprov := outage_joined_provenance h.pre.base.valid h.pre.base.delta
  have hRest := outage_continuation_public_heads_and_finality h hf origin htsrc hnamed
    hsrc hClean.state hprov he hc hβ
  exact ⟨outage_continuation_public_reads h hf origin htsrc hnamed hsrc hClean.state
    hprov he hc hβ hClean.history hClean.output, hRest⟩

end AvailableChain.FGSA.Run
end
