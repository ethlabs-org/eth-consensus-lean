module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedArming

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

variable [Fintype V] {fast : Bool} {pt : PtOut} {ΔF : Time}
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hClean : OutageCleanCutInputs (p := p) (c := c) E rho pt.b₀)

include hf hsrc htsrc hnamed hClean

/-- The protected initial read selects arming and its FG lift under OutagePrem.
This uses the outage premise alone, with no continuation window or synchrony. -/
theorem outage_protected_read (h : OutagePrem p c fast E rho pt ΔF)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T))
    (hne : B ≠ .genesis) :
    (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ y t, pt.b₀ ≤ t → t < pt.b₁ →
        outageConfirmedReader p c E rho fast pt.b₀ pt.b₁ y t →
        Block.Preceq B (V2.D.outputAt E rho g y t)) ∧
    DutiesExtendScoped p c E rho fast B pt.b₀ pt.b₁ ∧
    (∀ t y, 0 ≤ t → t < pt.b₁ → y ∈ rho.honest →
      Block.Compatible B (V2.D.outputAt E rho finalizedOut y t)) ∧
    (∀ t y, SA.gateTime p.toParams (coverLabel p pt.b₀) ≤ t → t < pt.b₁ →
      y ∈ coveredNodes p E rho fast pt.b₀ →
      let st := storeAt p c E rho (timeIdx rho t) y
      Block.Preceq B (eraseFG st.fg.F) ∨
        ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
          SA.gateTime p.toParams (coverLabel p pt.b₀) + L p ≤ dl ∧
          ((∃ X ∈ fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (controls p st).Z))) := by
  obtain ⟨D, Dh, hc⟩ := outage_scoped_arming h.set hf hsrc htsrc hClean hread hne
  obtain ⟨β, hβ⟩ := outage_protected_initial_lift h.set.pre.base.valid hc
  exact outage_protected_scoped h hf htsrc hnamed hsrc hClean.state
    (outage_joined_provenance h.set.pre.base.valid h.set.pre.base.delta) hne hc hβ
    hClean.history hClean.output

/-- Assemble the unchanged public outage type from the scoped protected producer. -/
theorem outage_compat_body (h : OutagePrem p c fast E rho pt ΔF) :
    ((∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho g x pt.T) →
      ∀ t y, pt.b₀ ≤ t ∧ t < pt.b₁ →
      outageConfirmedReader p c E rho fast pt.b₀ pt.b₁ y t →
      Block.Preceq B (V2.D.outputAt E rho g y t)) ∧
    (∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
      DutiesExtendScoped p c E rho fast B pt.b₀ pt.b₁ ∧
      ∀ t y, 0 ≤ t → t < pt.b₁ → y ∈ rho.honest →
      Block.Compatible B (V2.D.outputAt E rho finalizedOut y t))) ∧
    (∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
      B ≠ .genesis →
      ∀ t y, SA.gateTime p.toParams (coverLabel p pt.b₀) ≤ t → t < pt.b₁ →
      y ∈ coveredNodes p E rho fast pt.b₀ →
      let st := storeAt p c E rho (timeIdx rho t) y
      Block.Preceq B (eraseFG st.fg.F) ∨
        ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
          SA.gateTime p.toParams (coverLabel p pt.b₀) + L p ≤ dl ∧
          ((∃ X ∈ fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (controls p st).Z))) := by
  have hs := h.set.pre.base.valid.toScheduleWellFormed
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g hg x B _ hread t y ht hReader
    by_cases he : B = .genesis
    · subst B; exact block_genesis_preceq _
    have hStable : Block.Preceq B
        (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) := by
      rw [fgsa_outputAt_eq_S_at E rho hs g hg] at hread
      rwa [arming_stable_read hs]
    exact (outage_protected_read hf hsrc htsrc hnamed hClean h hStable he).1
      g hg y t ht.1 ht.2 hReader
  · intro x B _ hread
    by_cases he : B = .genesis
    · subst B
      refine ⟨?_, ?_⟩
      · intro y t o _ _ _ _
        exact ⟨fun H _ => block_genesis_preceq H,
          fun N _ => block_genesis_preceq N.parent.erase⟩
      · intro t y _ _ _
        exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)
    have hp := outage_protected_read hf hsrc htsrc hnamed hClean h hread he
    exact ⟨hp.2.1, hp.2.2.1⟩
  · intro x B _ hread hne
    exact (outage_protected_read hf hsrc htsrc hnamed hClean h hread hne).2.2.2

/-- The fast public claim is the P1 projection of the same scoped producer. -/
theorem fast_p1_body (h : OutagePrem p c true E rho pt ΔF) :
    (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho g x pt.T) →
      ∀ t y, pt.b₀ ≤ t ∧ t < pt.b₁ →
      outageConfirmedReader p c E rho true pt.b₀ pt.b₁ y t →
      Block.Preceq B (V2.D.outputAt E rho g y t)) ∧
    (∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
      DutiesExtendScoped p c E rho true B pt.b₀ pt.b₁ ∧
      ∀ t y, 0 ≤ t → t < pt.b₁ → y ∈ rho.honest →
      Block.Compatible B (V2.D.outputAt E rho finalizedOut y t)) :=
  (outage_compat_body hf hsrc htsrc hnamed hClean h).1

/-- The slow public claim retains the scoped pending lease clause. -/
theorem slow_p1_body (h : OutagePrem p c false E rho pt ΔF) :
    ((∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho g x pt.T) →
      ∀ t y, pt.b₀ ≤ t ∧ t < pt.b₁ →
      outageConfirmedReader p c E rho false pt.b₀ pt.b₁ y t →
      Block.Preceq B (V2.D.outputAt E rho g y t)) ∧
    (∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
      DutiesExtendScoped p c E rho false B pt.b₀ pt.b₁ ∧
      ∀ t y, 0 ≤ t → t < pt.b₁ → y ∈ rho.honest →
      Block.Compatible B (V2.D.outputAt E rho finalizedOut y t))) ∧
    (∀ x B, confirmedReader p c E rho x pt.T →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
      B ≠ .genesis →
      ∀ t y, SA.gateTime p.toParams (coverLabel p pt.b₀) ≤ t → t < pt.b₁ →
      y ∈ coveredNodes p E rho false pt.b₀ →
      let st := storeAt p c E rho (timeIdx rho t) y
      Block.Preceq B (eraseFG st.fg.F) ∨
        ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
          SA.gateTime p.toParams (coverLabel p pt.b₀) + L p ≤ dl ∧
          ((∃ X ∈ fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (controls p st).Z))) :=
  outage_compat_body hf hsrc htsrc hnamed hClean h

end AvailableChain.FGSA.Run
end
