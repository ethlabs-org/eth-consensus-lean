module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetHigh
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRaw

public section

/-! Blueprint 21 H.14:2815–2884, H.16:2924–2945, H.22:3259–3263,
3289–3300; plan J3 D3–D5; B1/B13/B17/B18.
DC: SAME source, parent and HEAD/output prefix transfer.
The all-cut carrier is an input; this file does not prove its induction. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

section Sources
variable [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (cap : RCap p c E rho)
    (source : TSrc p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec cap source rowCovered h0r

/-- Blueprint 21 H.14:2826–2845; plan J3 D3–D4 source route;
B1/B13/B17/B18. DC: SAME source below its actual gate result.
Named producers: sourceDiscipline_tSrc, fgsa_rCap_channel and
rowPermission_covered. No emitted row of this action is required. -/
theorem postReset_source_gate_result {y : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho y r = some (some K)) (hhK : high p w K) :
    ∃ C, gateResult p c E rho y (r * p.R) = some (some C) ∧
      Block.Preceq (eraseFG K) C ∧ w.sStar ≤ r * p.R := by
  have he : actionSource p c E rho y r = some (some (eraseFG K)) := by
    change (actionSourceFG p c E rho y r).map (Option.map eraseFG) = _
    rw [hsrc]
    rfl
  obtain ⟨X, C, -, hK, hC, hbelow, -⟩ := source y r (eraseFG K) hy he
  exact ⟨C, hC, hbelow _ hK,
    postReset_selected_label p c E rho rowCovered hrec cap h0r hy hsrc hhK⟩

/-- Blueprint 21 H.14 S2:2823, H.16:2924–2945, H2:3259–3263;
plan J3 D3; B1/B13/B17/B18. DC: SAME carrier-parent transfer.
Only inv.raw_transfer is used, through J5's all-cut projection.
Its parent reader cut is max (k + 1) (timeIdx rho (proposalTime v)). -/
theorem postReset_tCarrier_reset (inv : ∀ i, PostResetInv p c E rho w i) :
    TCarrier p c E rho w := by
  intro y r K v Q hy hsrc hhK hQ hv
  obtain ⟨C, hC, hKC, hj⟩ :=
    postReset_source_gate_result p c E rho hrec cap source rowCovered h0r hy hsrc hhK
  have raw := postReset_h5RawTransfer_body p c E rho h0r (fun i => (inv i).raw_transfer)
  exact Gen.Pure.block_preceq_trans hKC ((raw y (r * p.R) C hy hj hC).2.2.1 v Q hv hQ)

/-- Blueprint 21 H.14 S1/S3:2823, H.16:2924–2945, H2.A:3289–3295;
plan J3 D4; B1/B13/B17/B18. DC: SAME HEAD and output transfer.
Only inv.raw_transfer is used. J5 chooses max (k + 1) (timeIdx rho
(voteTime s)) for HEADs and max (k + 1) (a + 1) for output index a.
The action/gate deadline and frozen horizon guard are unchanged. -/
theorem postReset_h2A_reset (inv : ∀ i, PostResetInv p c E rho w i) :
    H2A p c E rho w := by
  intro y r K hy hsrc hhK
  obtain ⟨C, hC, hKC, hj⟩ :=
    postReset_source_gate_result p c E rho hrec cap source rowCovered h0r hy hsrc hhK
  have raw := postReset_h5RawTransfer_body p c E rho h0r (fun i => (inv i).raw_transfer)
  have h := raw y (r * p.R) C hy hj hC
  constructor
  · intro x s H hx hs hH
    exact Gen.Pure.block_preceq_trans hKC (h.2.1 x s H hx hs hH)
  · intro a x hx hhor ha
    exact Gen.Pure.block_preceq_trans hKC (h.2.2.2 a x hx hhor ha)

end Sources
end AvailableChain.FGSA.Run
end
