module
public import AvailableChainFGSAProofs.Proofs.Finality.Kernel
public import AvailableChainFGSAProofs.Proofs.Finality.ReceiptSuppliers
public import AvailableChainFGSAClaims.Statements.Packages.Healing

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Paper 00:1119–1134, 22:1171–1305; plan §4: build the W kernel premise.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL same-witness join.
One witness supplies the input, start and core services. -/
theorem finality_kernel_prem_W_of_joined
    (G ΔF : Time) (pt : PtR)
    (h : KernelJoinedPrem p c G ΔF E rho pt) :
    ∃ w : HealingWitness, KernelPrem_W p c G ΔF E rho ⟨w, pt.r⟩ := by
  obtain ⟨w, input, start⟩ := h.start
  exact ⟨w, {
    set := h.set
    bound := h.bound
    window := h.window
    start := start
    hhor := h.hhor
    input := input
    services := fgsa_coreServices E rho h.set.base w (finality_vote_receipts h.set) }⟩

/-- Paper 00:1119–1134, 22:1171–1305; plan §4: join the W kernel.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention and receipt.
One witness supplies the input, start and services; the round is unchanged. -/
theorem finality_kernel_joined_W_of
    (hServices : FinalityActionReceipts p c E rho)
    (G ΔF : Time) (hδ : p.δt = 2 * p.R) (pt : PtR)
    (h : KernelJoinedPrem p c G ΔF E rho pt)
    (hsel : TRowsSelect p c E rho)
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    KernelConclusion_W p c E rho ΔF pt.r := by
  obtain ⟨w, hK⟩ := finality_kernel_prem_W_of_joined p c E rho G ΔF pt h
  exact finality_kernel_W_of p c E rho hServices G ΔF hδ ⟨w, pt.r⟩ hK
    hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore

end AvailableChain.FGSA.Run
end
