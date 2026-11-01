module
public import AvailableChainPCSAProofs.Proofs.Recovery.RunInputs
public import AvailableChainPCSAProofs.Proofs.Shared.CollectClosed

public section

namespace AvailableChain.PCSA.Run

/-- Lane-neutral receipt facts for long-break recovery. The first label is
`g`, with the intended floor `GST ≤ v_g`; no proposal-time floor is required.
These fields contain no lock coverage, root compatibility, or walk conclusion.
PC receipt concerns held keys at early and vote cutoffs, including assembled and carried PCs. -/
structure RecoveryLockTransport (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) {m : FGMode} (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (g : Slot) : Prop where
  sameLabel : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ X Y,
      gateResultAt p c E rho x r = some (some X) →
      gateResultAt p c E rho y r = some (some Y) → Block.Compatible X Y
  earlyForward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ GridCO.earlyVotes p.toParams.engine (actView src.st) r,
      ∀ i, GridCO.headSeat? o = some i → ∀ H,
        GridCO.resolvedHead? (actView src.st) o = some H →
        ((o ∈ headSupport p dst.st (r + 1) ∧
          GridCO.resolvedHead? dst.st.base o = some H ∧
          GridCO.stampVote dst.st.base o < SA.freezeTime p.toParams r) ∨
          GridCO.equivocates (headVotes p dst.st (r + 1)) i = true) ∧
        H ∈ dst.st.base.blocks ∧
        GridCO.stampBlock dst.st.base H < SA.freezeTime p.toParams r ∧
        (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
          (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1))))
  voterBackward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ headVotes p dst.st (r + 1), ∀ i, GridCO.headSeat? o = some i →
        o ∈ GridCO.lateVotes p.toParams.engine (actView src.st) r ∨
        GridCO.equivocates (GridCO.lateVotes p.toParams.engine (actView src.st) r) i = true
  pcReceipt : ∀ t, (∃ s, t = SA.earlyTime p.toParams s ∨ t = SA.voteTime p.toParams s) →
    E.t_GST ≤ t → t + p.Δ ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ pc,
      pc ∈ (V2.D.Run.stateBeforeTime E rho t x).st.pcs →
      KeyHeld (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st pc.slot pc.target
  honestVoterInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ headSupport p dst.st (r + 1) ∧
      o ∈ headVotes p dst.st (r + 1) ∧
      GridCO.equivocates (headVotes p dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
        (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1))))
  honestProposerInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.proposalTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ proposerSupport dst.st (r + 1) ∧
      o ∈ proposerVotes dst.st (r + 1) ∧
      GridCO.equivocates (proposerVotes dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st (fullTree p dst.st))
  rootResolution : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ a b : Nat, ∀ X Y,
    X ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks →
    Y ∈ (V2.D.Run.stateBefore E rho b y).st.base.blocks →
    X.root = Y.root → X = Y

end AvailableChain.PCSA.Run
end
