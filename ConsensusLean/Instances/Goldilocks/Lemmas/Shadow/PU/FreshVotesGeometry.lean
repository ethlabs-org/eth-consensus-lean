module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesGeometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

/-! # Fresh-vote geometry over the shadow run and `FrameWindow'`

The stock `FreshVotesGeometry` endpoints restated over `Growing.GoldilocksRun'` and the P-U window
`FrameWindow' … M isTop J`: a P-U viable head transfers between readers of the window
(`WindowWitness`), and a frozen competitor reflects into the proposer's full viable tree. -/

public section

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}
variable {hold : Time}

/-- A viable head transfers between warm frames whenever the receiving tree holds it.
(`FrameWindow.viableHead_transfer_at` over the shadow run and `FrameWindow'`). -/
theorem viableHead_transfer_primed_at' {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i c : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hv : Q ∈ (Node.frame' (tr.state z c)).viableHeads)
    (hQ : Q ∈ (Node.frame' (tr.state y i)).tree) :
    Q ∈ (Node.frame' (tr.state y i)).viableHeads := by
  sorry

/-- A frozen competing child reflects into the actual proposer's full viable tree.
(`FrameWindow.frozen_competitor_reflect_at` over the shadow run and `FrameWindow'`). -/
theorem frozen_competitor_reflect_primed_at' {g ΔF b : Time} {s₀ s M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (AC.gbar g))
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hm : AC.gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode' sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (AC.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hpb : sp.ts (s + 1 : Nat) ≤ b)
    {X B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ ellp.frame.tree) (hrootX : ellp.frame.Anc ellp.frame.fcRoot X)
    (hBX : B.parent = some X.root) (hne : B ≠ P)
    (hB : B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  sorry

end Consensus.Goldilocks.Healing.Growing.Shadow

end
