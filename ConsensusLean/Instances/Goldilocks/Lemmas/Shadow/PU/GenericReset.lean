module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # Shared healing leaves instantiated for shadow execution

The reset, historical-row crossing and row-or-high proofs are shared with the stock run through
`LocalRunCore`. Only the shadow Goldilocks execution supplies the run-core adapter here.
-/

namespace Consensus.Goldilocks.Generic.Shadow

open AC (ACParams ReplayOrder Payload gbar)
open Healing.Growing (NoRestartAfter)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini}

/-- A high signing yields the first signing at the reset height in a shadow run. -/
theorem reset_of_height_advance_at_from
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g : Time} {y : Fin sp.n} {k : Nat} {att : FG.Att sp.n}
    (hq : (H (max (Healing.cutZ sp.toParams g) (tr.time k)))ᶜ.ncard < sp.toParams.fg.q)
    (hyz : y ∈ H (max (Healing.cutZ sp.toParams g) (tr.time k)))
    (hs : tr.SignAt y k att) (hh : Healing.Growing.HZ tr H g + 1 ≤ att.h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time k :=
  Generic.reset_of_height_advance_at_core hrun.toLocalRunCore hq hyz hs hh

/-- A high source yields a reset even when the shadow client suppresses its signature. -/
theorem reset_of_high_source_at_from
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g : Time} {y : Fin sp.n} {k : Nat} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    {s : Option (FG.Att sp.n)}
    (hyz : y ∈ H (max (Healing.cutZ sp.toParams g) (tr.time k)))
    (hq : (H (max (Healing.cutZ sp.toParams g) (tr.time k)))ᶜ.ncard < sp.toParams.fg.q)
    (hc : tr.CallAt y k (.fg (.attest C s)))
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time k :=
  Generic.reset_of_high_source_at_core hrun.toLocalRunCore hyz hq hc hh

/-- A high report yields a reset within the trace-level vote-latency deadline. -/
theorem reset_of_high_report_within_from
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g D : Time} {y : Fin sp.n} {i : Nat} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hlat : VoteLatencyAt tr H D)
    (hyz : y ∈ H (max (Healing.cutZ sp.toParams g) (tr.time i + D)))
    (hq : (H (max (Healing.cutZ sp.toParams g) (tr.time i + D)))ᶜ.ncard < sp.toParams.fg.q)
    (hR : ReportAt tr y i R)
    (hh : Healing.Growing.HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ a, Healing.Growing.IsReset tr H g a ∧ a ≤ tr.time i + D :=
  Generic.reset_of_high_report_within_core hrun.toLocalRunCore hlat hyz hq hR hh

/-- Delivered historical rows cross one height in the shadow Goldilocks run. -/
theorem round_cross_at_from
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hq : ∀ y, ({ goldilocksNode sp ro with initial := ini y } :
      NodeAC sp.toParams).Requirements)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b v hold : Time}
    (hrows : ∀ x i att, x ∈ H (tr.time i) → tr.SignAt x i att →
      (∀ k ≤ i, tr.SignAt x k att → tr.time k = tr.time i → hold ≠ 0 →
        x ∈ H (max (tr.time i) g + hold)) →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.time j ≤ b →
        tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
        ∃ k ≤ j, tr.ProcessAttAt y k att ∧
          tr.time k < tr.deadline y k (max (tr.time i) g) ΔF)
    (hhold : hold ≤ ΔF) (hnr : NoRestartAfter tr H (gbar g))
    {B D X : AC.Blk sp.n (List (FG.Att sp.n))} (hBH : B ∈ tr.HonestBlocksAt H)
    (hBD : Anc (tr.HonestBlocksAt H) B D) (hpar : X.parent = some D.root)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    (hX : tr.ProposesAt p kX X) (hf : 3 * (H (tr.time kX))ᶜ.ncard ≤ sp.n - 1)
    (hv : gbar g ≤ v) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hage : B.slot + sp.toParams.δt ≤ X.slot)
    (hrow : ∀ y ∈ H (tr.time kX),
      (∃ w c, w ∈ H (tr.time c) ∧ B ∈ (tr.state w c).fg.tree ∧
        ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧
          tr.time k ≤ v ∧ att.h = ((tr.state w c).fg.σ B.root).h ∧
          att.T = ((tr.state w c).fg.σ B.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocksAt H) R D ∧ ∃ w c, w ∈ H (tr.time c) ∧
        B ∈ (tr.state w c).fg.tree ∧ R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ B.root).h < ((tr.state w c).fg.σ R.root).h) :
    B ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ B.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h :=
  Generic.round_cross_at_core hrun.toLocalRunCore hq hroot hnc hrows hhold hnr hBH hBD
    hpar hp hX hf hv hvx hkb hage hrow

/-- A shadow attest call supplies a historical row or a higher source. -/
theorem row_or_high_of_attest_at_from
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g T : Time}
    (hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hna : NoAdvance tr H g T)
    {y : Fin sp.n} {k : Nat} {C B : AC.Blk sp.n (List (FG.Att sp.n))}
    {s : Option (FG.Att sp.n)}
    (hyz : y ∈ H (max (Healing.cutZ sp.toParams g) (tr.time k)))
    (hc : tr.CallAt y k (.fg (.attest C s))) (hkT : tr.time k < T)
    (hCm : C ∈ (tr.state y k).fg.tree) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hkind : ((tr.state y k).fg.σ C.root).h = ((tr.state y k).fg.σ B.root).h →
      ((tr.state y k).fg.σ B.root).h = Healing.Growing.HZ tr H g ∨
      (tr.state y k).fg.hj < ((tr.state y k).fg.σ B.root).h ∨
      ((tr.state y k).fg.hj = ((tr.state y k).fg.σ B.root).h ∧
        (tr.state y k).fg.Anc (tr.state y k).fg.J C)) :
    B ∈ (tr.state y k).fg.tree ∧ C ∈ (tr.state y k).fg.tree ∧
      ((∃ j att, y ∈ H (tr.time j) ∧ tr.SignAt y j att ∧ tr.time j ≤ tr.time k ∧
        att.h = ((tr.state y k).fg.σ B.root).h ∧
        att.T = ((tr.state y k).fg.σ B.root).Th) ∨
        ((tr.state y k).fg.σ B.root).h < ((tr.state y k).fg.σ C.root).h) :=
  Generic.row_or_high_of_attest_at_core hrun.toLocalRunCore hnc hf hna hyz hc hkT hCm hBC hkind

end Consensus.Goldilocks.Generic.Shadow

end
