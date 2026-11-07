module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending growing Healing interface of the route-A window

The growing forms of the Healing lemmas that the seed height and the anchor steps of the route-A
window consume, under their agreed names (static name + `_at`). Each node is honest at its own
cut; a reader of a held state is honest at an observation time after the state's cuts:

* `justify_of_signed_rows'_upTo_at`, `cross_of_signed_rows_upTo_at`
  (`Healing.justify_of_signed_rows'_upTo`, `Healing.cross_of_signed_rows_upTo`): each signer is
  honest at its signing;
* `ResetPremisesUpTo.row_signers_of_reports_at` (`ResetPremisesUpTo.row_signers_of_reports`):
  the reporters are the nodes honest at the report bound `d`, and so are the signers;
* `ResetPremisesUpTo.sign_of_report_at`, `ResetPremisesUpTo.row_target_of_sign_at`;
* `ResetPremisesUpTo.clean_source_proposal_parent_before_at`,
  `ResetPremisesUpTo.clean_optimistic_proposal_parent_at`.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-- **An honest proposal justifies the height of its parent's state** from a quorum of target
attestations signed by `v`, each by a signer honest at its signing, delivered by the HS premises
through the horizon. -/
theorem justify_of_signed_rows'_upTo_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hpar : X.parent = some Pr.root)
    (S : Finset (Fin sp.n)) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ v ∧
      att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
      att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ att.timeout = false ∧
      (((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
        (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J) ∈
          ((tr.state p kX).fg.σ Pr.root).pending →
        att.fin = some (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J))) :
    ((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h ∧
      ((tr.post kX).fg.σ X.root).J = ((tr.state p kX).fg.σ Pr.root).Th ∧
      (((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
        ((tr.post kX).fg.σ X.root).hF = ((tr.state p kX).fg.σ Pr.root).hj) := by
  sorry

/-- **An honest proposal crosses by timeout** from a quorum of target attestations for its
parent's entry signed by `v`, each by a signer honest at its signing, once the entry is `δt`
slots old. -/
theorem cross_of_signed_rows_upTo_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hpar : X.parent = some Pr.root)
    (S : Finset (Fin sp.n)) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ v ∧
      att.h = ((tr.state p kX).fg.σ Pr.root).h ∧ att.T = ((tr.state p kX).fg.σ Pr.root).Th)
    (hage : ((tr.state p kX).fg.σ Pr.root).ThSlot + sp.toParams.fg.δt ≤ X.slot) :
    ((tr.post kX).fg.σ X.root).h = ((tr.state p kX).fg.σ Pr.root).h + 1 ∧
      ((tr.post kX).fg.σ X.root).Th = X.root ∧
      (((tr.post kX).fg.σ X.root).previousHeightJustified ↔
        ((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h) ∧
      (((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h →
        ((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
        ((tr.post kX).fg.σ X.root).hF = ((tr.state p kX).fg.σ Pr.root).hj) := by
  sorry

namespace ResetPremisesUpTo

variable {b : Time}

/-- Same-height reports, by `d`, from every node honest at `d` yield a quorum of nodes honest at
`d` with exact entry signatures by `d`. Historical reports count without any freshness
assumption. -/
theorem row_signers_of_reports_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    {d : Time} (hd : 0 ≤ d) (hdb : d ≤ b)
    (hreports : ∀ z, z ∈ H d → ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ d ∧
      Anc (tr.HonestBlocksAt H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H d ∧ ∃ att j, tr.SignAt z j att ∧ att.val = z ∧
        att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧ tr.time j ≤ d ∧
        (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  sorry

/-- A bounded same-height report of a node honest at the report supplies a signature of it by
the report's time, including the case where previously signed content suppresses the call. -/
theorem sign_of_report_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {r : Nat} (hz : z ∈ H (tr.time r))
    {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hTC : Anc (tr.HonestBlocksAt H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocksAt H) T B) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.h = σT.h := by
  sorry

/-- Finite normalization of a high signature's target and timeout fields, for a signer honest
at its signing. -/
theorem row_target_of_sign_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {j : Nat} (hz : z ∈ H (tr.time j)) {att : FG.Att sp.n}
    (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocksAt H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false := by
  sorry

/-- A clean fast or slow lock source, written at a cut of a node honest at it, extends the duty
head of every later honest proposal call two slots on, within the finite horizon. -/
theorem clean_source_proposal_parent_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x p : Fin sp.n} {r s i u : Nat}
    (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s + 2 ≤ u) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) : Anc (tr.HonestBlocksAt H) B d.head := by
  sorry

/-- A clean optimistic source, written at a cut of a node honest at it, extends the duty head of
the next honest proposal call, within the finite horizon. -/
theorem clean_optimistic_proposal_parent_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x p : Fin sp.n} {r s i : Nat}
    (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocksAt H) B d.head := by
  sorry

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end
