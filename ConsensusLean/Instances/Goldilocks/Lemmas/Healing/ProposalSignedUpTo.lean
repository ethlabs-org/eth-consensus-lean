module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo

public section

/-! # Goldilocks Healing: justification and crossing from signed attestations through a horizon

`justify_of_signed_rows'` and `cross_of_signed_rows`
take the whole-run `HSShared`; here the delivery premise comes from `HSSharedUpTo … b` by
`rows_delivered_upTo`, so the proposal cut needs `t_{kX} ≤ b`. No other fact after `b` is used:
the parent is held at the proposal cut, and every attestation is signed by `v ≤ t_{kX} - Δ_F`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The justification from signed attestations through the horizon `b`**
(`justify_of_signed_rows'` from `HSSharedUpTo … b`, for a proposal cut with `t_{kX} ≤ b`). -/
theorem justify_of_signed_rows'_upTo (hrun : GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hpar : X.parent = some Pr.root)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧
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
  obtain ⟨Pr', hpar', hPr'⟩ := proposal_parent_held hrun hs.noColl hp hX
  have hr : Pr'.root = Pr.root := Option.some.inj (hpar'.symm.trans hpar)
  have hnr : ∀ r ≤ kX, tr.RestartAt p r → tr.time r ≤ gbar g :=
    fun r hr hrs => hs.noRestart p hp r hrs ((hrun.time_mono hr).trans hkb)
  have := justify_of_rows' hrun hs.noColl hp hX hpar' hPr' S hSH hS
    fun y hy => by
      obtain ⟨k, att, hsg, hk, hah, haT, hto, hfin⟩ := hsig y hy
      obtain ⟨k', hk', hproc, _⟩ :=
        rows_delivered_upTo hrun hs.sync hv hp hnr hX hvx hkb (hSH y hy) hsg hk
      exact ⟨k, att, hsg, by rw [hr]; exact hah, by rw [hr]; exact haT, hto,
        by rw [hr]; exact hfin, k', hk', hproc⟩
  rw [hr] at this
  exact this

/-- **The crossing from signed attestations through the horizon `b`** (`cross_of_signed_rows` from
`HSSharedUpTo … b`, for a proposal cut with `t_{kX} ≤ b`). -/
theorem cross_of_signed_rows_upTo (hrun : GoldilocksRun proposer dg H tr) {g ΔF v b : Time}
    (hs : HSSharedUpTo tr H dg g ΔF b) (hv : gbar g ≤ v)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hpar : X.parent = some Pr.root)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧
      att.h = ((tr.state p kX).fg.σ Pr.root).h ∧ att.T = ((tr.state p kX).fg.σ Pr.root).Th)
    (hage : ((tr.state p kX).fg.σ Pr.root).ThSlot + sp.toParams.fg.δt ≤ X.slot) :
    ((tr.post kX).fg.σ X.root).h = ((tr.state p kX).fg.σ Pr.root).h + 1 ∧
      ((tr.post kX).fg.σ X.root).Th = X.root ∧
      (((tr.post kX).fg.σ X.root).previousHeightJustified ↔
        ((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h) ∧
      (((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h →
        ((tr.state p kX).fg.σ Pr.root).previousHeightJustified →
        ((tr.post kX).fg.σ X.root).hF = ((tr.state p kX).fg.σ Pr.root).hj) := by
  obtain ⟨Pr', hpar', hPr'⟩ := proposal_parent_held hrun hs.noColl hp hX
  have hr : Pr'.root = Pr.root := Option.some.inj (hpar'.symm.trans hpar)
  have hnr : ∀ r ≤ kX, tr.RestartAt p r → tr.time r ≤ gbar g :=
    fun r hr hrs => hs.noRestart p hp r hrs ((hrun.time_mono hr).trans hkb)
  have := cross_of_rows hrun hs.noColl hp hX hpar' hPr' S hSH hS
    (fun y hy => by
      obtain ⟨k, att, hsg, hk, hah, haT⟩ := hsig y hy
      obtain ⟨k', hk', hproc, _⟩ :=
        rows_delivered_upTo hrun hs.sync hv hp hnr hX hvx hkb (hSH y hy) hsg hk
      exact ⟨k, att, hsg, by rw [hr]; exact hah, by rw [hr]; exact haT,
        k', hk', hproc⟩)
    (by rw [hr]; exact hage)
  rw [hr] at this
  exact this

end Consensus.Goldilocks.Healing

end
