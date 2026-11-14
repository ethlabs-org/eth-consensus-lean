module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalCrosses
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Signed rows at an honest proposal, under growing faults

The justification from signed attestations under growing faults. The proposer is honest at its
proposal cut and read on the prefix through it; each signer is honest at its signing, which is all
the delivery of its row (`ResetService.signedRow`) and its validity need:

* `justify_of_signed_rows'_upTo_at`: a quorum of target rows signed by `v` justifies the height
  of the parent's state at the proposal;
* `cross_of_signed_rows_upTo_at`: the same rows cross the proposal by timeout once the parent's
  entry is `δt` slots old. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A row signed by `v` by a signer honest at its signing is processed by an honest proposer
before a proposal at `t ≥ v + ΔF` within the horizon (no restart of the proposer after `ḡ`). -/
private theorem rows_delivered_upTo_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b) {v : Time}
    (hv : gbar g ≤ v) {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    (hnr : ∀ r ≤ kX, tr.RestartAt p r → tr.time r ≤ gbar g)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X)
    (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n}
    (hsig : tr.SignAt y k att) (hk : tr.time k ≤ v) :
    ∃ k' < kX, tr.ProcessAttAt p k' att ∧ tr.time k' < tr.time kX := by
  have hg : max (tr.time k) g ≤ v := max_le hk ((le_gbar g).trans hv)
  have hdl : ∀ j ≤ kX, tr.deadline p j (max (tr.time k) g) ΔF ≤ v + ΔF := fun j hj => by
    have h := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
      (fun r hr hrs => hnr r (hr.trans hj) (Compose.projAC_restartAt.1 hrs)) (max (tr.time k) g)
    simp only [ACTrace.deadline, RunTrace.deadline, Compose.projAC_lastWake] at h ⊢
    have := max_le hg hv
    linarith
  obtain ⟨acc, hcall⟩ := hX.1.1
  obtain ⟨k', hk', hproc, hlt⟩ := hsvc.signedRow y k att hy hsig p kX hp ⟨_, hcall⟩ hkb
    (by linarith [hdl kX le_rfl])
  have htime : tr.time k' < tr.time kX := hlt.trans_le ((hdl k' hk').trans hvx)
  exact ⟨k', lt_of_not_ge (fun h => (not_lt_of_ge (hrun.time_mono h)) htime), hproc, htime⟩

/-- The proposer's side of an honest proposal on the prefix through its cut: the FG projection
of the prefix is a local run, the store after the cut holds `X` and its parent `Pr` with their
states, and every row the proposer processed before the cut that names `Pr`'s entry is in `X`'s
payload or on `Pr`'s chain. -/
private theorem proposal_rows_placed_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hpar : X.parent = some Pr.root)
    (hPr : Pr ∈ (tr.state p kX).fg.tree) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload (H (tr.time kX))
        ((tr.upTo (tr.time kX)).HonestBlocks (H (tr.time kX))) (tr.upTo (tr.time kX)).projFG ∧
      X ∈ ((tr.upTo (tr.time kX)).projFG.store p (kX + 1)).tree ∧
      Pr ∈ ((tr.upTo (tr.time kX)).projFG.store p (kX + 1)).tree ∧
      (tr.post kX).fg.σ X.root = ((tr.upTo (tr.time kX)).projFG.store p (kX + 1)).σ X.root ∧
      (tr.state p kX).fg.σ Pr.root =
        ((tr.upTo (tr.time kX)).projFG.store p (kX + 1)).σ Pr.root ∧
      ∀ att, (∃ k' < kX, tr.ProcessAttAt p k' att) →
        att.h = ((tr.state p kX).fg.σ Pr.root).h → att.T = ((tr.state p kX).fg.σ Pr.root).Th →
        att ∈ X.fgPayload ∨
          ((tr.upTo (tr.time kX)).projFG.store p (kX + 1)).OnChain Pr att := by
  have hd := hrun.time_nonneg kX
  have hst : (tr.upTo (tr.time kX)).state p kX = tr.state p kX :=
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  obtain ⟨hfg, hXt, hPrt, hσX, hσPr, hplace⟩ := Healing.proposal_rows_placed (hrun.upTo hd)
    (hnc.upTo _) hp hX' hpar (by rw [hst]; exact hPr)
  rw [hst] at hσPr hplace
  refine ⟨hfg, hXt, hPrt, hσX, hσPr, fun att ⟨k', hk', hproc⟩ hah haT => ?_⟩
  exact hplace att ⟨k', hk', (RunTrace.upTo_processAttAt _).mpr
    ⟨hrun.time_mono hk'.le, hproc⟩⟩ hah haT

/-- A row signed by a signer honest at its signing names its signer. -/
private theorem signAt_val_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) : att.val = y :=
  Healing.signAt_val (hrun.upTo (hrun.time_nonneg k)) hy
    ((RunTrace.upTo_signAt _).mpr ⟨le_rfl, hs⟩)

/-- No restart of a node honest at a proposal cut within the horizon after `ḡ`. -/
private theorem no_restart_before {g ΔF b : Time} {hs : HSSharedUpTo tr H dg g ΔF b}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX)) (hkb : tr.time kX ≤ b) :
    ∀ r ≤ kX, tr.RestartAt p r → tr.time r ≤ gbar g := fun r hr hrs =>
  hs.noRestart p r (hrun.antitone (hrun.time_mono hr) hp) hrs ((hrun.time_mono hr).trans hkb)

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
  classical
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  obtain ⟨Pr', hpar', hPr'⟩ := Healing.proposal_parent_held (hrun.upTo (hrun.time_nonneg kX))
    (hs.noColl.upTo _) hp hX'
  rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at hPr'
  have hr : Pr'.root = Pr.root := Option.some.inj (hpar'.symm.trans hpar)
  have hnr := no_restart_before (hs := hs) hrun hp hkb
  obtain ⟨hfg, hXt, hPrt, hσX, hσPr, hplace⟩ :=
    proposal_rows_placed_at hrun hs.noColl hp hX hpar' hPr'
  have := Healing.justify_step' hfg hp hXt hPrt hpar' S hS fun y hy => by
    obtain ⟨k, att, hyk, hsg, hk, hah, haT, hto, hfin⟩ := hsig y hy
    obtain ⟨k', hk', hproc, _⟩ :=
      rows_delivered_upTo_at hrun hs.sync hv hp hnr hX hvx hkb hyk hsg hk
    rw [← hσPr]
    refine ⟨att, signAt_val_at hrun hyk hsg, by rw [hr]; exact hah, by rw [hr]; exact haT, hto,
      by rw [hr]; exact hfin, hplace att ⟨k', hk', hproc⟩ (by rw [hr]; exact hah)
        (by rw [hr]; exact haT)⟩
  rw [← hσX, ← hσPr, hr] at this
  exact this

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
  classical
  have hX' : (tr.upTo (tr.time kX)).ProposesAt p kX X :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hX.1⟩, hX.2.1, hX.2.2⟩
  obtain ⟨Pr', hpar', hPr'⟩ := Healing.proposal_parent_held (hrun.upTo (hrun.time_nonneg kX))
    (hs.noColl.upTo _) hp hX'
  rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at hPr'
  have hr : Pr'.root = Pr.root := Option.some.inj (hpar'.symm.trans hpar)
  have hnr := no_restart_before (hs := hs) hrun hp hkb
  obtain ⟨hfg, hXt, hPrt, hσX, hσPr, hplace⟩ :=
    proposal_rows_placed_at hrun hs.noColl hp hX hpar' hPr'
  have := Healing.cross_step hfg hp hXt hPrt hpar' S hS (fun y hy => by
      obtain ⟨k, att, hyk, hsg, hk, hah, haT⟩ := hsig y hy
      obtain ⟨k', hk', hproc, _⟩ :=
        rows_delivered_upTo_at hrun hs.sync hv hp hnr hX hvx hkb hyk hsg hk
      rw [← hσPr]
      exact ⟨att, signAt_val_at hrun hyk hsg, by rw [hr]; exact hah, by rw [hr]; exact haT,
        hplace att ⟨k', hk', hproc⟩ (by rw [hr]; exact hah) (by rw [hr]; exact haT)⟩)
    (by rw [← hσPr, hr]; exact hage)
  rw [← hσX, ← hσPr, hr] at this
  exact this

end Consensus.Goldilocks.Healing.Growing

end
