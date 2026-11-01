module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalJustifies
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMature

public section

/-! # Goldilocks Healing: Lemma 3′ from signed rows

`justify_of_rows` (`ProposalJustifies`) with its two run-level premises discharged:

* the parent of an honest proposal is held by the proposer at the proposal cut
  (`proposal_parent_held`: `onBlock` accepts only a block whose parent is stored);
* the delivery premise `∃ k' < kX, ProcessAttAt p k' att` follows from a signing time `≤ v`
  with `ḡ ≤ v` and `v + Δ_F ≤ t_{kX}`, by `rows_delivered` (`ConsumeMature`; `GST(g)`'s
  attestation delivery `SyncOn.attestation` inside `HSShared.healthy`, and no honest restart
  after `ḡ`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The parent of an honest proposal is held at its cut**: the proposer's FG store before the
proposal cut `kX` holds a block `Pr` with `X.parent = some Pr.root` (`onBlock` accepts `X`). -/
theorem proposal_parent_held (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} (hp : p ∈ H) {kX : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : tr.ProposesAt p kX X) :
    ∃ Pr : SA.Blk sp.n (List (FG.Att sp.n)), X.parent = some Pr.root ∧
      Pr ∈ (tr.state p kX).fg.tree := by
  obtain ⟨hacc, -, -⟩ := accept_of_proposesAt hrun hnc hp hX
  obtain ⟨pr, _, _, hsome, hpar, _⟩ :=
    Goldilocks.Store.onBlock_fields (hrun.cutLaw p hp kX _ hacc).2.1
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 hsome
  have hR := Compose.fg_reachable hrun.toLocalRun hp kX
  have hroot : Y.root = pr := hR.blocks_root hY
  refine ⟨Y, by rw [hpar, hroot], ?_⟩
  change (tr.state p kX).fg.blocks Y.root = some Y
  rw [hroot]
  exact hY

/-- **Lemma 3′ from signed rows** (`justify_of_rows` with delivery from `GST(g)`): an honest
proposal `X` at the cut `kX` with `t_{kX} ≥ v + Δ_F`, `v ≥ ḡ`, on the parent `Pr`, with
`(h_j, J)` pending at `σ = σ[Pr]` when `σ` is bound, and a set `S ⊆ H` of weight `≥ q` of
honest validators, each of which signed by `v` a target row for `(σ.h, σ.T_h)` (with the
finality pair `(σ.h_j, σ.J)` at a bound height): `X`'s state justifies `(σ.h, σ.T_h)`, and at a
bound height it finalizes `σ.h_j`. -/
theorem justify_of_signed_rows (hrun : GoldilocksRun proposer dg H tr) {g ΔF v : Time}
    (hs : HSShared tr H dg g ΔF) (hv : gbar g ≤ v)
    {p : Fin sp.n} (hp : p ∈ H) {kX : Nat} {X Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p kX X) (hvx : v + ΔF ≤ tr.time kX) (hpar : X.parent = some Pr.root)
    (hpend : ((tr.state p kX).fg.σ Pr.root).bound →
      (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J) ∈
        ((tr.state p kX).fg.σ Pr.root).pending)
    (S : Finset (Fin sp.n)) (hSH : ∀ v ∈ S, v ∈ H) (hS : sp.toParams.fg.q ≤ S.card)
    (hsig : ∀ y ∈ S, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧
      att.h = ((tr.state p kX).fg.σ Pr.root).h ∧
      att.T = ((tr.state p kX).fg.σ Pr.root).Th ∧ att.timeout = false ∧
      (((tr.state p kX).fg.σ Pr.root).bound →
        att.fin = some (((tr.state p kX).fg.σ Pr.root).hj, ((tr.state p kX).fg.σ Pr.root).J))) :
    ((tr.post kX).fg.σ X.root).hj = ((tr.state p kX).fg.σ Pr.root).h ∧
      ((tr.post kX).fg.σ X.root).J = ((tr.state p kX).fg.σ Pr.root).Th ∧
      (((tr.state p kX).fg.σ Pr.root).bound →
        ((tr.post kX).fg.σ X.root).hF = ((tr.state p kX).fg.σ Pr.root).hj) := by
  obtain ⟨Pr', hpar', hPr'⟩ := proposal_parent_held hrun hs.noColl hp hX
  have hr : Pr'.root = Pr.root := Option.some.inj (hpar'.symm.trans hpar)
  have := justify_of_rows hrun hs.noColl hp hX hpar' hPr' (by rw [hr]; exact hpend) S hSH hS
    fun y hy => by
      obtain ⟨k, att, hsg, hk, hah, haT, hto, hfin⟩ := hsig y hy
      exact ⟨k, att, hsg, by rw [hr]; exact hah, by rw [hr]; exact haT, hto,
        by rw [hr]; exact hfin, rows_delivered hs hv hp hX hvx (hSH y hy) hsg hk⟩
  rw [hr] at this
  exact this

end Consensus.Goldilocks.Healing
