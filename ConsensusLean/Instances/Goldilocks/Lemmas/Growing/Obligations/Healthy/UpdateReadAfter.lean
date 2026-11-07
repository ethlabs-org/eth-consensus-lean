module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ConfirmedPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.AncestorCandidate

public section

/-! # The read after an operational update, under growing faults (open)

`operational_update_read_after_at`, the growing form of
`Obligations.operational_update_read_after`: the fresh fast lock and the effective record of an
actual honest update of the post-drain operational proposal `P` of slot `u` put `P` under the
confirmed read of the updater at the end of the update time `t_u + 6Δ`. The proposer is honest
through `t_u + Δ`, the updater and reader is honest at the read time (so at its update cut, of the
same time), and ancestry is in the blocks held while honest. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- OPEN. **The read after an actual update** of the operational proposal `P` of slot `u`, by a
node honest at the end of the update time, at the first cut after it. -/
theorem operational_update_read_after_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} (hy : y ∈ H (sp.ts u + 6 * sp.Δ))
    {j : Nat} {ell : ACLabel (goldilocksNode sp ro)} (hup : SA.UpdateAt tr.projAC y j u ell)
    (hlock : ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks)
    {J : Nat} (hJ : Regimes.CutAfter tr J (sp.ts u + 6 * sp.Δ)) :
    Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y J (sp.ts u + 6 * sp.Δ)) := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end
