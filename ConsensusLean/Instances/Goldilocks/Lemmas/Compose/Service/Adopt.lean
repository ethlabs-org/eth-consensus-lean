module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction

public section

/-! # Goldilocks under `Sleepy`: an honest proposal is adopted by the update of its slot (open)

workbench#12 (`sleepy-proposal-adoption.md`, f42c0ad) §4, A1.7's supplier over the Sleepy
invariant: every honest slot-`s` vote is the honest proposal `P` of slot `s`; at an honest node's
joined update of slot `s`, the result is exactly `P` and not vetoed, so the record afterwards
names a descendant of `P` (or keeps an already deeper one). The proof is a finite bootstrap
(S1P–S3P) for `B := P` with the Sleepy step lemmas stated for a protected block
(`vote_frame`, `later_transfer_step`, `vote_locks_compatible`, `held_origin_viable`); after the
update, `P` is a regular origin (`Origin.of_result`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The update of slot `s` adopts the honest proposal of slot `s`**: after an honest node's
joined update of slot `s`, its record names a block of the honest blocks that extends `P`. -/
theorem update_adopts {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) P E := by
  sorry

end Consensus.Goldilocks.Compose

end
