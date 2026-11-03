module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.CarrierCoverage

public section

/-! # Goldilocks Recovery: a stretch carrier gives `HighCoverageAt` (C1.3, final glue)

`high_coverage_of_stretch_carrier` packages an actual high ready proposal `P` of a slot in
`[v, v + M]`, with `t ≤ t_v ≤ t + 4Δ(W + 1)`, and an actual honest acceptance of a carrier `X`
before `t_{v+M}` whose replay-finalized block extends `P`, into
`HighCoverageAt tr H g t (4Δ(W + 1 + M))`. The coverage of the honest caches and their high
finality come from `coverage_of_finalizing_carrier` (C5) at `D = t_{v+M}`, whose deadline
`D + Δ` is at most the public one, `t + 4Δ(W + 1 + M) + Δ`; equal deadlines are included. -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- **Final C1.3 glue**: an actual high stretch proposal and an actual finalizing carrier
before `t_{v+M}` give `HighCoverageAt` at the public duration `4Δ(W + 1 + M)`. -/
theorem high_coverage_of_stretch_carrier {t : Time} {W M v : Nat} {q : Fin sp.n} {kP iP : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {x : Fin sp.n} {kX : Nat}
    {X Fx : SA.Blk sp.n (List (FG.Att sp.n))}
    (hp : ResetPremises tr H proposer dg g ΔF a)
    (hvtime : t ≤ sp.ts v ∧ sp.ts v ≤ t + 4 * sp.Δ * ((W : Time) + 1))
    (hP : ReadyProposal tr H proposer q kP P.slot P)
    (haccept : tr.AcceptAt q iP P)
    (hhigh : HZ tr H g + 1 ≤ ((tr.post iP).fg.σ P.root).h)
    (hvs : v ≤ P.slot) (hPs : P.slot ≤ v + M)
    (hx : x ∈ H) (hX : tr.AcceptAt x kX X)
    (hFx : Fx ∈ (tr.post kX).fg.tree)
    (hroot : Fx.root = ((tr.post kX).fg.σ X.root).F)
    (hPF : Anc (tr.HonestBlocks H) P Fx)
    (hgX : g ≤ tr.time kX) (hXD : tr.time kX < sp.ts (v + M : Nat)) :
    HighCoverageAt tr H g t (4 * sp.Δ * ((W : Time) + 1 + M)) := by
  obtain ⟨hqH, -, -, hProp, -, -⟩ := hP
  have hts {c d : Nat} (h : c ≤ d) : sp.ts c ≤ sp.ts d :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hvM : sp.ts (v + M : Nat) = sp.ts v + 4 * sp.Δ * (M : Time) := by
    simp only [SAParams.ts]; push_cast; ring
  -- the carrier's deadline is at most the public one
  have hD : sp.ts (v + M : Nat) ≤ t + 4 * sp.Δ * ((W : Time) + 1 + M) := by
    rw [hvM]; linarith [hvtime.2]
  have hgD : gbar g ≤ sp.ts (v + M : Nat) :=
    (max_le hgX (hp.run.time_nonneg kX)).trans hXD.le
  obtain ⟨hcover, hF⟩ := coverage_of_finalizing_carrier hp hqH haccept hhigh hx hX hFx hroot
    hPF hgX hXD hgD
  refine ⟨⟨q, kP, P, hqH, hProp, hvtime.1.trans (hts hvs), (hts hPs).trans hD,
    ⟨iP, haccept, hhigh⟩, ⟨x, hx, kX, X, hX, Fx, hFx, hroot, hPF⟩,
    fun y hy k hc hk => hcover y hy k hc (by linarith)⟩,
    ⟨fun y hy k hc hk => hF.at_call y hy k hc (by linarith)⟩⟩

end Consensus.Goldilocks.Healing.Recovery

end
