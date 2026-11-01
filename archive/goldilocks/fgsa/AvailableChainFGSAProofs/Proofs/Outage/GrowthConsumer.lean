module
public import AvailableChainFGSAProofs.Proofs.Outage.Growth
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- Clean truncation compares each earlier confirmed reader with one
confirmed inclusion witness at the proposal's gate. The two readers can be
different; the earlier reader can sleep before the gate or deadline. -/
theorem clean_growth_compatible_of_outputs {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (hset : CleanSet p c E rho ΔF)
    (hOutputs : ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedCompat (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
        (fun t => 0 ≤ t ∧ t ≤ rho.horizon))
    {s : Slot} {B : Block} (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    (hWitness : ∃ y, confirmedReader p c E rho y (SA.gateTime p.toParams s) ∧
      Block.Preceq B (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams s)) y))
    {u : Time} {x : V} {g : V2.D.Output (fgsa p c)}
    (hu : 0 ≤ u) (hus : u < V2.D.proposalTime (fgsaInterface p c) s)
    (hx : confirmedReader p c E rho x u)
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Compatible (V2.D.outputAt E rho g x u) B := by
  obtain ⟨y, hy, hB⟩ := hWitness
  have hd := p.deltaPos
  have hgate0 : 0 ≤ SA.gateTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    positivity
  have hugate : u ≤ SA.gateTime p.toParams s := by
    change u < 4 * p.Δ * (s : Time) at hus
    change u ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hc := (hOutputs g hg) u (SA.gateTime p.toParams s) x y
    ⟨hu, hugate.trans hhor⟩ ⟨hgate0, hhor⟩ hx hy
  change Block.Compatible (V2.D.outputAt E rho g x u)
    (V2.D.outputAt E rho g y (SA.gateTime p.toParams s)) at hc
  rw [fgsa_outputAt_eq_S_at E rho hset.pre.base.valid.toScheduleWellFormed
    g hg y (SA.gateTime p.toParams s)] at hc
  rcases Bool.or_eq_true_iff.mp hc with hXS | hSX
  · exact Gen.Pure.block_compatible_of_common hXS hB
  · exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
      (Gen.Pure.block_preceq_trans hB hSX)

/-- P20: the public binders and deadline stay unchanged. The two internal
suppliers use independent confirmed readers. Assembly must prove them from
Clean history and scoped inclusion. This is the unfolded production consumer;
only Outage/Export imports public claim predicates. -/
theorem clean_growth_claim_body (p : Params)
    (hcompatible : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) s →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Compatible (V2.D.outputAt E rho g x u) B)
    (hinclusion : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Preceq B (V2.D.outputAt E rho g x u)) :
    ∀ (G ΔF : Time) {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (t : Time),
      CleanSet p c E rho ΔF → AwakeProposerRecurrenceFrom p c E rho 0 G →
      4 * p.Δ ≤ G → 0 ≤ t → t + G + 6 * p.Δ ≤ rho.horizon →
      ∃ s B, t < V2.D.proposalTime (fgsaInterface p c) s ∧
        HonestProposal E rho (fgsaInterface p c) s B ∧
        ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
          (∀ x, confirmedReader p c E rho x t →
            Block.Prec (V2.D.outputAt E rho g x t) B) ∧
          (∀ x, confirmedReader p c E rho x (t + G + 6 * p.Δ) →
            Block.Preceq B (V2.D.outputAt E rho g x (t + G + 6 * p.Δ))) := by
  intro G ΔF V _ _ In c E rho t hset hrec hgap ht hhor
  exact clean_growth_body E rho G ΔF hset
    (hcompatible c E rho ΔF hset) (hinclusion c E rho ΔF hset) hrec hgap t ht hhor

end AvailableChain.FGSA.Run
end
