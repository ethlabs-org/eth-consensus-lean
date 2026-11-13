module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks milestone Regimes: R.7 (accountability) and the rows that hold always

The R.7 rows of `Statements/Regimes/Always` over the Goldilocks run, from M₁ (G0.5, G1.3) and
FGStore (G1.4) through the run's FG projection:

* `final_accountable` (G1.3 with G1.5's binding; `NoColl`): each honest finalized tip is the
  finalization of a chain in the node's tree (`Store.finalized_chain`); two conflicting tips give
  chains that finalize conflicting blocks, so accountable safety convicts `2q − n` validators from
  the attestations of the two chains, which are on the chains of two blocks the readers hold.
* `non_framing` (G0.5; no `NoColl`): the FG projection executes the FG at the honest nodes
  (`fg_exec`), so an honest validator's signings are the outputs of one client run
  (`Store.signed_run_of_exec`), which signs no slashable pair (`FG.client_safety`).
* `finalized_safe` (G1.4; `NoColl`, `f < 2q − n`): `Store.finalized_safety` over the FG
  projection (`fg_projection`).

R.7 and R.8 (`Outputs`) are `Challenge` statements, each proved by its own theorem. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)
open Compose

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The FG projection of a Goldilocks run under `NoColl` is an FG trace with its contract. -/
private theorem fg_run (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  fg_projection _ _ dg H _ tr proposer
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc

private theorem store_eq (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    tr.projFG.store y i = (tr.state y i).fg := by
  change (tr.projFG.state y i).1 = _
  rw [projFG_state hrun.toLocalRun hy i]

/-- **R.7, `finalAccountable`.** -/
theorem final_accountable : FinalAccountable := by
  intro sp ro dg H tr proposer hrun hnc y hy z hz i j hne
  have hr := fg_run hrun hnc
  obtain ⟨c₁, σ₁, h₁, hF₁, hU₁, hc₁, -, X₁, hX₁, hb₁⟩ := Store.finalized_chain hr hy i
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, -, X₂, hX₂, hb₂⟩ := Store.finalized_chain hr hz j
  rw [store_eq hrun hy] at hF₁ hU₁ hc₁ hX₁ hb₁
  rw [store_eq hrun hz] at hF₂ hU₂ hc₂ hX₂ hb₂
  obtain ⟨S, hS, hSv⟩ := FG.accountable_safety sp.toParams.fg c₁ c₂ σ₁ σ₂ h₁ h₂
    (fun h => hne (hc₂ _ hU₁ (hF₁ ▸ h))) (fun h => hne (hc₁ _ hU₂ (hF₂ ▸ h)).symm)
  have hmem : ∀ a ∈ sp.toParams.fg.chainAtts c₁ ++ sp.toParams.fg.chainAtts c₂,
      a ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂ := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨Y, hY, hYX, haY⟩ := hb₁ a ha
      exact Or.inl ⟨Y, hY, hYX, haY⟩
    · obtain ⟨Y, hY, hYX, haY⟩ := hb₂ a ha
      exact Or.inr ⟨Y, hY, hYX, haY⟩
  refine ⟨X₁, hX₁, X₂, hX₂, S, hS, fun v hv => ?_⟩
  obtain ⟨a, ha, b, hb, hav, hab⟩ := hSv v hv
  exact ⟨a, hmem a ha, b, hmem b hb, hav, hab⟩

/-- **R.7, `nonFraming`** of a Goldilocks run from any AC starts `ini`: the FG projection
executes the FG at the honest nodes, whose clients sign no slashable pair. -/
theorem goldilocksRun_nonFraming {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini) {v : Fin sp.n} (hv : v ∈ H)
    {k k' : Nat} {a b : FG.Att sp.n} (ha : tr.SignAt v k a) (hb : tr.SignAt v k' b) :
    ¬ FG.slashable a b := by
  obtain ⟨inputs, hin, hsign⟩ := Store.signed_run_of_exec (fg_exec hrun.toLocalRun) hv
    (max k k' + 1)
  have conv : ∀ m c, tr.SignAt v m c → tr.projFG.SignAt v m c := fun m c ⟨src, hs⟩ =>
    ⟨src, projFG_callAt.2 hs⟩
  exact FG.client_safety sp.toParams.fg v inputs hin a
    (hsign k (by omega) a (conv k a ha)) b (hsign k' (by omega) b (conv k' b hb))

/-- **R.7, `nonFraming`.** -/
theorem non_framing : NonFraming :=
  fun _ _ _ _ _ _ hrun _ hv _ _ _ _ ha hb => goldilocksRun_nonFraming hrun hv ha hb

/-- **R.7, `finalized_safe_below_third`.** -/
theorem finalized_safe : FinalizedSafe := by
  intro sp ro dg H tr proposer hrun hnc hf y hy z hz i j
  have h := Store.finalized_safety sp.toParams _ _ H _ tr.projFG (fg_run hrun hnc) hf y hy z hz i j
  rwa [store_eq hrun hy, store_eq hrun hz] at h

end Consensus.Goldilocks.Regimes

end
