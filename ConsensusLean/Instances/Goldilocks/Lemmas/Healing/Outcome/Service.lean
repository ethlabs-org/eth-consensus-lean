module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Service

public section

/-! # Goldilocks Healing: C1.2, AC outcome service for honest entries (assembly)

C1.2 (`Compose.OutcomeService`, claims C1.2 at goldilocks `6703bf05`) from the post-reset duty
supplier (`Outcome/Supplier`) and two C1.2-specific steps, following
fradamt-agent/workbench `producer-reset-continuation.md` §17, §18 (BA) and §26:

* **Entry rows** (`entry_rows`, §17 corrected, §18 BA): for a served entry `E = (h, T, u)` (an
  honest ready proposal `T` of slot `u ≥` the drain, at height `h ≥ H_z + 1`, with a high
  predecessor when bound), by `t_u + 6Δ` either honest validators of weight `q` have signed a
  target row for `E`, carrying the predecessor `(h − 1, J)` at a bound entry, or an honest
  accepted block has justified `E` (and finalized the predecessor at a bound entry) — the
  retained justified crossing. From `ready_unanimous`, `ready_update`, HR.4 (R1), (R4), G0.10
  and `δ_t ≥ 2` (no timeout through `t_u + 6Δ`).
* **The outcome** (`outcome_of_rows`, §26): with the window's honest ready proposal `W` whose
  parent extends `T` (retained ready inclusion), the rows reach `W`'s proposer before `t_{W.slot}`
  (`6Δ + Δ_F ≤ 4Δ·𝓕`) and give the literal `GW(E, 0, k_F)` at its acceptance of `W` (C0.3), unless
  a retained chain justified `E` first (branch (ii)); the carrier is relayed within `Δ`; at an
  unbound entry `E` is justified by the window's end in both branches (G1.7 in branch (i)).

Interface: `entry_rows` and `outcome_of_rows` are open. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The rows of a served entry by its deadline**: the entry `T` of height `h` (bound when
`bound`, with predecessor justification `Jr` at `hj`) has, by `d`, a quorum of honest target rows
signed by `d`, carrying the predecessor at a bound entry; or an honest node has accepted by `d` a
block `X` that justifies `T` at `h` and, at a bound entry, has finalized the predecessor. -/
def EntryRows (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (T : SA.Blk sp.n (List (FG.Att sp.n))) (h hj : Nat) (bound : Bool) (Jr : Nat) (d : Time) :
    Prop :=
  (∃ R : Finset (FG.Att sp.n), sp.toParams.fg.q ≤ (R.image FG.Att.val).card ∧
    ∀ r ∈ R, r.val ∈ H ∧ (∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ d) ∧
      r.h = h ∧ r.T = T.root ∧ r.timeout = false ∧ (bound = true → r.fin = some (hj, Jr))) ∨
  ∃ y ∈ H, ∃ k X, tr.AcceptAt y k X ∧ tr.time k ≤ d ∧
    Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T h X ∧
    (bound = true → ((tr.post k).fg.σ X.root).hF + 1 = h ∧ ((tr.post k).fg.σ X.root).F = Jr)

theorem entryRows_iff {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {h hj : Nat} {bound : Bool} {Jr : Nat} {d : Time} :
    EntryRows tr H T h hj bound Jr d ↔
      ((∃ R : Finset (FG.Att sp.n), sp.toParams.fg.q ≤ (R.image FG.Att.val).card ∧
        ∀ r ∈ R, r.val ∈ H ∧ (∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ d) ∧
          r.h = h ∧ r.T = T.root ∧ r.timeout = false ∧
          (bound = true → r.fin = some (hj, Jr))) ∨
      ∃ y ∈ H, ∃ k X, tr.AcceptAt y k X ∧ tr.time k ≤ d ∧
        Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T h X ∧
        (bound = true →
          ((tr.post k).fg.σ X.root).hF + 1 = h ∧ ((tr.post k).fg.σ X.root).F = Jr)) :=
  Iff.rfl

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp a : Time} {cF kF : Nat}

/-- **Entry rows** (§17 corrected, §18 BA): under C1.2's premises, a served entry has its rows,
or a retained justified crossing, by `t_u + 6Δ`. -/
theorem entry_rows (hrun : GoldilocksRun dg H tr) (hsh : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hcF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time))
    (hδ : cF + kF ≤ sp.toParams.δt) (ha : IsReset tr H g a) {p y : Fin sp.n} {k i u : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u T)
    (hE : Compose.RunEntry tr H y i T) (hR : drainTime sp a ≤ sp.ts u)
    (hh : HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).h)
    (hhj : 0 < ((tr.post i).fg.σ T.root).hj →
      ((tr.post i).fg.σ T.root).hj + 1 = ((tr.post i).fg.σ T.root).h →
      HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).hj) :
    EntryRows tr H T ((tr.post i).fg.σ T.root).h ((tr.post i).fg.σ T.root).hj
      (decide ((tr.post i).fg.σ T.root).bound) ((tr.post i).fg.σ T.root).J
      (sp.ts u + 6 * sp.Δ) := by
  sorry

/-- **The outcome from the rows** (§26): with the window's honest ready proposal whose parent
extends `T`, the rows (or the retained crossing) give C1.2's conclusion: the literal good window
or the early outcome, with the carrier relayed, and at an unbound entry a justification by the
window's end. -/
theorem outcome_of_rows (hrun : GoldilocksRun dg H tr) (hsh : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hpp : PropPlus tr H g Gp)
    (hcF₁ : 4 * sp.Δ * ((cF : Time) - 1) < 6 * sp.Δ + ΔF)
    (hcF₂ : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time)) (hδ : cF + kF ≤ sp.toParams.δt)
    (ha : IsReset tr H g a) {p y : Fin sp.n} {k i u : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u T)
    (hE : Compose.RunEntry tr H y i T) (hR : drainTime sp a ≤ sp.ts u)
    (hW : ∃ (w : Fin sp.n) (kw : Nat) (W : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H w kw W.slot W ∧ u + cF ≤ W.slot ∧ W.slot ≤ u + cF + kF ∧
      ∃ Pr, W.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) T Pr)
    (hrows : EntryRows tr H T ((tr.post i).fg.σ T.root).h ((tr.post i).fg.σ T.root).hj
      (decide ((tr.post i).fg.σ T.root).bound) ((tr.post i).fg.σ T.root).J
      (sp.ts u + 6 * sp.Δ)) :
    let h := ((tr.post i).fg.σ T.root).h
    let bound := decide ((tr.post i).fg.σ T.root).bound
    let T₁ := sp.ts (u + cF + kF + 1 : Nat)
    ((∃ (q : Fin sp.n) (j : Nat) (Bs Pr : SA.Blk sp.n (List (FG.Att sp.n)))
        (R : Finset (FG.Att sp.n)),
        tr.projFG.time j < T₁ ∧
        Store.GoodWindow sp.toParams (Payload sp.n) H tr.projFG cF T 0 kF q j Bs Pr R ∧
        ∀ z ∈ H, ∃ k', tr.AcceptAt z k' Bs ∧ tr.time k' < T₁ + sp.Δ) ∨
      Compose.EarlyOutcome tr H T h bound ((tr.post i).fg.σ T.root).J T₁) ∧
    (bound = false → ∃ y ∈ H, ∃ k' X, tr.AcceptAt y k' X ∧ tr.time k' < T₁ ∧
      Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k').fg T h X) := by
  sorry

/-- **C1.2, AC outcome service for honest entries.** -/
theorem outcome_service : Compose.OutcomeService := by
  intro sp ro dg H tr g ΔF Gp a cF kF hrun hsh hc hpp hcF₁ hcF₂ hδ ha p k i T u hP hE hu hh hhj
    hW
  have hR : drainTime sp a ≤ sp.ts u := by rw [drainTime_eq]; exact hu
  exact outcome_of_rows hrun hsh hc hpp hcF₁ hcF₂ hδ ha hP hE hR hW
    (entry_rows hrun hsh hc hcF₂ hδ ha hP hE hR hh hhj)

end Consensus.Goldilocks.Healing

end
