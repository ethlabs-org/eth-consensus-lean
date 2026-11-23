module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService

public section

/-! # Row supply within a signing delay

The quorum of exact entry rows that an anchor step consumes, stated as one premise with the
signing delay `D` as a parameter. `RowSupplyWithin tr H g b D`: same-height reports of an entry, by
`d`, of every node honest at `d` and at `c_z` yield, by `d + D`, either a quorum of nodes honest at
`d + D` and at `c_z` with exact entry signatures, or a report above the entry, in `[d, d + D]`, by a
node honest at it. The second branch is where a delayed vote may use a newer, higher source.

The signing deadline `d + D` and the signers' honesty cutoff are read here; delivery is not. A
consumer pairs the rows with its own delivery premise (`v + ΔF ≤` the serving proposal).

* `ResetPremisesUpTo.rowSupplyWithin_zero`: the same-tick FG update supplies rows with `D = 0`
  (`row_signers_of_reports_at`). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **Row supply within `D`**, through the horizon `b`. -/
structure RowSupplyWithin (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g b D : Time) : Prop where
  supply : ∀ {T : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time},
    0 ≤ t → (∀ q < m, tr.time q ≤ t) → y ∈ H t → T ∈ (tr.state y m).fg.tree →
    ∀ {σT : FG.ChainState sp.n}, (tr.state y m).fg.σ T.root = σT → σT.Th = T.root →
    HZ tr H g + 1 ≤ σT.h → (σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj) →
    ∀ {d : Time}, 0 ≤ d → d + D ≤ b →
    (∀ z, z ∈ H (max (cutZ sp.toParams g) d) → ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ d ∧ Anc (tr.HonestBlocksAt H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) →
    (∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H (max (cutZ sp.toParams g) (d + D)) ∧ ∃ att j, tr.SignAt z j att ∧
        att.val = z ∧ att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
        tr.time j ≤ d + D ∧ (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J))) ∨
    ∃ x r ell C, x ∈ H (tr.time r) ∧ AC.ToFGAt tr.projAC x r ell C ∧ d ≤ tr.time r ∧
      tr.time r ≤ d + D ∧ σT.h < ((tr.state x r).fg.σ C.root).h

namespace ResetPremisesUpTo

variable {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The same-tick FG update supplies rows with no delay. -/
theorem rowSupplyWithin_zero {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) : RowSupplyWithin tr H g b 0 := by
  refine ⟨?_⟩
  intro T y m t ht hle hy hT σT hσ hTe hhT hhj d hd hdb hrep
  left
  simp only [add_zero] at hdb ⊢
  exact hp.row_signers_of_reports_at ht hle hy hT hσ hTe hhT hhj hd hdb hrep

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end
