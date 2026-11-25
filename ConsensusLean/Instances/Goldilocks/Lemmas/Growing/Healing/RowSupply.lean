module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService

public section

/-! # Row supply within a signing delay

The quorum of exact entry rows that an anchor step consumes, stated as one premise with the
signing delay `D` and the release hold `E` as parameters. `RowSupplyWithin tr H g b D E`:
same-height reports of an entry, by `d`, of every node honest at `d` and at `c_z` yield either a
quorum of nodes honest at `d + D + E` and at `c_z` with exact entry signatures by `d + D`, or a
report above the entry, in `[d, d + D]`, by a node honest at it. The second branch is where a
delayed vote may use a newer, higher source. A signer honest at `d + D + E` is still honest when
its held signature is released.

The signing deadline `d + D` and the signers' honesty cutoff `d + D + E` are read here; delivery is
not. A consumer pairs the rows with its own delivery premise (`v + ΔF ≤` the serving proposal).

An actual report already supplies its signature, so `ResetPremisesUpTo.rowSupplyWithin` holds
for every nonnegative delay. The calendar wait is needed to produce the reports, not to turn
existing reports into rows. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **Row supply within `D`**, with signers honest a hold `E` later, through the horizon `b`. -/
structure RowSupplyWithin (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (g b D E : Time) : Prop where
  supply : ∀ {T : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time},
    0 ≤ t → (∀ q < m, tr.time q ≤ t) → y ∈ H t → T ∈ (tr.state y m).fg.tree →
    ∀ {σT : FG.ChainState sp.n}, (tr.state y m).fg.σ T.root = σT → σT.Th = T.root →
    HZ tr H g + 1 ≤ σT.h → (σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj) →
    ∀ {d : Time}, 0 ≤ d → d + D + E ≤ b →
    (∀ z, z ∈ H (max (cutZ sp.toParams g) d) → ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ d ∧ Anc (tr.HonestBlocksAt H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) →
    (∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H (max (cutZ sp.toParams g) (d + D + E)) ∧ ∃ att j, tr.SignAt z j att ∧
        att.val = z ∧ att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
        tr.time j ≤ d + D ∧ (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J))) ∨
    ∃ x r ell C, x ∈ H (tr.time r) ∧ AC.ToFGAt tr.projAC x r ell C ∧ d ≤ tr.time r ∧
      tr.time r ≤ d + D ∧ σT.h < ((tr.state x r).fg.σ C.root).h

namespace ResetPremisesUpTo

variable {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- Actual same-height reports supply exact rows within any nonnegative delay. The quorum is
chosen among nodes still honest at the deadline plus the hold, whose earlier reports remain
usable. -/
theorem rowSupplyWithin {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {D E : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    RowSupplyWithin tr H g b D E := by
  refine ⟨?_⟩
  intro T y m t ht hle hy hT σT hσ hTe hhT hhj d hd hdb hrep
  left
  apply hp.row_signers_of_reports_at ht hle hy hT hσ hTe hhT hhj
    (hd.trans (le_add_of_nonneg_right hD)) (le_add_of_nonneg_right hE) hdb
  intro z hz
  obtain ⟨r, ell, C, hr, hrd, hTC, hh⟩ :=
    hrep z (hp.run.antitone (max_le_max le_rfl (le_add_of_nonneg_right hD)) hz)
  exact ⟨r, ell, C, hr, hrd.trans (le_add_of_nonneg_right hD), hTC, hh⟩

/-- The same-tick FG update supplies rows with no delay. -/
theorem rowSupplyWithin_zero {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {E : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) (hE : 0 ≤ E) :
    RowSupplyWithin tr H g b 0 E :=
  hp.rowSupplyWithin le_rfl hE

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end
