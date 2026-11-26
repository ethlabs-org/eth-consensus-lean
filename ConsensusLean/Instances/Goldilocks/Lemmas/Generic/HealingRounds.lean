module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.StatementsBundle
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Generic healing rounds

The healing leaves over any healing supplier: for any node AC `A`, run predicate
`runs : ACRun A sg` and supplier `O : ACHealing A sg runs`, each theorem's type is the generic leaf
Prop over `O` (Milestones/Statements/Generic/Healing.lean). The proofs read the node run through
`ACRun.run_local` and apply the run-level leaves of `HealingLeaves`.

Leaf 12 (`high_row_source_at_of_healing`), over any `ACHealing`: a high signing by the horizon of
a premised reset comes from a report at the same time (leaf 7). `ACHealing.report_origin` gives
that report a high origin no later, and the signed entry, below the report, is below the origin in
the origin's store with the same replay state (`origin_below_report`).

Leaf 13 (`no_high_contest_at_of_healing`), over any `ACHealing`: in a contest at `h_max ≥ HZ + 2`,
`J` and the entry of the contested chain at `h_j` are two high self-entries, each left by a held
block. A held honest attestation on each (`Healing.honest_att_of_left`) was signed from a report
(leaf 7) whose origin holds the entry (`origin_below_report`); `ACHealing.origins_comparable`
makes the two origins compatible, and leaf 14 makes the entries equal, so `J` is below the chain.
Leaf 14 (`high_entry_eq_at_of_healing`), over any `ACHealing`: the two high origins are compatible
by `ACHealing.origins_comparable`, and `high_entry_eq_at_from` applies on the run.
-/

namespace Consensus.Goldilocks.Generic

/-! ## Fault and report-delay arithmetic -/

section HighProposal

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing (cutZ)

/-- The fault bound up to the horizon gives fewer than `q` faulty nodes there. -/
theorem faults_lt_q {H : Time → Set (Fin P.n)} {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) {t : Time} (ht : 0 ≤ t)
    (htb : t ≤ b) : (H t)ᶜ.ncard < P.fg.q := by
  have h3 := hf t ht htb
  have hn := P.hn
  change _ < (2 * P.n + 2) / 3
  omega

/-- Arithmetic form of the report-time shift, including its zero case. -/
theorem shiftDelay_eq_add (P : Params) (d : Nat) (t : Time) :
    shiftDelay P d t = t + (d : Time) * P.Δ := by
  cases d with
  | zero => simp [shiftDelay]
  | succ d => rfl

end HighProposal

/-! ## Leaf 12 -/

section HighRowSource

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing (cutZ)
open Healing.Growing (HZ IsReset)

/-- A high report, by a reader honest at it and at `c_z`, by the horizon of a premised reset, has
a high origin no later (`ACHealing.report_origin`); every entry below the report in the reader's
store is below the origin in the origin's store, with the same replay state. -/
private theorem origin_below_report {hold : Time}
    (O : ACHealing A sg runs hold) {cm proposer dg H tr} {βK : ℚ}
    {g ΔF a b : Time} (hβ : βK ≤ 1 / 2) (hrun : runs.Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg sg g ΔF b hold) (hres : IsReset tr H g a) (hab : a ≤ b)
    {y : Fin P.n} {i : Nat} {R E : A.Blk} (hyz : y ∈ H (max (cutZ P g) (tr.time i)))
    (hib : tr.time i ≤ b) (hR : ReportAt tr y i R)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) (hE : E ∈ (tr.state y i).fg.tree)
    (hER : (tr.state y i).fg.Anc E R) :
    ∃ r ≤ i, ∃ l Og, HighOrigin A sg O tr H g y r l Og ∧ E ∈ (tr.state y r).fg.tree ∧
      (tr.state y r).fg.Anc E Og ∧ (tr.state y r).fg.σ E.root = (tr.state y i).fg.σ E.root := by
  have hl := runs.run_local hrun
  have hnc := hp.noColl
  have hy := hl.antitone (le_max_right _ _) hyz
  have hi0 := hl.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hl.time_mono hq.le
  obtain ⟨r, hri, l, Og, -, hO, hOg, hROg⟩ := O.report_origin hβ hrun hp hres hab hy hib hR hh
  have hler : ∀ q < r, tr.time q ≤ tr.time i := fun q hq => hl.time_mono (by omega)
  have hRi := (O.report_in_frame hrun hy hR).1
  have hRr := mem_of_honest_anc_at_from hl hnc hi0 hler hy hROg hOg
  have hσR := σ_eq_honest_at_from hl hnc hi0 hler hy hi0 hlei hy hRr hRi
  have hROgh := Healing.h_le_of_store_anc (fg_reachable_at_from hl hi0 hler hy)
    (store_anc_of_honest_anc_at_from hl hnc hi0 hler hy hROg hOg)
  have hEOg := (honest_anc_of_store_anc_at_from hi0 hlei hy hER).trans hROg
  have hEr := mem_of_honest_anc_at_from hl hnc hi0 hler hy hEOg hOg
  refine ⟨r, hri, l, Og, ⟨hl.antitone (max_le_max le_rfl (hl.time_mono hri)) hyz, hO, ?_⟩, hEr,
    store_anc_of_honest_anc_at_from hl hnc hi0 hler hy hEOg hOg,
    σ_eq_honest_at_from hl hnc hi0 hler hy hi0 hlei hy hEr hE⟩
  rw [hσR] at hROgh
  omega

/-- Leaf 12: a high signing, by a signer honest at it and at `c_z`, by the horizon of a premised
reset, has a high origin strictly before it holding the signed entry. The signing comes from a
report at the same time (leaf 7), whose origin `ACHealing.report_origin` supplies. -/
theorem high_row_source_at_of_healing {hold : Time}
    (O : ACHealing A sg runs hold) : high_row_source_at A sg O := by
  intro cm proposer dg H tr βK g ΔF a b v d att hβ hrun hp hres hab hvz hdb hs hh
  have hl := runs.run_local hrun
  obtain ⟨i, hid, R, hR, hti, hhR, E, hE, hER, hEr, hEh, hETh⟩ :=
    sign_from_report_at_from hl (runs.run_requirements hrun) (hl.antitone (le_max_right _ _) hvz)
      hs
  obtain ⟨r, hri, l, Og, ho, hEm, hEOg, hσ⟩ := origin_below_report O hβ hrun hp hres hab
    (by rw [hti]; exact hvz) (by rw [hti]; exact hdb) hR (hh.trans hhR) hE hER
  exact ⟨r, by omega, l, Og, ho, E, hEm, hEOg, hEr, by rw [hσ, hEh], by rw [hσ, hETh]⟩

end HighRowSource

/-! ## Leaf 13 -/

section NoHighContest

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

open Healing (cutZ)
open Healing.Growing (HZ IsReset)

/-- A high self-entry, held at an observation honest by the horizon of a premised reset and left
by a held block, lies below a high origin. A held attestation on it by a signer honest at `c_z`
and at the observation (`Healing.honest_att_of_left`) was signed before the cut, from a report
(leaf 7) whose origin holds the entry (`origin_below_report`). -/
private theorem origin_of_left_entry {hold : Time}
    (O : ACHealing A sg runs hold) {cm proposer dg H tr} {βK : ℚ}
    {g ΔF a b : Time} (hβ : βK ≤ 1 / 2) (hrun : runs.Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg sg g ΔF b hold) (hres : IsReset tr H g a) (hab : a ≤ b)
    {y : Fin P.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hyt : y ∈ H t) (htb : t ≤ b) (hq : (H (max (cutZ P g) t))ᶜ.ncard < P.fg.q)
    {E C : A.Blk} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ v r l Og, HighOrigin A sg O tr H g v r l Og ∧ tr.time r ≤ b ∧
      Anc (tr.HonestBlocksAt H) E Og := by
  have hl := runs.run_local hrun
  have hnc := hp.noColl
  obtain ⟨W, hW, att, hatt, haT, haH⟩ :=
    Healing.honest_att_of_left (fg_reachable_at_from hl ht hle hyt) hq hET hEC hlt
  obtain ⟨d, hdk, hs⟩ := held_att_signed_at_from hl ht hle hyt ⟨W, hW, hatt⟩
    (hl.antitone (le_max_right _ _) haH)
  have hdt := hle d hdk
  obtain ⟨i, -, R, hR, hti, hah, E', hE', hE'R, hE'r, hE'h, -⟩ :=
    sign_from_report_at_from hl (runs.run_requirements hrun)
      (hl.antitone hdt (hl.antitone (le_max_right _ _) haH)) hs
  have hit : tr.time i ≤ t := hti ▸ hdt
  have hvi : att.val ∈ H (tr.time i) := hl.antitone hit (hl.antitone (le_max_right _ _) haH)
  have hi0 := hl.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hl.time_mono hq.le
  obtain rfl : E' = E := (Compose.Growing.honest_blocks_coherent_local hl hnc).1
    ⟨att.val, i, tr.time i, hi0, hlei, hvi, hE'⟩ ⟨y, k, t, ht, hle, hyt, hE⟩ (hE'r.trans haT)
  have hσE := σ_eq_honest_at_from hl hnc hi0 hlei hvi ht hle hyt hE' hE
  rw [hσE] at hE'h
  obtain ⟨r, hri, l, Og, ho, -, hEOg, -⟩ := origin_below_report O hβ hrun hp hres hab
    (hl.antitone (max_le_max le_rfl hit) haH) (hit.trans htb) hR (by omega) hE' hE'R
  exact ⟨att.val, r, l, Og, ho, (hl.time_mono hri).trans (hit.trans htb),
    honest_anc_of_store_anc_at_from hi0 (fun q hq => hl.time_mono (by omega)) hvi hEOg⟩

/-- Leaf 13: by the horizon of a premised reset, no honest store contests at `h_max ≥ HZ + 2`.
In a contest, `J` is a self-entry at `h_j ≥ HZ + 1` not below the contested chain `C`; the entry
of `C` at `h_j` is another. Both are left by held blocks, so both lie below high origins
(`origin_of_left_entry`), which `ACHealing.origins_comparable` makes compatible; leaf 14 makes the
two entries equal, so `J` is below `C`. -/
theorem no_high_contest_at_of_healing {hold : Time}
    (O : ACHealing A sg runs hold) : no_high_contest_at A sg O := by
  intro cm proposer dg H tr βK g ΔF a b p i hβ hrun hp ha hab hpH hib
  rintro ⟨⟨hmj, C, hC, -, hCh, hJC⟩, hmax⟩
  have hrl := runs.run_local hrun
  have ht := hrl.time_nonneg i
  have hi : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrl.time_mono hq.le
  have hU := Compose.Growing.honest_blocks_coherent_local hrl hp.noColl
  have hreach := fg_reachable_at_from hrl ht hi hpH
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨p, i, tr.time i, ht, hi, hpH, h⟩
  have hq : (H (max (cutZ P g) (tr.time i)))ᶜ.ncard < P.fg.q := by
    obtain ⟨j, hj, hjb⟩ := hp.snapshot
    exact faults_lt_q hp.faults (ht.trans (le_max_right _ _)) (max_le (hj.2.le.trans hjb) hib)
  obtain ⟨_, hJm, _, ⟨Bj, hBj, hBjJ, hBjhj⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Healing.Store.J_entry_of_reachable hreach hBj
  obtain rfl : EJ = (tr.state p i).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · exact hJC (hg ▸ (Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
  have hjlt := Healing.Store.hj_lt_h hreach hBj
  obtain ⟨EC, hEC, hECC, hECh, hECT⟩ := Healing.entry_at_height hreach hC
    (h := (tr.state p i).fg.hj) (by omega) (by omega)
  obtain ⟨v₁, r₁, l₁, B₁, ho₁, hr₁b, hJB₁⟩ := origin_of_left_entry O hβ hrun hp ha hab
    ht hi hpH hib hq hEJ hJT (by omega) hEJB (by omega)
  obtain ⟨v₂, r₂, l₂, B₂, ho₂, hr₂b, hECB₂⟩ := origin_of_left_entry O hβ hrun hp ha hab
    ht hi hpH hib hq hEC hECT (by omega) hECC (by omega)
  have he := high_entry_eq_at_from hrl hp.noColl
    (O.origins_comparable hβ hrun hp ha hab ho₁.1 ho₁.2.1 hr₁b ho₁.2.2 ho₂.1 ho₂.2.1 hr₂b
      ho₂.2.2)
    hJB₁ hECB₂ ht hi hpH ht hi hpH hEJ hEC (by omega) hJT hECT
  have heq : EC = (tr.state p i).fg.J := hU.1 (hsub hEC) (hsub hEJ) he.symm
  exact hJC (heq ▸ hECC)

end NoHighContest

/-! ## Leaf 14 over a healing supplier -/

section HighEntrySupplier

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}

/-- Leaf 14 over any healing supplier: the two high origins are compatible by
`ACHealing.origins_comparable`, and `high_entry_eq_at_from` applies on the run. -/
theorem high_entry_eq_at_of_healing {runs : ACRun A sg} {hold : Time}
    (O : ACHealing A sg runs hold) :
    high_entry_eq_at A sg O := by
  intro cm proposer dg H tr βK g ΔF a b x x' i j i' j' B B' Z₁ Z₂ y₁ y₂ m₁ m₂ t₁ t₂ hβ hrun hP
    hr hab ho hib ho' hi'b h₁ h₂ ht₁ hle₁ hy₁ ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂
  exact high_entry_eq_at_from (runs.run_local hrun) hP.noColl
    (O.origins_comparable hβ hrun hP hr hab ho.1 ho.2.1 hib ho.2.2 ho'.1 ho'.2.1 hi'b ho'.2.2)
    h₁ h₂ ht₁ hle₁ hy₁ ht₂ hle₂ hy₂ hZ₁ hZ₂ hh hT₁ hT₂

end HighEntrySupplier

end Consensus.Goldilocks.Generic
