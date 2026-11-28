module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: sources of the proposal attestations

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {g ΔF a : Time}

/-! ### Sources of the proposer's attestations -/

/-- Finite high-origin labels preceding an actual proposal are strictly older. -/
theorem ResetPremisesUpTo.origin_label_lt_at_proposal {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} {r l : Nat}
    {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u := by
  obtain ⟨_, D, CV, _, hfl, _⟩ := hp.highOrigin_mem ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | hop
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    exact_mod_cast (AC.ts_lt_iff sp).mp (show sp.ts l < sp.ts u by linarith only [ht', hrt, hΔ])
  · obtain ⟨_, _, _, hsl, _⟩ := id hop
    have hle : l ≤ u := by
      have hts : sp.ts l ≤ tr.time r :=
        (AC.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by omega)
      exact_mod_cast (AC.ts_le_iff sp).mp (hts.trans hrt)
    have hl1 := slot_gbar_lt_of_cutZ_le (hp.cutZ_le_ts_of_highOrigin ho)
    have hne : l ≠ u := fun he => Compose.proposal_no_optimistic_of hp.run hp.noColl hp.hP
      (hp.cs2 (he ▸ hl1)) hpH hci hcall hti v ho.1 r hri D CV (he ▸ hop)
    clear * - hle hne; omega

/-- An origin already preceding an honest signature before a proposal has an older label.
This bound does not require the origin to precede a later receiving cast. -/
theorem origin_label_lt_at_proposal (hp : ResetPremises tr H K proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} {r l : Nat}
    {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u :=
  (hp.toUpTo tr H le_rfl).origin_label_lt_at_proposal hpH hci hcall hti hri ho

end Consensus.Goldilocks.Healing
