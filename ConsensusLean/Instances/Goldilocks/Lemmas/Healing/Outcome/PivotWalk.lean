module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRowSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
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
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: proposal walks and old locks

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n} {g ΔF a : Time}

/-! ### The proposal walk and fork-choice roots -/

/-- A non-current read-point lock sits below a raw source of the receiver. Its source
precedes the receiving cast, not necessarily the proposal. -/
theorem ResetPremisesUpTo.vote_old_lock_source_before {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hR : drainTime sp a ≤ sp.ts u)
    {l : AC.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : AC.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ell.frame.tree) (hLr : L.root = l.block) :
    ∃ r D, r < j ∧ cleanLabel sp a + sp.k + 2 ≤ l.slot ∧ l.slot < u ∧
      ((∃ CV, AC.FastLockAt tr.projAC y r l.slot D CV) ∨
        AC.SlowLockAt tr.projAC y r l.slot D) ∧
      Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) D := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc.1
  have hslot : sp.slot (tr.time j) = u := ((AC.castAt_specU hr.toU hy hc).2.1).symm.trans hes
  have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by
    rw [drainTime_eq] at hR
    have := (AC.ts_le_iff sp).mp hR
    rw [hslot] at hlive
    rw [cleanLabel_eq]
    clear * - hlive this; omega
  have hu : 0 < u := by
    rw [drainTime_eq] at hR
    have := (AC.ts_le_iff sp).mp hR
    clear * - this; omega
  obtain ⟨l₀, hl₀, hs, B, hB, hBr, L', hL', hL'r, hLB⟩ :=
    AC.readPoint_locks_below_stored hr hy hc
      (by change 0 < sp.slot (tr.time j); rw [hslot]; exact hu) l hl
      (by change l.slot ≠ sp.slot (tr.time j); simpa only [hslot] using hne)
  obtain rfl : L' = L := hPhi.coherent.1 hL' hL (hL'r.trans hLr.symm)
  obtain ⟨r, hrj, D, hraw, X, hX, hXr, hXD⟩ :
      ∃ r < j, ∃ D,
        ((∃ CV, AC.FastLockAt tr.projAC y r l₀.slot D CV) ∨
          AC.SlowLockAt tr.projAC y r l₀.slot D) ∧
        ∃ X ∈ tr.HonestBlocks H, X.root = l₀.block ∧ Anc (tr.HonestBlocks H) X D := by
    cases hf : l₀.fast with
    | false =>
      obtain ⟨r, hrj, D, hslow, hX⟩ := AC.slow_lock_provenance hr
          hp.run.vstart hy j l₀ hl₀ hf
      exact ⟨r, hrj, D, Or.inr hslow, hX⟩
    | true =>
      obtain ⟨r, hrj, D, CV, hfast, hX⟩ := AC.fast_lock_provenance hr
        hp.run.vstart hy j l₀ hl₀ hf
      exact ⟨r, hrj, D, Or.inl ⟨CV, hfast⟩, hX⟩
  obtain rfl : X = B := hr.coherent.1 hX (hPhiU hB) (hXr.trans hBr.symm)
  have hle : l₀.slot ≤ u := by
    have ht : sp.ts l₀.slot ≤ tr.time r := by
      rcases hraw with ⟨CV, hf⟩ | ⟨ellX, C, hupd, _⟩
      · rcases hf with ⟨ellX, C, hupd, _⟩ | ⟨ellX, A, _, hsl, _⟩
        · have ht : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := hupd.2.2.1
          have := sp.toParams.hΔ
          linarith only [ht, this]
        · change sp.slot (tr.time r) = l₀.slot at hsl
          exact (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) l₀.slot).mpr (by
              clear * - hsl; omega)
      · have ht : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := hupd.2.2.1
        have hΔ : 0 < sp.Δ := sp.toParams.hΔ
        linarith only [ht, hΔ]
    have htj : l₀.slot ≤ sp.slot (tr.time j) := by
      exact_mod_cast (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg j) l₀.slot).mp
        (ht.trans (hp.run.time_mono hrj.le))
    omega
  refine ⟨r, D, hrj, hclean, by clear * - hne hs hle; omega, hs ▸ hraw, ?_⟩
  exact (Anc.mono hPhiU ((AC.anc_viableAncestor ell.frame L').trans hLB)).trans hXD

/-- Whole-run specialization of actual read-point lock provenance. -/
theorem vote_old_lock_source_before (hp : ResetPremises tr H K proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hR : drainTime sp a ≤ sp.ts u)
    {l : AC.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : AC.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ell.frame.tree) (hLr : L.root = l.block) :
    ∃ r D, r < j ∧ cleanLabel sp a + sp.k + 2 ≤ l.slot ∧ l.slot < u ∧
      ((∃ CV, AC.FastLockAt tr.projAC y r l.slot D CV) ∨
        AC.SlowLockAt tr.projAC y r l.slot D) ∧
      Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) D :=
  (hp.toUpTo tr H (le_refl a)).vote_old_lock_source_before hy hc hes hR hl hne hlive hL hLr

section Support

variable (hp : ResetPremises tr H K proposer dg g ΔF a)
  (hc : CatchRun tr H g (2 * sp.Δ))
  {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
  (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
  {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
  (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (AC.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
  (hcy : AC.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = u)
  (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', AC.VoteAt tr.projAC x j' e' →
    e'.msg.slot = u → e'.msg.head = P.root)

end Support

end Consensus.Goldilocks.Healing
