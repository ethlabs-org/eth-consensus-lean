module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRowSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

/-! # Goldilocks Healing: proposal walks and old locks

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-! ### The proposal walk and fork-choice roots -/

/-- An optimistic prefix compares with an old high origin. Strictly earlier origin
labels use historical vote extension; equal labels use fast/optimistic compatibility. -/
theorem optimistic_prefix_compatible_old
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {r u : Nat}
    {D L O : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC p r (u - 1) D CV)
    (_hLu : L ∈ tr.HonestBlocks H) (hLD : Anc (tr.HonestBlocks H) L D)
    {x : Fin sp.n} {i j : Nat} (ho : HighOrigin tr H g x i j O)
    (_hOld : tr.time i < sp.ts u) (hj : j ≤ u - 1) :
    Compatible (tr.HonestBlocks H) L O := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hDO : Compatible (tr.HonestBlocks H) D O := by
    rcases hj.lt_or_eq with hj | rfl
    · apply SA.optimisticLock_compatible hrun (faulty_lt_half hp p) hpH hop
      intro z hz q e hv hs
      obtain ⟨ell, hc, he⟩ := hv
      have hvotes := (historical_activation_before hp (tr.time q) q le_rfl).2
      exact ((rawVoteAt_iff _ _ _).mp hvotes O j
        ((historicalTargets_iff O j).mpr ⟨x, i, ho⟩) z hz ell e ⟨hc, he⟩
        (by omega) le_rfl).1
    · obtain ⟨CV', hst⟩ := ho.2.2.1
      obtain ⟨_, C, hfl, hOC⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
      have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H
        (fun v => v.val) tr proposer ΔF (sp.ts (u - 1 : Nat)) (sp.ts (u - 1 + 1 : Nat) + sp.Δ)
        hp.run.toLocalRun (syncRun_of_gst hp.healthy.1 (le_ts_of_highOrigin hp ho))
      rcases SA.fastLock_same_slot hrun hpH (Or.inr hop) ho.1 hfl hsync
        (faulty_lt_half hp p) with hDC | hCD
      · exact SA.anc_total hrun.localRun.coherent hDC hOC
      · exact Or.inr (hOC.trans hCD)
  rcases hDO with hDO | hOD
  · exact Or.inl (hLD.trans hDO)
  · exact SA.anc_total hrun.localRun.coherent hLD hOD

/-- At proposal time, stored high locks can only come from an optimistic write of the
previous label. Regular updates are too late and current-label optimism is excluded. -/
theorem proposal_stored_locks_compatible_old
    (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (_hR : drainTime sp a ≤ sp.ts u)
    {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts u) :
    ∀ O, OldSrc tr H g u O →
      SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
        (tr.time i) (u - 1) O := by
  intro O hO
  obtain ⟨x, q, j, ho, hOld⟩ := oldSrc_iff.1 hO
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  rw [SA.highLocksCompatible_iff]
  intro l hl _ hlabel L hL hLr
  obtain ⟨r, hri, D, hwrite, L', hL', hL'r, hLD⟩ := SA.lock_provenance hr hP.1 i l hl
  obtain rfl : L' = L := hr.coherent.1 hL' hL (hL'r.trans hLr.symm)
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  rcases hwrite with ⟨CV, hop⟩ | ⟨ell, hupd⟩
  · have hle : l.slot ≤ u := by
      have ht := ts_le_of_fastLock hp (Or.inr hop)
      have := (SA.ts_le_iff sp).mp (ht.trans hrt)
      exact_mod_cast this
    have hne : l.slot ≠ u := by
      intro heq
      exact proposal_no_optimistic hp hP.1 hci hcall hti p hP.1 r hri D CV (heq ▸ hop)
    have heq : l.slot = u - 1 := by omega
    rw [heq] at hop
    exact optimistic_prefix_compatible_old hp hP.1 hop hL hLD ho hOld
      (by have := label_lt_of_old hp ho hOld; omega)
  · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    have hslots : sp.ts u ≤ sp.ts (l.slot + 1 : Nat) :=
      (SA.ts_le_iff sp).mpr (by omega)
    have hsucc : sp.ts (l.slot + 1 : Nat) = sp.ts l.slot + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [hsucc] at hslots
    linarith

/-- Stored proposal high locks compare with every high origin in the finite horizon. -/
theorem ResetPremisesUpTo.proposal_stored_locks_compatible_old {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} (hci : tr.projAC.CallAt p i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {q j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x q j O) (hqb : tr.time q ≤ b) :
    SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.time i) (u - 1) O := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos p; omega
  rw [SA.highLocksCompatible_iff]
  intro l hl _ hlabel L hL hLr
  obtain ⟨r, hri, D, hwrite, L', hL', hL'r, hLD⟩ := SA.lock_provenance hr hpH i l hl
  obtain rfl : L' = L := hr.coherent.1 hL' hL (hL'r.trans hLr.symm)
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  rcases hwrite with ⟨CV, hop⟩ | ⟨ell', hupd⟩
  · have hle : l.slot ≤ u := by
      obtain ⟨_, _, _, hsl, _⟩ := id hop
      have ht : sp.ts l.slot ≤ tr.time r :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) l.slot).mpr (by omega)
      exact_mod_cast (SA.ts_le_iff sp).mp (ht.trans hrt)
    have hne : l.slot ≠ u := fun he =>
      proposal_no_optimistic_of_run hp.run hp.noColl hf hpH hci hcall hti
        p hpH r hri D CV (he ▸ hop)
    have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by
      change u - 1 ≤ l.slot at hlabel
      rw [drainTime_eq] at hR
      have := (SA.ts_le_iff sp).mp hR
      have := sp.two_le_k
      rw [cleanLabel_eq]
      omega
    rcases hp.protected_source_compatible_high_origin hc hpH (Or.inl ⟨CV, Or.inr hop⟩)
        hclean ((hp.run.time_mono hri.le).trans hib) ho hqb with h | h
    · exact Or.inl (hLD.trans h)
    · exact SA.anc_total hr.coherent hLD h
  · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    have hslots : sp.ts u ≤ sp.ts (l.slot + 1 : Nat) :=
      (SA.ts_le_iff sp).mpr (by omega)
    have hsucc : sp.ts (l.slot + 1 : Nat) = sp.ts l.slot + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [hsucc] at hslots
    have := sp.toParams.hΔ
    linarith

/-- A non-current read-point lock sits below a raw source of the receiver. Its source
precedes the receiving cast, not necessarily the proposal. -/
theorem ResetPremisesUpTo.vote_old_lock_source_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hR : drainTime sp a ≤ sp.ts u)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ell.frame.tree) (hLr : L.root = l.block) :
    ∃ r D, r < j ∧ cleanLabel sp a + sp.k + 2 ≤ l.slot ∧ l.slot < u ∧
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot D CV) ∨
        SA.SlowLockAt tr.projAC y r l.slot D) ∧
      Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hslot : sp.slot (tr.time j) = u := ((SA.castAt_spec hr hy hc).2.1).symm.trans hes
  have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    rw [hslot] at hlive
    rw [cleanLabel_eq]
    omega
  have hu : 0 < u := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    omega
  obtain ⟨l₀, hl₀, hs, B, hB, hBr, L', hL', hL'r, hLB⟩ :=
    SA.readPoint_locks_below_stored hr hy hc
      (by change 0 < sp.slot (tr.time j); rw [hslot]; exact hu) l hl
      (by change l.slot ≠ sp.slot (tr.time j); simpa only [hslot] using hne)
  obtain rfl : L' = L := hPhi.coherent.1 hL' hL (hL'r.trans hLr.symm)
  obtain ⟨r, hrj, D, hraw, X, hX, hXr, hXD⟩ :
      ∃ r < j, ∃ D,
        ((∃ CV, SA.FastLockAt tr.projAC y r l₀.slot D CV) ∨
          SA.SlowLockAt tr.projAC y r l₀.slot D) ∧
        ∃ X ∈ tr.HonestBlocks H, X.root = l₀.block ∧ Anc (tr.HonestBlocks H) X D := by
    cases hf : l₀.fast with
    | false =>
      obtain ⟨r, hrj, D, hslow, hX⟩ := SA.slow_lock_provenance hr hy j l₀ hl₀ hf
      exact ⟨r, hrj, D, Or.inr hslow, hX⟩
    | true =>
      obtain ⟨r, hrj, D, CV, hfast, hX⟩ := SA.fast_lock_provenance hr hy j l₀ hl₀ hf
      exact ⟨r, hrj, D, Or.inl ⟨CV, hfast⟩, hX⟩
  obtain rfl : X = B := hr.coherent.1 hX (hPhiU hB) (hXr.trans hBr.symm)
  have hle : l₀.slot ≤ u := by
    have ht : sp.ts l₀.slot ≤ tr.time r := by
      rcases hraw with ⟨CV, hf⟩ | ⟨ellX, C, hupd, _⟩
      · rcases hf with ⟨ellX, C, hupd, _⟩ | ⟨ellX, A, _, hsl, _⟩
        · have ht : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := hupd.2.2.1
          have := sp.toParams.hΔ
          linarith
        · change sp.slot (tr.time r) = l₀.slot at hsl
          exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) l₀.slot).mpr (by omega)
      · have ht : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := hupd.2.2.1
        have hΔ : 0 < sp.Δ := sp.toParams.hΔ
        linarith
    have htj : l₀.slot ≤ sp.slot (tr.time j) := by
      exact_mod_cast (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg j) l₀.slot).mp
        (ht.trans (hp.run.time_mono hrj.le))
    omega
  refine ⟨r, D, hrj, hclean, by omega, hs ▸ hraw, ?_⟩
  exact (Anc.mono hPhiU ((SA.anc_viableAncestor ell.frame L').trans hLB)).trans hXD

/-- Whole-run specialization of actual read-point lock provenance. -/
theorem vote_old_lock_source_before (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hR : drainTime sp a ≤ sp.ts u)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ell.frame.tree) (hLr : L.root = l.block) :
    ∃ r D, r < j ∧ cleanLabel sp a + sp.k + 2 ≤ l.slot ∧ l.slot < u ∧
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot D CV) ∨
        SA.SlowLockAt tr.projAC y r l.slot D) ∧
      Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) D :=
  (hp.toUpTo tr H (le_refl a)).vote_old_lock_source_before hy hc hes hR hl hne hlive hL hLr

/-- A finite noncurrent voter lock lies below the actual proposal parent. -/
theorem ResetPremisesUpTo.vote_old_live_lock_below_parent {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ elly.frame.tree) (hLr : L.root = l.block) :
    Anc (tr.HonestBlocks H) (elly.frame.viableAncestor L) d.head := by
  obtain ⟨r, D, hrj, hclean, hlu, hsource, hLD⟩ :=
    hp.vote_old_lock_source_before hy hcy hes hR hl hne hlive hL hLr
  have hrb := (hp.run.time_mono hrj.le).trans hjb
  apply hLD.trans
  by_cases hgap : l.slot + 2 ≤ u
  · exact hp.clean_source_proposal_parent_before hc hy hpH hsource hclean hgap hrb hR
      hci hcall hd hti hib
  have he : u = l.slot + 1 := by omega
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have htj := (Compose.cast_head_fcRoot hr hy hcy).2
  rw [hes, he] at htj
  have hrt := hp.run.time_mono hrj.le
  have hts : sp.ts (l.slot + 1 : Nat) = sp.ts l.slot + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hΔ := sp.toParams.hΔ
  rcases hsource with ⟨CV, hfast⟩ | ⟨ellX, C, hupd, _⟩
  · rcases hfast with ⟨ellX, C, hupd, _⟩ | hop
    · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      rw [hts] at htj
      change tr.time j ≤ _ at htj
      exfalso
      linarith
    · exact hp.clean_optimistic_proposal_parent hc hy hpH hop hclean hrb (he ▸ hR)
        hci hcall hd (he ▸ hti) hib
  · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    rw [hts] at htj
    change tr.time j ≤ _ at htj
    exfalso
    linarith

section Support

variable (hp : ResetPremises tr H proposer dg g ΔF a)
  (hc : CatchRun tr H g (2 * sp.Δ))
  {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
  (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
  {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
  (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
  (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = u)
  (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
    e'.msg.slot = u → e'.msg.head = P.root)

include hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE in
set_option linter.unusedSectionVars false in
/-- Non-current live locks move back below the proposal parent. -/
theorem vote_old_live_lock_below_parent
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ℓy.frame.tree) (hLr : L.root = l.block) :
    Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor L) d.head := by
  obtain ⟨r, D, hrj, hclean, hlu, hsource, hLD⟩ :=
    vote_old_lock_source_before hp hy hcy hes hR hl hne hlive hL hLr
  apply hLD.trans
  by_cases hgap : l.slot + 2 ≤ u
  · exact clean_source_proposal_parent_before hp hc hy hP.1 hsource hclean hgap hR
      hci hcall hd hti
  have he : u = l.slot + 1 := by omega
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have htj := (Compose.cast_head_fcRoot hr hy hcy).2
  rw [hes, he] at htj
  have hrt := hp.run.time_mono hrj.le
  have hts : sp.ts (l.slot + 1 : Nat) = sp.ts l.slot + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hΔ := sp.toParams.hΔ
  rcases hsource with ⟨CV, hfast⟩ | ⟨ellX, C, hupd, _⟩
  · rcases hfast with ⟨ellX, C, hupd, _⟩ | hop
    · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      rw [hts] at htj
      change tr.time j ≤ _ at htj
      exfalso
      linarith
    · exact clean_optimistic_proposal_parent hp hc hy hP.1 hop hclean (he ▸ hR)
        hci hcall hd (he ▸ hti)
  · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    rw [hts] at htj
    change tr.time j ≤ _ at htj
    exfalso
    linarith

end Support


end Consensus.Goldilocks.Healing
