module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotOldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Strict
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Operational update selection and reports after the drain

Finite-horizon vote propagation, update selection and report coverage shared by Healing and
the obligations proof. Start with `UpTo.operational_update_selection`; its supporting arguments
work backwards from actual bounded calls to unanimous votes, retained sources and compatible locks.
Generic effective-record preservation and interval contracts are in `Obligations/HealthyEffective`.
-/

namespace Consensus.Goldilocks.Obligations

variable {sp : AC.ACParams} {FGP : Type} {U : Set (AC.Blk sp.n FGP)}

/-- Writing a held candidate leaves that candidate or a strictly later descendant.
The guard can retain a record only above the candidate, never an older fork. -/
theorem effective_record_update_slot_growth
    {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {A : AC.ACState sp.n}
    {P : AC.Blk sp.n FGP} (hP : P ∈ Φ.tree) :
    let C := (AC.lookup Φ (AC.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F
    Φ.Anc P C ∧ (C = P ∨ P.slot < C.slot) := by
  classical
  dsimp only
  have lookup_self : ∀ D ∈ Φ.tree, AC.lookup Φ D.root = some D := by
    intro D hD
    cases he : AC.lookup Φ D.root with
    | none => exact False.elim (AC.lookup_eq_none he ⟨D, hD, rfl⟩)
    | some C =>
      obtain ⟨hC, hr⟩ := AC.lookup_eq_some he
      exact congrArg some (hΦ.coherent.1 hC hD hr)
  have hanc : Φ.Anc P
      ((AC.lookup Φ (AC.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F) := by
    unfold AC.updateLatestConfirmed
    split_ifs with hg
    · obtain ⟨C, hC, hr, hPC⟩ := hg
      rw [← hr, lookup_self C hC]
      exact hPC
    · change Φ.Anc P ((AC.lookup Φ P.root).getD Φ.F)
      rw [lookup_self P hP]
      exact .refl
  refine ⟨hanc, ?_⟩
  by_cases he : (AC.lookup Φ (AC.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F = P
  · exact Or.inl he
  · exact Or.inr ((hanc.slot_le hΦ.coherent).2 (Ne.symm he))

section CoveredEndpoint

variable {ro : AC.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {K : AC.CommitteeDict sp.n} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g ΔF a : Time}

namespace UpTo

/-- Reset and drain timing put every bounded honest restart before the preceding
slot's join threshold; no last-wake bound at GST is assumed. -/
theorem restart_before_unanimous_slot {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {r : Nat} (hr : tr.RestartAt y r)
    (hrb : tr.time r ≤ b) : tr.time r ≤ sp.ts ((u : Int) - 1) := by
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := AC.gbar_nonneg g
    linarith [sp.toParams.hΔ]
  rw [Healing.cutZ_eq] at hca
  have hqa := (AC.ts_le_iff_le_slot sp ha0 _).1 hca.le
  rw [Healing.drainTime_eq] at hR
  have hAu := (AC.ts_le_iff sp).1 hR
  apply (Healing.restart_le_before hp hy hr hrb).trans
  apply (AC.ts_le_iff sp).2
  push_cast at hqa hAu ⊢
  omega

/-- The drain puts the slot before it at or after `c_z = g' + 8Δ`, `g' = t_{slot(ḡ)+1}`: the
AC base from `g'` serves it. -/
theorem slotAfter_add_le_of_drain {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat)) :
    AC.gbar (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) + 4 * sp.Δ ≤ sp.ts u := by
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := AC.gbar_nonneg g
    linarith [sp.toParams.hΔ]
  have hcz : Healing.cutZ sp.toParams g ≤ sp.ts u := by
    rw [Healing.cutZ_eq] at hca ⊢
    have hqa := (AC.ts_le_iff_le_slot sp ha0 _).1 hca.le
    rw [Healing.drainTime_eq] at hR
    have hAu := (AC.ts_le_iff sp).1 hR
    apply (AC.ts_le_iff sp).2
    push_cast at hqa hAu ⊢
    omega
  rw [Healing.gbar_slotAfter]
  rw [Healing.cutZ_eq_slotAfter] at hcz
  linarith [sp.toParams.hΔ]

/-- Finite reset service supplies actual votes from every honest member of the slot's committee
by the slot deadline. -/
theorem honest_votes_in_slot {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y ∈ H, y ∈ K.committee u → ∃ j e, AC.VoteAt tr.projAC y j e ∧ e.msg.slot = u ∧
      tr.time j ≤ sp.ts u + sp.Δ := by
  intro y hy hyK
  refine AC.honest_votes_in_slot_before (Healing.healthy_base_of_reset_catch_before hp hc)
    (slotAfter_add_le_of_drain hp hR) hub ?_ y hy hyK
  intro y hy r hr hrs
  exact restart_before_unanimous_slot hp hR hy
    (Compose.projAC_restartAt.mp hrs) (hr.trans hub)

/-- The honest voters of the slot are half of the committee size, so one of them votes by the
slot deadline. These witnesses seed the old-origin ancestry argument. -/
theorem exists_honest_vote_in_slot {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∃ z ∈ H, ∃ j e, AC.VoteAt tr.projAC z j e ∧ e.msg.slot = u ∧
      tr.time j ≤ sp.ts u + sp.Δ := by
  obtain ⟨z, hz, j, e, hv, hs, ht⟩ := Set.nonempty_of_ncard_ne_zero (s := {x | x ∈ H ∧
    ∃ j e, AC.VoteAt tr.projAC x j e ∧ e.msg.slot = u ∧ tr.projAC.time j ≤ sp.ts u + sp.Δ})
      (by
      have := AC.honest_voters_half_before (Healing.healthy_base_of_reset_catch_before hp hc)
        (slotAfter_add_le_of_drain hp hR) hub fun y hy r ht hrs =>
          restart_before_unanimous_slot hp hR hy (Compose.projAC_restartAt.mp hrs)
            (ht.trans hub)
      have := hp.committee_pos
      omega)
  exact ⟨z, hz, j, e, hv, hs, ht⟩

/-- The drain puts the slot after the slot of `ḡ`. -/
theorem slot_gbar_lt_of_drain {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat)) :
    sp.slot (AC.gbar g) + 1 ≤ u := by
  have h := slotAfter_add_le_of_drain hp hR
  rw [Healing.gbar_slotAfter] at h
  exact Healing.slot_gbar_lt_of_slotAfter_le (by linarith [sp.toParams.hΔ])

/-- Finite writer service carries the previous honest vote batch to a bounded
next-slot cast. Only actual previous votes, bounded by this cast, are consulted. -/
theorem unanimous_carry_votes {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocks H) ell.frame.F P) :
    AC.CarryAt tr.projAC (tr.HonestBlocks H) y i e u (Compose.honestVotes tr H u) := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hDelta := sp.toParams.hΔ
  apply AC.carryAt_of_each (hr.awake_of_call y hy i ell hcast.1)
    (AC.castAt_specU hr.toU hy hcast).2.2.1
  rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hsl⟩
  have hqi : q < i := by
    by_contra hn
    have := AC.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
    have := (AC.castAt_specU hr.toU hz hc').2.1
    have := (AC.castAt_specU hr.toU hy hcast).2.1
    omega
  obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hr
      hp.run.vstart hz hc'
  have hHdP : Hd = P := hr.coherent.1 ((AC.frameIn_of_callAt hr hz hc'.1).2 hHd) hP
    (hHdr.trans (hun z hz q e' ⟨ell', hc'⟩ ((hp.run.time_mono hqi.le).trans hib) hsl))
  subst Hd
  apply Compose.carryAt_of_writer_window_before hr hp.run.vstart
    (AC.serviceWindowBefore_of_sync (Healing.sync_window_of_service hp.run hp.sync))
    (by linarith : AC.gbar g ≤ sp.ts u) (Healing.catch_window_of_run hp.run hc) (by linarith)
    hz hy hcast hs hib
  rintro v rfl
  have ht : tr.projAC.time q < sp.ts u + 2 * sp.Δ := by rw [hsl] at hqt; linarith
  refine ⟨hsl, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg q) u).mpr
      (by rw [← (AC.castAt_specU hr.toU hz hc').2.1, hsl]), ht⟩, P, hP, hHdr, hFP, ?_⟩
  rcases Compose.frame_anc_acceptedU hr.toU hz q ell' hc'.1 P hHd P .refl with hg | ⟨k, hk, ha⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩

/-- Every honest unanimous vote is uniquely present and early-resolved in a
bounded post-service call holding P. Restart and deadline duties are derived. -/
theorem unanimous_pool {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hPt : P ∈ ell.frame.tree) :
    ∀ x ∈ H, x ∈ K.committee u →
      ∃ v ∈ (tr.projAC.state y j).pool u, v.val = x ∧ v.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame v < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.projAC.state y j).pool u, v'.val = x → v' = v := by
  have hS := Healing.healthy_base_of_reset_catch_before hp hc
  have hrestart : ∀ k ≤ j, tr.projAC.RestartAt y k → tr.projAC.time k < sp.ts u := by
    intro k hkj hk
    have h := restart_before_unanimous_slot hp hR hy (Compose.projAC_restartAt.mp hk)
      ((hp.run.time_mono hkj).trans hjb)
    exact h.trans_lt ((AC.ts_lt_iff sp).2 (by omega))
  refine AC.unanimous_pool_before hS hy hcall (slotAfter_add_le_of_drain hp hR) ht hjb ?_
    hrestart hPt ?_
  · intro k hkj t _
    exact Compose.ac_deadline_le_of_restarts
      (fun r hr hrs => (hrestart r (hr.trans hkj) hrs).le) t
  · intro x hx hxK
    have hub : sp.ts u + sp.Δ ≤ b := by linarith [sp.toParams.hΔ]
    obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot hp hc hR hub x hx hxK
    exact ⟨q, e, hv, hs, hun x hx q e hv (hq.trans hub) hs⟩

/-- A deepest block of `T` lying in `S ⊆ T` is the deepest block of `S`. -/
theorem deepest_of_subset {FGP : Type} {Φ : AC.Frm sp.n FGP}
    {S T : Set (AC.Blk sp.n FGP)} {D : AC.Blk sp.n FGP} (hT : AC.deepest Φ T = some D)
    (hST : S ⊆ T) (hD : D ∈ S) : AC.deepest Φ S = some D := by
  have h : AC.IsDeepest Φ S D := ⟨hD, fun C hC hne => (AC.deepest_mem hT).2 C (hST hC) hne⟩
  cases hd : AC.deepest Φ S with
  | none =>
    unfold AC.deepest at hd
    simp only [show ∃ B, AC.IsDeepest Φ S B from ⟨D, h⟩, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := AC.deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- Full viability makes the newly selected fast lock an exact toFG candidate,
including the second normalization by liveLocks at the adjacent call. -/
theorem candidate_after_fast_update {A : AC.ACState sp.n} {Phi : AC.Frm sp.n FGP}
    (hPhi : FrameOK Phi) {t : Time} {u : Nat} {P : AC.Blk sp.n FGP}
    (hPv : P ∈ Phi.viableTree Phi.tree)
    (hconf : AC.getConfirmation sp A Phi u = some P)
    (hnv : ¬ AC.conflictsWithLock sp A.locks Phi t P)
    (hfast : AC.fastSelect sp A Phi u P = some P)
    (_hlive : sp.slot t ≤ u + sp.k) (hage : sp.slot t ≤ u + 2) :
    P ∈ AC.toFGCandidates sp (AC.updateConfirmation sp A Phi t u) Phi t := by
  have hself : Phi.viableAncestor P = P := AC.viableAncestor_self hPhi hPv.1 (Or.inl hPv)
  -- unvetoed, so the filtered fast selection is the raw one; its expiry is `fastExpiry ≥ u + 2`
  have hD := deepest_of_subset (S := {B | B ∈ {B | B ∈ AC.confirmationPath sp Phi P ∧
      ¬ AC.conflictsWithLock sp A.locks Phi t B} ∧ AC.FastTest sp A Phi u B}) hfast
    (fun B hB => ⟨hB.1.1, hB.2⟩)
    ⟨⟨(AC.deepest_mem hfast).1.1, hnv⟩, (AC.deepest_mem hfast).1.2⟩
  have hlock : ∃ e, sp.slot t ≤ e ∧ (⟨P.root, u, true, e⟩ : AC.Lock) ∈
      (AC.updateConfirmation sp A Phi t u).locks := by
    unfold AC.updateConfirmation
    simp only [hconf]
    rw [ite_eq_right hnv]
    exact ⟨_, hage.trans (AC.le_fastExpiry sp _ _ _ _), ⟨P.root, u, true, _⟩,
      Or.inr ⟨_, Or.inl ⟨P, hD, rfl⟩, rfl⟩, P, hPv.1, rfl,
      hage.trans (AC.le_fastExpiry sp _ _ _ _), by rw [hself]⟩
  obtain ⟨e, he, hlock⟩ := hlock
  exact ⟨hPv, ⟨P.root, u, true, e⟩, ⟨⟨P.root, u, true, e⟩, hlock, P, hPv.1, rfl, he,
    by rw [hself]⟩, rfl, rfl, hage⟩

/-- The exact fast candidate persists into an adjacent call with the same frame
and timestamp; these are the equalities supplied by `update_toFG_calls`. -/
theorem candidate_at_adjacent_call
    {y : Fin sp.n} {j u : Nat} {ell ell' : ACLabel (goldilocksNode sp ro)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hc : tr.projAC.CallAt y j ell) (hPhi : FrameOK ell.frame)
    (hframe : ell'.frame = ell.frame) (htime : tr.time (j + 1) = tr.time j)
    (hPv : P ∈ ell.frame.viableTree ell.frame.tree)
    (hconf : AC.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P)
    (hnv : ¬ AC.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P)
    (hfast : AC.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P)
    (hpost : tr.projAC.post j =
      AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u)
    (hlive : sp.slot (tr.time j) ≤ u + sp.k) (hage : sp.slot (tr.time j) ≤ u + 2) :
    P ∈ AC.toFGCandidates sp (tr.projAC.state y (j + 1)) ell'.frame (tr.time (j + 1)) := by
  rw [tr.projAC.state_succ_of_call hc, hpost, hframe, htime]
  exact candidate_after_fast_update hPhi hPv hconf hnv hfast hlive hage

/-- A full viable unanimous pool at an actual update produces an actual report
at or before the adjacent toFG call, not merely a selected candidate. -/
theorem report_of_viable_unanimous_pool {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat}
    {ell ell' : ACLabel (goldilocksNode sp ro)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hu : AC.UpdateAt tr.projAC y j u ell)
    (hc : tr.projAC.CallAt y (j + 1) ell') (hto : ell'.call = .toFG)
    (hframe : ell'.frame = ell.frame) (htime : tr.time (j + 1) = tr.time j)
    (hjoin : AC.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)))
    (hPg : P.root ≠ sp.genesisRoot) (hPv : P ∈ ell.frame.viableTree ell.frame.tree)
    (hu1 : sp.slot (AC.gbar g) + 1 ≤ u)
    (hpool : ∀ v ∈ H, v ∈ K.committee u → ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame vote < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P)
    (hnext : ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y (j + 1)) ell'.frame (tr.time (j + 1)),
      Compatible (tr.HonestBlocks H) C P)
    (hlive : sp.slot (tr.time j) ≤ u + sp.k) (hage : sp.slot (tr.time j) ≤ u + 2) :
    ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧ tr.time r ≤ tr.time (j + 1) ∧
      Anc (tr.HonestBlocks H) P R := by
  obtain ⟨hconf, hnv, hfast, hpost, _⟩ :=
    hp.ready_update_selection_of_pool hy hu1 hu hPv.1 hPg hpool hlocks
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hPc := candidate_at_adjacent_call hu.1 (AC.frameIn_of_callAt hr hy hu.1).1
    hframe htime hPv hconf hnv hfast hpost hlive hage
  exact Healing.report_of_compatible_candidate_of_run hp.run hp.noColl hy hc hto hjoin hPg hPc hnext

/-- An honest node retains its unanimous vote head at a later call whenever
that call's finality is still below the head. -/
theorem unanimous_head_held_at_call {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hFP : Anc (tr.HonestBlocks H) (tr.state y j).fg.F P) :
    P ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  -- an honest slot-`u` voter holds `P` by `t_u + Δ`; the relay reaches `y` by `t_u + 2Δ`
  obtain ⟨z, hz, q, e, ⟨ellv, hv⟩, hs, hq⟩ := exists_honest_vote_in_slot hp hc hR hub
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hr hp.run.vstart hz hv
  have heq : Hd = P := hr.coherent.1 ((AC.frameIn_of_callAt hr hz hv.1).2 hHd) hP
    (he.trans (hun z hz q e ⟨ellv, hv⟩ (hq.trans hub) hs))
  rw [heq] at hHd
  have hg' := slotAfter_add_le_of_drain hp hR
  rw [Healing.gbar_slotAfter] at hg'
  have hF : Anc (tr.HonestBlocks H) ell.frame.F P := by
    rw [Compose.frame_of_projAC hp.run hy hcall]
    exact hFP
  exact hp.reset_frame_relay hc hz hy hv.1 hcall hHd hjb (by linarith) (by linarith)
    (by linarith) hF

end UpTo

end CoveredEndpoint

end Consensus.Goldilocks.Obligations
end
