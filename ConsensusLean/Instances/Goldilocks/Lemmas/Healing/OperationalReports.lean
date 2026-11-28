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

variable {tr : GoldilocksTrace sp}
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
    (_hlive : sp.slot t ≤ u + sp.k) (hage : sp.slot t ≤ u + 2)
    (hcap : ∀ l ∈ A.locks, l.expiry ≤ l.slot + sp.k) :
    P ∈ AC.toFGCandidates sp (AC.updateConfirmation sp A Phi t u) Phi t := by
  have hself : Phi.viableAncestor P = P := AC.viableAncestor_self hPhi hPv.1 (Or.inl hPv)
  -- Unvetoed, so the filtered fast selection is the raw one; its expiry is still live.
  have hD := deepest_of_subset (S := {B | B ∈ {B | B ∈ AC.confirmationPath sp Phi P ∧
      ¬ AC.conflictsWithLock sp A.locks Phi t B} ∧ AC.FastTest sp A Phi u B}) hfast
    (fun B hB => ⟨hB.1.1, hB.2⟩)
    ⟨⟨(AC.deepest_mem hfast).1.1, hnv⟩, (AC.deepest_mem hfast).1.2⟩
  have hlock : ∃ e, sp.slot t ≤ e ∧ (⟨P.root, u, true, e⟩ : AC.Lock) ∈
      (AC.updateConfirmation sp A Phi t u).locks := by
    unfold AC.updateConfirmation
    simp only [hconf]
    rw [ite_eq_right hnv]
    rw [AC.updateLatestConfirmed_keeps_locks]
    exact ⟨_, AC.slot_le_fastExpiry sp _ _ _ _ hcap hage, ⟨P.root, u, true, _⟩,
      Or.inr ⟨_, Or.inl ⟨P, hD, rfl⟩, rfl⟩, P, hPv.1, rfl,
      AC.slot_le_fastExpiry sp _ _ _ _ hcap hage, by rw [hself]⟩
  obtain ⟨e, he, hlock⟩ := hlock
  exact ⟨hPv, ⟨P.root, u, true, e⟩, ⟨⟨P.root, u, true, e⟩, hlock, P, hPv.1, rfl, he,
    by rw [hself]⟩, rfl, rfl, hage⟩

/-- The exact fast candidate persists into an adjacent call with the same frame
and timestamp; these are the equalities supplied by `update_toFG_calls`. -/
theorem candidate_at_adjacent_call
    {y : Fin sp.n} {j u : Nat} {ell ell' : ACLabel (goldilocksNode sp)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hc : tr.projAC.CallAt y j ell) (hPhi : FrameOK ell.frame)
    (hframe : ell'.frame = ell.frame) (htime : tr.time (j + 1) = tr.time j)
    (hPv : P ∈ ell.frame.viableTree ell.frame.tree)
    (hconf : AC.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P)
    (hnv : ¬ AC.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P)
    (hfast : AC.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P)
    (hpost : tr.projAC.post j =
      AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u)
    (hlive : sp.slot (tr.time j) ≤ u + sp.k) (hage : sp.slot (tr.time j) ≤ u + 2)
    (hcap : ∀ l ∈ (tr.projAC.state y j).locks, l.expiry ≤ l.slot + sp.k) :
    P ∈ AC.toFGCandidates sp (tr.projAC.state y (j + 1)) ell'.frame (tr.time (j + 1)) := by
  rw [tr.projAC.state_succ_of_call hc, hpost, hframe, htime]
  exact candidate_after_fast_update hPhi hPv hconf hnv hfast hlive hage hcap

end UpTo

end CoveredEndpoint

end Consensus.Goldilocks.Obligations
end
