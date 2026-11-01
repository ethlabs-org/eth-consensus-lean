module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossCause -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes -- shake: keep (fault bound)

set_option linter.privateModule false

/-!
H-DESCENT D2 coverage (plan fgsa-s5-m5-d2d4 B and D tests item 2, 2026-10-03):

* The unrestricted `support` of the original skeleton with the concrete `Lost`
  is not instantiable (blocker B1).
* The corrected first-failure instance at c₀ = μ + 1, with the inline facts
  discharged by their Foundations producers (`emittedName_window` is the
  window projection of `sourceDiscipline_emittedName`).
* Same-label high sources; a pre-GST source has height at most μ.
* A later-label conflict gives an earlier event, not a smaller label.
* The first transfer v_(sB+1) is before the row of B (blocker B2); from label
  sB + 2 the row is an earlier event.
* F covers B; strict time order gives strict event order.
-/

section
namespace AvailableChain.FGSA.Run.Tests.HealingDescentLoss
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- B1: the unrestricted `support` forces every block that is not a high source to be
-- compatible with every high source of a later label. A sibling of a high source in a
-- concrete run refutes this; that run needs a model, so only the consequence is checked.
example (old : ∀ i K s B sB, SourceBefore p c E rho i K s →
      muOf p c E rho + 1 ≤ (heightView p K).h → sB < s →
      ¬ Block.Compatible (eraseFG B) (eraseFG K) → ∃ k < i, Lost p c E rho B sB k)
    {i : Nat} {K B : FGBlock (Fin p.n)} {s sB : Slot} (hK : SourceBefore p c E rho i K s)
    (hc : muOf p c E rho + 1 ≤ (heightView p K).h) (hlt : sB < s)
    (hB : ¬ HighSrcN p c E rho B sB) :
    Block.Compatible (eraseFG B) (eraseFG K) := by
  by_contra hn
  obtain ⟨k, -, hL⟩ := old i K s B sB hK hc hlt hn
  rw [Lost_def] at hL
  exact hB hL.1

-- The corrected instance: the Foundations producers discharge every input under
-- HealingSet. No loss occurs and all high sources are pairwise compatible.
example [Fintype V] {G ΔF : Time} (h : HealingSet p c E rho G ΔF)
    (hScopes : LossServiceScope p c E rho) :
    (∀ k K s, ¬ Lost p c E rho K s k) ∧
      ∀ i K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
        muOf p c E rho + 1 ≤ (heightView p K).h → muOf p c E rho + 1 ≤ (heightView p K').h →
        Block.Compatible (eraseFG K) (eraseFG K') := by
  have hs := h.base.valid.toScheduleWellFormed
  exact healing_high_source_compat p c E rho h hScopes (fgsa_rMonoAll p c E rho)
    (fun ha => sourceDiscipline_emittedNonempty p c E rho ha)
    (emittedName_window p c E rho hs)
    (fgsa_leaseOrigins_lastWrite p c E rho hs)
    (fgsa_apiFinalLockClaim_body p c E rho () ⟨h.base, h.fault⟩)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨h.base, h.faultQ⟩ (fgsa_rStore p c E rho))

-- Same-label high sources are compatible (IF.6 on the two genuine gate results).
example [Fintype V] {G ΔF : Time} (h : HealingSet p c E rho G ΔF)
    (hScopes : LossServiceScope p c E rho)
    {i : Nat} {K K' : FGBlock (Fin p.n)} {s : Slot}
    (hK : SourceBefore p c E rho i K s) (hK' : SourceBefore p c E rho i K' s)
    (hc : muOf p c E rho + 1 ≤ (heightView p K).h)
    (hc' : muOf p c E rho + 1 ≤ (heightView p K').h) :
    Block.Compatible (eraseFG K) (eraseFG K') := by
  have hs := h.base.valid.toScheduleWellFormed
  exact healing_loss_same p c E rho h.toRecovery₂
    (fun ha => sourceDiscipline_emittedNonempty p c E rho ha)
    (emittedName_window p c E rho hs) hScopes.same i K K' s hK hK' hc hc'

-- A source that votes before GST has height at most μ: it is never high.
example (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot} (hK : SourceBefore p c E rho i K s)
    (hpre : SA.voteTime p.toParams s < E.t_GST) :
    (heightView p K).h ≤ muOf p c E rho := by
  by_contra hn
  have hg := healing_high_source_sync p c E rho
    (fun ha => sourceDiscipline_emittedNonempty p c E rho ha)
    (emittedName_window p c E rho hs) hK (Nat.lt_of_not_le hn)
  exact absurd hg (not_le.mpr hpre)

-- A later-label conflict gives a loss at an earlier EVENT (before the row of K at
-- index < i); the loss label is s, not a smaller source label.
example [Fintype V] {G ΔF : Time} (h : HealingSet p c E rho G ΔF)
    {i : Nat} {K B : FGBlock (Fin p.n)} {s sB : Slot}
    (hK : SourceBefore p c E rho i K s) (hc : muOf p c E rho + 1 ≤ (heightView p K).h)
    (hB : SourceBefore p c E rho i B sB) (hcB : muOf p c E rho + 1 ≤ (heightView p B).h)
    (hlt : sB < s) (hn : ¬ Block.Compatible (eraseFG B) (eraseFG K)) :
    ∃ k < i, Lost p c E rho B sB k := by
  have hs := h.base.valid.toScheduleWellFormed
  exact healing_loss_support p c E rho h.toRecovery₂
    (fun ha => sourceDiscipline_emittedNonempty p c E rho ha)
    (emittedName_window p c E rho hs) i K s B sB hK hc hB hcB hlt hn

-- B2: at the first transfer v_(sB+1) the row of B is not an earlier event
-- (v_(sB+1) < d_sB). A `SourceBefore k B sB` field in `Lost` would delete this case.
example (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {x : V}
    {B : FGBlock (Fin p.n)} {sB : Slot}
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams (sB + 1))))
    (hB : SourceBefore p c E rho k B sB) : False := by
  have hg := healing_source_gate p c E rho hs hB hk
  change 4 * p.Δ * (sB : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((sB + 1 : Nat) : Int) + p.Δ at hg
  push_cast at hg
  linarith [p.deltaPos]

-- From label sB + 2 on, the row of B is an earlier event.
example (hs : V2.D.ScheduleWellFormed E rho) {B : FGBlock (Fin p.n)} {sB : Slot}
    (hB : SrcN p c E rho B sB) {k : Nat} {x : V}
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams (sB + 2)))) :
    SourceBefore p c E rho k B sB :=
  healing_loss_late_source p c E rho hs hB le_rfl hk

-- A loss at the first transfer is a `Lost` value without any row of B before it.
example {B : FGBlock (Fin p.n)} {sB : Slot} {k : Nat} {x : V}
    (hB : HighSrcN p c E rho B sB) (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams (sB + 1))))
    (hn : ¬ Block.Preceq (eraseFG B) (headAtIdx p c E rho k (sB + 1))) :
    Lost p c E rho B sB k := by
  rw [Lost_def]
  exact ⟨hB, x, sB + 1, hx, le_rfl, hk, hn⟩

-- F covers B: a block below F of the reader is below its HEAD at a positive label.
example {k : Nat} {x : V} {l : Slot} (hl : l ≠ 0)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)))
    {B : FGBlock (Fin p.n)} (hB : FGBlock.Preceq B (storeAt p c E rho k x).fg.F) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho k l) :=
  healing_head_covers_root p c E rho hk hl (Or.inr hB)

-- Strict time order gives strict event order (equal times give no order).
example (hs : V2.D.ScheduleWellFormed E rho) {a b : Nat} {x y : V} {s : Slot}
    (ha : rho.events[a]? = some (.tick x (SA.voteTime p.toParams s)))
    (hb : rho.events[b]? = some (.tick y (SA.gateTime p.toParams s))) : a < b := by
  refine healing_idx_lt_of_time_lt p c E rho hs ha hb ?_
  change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
  linarith [p.deltaPos]

end AvailableChain.FGSA.Run.Tests.HealingDescentLoss
end
