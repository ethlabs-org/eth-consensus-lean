module
public import AvailableChainFGSAProofs.Proofs.Healing.Descent
-- shake: keep (descent boundary tests)
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (producer)
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes -- shake: keep (fault bound)

set_option linter.privateModule false

/-!
H-DESCENT coverage (plan S25/S27, 2026-10-02):

* D1: `healing_source_gate` and `healing_source_read` (B16 base form).
* D2: `healing_high_pair_compat`, `healing_high_source_first_failure`,
  `healing_descent_pair` and `healing_entry_pair_incompatible`.
* D3: `healing_descent`, the restricted coverage-aware descent (B18).
* D4: `healing_finality_source` and `healing_justified_source`.
* D5: `healing_rExcl`, a direct corollary of D3.
-/

section
namespace AvailableChain.FGSA.Run.Tests.HealingDescent
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

-- The foundation producers discharge the descent channels under HealingSet.
example [Fintype V] {G ΔF : Time} (h : HealingSet p c E rho G ΔF) : RExcl p c E rho :=
  healing_rExcl (hroots := hroots) p c E rho (fgsa_apiFinalLockClaim_body p c E rho () ⟨h.base,
      h.fault⟩)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨h.base, h.faultQ⟩
      (fgsa_rStore p c E rho))

-- The restricted cover reads only earlier sources above F that extend C.
-- A source that conflicts with C needs no view membership.
example (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {i : Nat} {x : V} {X : Finset (FGBlock (Fin p.n))} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF) (hC : C ∈ X)
    (cover : ∀ K s, SourceBefore p c E rho i K s → FGBlock.Preceq C K → K ∈ X) :
    KeepOrCause p c E rho i x X C :=
  healing_descent (hroots := hroots) p c E rho xing origin hx hX hC
    (fun K s hK _ hCK _ => Or.inl (cover K s hK hCK))

-- The full view of the store satisfies the cover for each held block.
example (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hC : C ∈ (storeAt p c E rho i x).fg.TF)
    (held : ∀ K s, SourceBefore p c E rho i K s → K ∈ (storeAt p c E rho i x).fg.TF) :
    KeepOrCause p c E rho i x (storeAt p c E rho i x).fg.TF C :=
  healing_descent (hroots := hroots) p c E rho xing origin hx subset_rfl hC
    (fun K s hK _ _ _ => Or.inl (held K s hK))

-- B16: freeze and release reads see only strictly earlier labels.
example (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s u : Slot}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x (SA.freezeTime p.toParams u))) : s + 1 ≤ u :=
  (healing_source_read p c E rho hs hsource hi).1 rfl

example (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s u : Slot}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x (SA.releaseTime p.toParams u))) : s + 1 ≤ u :=
  (healing_source_read p c E rho hs hsource hi).2.1 rfl

-- A gate read can see a source of its own label (same-time tick order).
example (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s u : Slot}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams u))) : s ≤ u :=
  (healing_source_read p c E rho hs hsource hi).2.2 rfl

-- Natural subtraction must not allow an earlier source at a slot-0 freeze.
example (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s : Slot}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x (SA.freezeTime p.toParams 0))) : False := by
  exact Nat.not_succ_le_zero s ((healing_source_read p c E rho hs hsource hi).1 rfl)

-- No loss predicate: every two high sources are compatible from IF.6 alone.
example (c₀ : Nat)
    (same : ∀ i K K' s, SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s →
      c₀ ≤ (heightView p K).h → c₀ ≤ (heightView p K').h →
      Block.Compatible (eraseFG K) (eraseFG K'))
    (support : ∀ i K s (B : FGBlock (Fin p.n)) sB, SourceBefore p c E rho i K s →
      c₀ ≤ (heightView p K).h → SourceBefore p c E rho i B sB → c₀ ≤ (heightView p B).h →
      sB < s → ¬ Block.Compatible (eraseFG B) (eraseFG K) → ∃ k < i, False)
    {i : Nat} {K K' : FGBlock (Fin p.n)} {s s' : Slot}
    (hK : SourceBefore p c E rho i K s) (hK' : SourceBefore p c E rho i K' s')
    (hc : c₀ ≤ (heightView p K).h) (hc' : c₀ ≤ (heightView p K').h) :
    Block.Compatible (eraseFG K) (eraseFG K') :=
  healing_high_pair_compat p c E rho c₀ (fun _ _ _ => False) same support
    (fun _ _ _ _ h => h) hK hK' hc hc'

-- The descent cause is the pair cause of the first-failure lemma.
example (c₀ : Nat) (Lost : FGBlock (Fin p.n) → Slot → Nat → Prop)
    (same : ∀ i K K' s, SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s →
      c₀ ≤ (heightView p K).h → c₀ ≤ (heightView p K').h →
      Block.Compatible (eraseFG K) (eraseFG K'))
    (support : ∀ i K s B sB, SourceBefore p c E rho i K s → c₀ ≤ (heightView p K).h →
      SourceBefore p c E rho i B sB → c₀ ≤ (heightView p B).h →
      sB < s → ¬ Block.Compatible (eraseFG B) (eraseFG K) → ∃ k < i, Lost B sB k)
    (loss : ∀ k K s, Lost K s k → c₀ ≤ (heightView p K).h ∧ SourceBefore p c E rho k K s ∧
      ∃ x X, KeepOrCause p c E rho k x X K ∧ ¬ Kept p c E rho k x X K) :
    ∀ k K s, ¬ Lost K s k := by
  refine (healing_high_source_first_failure p c E rho c₀ Lost same support ?_).1
  intro k K s _ hL
  obtain ⟨hc, hsrc, x, X, hk, hn⟩ := loss k K s hL
  rcases healing_descent_pair p c E rho hsrc hc hk with hkept | hpair
  · exact absurd hkept hn
  · exact hpair

-- D4: the finality source is no later than the read event.
example (hs : V2.D.ScheduleWellFormed E rho) (origin : RQCOrigin p c E rho)
    {i : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x t))
    (hF : (storeAt p c E rho i x).fg.F ≠ .genesis) :
    ∃ K s, SourceBefore p c E rho i K s ∧
      FGBlock.Preceq (storeAt p c E rho i x).fg.F K ∧ SA.gateTime p.toParams s ≤ t := by
  obtain ⟨-, -, -, K, s, hK, -, hT, ht⟩ :=
    healing_finality_source (hroots := hroots) p c E rho hs origin hx hF
  have he := (fgCertificateLaws p).height.entry_preceq K
  rw [hT] at he
  exact ⟨K, s, hK, he, ht _ hi⟩

end AvailableChain.FGSA.Run.Tests.HealingDescent
end
