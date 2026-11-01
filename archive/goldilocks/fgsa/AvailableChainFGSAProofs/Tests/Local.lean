module
public import AvailableChainFGSAProofs.Proofs.Finality.Local -- shake: keep (examples)

public section

namespace AvailableChain.FGSA.Run.Tests.Local
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Pure/model, paper 22:1395–1400; firstfin plan §5 tests.
DC: INTENTIONAL g=1, κ=R and exact horizon equality. Equal-opening and
just-after-opening triggers use the same full guard. This is not a run. -/
example (t : Time) (ht : t = 8 ∨ t = 9) :
    ∃ q r : Nat, t ≤ (q : Time) * 8 ∧ (q : Time) * 8 < t + 8 ∧
      Gen.Pure.InWindow q 1 r ∧ Gen.Pure.FGoodE_W (fun _ => True) 2 2 r := by
  have hrec : Gen.Pure.RecFE_W (fun _ => True) 2 2 8 1 8 0 (t + 33) 1 := by
    refine ⟨by decide, ?_⟩
    intro q _ _ _
    refine ⟨q, ⟨le_rfl, by omega⟩, trivial, trivial, ?_, trivial⟩
    exact ⟨(q + 2) * 2, by omega, le_rfl, trivial⟩
  have htpos : (0 : Time) < t := by
    rcases ht with h | h <;> rw [h] <;> decide
  have hguard : t + ((1 : Time) + 2) * 8 + 8 + 1 ≤ t + 33 := le_of_eq (by ring)
  exact Gen.Pure.recFE_W_extract (t := t) hrec (by decide) htpos htpos.le hguard

/-- Pure/model, paper 22:1395–1400; firstfin plan §5 tests.
DC: INTENTIONAL a non-earliest FE carrier and a separate F4 sample. -/
example : Gen.Pure.FGoodE_W (fun s => s ∈ ([4, 8, 11, 14] : List Nat)) 4 2 1 ∧
    ¬ Gen.Pure.FGood4_W (fun s => s ∈ ([4, 8, 11, 14] : List Nat)) 4 2 1 := by
  constructor
  · refine ⟨by decide, by decide, ⟨11, by decide, by decide, by decide⟩, by decide⟩
  · intro h
    exact (by decide : ¬ ((8 + 2 : Nat) ∈ [4, 8, 11, 14])) h.2

/-- Pure/model, paper 22:1395–1400; firstfin plan §5 tests.
DC: INTENTIONAL Δ=1, ΔF=3>2Δ, κ=3<R=4, β=12 and a full receipt tail.
The guard admits horizon equality; this fixture is not a run. -/
example :
    ∃ q r : Nat, (17 : Time) ≤ (q : Time) * 16 ∧ (q : Time) * 16 < 17 + 16 ∧
      Gen.Pure.InWindow q 1 r ∧ Gen.Pure.FGoodE_W (fun _ => True) 4 3 r := by
  have hrec : Gen.Pure.RecFE_W (fun _ => True) 4 3 16 1 12 0 78 1 := by
    refine ⟨by decide, ?_⟩
    intro q _ _ _
    refine ⟨q, ⟨le_rfl, by omega⟩, trivial, trivial, ?_, trivial⟩
    exact ⟨(q + 2) * 4, by omega, le_rfl, trivial⟩
  exact Gen.Pure.recFE_W_extract (t := 17) hrec (by decide) (by decide) (by decide) (by decide)

/-- Pure/model, paper 22:1377–1380; firstfin plan §5 tests.
DC: SAME event cut order. A same-time delivery at t precedes a later gate,
but a delivery exactly at D does not meet the strict-before cutoff. -/
example (t a D : Time) (hta : t < a) :
    toLex (t, (2 : Nat)) < toLex (a, 1) ∧ ¬ D < D := by
  exact ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inl hta), lt_irrefl D⟩

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {g : Nat} {w : HealingWitness} {t : Time}

/-- Conditional package, paper 22:1371–1400; firstfin plan §5 tests.
DC: INTENTIONAL actual opening. With no proposal the kernel is vacuous,
but the forward output is false. This is not a complete execution. -/
example (hnone : ∀ r A,
    ¬ HonestProposal E rho (fgsaInterface p c) (r * p.R) A) :
    (∀ r, KernelConclusion_W p c E rho ΔF r) ∧
      ¬ ForwardWitness_W p c E rho ΔF g w t := by
  constructor
  · intro r A hA
    exact False.elim (hnone r A hA)
  · intro hf
    rw [ForwardWitness_W_def] at hf
    obtain ⟨_, r, A, _, _, _, _, _, _, _, _, _, hA, _⟩ := hf
    exact hnone r A hA

/-- Conditional package, paper 22:1371–1380; firstfin plan §5 tests.
DC: INTENTIONAL trigger t=tstar; the two output bounds remain per node.
No common honest F state is a premise. This is not a complete execution. -/
example {G : Time}
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho ⟨tstar p w⟩)
    (hf : ForwardWitness_W p c E rho ΔF g w (tstar p w)) :
    ∃ U : FGBlock (Fin p.n), ∀ x ∈ rho.honest,
      Block.Prec (V2.D.Run.readAt E rho (tstar p w) x).st.base.stableRecord (eraseFG U) := by
  obtain ⟨U, hs, _, _⟩ := finality_liveness_of_forward_W p c E rho h hf
  exact ⟨U, hs⟩

/-- Conditional package, paper 22:1371–1380; firstfin plan §5 tests.
DC: INTENTIONAL two accepted carriers of current genesis, with certificate
heights 0 and 1. Both are bounded; this is not a complete execution. -/
example {G : Time} {pt : PtT}
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt)
    (hf : ForwardWitness_W p c E rho ΔF g w pt.t) (x : V) (hx : x ∈ rho.honest)
    (K₀ K₁ : FGBlock (Fin p.n))
    (hK₀ : K₀ ∈ (V2.D.Run.readAt E rho pt.t x).st.fg.TF)
    (hK₁ : K₁ ∈ (V2.D.Run.readAt E rho pt.t x).st.fg.TF)
    (hgen : (V2.D.Run.readAt E rho pt.t x).st.fg.F = .genesis)
    (hF₀ : (finalityView p K₀).F = .genesis)
    (hF₁ : (finalityView p K₁).F = .genesis)
    (hh₀ : (finalityView p K₀).h_F = 0) (hh₁ : (finalityView p K₁).h_F = 1) :
    ∃ U : FGBlock (Fin p.n), 0 < (heightView p U).h ∧ 1 < (heightView p U).h := by
  obtain ⟨U, _, hc, _⟩ := finality_liveness_of_forward_W p c E rho h hf
  have h₀ := hc x hx K₀ hK₀ (hF₀.trans hgen.symm)
  have h₁ := hc x hx K₁ hK₁ (hF₁.trans hgen.symm)
  rw [hh₀] at h₀
  rw [hh₁] at h₁
  exact ⟨U, h₀, h₁⟩

/-- Conditional package, paper 22:1371–1380; firstfin plan §5 tests.
DC: INTENTIONAL nonidentical honest F values. Both nodes share strict output
extension without sharing F. This is not a complete execution. -/
example {G : Time} {pt : PtT}
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt)
    (hf : ForwardWitness_W p c E rho ΔF g w pt.t)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hne : (V2.D.Run.readAt E rho pt.t x).st.fg.F ≠
      (V2.D.Run.readAt E rho pt.t y).st.fg.F) :
    (V2.D.Run.readAt E rho pt.t x).st.fg.F ≠ (V2.D.Run.readAt E rho pt.t y).st.fg.F ∧
      ∃ U : FGBlock (Fin p.n),
        Block.Prec (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord (eraseFG U) ∧
        Block.Prec (V2.D.Run.readAt E rho pt.t y).st.base.stableRecord (eraseFG U) := by
  obtain ⟨U, hs, _, _⟩ := finality_liveness_of_forward_W p c E rho h hf
  exact ⟨hne, U, hs x hx, hs y hy⟩

end AvailableChain.FGSA.Run.Tests.Local
end
