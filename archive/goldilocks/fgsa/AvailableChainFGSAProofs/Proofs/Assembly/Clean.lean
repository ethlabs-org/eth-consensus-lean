module
public import AvailableChainFGSAProofs.Proofs.Clean.Export -- shake: keep (L42 export boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (L42 positive-cut foundation exports)
public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep (Clean claim implications)
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes -- shake: keep (positive-cut quorum producer)

public section

/-! Clean claim assembly through the L42 lane export boundary. -/

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

variable (p : Params)

/-- P3 §§4.7, 8.5, SYN L39; DC Legacy/Definitions/SafetyRegimes:53–80
and Generic/Conditions:134. INTENTIONAL difference: FG-SA has a finite
inclusive cut and strict-before-cut participation. Only a positive cut
supplies quorum for the two F1 channels. Both branches use the sleep prefix
from CleanCutPrem.set. Assembly makes the single cut split.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_cleanCutClaim : CleanCutClaim p := by
  intro V _ _ In c E rho ΔF pt hc
  have hnonneg : 0 ≤ pt.b₀ := hc.set.cut.1
  by_cases hz : pt.b₀ = 0
  · cases pt with
    | mk b₀ =>
      change b₀ = 0 at hz
      subst b₀
      exact cleanCutZero_export p c E rho hc
  · have hb : 0 < pt.b₀ := lt_of_le_of_ne hnonneg (Ne.symm hz)
    have hq := hc.set.faultQ_of_pos hb
    have hsource : SourceDisciplinePrem p c E rho () := ⟨hc.set.base, hq⟩
    exact cleanCutPos_export p c E rho pt hc hb
      (fgsa_fgFoundationClaim p c E rho () hsource)
      (fgsa_srcFrameAboveClaim p c E rho () hsource)

/-- P3 §4.7 (OD16), bp02 §§5.4–6; DC Legacy/Definitions/SafetyRegimes:53–80.
INTENTIONAL difference: finite inclusive event history. The frozen
CleanPrefixPrem supplies its joined sleep prefix. -/
theorem fgsa_cleanHistoryClaim : CleanHistoryClaim p :=
  cleanHistory_of_cut (fgsa_cleanCutClaim p)

/-- P3 §4.7 (OD16), bp02 §6; DC Legacy/Definitions/SafetyRegimes:53–80.
INTENTIONAL difference: FG-SA truncation includes finite event states and
public reads at confirmed readers. -/
theorem fgsa_cleanPrefixTruncationClaim : CleanPrefixTruncationClaim p :=
  cleanPrefixTruncation_of_cut (fgsa_cleanCutClaim p)

/-- The Clean sleep cut produces the state pair before reader restriction. -/
theorem assembly_clean_state
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (h : CleanSet p c E rho ΔF) :
    Gen.Pure.CompatOn (· ∈ rho.honest) (S_at p c E rho)
        (· ≤ timeIdx rho rho.horizon) ∧
      Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho)
        (· ≤ timeIdx rho rho.horizon) := by
  have hc := h.sleepPre.sleepPre
  have hq := h.pre.faultQ
  have hsource : SourceDisciplinePrem p c E rho () := ⟨hc.base, hq⟩
  have hf := fgsa_fgFoundationClaim p c E rho () hsource
  have hf' : FGFoundation p c E rho :=
    ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩
  have hsrc := fgsa_srcFrameAboveClaim p c E rho () hsource
  refine ⟨clean_sCompatible p c E rho hc hq hf' hsrc, ?_⟩
  intro i j x _ hj hij _
  exact sExtends p c E rho hc hq hf' hsrc x i j hij hj

/-- P3 §8.5, bp02 §6, S3 D43/D61; DC Generic/Properties:27,41,48 and
Generic/Interface:64. Safety has the same meaning. INTENTIONAL difference:
one generic property kernel covers all integer reads of the two S outputs.
CleanPrem supplies the sleep regime and the all-node state pair. -/
theorem fgsa_cleanSafetyClaim : CleanSafetyClaim p :=
  cleanSafety_of_cut p (fgsa_cleanCutClaim p) (assembly_clean_state p)

/-- bp02 §6, S3 D43/D61; DC Generic/Properties:27,41,48 and Interface:64.
INTENTIONAL difference: stable and confirmed both read S at all integer
times at confirmed readers.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_cleanSafety_outputs
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {pt : Unit}
    (hc : CleanPrem p c E rho pt ΔF) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedCompat (confirmedReader p c E rho)
        (fun t x => V2.D.outputAt E rho g x t) (fun _ => True) ∧
      ScopedMono (confirmedReader p c E rho)
        (fun t x => V2.D.outputAt E rho g x t) (fun _ => True) :=
  cleanSafety_outputs (fgsa_cleanSafetyClaim p) hc


end AvailableChain.FGSA.Run
end
