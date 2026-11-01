module
public import AvailableChainFGSAClaims.Claims.Clean
public import AvailableChainFGSAProofs.Proofs.Clean.Zero
public import AvailableChainFGSAProofs.Proofs.Clean.Safety
public import AvailableChainFGSAProofs.Proofs.Clean.Closure
public import AvailableChainFGSAProofs.Proofs.Clean.EpochSaved -- shake: keep (facade coverage)
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- P10/P11: at the zero cut there is no gate origin in any epoch.
The base supplies the exact positive wake-restart law; no NoRestart is used. -/
theorem cleanHistoryAt_zero (h : HealthyPrefix₂ p c E rho 0 ΔF) :
    CleanHistoryAt p c E rho 0 := by
  have hh := (cleanCut_zero_body h).1
  refine ⟨?_, ?_, ?_, ?_, hh.2.2.2.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2⟩
  · intro x y r s B C hx hy hr hs _ _ hB hC
    exact hh.1 x y r s B C hx hy hr hs hB hC
  · intro j x s hj hx hg
    exact hh.2.1 j x s hj hx hg.1
  · intro x y s B H hx hy hs hB _ hH
    exact hh.2.2.1 x y s B H hx hy hs hB hH
  · intro i v hi hv
    have hl := hh.2.2.2.1 i v hi hv
    refine ⟨hl.1, hl.2.1, hl.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro row hrow
      obtain ⟨_, j, hj, s, B, hg, _⟩ := hl.2.2.2.1 row hrow
      exact (zero_export_no_gate h (hj.trans_le hi) hg).elim
    · intro s C hC
      obtain ⟨_, j, hj, hg, _⟩ := hl.2.2.2.2.1 s C hC
      exact (zero_export_no_gate h (hj.trans_le hi) hg).elim
    · intro j s C hj hg _ _ hC
      exact hl.2.2.2.2.2.1 j s C hj hg.1 hC
    · intro s X hX
      obtain ⟨_, j, hj, hg, _⟩ := hl.2.2.2.2.2.2.1 s X hX
      exact (zero_export_no_gate h (hj.trans_le hi) hg).elim
    · rcases hl.2.2.2.2.2.2.2 with hz | ⟨j, hj, s, hg, _⟩ | hf
      · exact Or.inl hz
      · exact (zero_export_no_gate h (hj.trans_le hi) hg).elim
      · exact Or.inr (Or.inr hf)

/-- P10: zero-cut public reads and event reads use the approved reader scopes. -/
theorem cleanTruncAt_zero (h : HealthyPrefix₂ p c E rho 0 ΔF) :
    CleanTruncAt p c E rho 0 := by
  have ht := (cleanCut_zero_body h).2
  refine ⟨?_, ?_, ?_, cleanHistoryAt_zero h, ht.2.2.2.2.1, ?_⟩
  · intro i j x y hi hj hx hy
    exact ht.1 i j x y hi hj hx.1.1 hy.1.1
  · intro i j x hi hj hij hx _
    exact ht.2.1 i j x hi hj hij hx.1.1
  · intro g hg
    refine ⟨?_, ?_⟩
    · intro i j x y hi hj hx hy
      exact (ht.2.2.1 g hg).1 i j x y hi hj hx.1 hy.1
    · intro i j x hi hj hij hx _
      exact (ht.2.2.1 g hg).2 i j x hi hj hij hx.1
  · intro l x hl hx _
    have hd := p.deltaPos
    have hn : (0 : Time) ≤ l := Int.natCast_nonneg l
    change 4 * p.Δ * (l : Time) + 6 * p.Δ ≤ 0 at hl
    nlinarith

/-- P10/P11: the zero lane needs no quorum or channel premise. -/
theorem cleanCutZero_export (p : Params) : CleanCutZeroClaim p := by
  intro V _ _ In c E rho ΔF h
  exact ⟨cleanHistoryAt_zero h.set.toHealthyPrefix₂,
    cleanTruncAt_zero h.set.toHealthyPrefix₂⟩

/-- P3 §§4.7, 8.5; bp02 §§5.4–6. Class B. DC counterparts:
Legacy/Definitions/SafetyRegimes:53–80 and Protocol/Grades/JointHistoryGapsIdx:26,141.
INTENTIONAL divergence: FG-SA uses raw SA results, exact lease/saved/fast-write
origins, and a finite inclusive event cut. This wrapper restores the frozen
Claims conclusion. The sleep cut supplies joined participation and the wake-restart law.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanHistoryAt (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {b₀ : Time} (h : CleanCutSet p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    CleanHistoryAt p c E rho b₀ := by
  exact cleanHistoryAt_body p c E rho h hq hf hsrc

/-- P3 §8.5, bp02 §6; DC Generic/Properties:27,41,48 and Generic/Interface:64.
Compatibility and monotonicity have the same meaning. INTENTIONAL
representation and domain divergence: both getters read S, and each
finite read index is at most the event count at all integer times
(S3 D43/D61). No restart, quorum, channel, or extra honesty premise is used.
The input is the all-node state pair produced before reader restriction. -/
theorem cleanSafetyAt_of_trunc (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (ht : Gen.Pure.CompatOn (· ∈ rho.honest) (S_at p c E rho)
        (· ≤ timeIdx rho rho.horizon) ∧
      Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho)
        (· ≤ timeIdx rho rho.horizon)) : CleanSafetyAt p c E rho := by
  exact cleanSafety_of_trunc_body p c E rho hs ht

/-- P3:3331–3335, bp02 §5.5; DC Legacy/Definitions/SafetyRegimes:61–75.
INTENTIONAL difference: raw SA results, a whole-result guard, and the cut
before same-time deliveries. The sleep cut supplies joined participation and the wake-restart law.
This wrapper restores the exact frozen Claims conclusion.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanGateAt (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {b₀ : Time} (h : CleanCutSet p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    CleanGateAt p c E rho b₀ := by
  exact cleanGateAt_body p c E rho h hq hf hsrc

/-- P3 §8.5, bp02 §§5.4–6; DC Legacy/Definitions/SafetyRegimes:53–80.
INTENTIONAL difference: six finite-cut clauses use raw SA gates and exact
FG-SA state origins. The sleep cut supplies joined participation and the wake-restart law.
This wrapper restores the exact frozen Claims conclusion.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanTruncAt (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {b₀ : Time} (h : CleanCutSet p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    CleanTruncAt p c E rho b₀ := by
  exact cleanTruncAt_body p c E rho h hq hf hsrc

/-- P3:5296–5311, L39; DC Legacy/Definitions/SafetyRegimes:53–80 and
Generic/Conditions:134. INTENTIONAL difference: a positive finite cut
supplies quorum from strict-before-cut participation and takes both F1
channels. The sleep cut supplies joined participation. Assembly owns the cut split.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanCutPos_export (p : Params) : CleanCutPosClaim p := by
  intro V _ _ In c E rho ΔF pt hc hb hf hsrc
  have hq := hc.set.toHealthyPrefix₂.faultQ_of_pos hb
  have hf' : FGFoundation p c E rho :=
    ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩
  exact ⟨cleanHistoryAt p c E rho hc.set hq hf' hsrc,
    cleanTruncAt p c E rho hc.set hq hf' hsrc⟩

/-- P3 §8.5, bp02 §6; DC Generic/Properties:27,41,48 and Interface:64.
INTENTIONAL difference: the Clean core gives safety at every integer read,
since each read index is at most the event count. Assembly supplies its all-node
state pair before reader restriction. Results use confirmed readers under sleep.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanSafety_of_cut (p : Params) (_hcut : CleanCutClaim p)
    (hstate : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      Gen.Pure.CompatOn (· ∈ rho.honest) (S_at p c E rho)
          (· ≤ timeIdx rho rho.horizon) ∧
        Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho)
          (· ≤ timeIdx rho rho.horizon)) : CleanSafetyClaim p := by
  intro V _ _ In c E rho ΔF _ h
  exact cleanSafetyAt_of_trunc p c E rho h.set.pre.base.valid.toScheduleWellFormed
    (hstate c E rho ΔF h.set)

end AvailableChain.FGSA.Run
end
