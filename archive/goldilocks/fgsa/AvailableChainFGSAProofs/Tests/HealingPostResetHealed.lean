module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetHealed -- shake: keep (J7 fixtures)

set_option linter.privateModule false

/-! Blueprint 21 H.18:3049–3103; plan J7 T. DC: SAME conditional applications.
D tests stable and cross-node finality clauses, then the full H4 producer. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetHealed

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:3373–3374; plan J7 T/A. DC: SAME derived source prefix.
Named TCarrier producer: J3 rest. -/
example {w : HealingWitness} (carrier : TCarrier p c E rho w)
    (reset : H0Reset p c E rho w) (start : PostResetStart p c E rho w) :
    Block.Preceq w.CStar w.QStar :=
  healing_sourcePrefix p c E rho carrier reset start

/-- Blueprint 21:3097–3100; plan J7 T/B. DC: SAME first proposal and deadline. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (reset : H0Reset p c E rho w)
    (horizon : p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon) :
    ∃ u Q, PostResetStart p c E rho {w with u := u, QStar := Q} ∧
      tstar p {w with u := u, QStar := Q} ≤
        p.actionTime w.rStar + Γ p G + 4 * p.Δ :=
  healing_firstProposal p c E rho rec reset horizon

/-- Blueprint 21:3371–3374; plan J7 T/C. DC: SAME reset data in the new H0 witness.
Named TCarrier producer: J3 rest. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (carrier : TCarrier p c E rho w) (reset : H0Reset p c E rho w)
    (horizon : p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon) :
    ∃ w', H0 p c E rho w' ∧ w'.rG = w.rG ∧ w'.u₀ = w.u₀ ∧ w'.M = w.M ∧
      w'.rStar = w.rStar ∧ w'.sStar = w.sStar ∧ w'.CStar = w.CStar ∧
      tstar p w' ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  obtain ⟨u, Q, h0, htime⟩ := healing_h0_of p c E rho rec carrier reset horizon
  exact ⟨{w with u := u, QStar := Q}, h0, rfl, rfl, rfl, rfl, rfl, rfl, htime⟩

/-- Blueprint 21:3061; plan J7 T/D. DC: SAME stable output at tstar.
Named H3 producer: J6-3 PostResetService/opening_domain. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (start : PostResetStart p c E rho w)
    (service : H3 p c E rho w) (horizon : tstar p w ≤ rho.horizon) :
    ∀ x ∈ rho.honest,
      (fgsaInterface p c).stable (afterTicks E rho (tstar p w) x) = w.QStar :=
  healing_h4_stable p c E rho rec start service horizon

/-- Blueprint 21:3061; plan J7 T/D. DC: SAME named carrier cut.
Named PostResetService producer: J6-3/opening_domain. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (start : PostResetStart p c E rho w)
    (service : PostResetService p c E rho w rho.events.length)
    (horizon : tstar p w ≤ rho.horizon) :
    ∀ x ∈ rho.honest,
      (fgsaInterface p c).stable (afterTicks E rho (tstar p w) x) = w.QStar :=
  healing_h4_stable_of_service p c E rho rec start service horizon

/-- Blueprint 21:3076–3093; plan J7 T/D. DC: SAME cross-node coverage at any suffix read.
Named H2A producer: J3 rest. Named PostResetInv producer: the joint induction
PostResetInv ∧ ResetLeaseCompatible ∧ OpeningDomain. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (start : PostResetStart p c E rho w) (h2A : H2A p c E rho w)
    (inv : ∀ i, PostResetInv p c E rho w i) (horizon : tstar p w ≤ rho.horizon)
    (i : Nat) (x y : V) (suffix : HealSuffix p c rho (tstar p w) i)
    (hx : x ∈ rho.honest) (hy : confirmedReaderIdx p c E rho y i) :
    Block.Preceq (F_at p c E rho i x) (S_at p c E rho i y) :=
  healing_h4_crossBelow p c E rho rec start h2A inv horizon i x y suffix hx hy

/-- Blueprint 21:3097–3101; plan J7 T/E. DC: SAME H4 plus later proposal service.
Named H3 producer: J6-3 PostResetService/opening_domain; H4 producer: J7 D. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (start : PostResetStart p c E rho w)
    (h4 : H4 p c E rho w) (h3 : H3 p c E rho w) : Healed p c E rho (tstar p w) :=
  healing_healed p c E rho rec start h4 h3

/-- Blueprint 21:3097–3101; plan J7 T/E. DC: SAME service at a later proposal's gate.
Named H3 producer: J6-3 PostResetService/opening_domain; H4 producer: J7 D. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (start : PostResetStart p c E rho w)
    (h4 : H4 p c E rho w) (h3 : H3 p c E rho w) (s : Slot) (B : Block)
    (later : tstar p w ≤ V2.D.proposalTime (fgsaInterface p c) s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon)
    (proposal : HonestProposal E rho (fgsaInterface p c) s B) :
    ∀ x, confirmedReader p c E rho x (SA.gateTime p.toParams s) → Block.Preceq B
      ((fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams s) x)) := by
  intro x hx
  exact (healing_healed p c E rho rec start h4 h3).2.2.2 s B later horizon proposal _ x rfl hx

/-- Blueprint 21:3049–3095; plan J7 T/D–E. DC: SAME full H4 and HEALED from named fields.
Named H2A producer: J3 rest; H3/PostResetService/opening_domain: J6-3;
H5RawTransfer: J5-A; PostResetInv: the joint induction
PostResetInv ∧ ResetLeaseCompatible ∧ OpeningDomain. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF)
    {w : HealingWitness} (start : PostResetStart p c E rho w) (h2A : H2A p c E rho w)
    (h3 : H3 p c E rho w) (h5 : H5RawTransfer p c E rho w)
    (inv : ∀ i, PostResetInv p c E rho w i) (horizon : tstar p w ≤ rho.horizon)
    (readers : ∀ i x, HealSuffix p c rho (tstar p w) i → x ∈ rho.honest →
      confirmedReaderIdx p c E rho x i) :
    H4 p c E rho w ∧ Healed p c E rho (tstar p w) := by
  have h4 := healing_h4 p c E rho rec start h2A h3 h5 inv horizon readers
  exact ⟨h4, healing_healed p c E rho rec start h4 h3⟩

/-- Blueprint 21:3057–3059,3097–3100; plan J7 T/B. DC: SAME Δ=1, R=3 grid.
This local arithmetic fixture imports no NonVacuity module. -/
private def arithmeticParams : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩,
    3, 6, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩

/-- Blueprint 21:3057–3059,3097–3100; plan J7 T/B. DC: SAME first-slot arithmetic.
For s*=9 and u=11: t_10=40 < t_11=44 ≤ 44 and d_11=50=a_3+Γ+4Δ. -/
example :
    SA.proposalTime arithmeticParams.toParams 10 = 40 ∧
    SA.proposalTime arithmeticParams.toParams 10 < SA.proposalTime arithmeticParams.toParams 11 ∧
    SA.proposalTime arithmeticParams.toParams 11 ≤
      SA.proposalTime arithmeticParams.toParams 10 + Γ arithmeticParams 4 ∧
    SA.gateTime arithmeticParams.toParams 11 = 50 ∧
    SA.gateTime arithmeticParams.toParams 11 =
      SA.releaseTime arithmeticParams.toParams 9 + Γ arithmeticParams 4 +
        5 * arithmeticParams.Δ ∧
    SA.gateTime arithmeticParams.toParams 11 =
      arithmeticParams.actionTime 3 + Γ arithmeticParams 4 + 4 * arithmeticParams.Δ := by
  decide

/-- Blueprint 21:3097–3100; plan J7 B, ∀-w form. DC: SAME J10 timeBound field shape.
Named ResetArrivalStatement producer: J8 H-RESET. -/
example (G ΔF : Time) (hReset : ResetArrivalStatement p G ΔF) :
    p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ :=
  healing_timeBound_of_resetArrival p G ΔF hReset

/-- Blueprint 21:3097–3100; plan J7 B. DC: SAME every full witness meets the deadline. -/
example [Fintype V] {G ΔF : Time} (rec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness}
    (h0 : H0 p c E rho w) (horizon : p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon) :
    tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ :=
  healing_tstar_le_of_h0 p c E rho rec h0 horizon

end AvailableChain.FGSA.Run.Tests.HealingPostResetHealed
end
