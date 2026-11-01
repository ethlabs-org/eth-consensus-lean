module
public import AvailableChainFramework.Catalog.Standard
public import AvailableChainFramework.Catalog.Strong

@[expose] public section

/-! The profiles `ac-4.3` and `strong-1` (design §4, profiles), and their
equivalences with the v1 bundles `AvailableChain` and `StrongClaims`. The
equivalence is between claim propositions: for each entry, the claim at the
projection of the shared constant says what one bundle field says.

A regime of a bundle field reads the whole `Constants` argument. The regime
of a claim reads `{ zeroConstants with … }`, with only the fields that it
uses. These are not definitionally equal, so each regime has one adapter
lemma. -/

namespace AvailableChain.Framework.Catalog

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

/-! ### Regime adapters -/

section Adapters

variable {V : Type} [DecidableEq V] [Fintype V] {n : Nat} {P : ProtocolSpec n}
  {E : Env V} {I : Interface P} {rho : Run V P}

/-- The Stable Sleepy regime reads only `η` and `θ`. -/
theorem stableSleepyRegime_iff {C : Constants} {t₀ : Time} :
    StableSleepyRegime P E I C rho t₀ ↔
      StableSleepyRegime P E I { zeroConstants with η := C.η, θ := C.θ } rho t₀ :=
  ⟨fun h => { h with }, fun h => { h with }⟩

/-- The Outage regime reads only `η`, `θ`, `armingLag` and `budget`. -/
theorem outageRegime_iff {C : Constants} {T b₀ b₁ : Time} :
    OutageRegime P E I C rho T b₀ b₁ ↔
      OutageRegime P E I
        { zeroConstants with
          η := C.η, θ := C.θ, armingLag := C.armingLag, budget := C.budget }
        rho T b₀ b₁ :=
  ⟨fun h => { h with }, fun h => { h with }⟩

/-- The Fast Outage regime reads only `η`, `θ`, `fastArmingLag` and `budget`. -/
theorem fastOutageRegime_iff {C : Constants} {T b₀ b₁ : Time} :
    FastOutageRegime P E I C rho T b₀ b₁ ↔
      FastOutageRegime P E I
        { zeroConstants with
          η := C.η, θ := C.θ, fastArmingLag := C.fastArmingLag, budget := C.budget }
        rho T b₀ b₁ :=
  ⟨fun h => { toOutageRegime := { h.toOutageRegime with },
              highParticipation := h.highParticipation },
   fun h => { toOutageRegime := { h.toOutageRegime with },
              highParticipation := h.highParticipation }⟩

/-- The Recovery regime reads only `θrec`, `recoveryFull`, `proposerGap` and
`recoveryBound`. -/
theorem recoveryRegime_iff {C : Constants} :
    RecoveryRegime P E I C rho ↔
      RecoveryRegime P E I
        { zeroConstants with
          θrec := C.θrec, recoveryFull := C.recoveryFull, proposerGap := C.proposerGap,
          recoveryBound := C.recoveryBound } rho :=
  ⟨fun h => { h with }, fun h => { h with }⟩

omit [Fintype V] in
/-- The recovered conclusions read only `D_c` and `D_s`. -/
theorem recoveredAt_iff {C : Constants} {t₀ : Time} :
    RecoveredAt P E I C rho t₀ ↔
      RecoveredAt P E I { zeroConstants with D_c := C.D_c, D_s := C.D_s } rho t₀ :=
  ⟨fun h => { h with }, fun h => { h with }⟩

end Adapters

/-! ### `ac-4.3` -/

/-- The profile `ac-4.3`: the nine claims of the bundle `AvailableChain`, at
the projections of one `Constants`. `valid` is all of `Constants.Valid`, so
the cross-claim condition `fastArmingLag ≤ armingLag` is checked once, here. -/
def ac43 : Profile ClaimDomain.v1 where
  id := `«ac-4.3»
  Shared := Constants
  valid := Constants.Valid
  entries :=
    [⟨safeConfirmed, fun _ => ()⟩, ⟨safeStable, fun _ => ()⟩,
     ⟨prefixOrder, fun _ => ()⟩, ⟨includedConfirmed, fun C => C.D_c⟩,
     ⟨includedStable, fun C => (⟨C.η, C.θ, C.D_s⟩ : EtaConst)⟩,
     ⟨includedStableFast, fun C => C.D_f⟩,
     ⟨persistOutage, fun C => (⟨C.η, C.θ, C.armingLag, C.budget⟩ : OutageConst)⟩,
     ⟨persistOutageFast, fun C => (⟨C.η, C.θ, C.fastArmingLag, C.budget⟩ : OutageConst)⟩,
     ⟨recovered, fun C =>
       (⟨C.θrec, C.recoveryFull, C.proposerGap, C.recoveryBound, C.D_c, C.D_s⟩ :
         RecoveryConst)⟩]

/-- `ac-4.3` is today's bundle (design §4, profiles). -/
theorem ac43_iff (I : Instance) (C : Constants) :
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → AvailableChain I.P E I.iface C) ↔
      ac43.holdsAt I C := by
  constructor
  · intro h
    -- One environment with the instance's Δ gives `C.Valid` (Review Focus 5).
    have hC : C.Valid :=
      (h ⟨Fin 1, inferInstance, inferInstance⟩
        ⟨I.Δ, I.Δ_pos, 0, le_rfl, fun _ _ => true⟩ rfl).constants
    refine ⟨hC, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨trivial, fun W x hx t₀ hr => (h W x.E hx).confirmedSafe x.rho t₀ hr⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨trivial, fun W x hx t₀ hr => (h W x.E hx).stableSafe x.rho t₀ hr⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨trivial, fun W x hx _ _ => (h W x.E hx).nested x.rho⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hC.delays_nonneg.1,
        fun W x hx t₀ hr => (h W x.E hx).confirmedIncluded x.rho t₀ hr⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨⟨hC.eta_nonneg, hC.theta_lower, hC.theta_upper, hC.delays_nonneg.2.1⟩,
        fun W x hx t₀ hr =>
          (h W x.E hx).stableIncluded x.rho t₀ (stableSleepyRegime_iff.2 hr)⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hC.delays_nonneg.2.2,
        fun W x hx t₀ hr => (h W x.E hx).stableIncludedFast x.rho t₀ hr⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨⟨hC.eta_nonneg, hC.theta_lower, hC.theta_upper, hC.armingLag_nonneg,
          hC.budget_nonneg, hC.budget_le_eta⟩,
        fun W x hx p hr =>
          (h W x.E hx).stableResilient x.rho p.1 p.2.1 p.2.2 (outageRegime_iff.2 hr)⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨⟨hC.eta_nonneg, hC.theta_lower, hC.theta_upper, hC.fastArmingLag_nonneg,
          hC.budget_nonneg, hC.budget_le_eta⟩,
        fun W x hx p hr =>
          (h W x.E hx).stableResilientFast x.rho p.1 p.2.1 p.2.2
            (fastOutageRegime_iff.2 hr)⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨⟨hC.thetaRec_lower, hC.thetaRec_upper, hC.proposerGap_pos,
          hC.recoveryBound_nonneg, hC.delays_nonneg.1, hC.delays_nonneg.2.1⟩,
        fun W x hx _ hr =>
          recoveredAt_iff.1 ((h W x.E hx).recovered x.rho (recoveryRegime_iff.2 hr))⟩
    exact absurd he List.not_mem_nil
  · rintro ⟨hC, h⟩ W E hE
    have hsc := (h ⟨safeConfirmed, fun _ => ()⟩ (.head _)).2
    have hss := (h ⟨safeStable, fun _ => ()⟩ (.tail _ (.head _))).2
    have hpo := (h ⟨prefixOrder, fun _ => ()⟩ (.tail _ (.tail _ (.head _)))).2
    have hic := (h ⟨includedConfirmed, fun C => C.D_c⟩
      (.tail _ (.tail _ (.tail _ (.head _))))).2
    have his := (h ⟨includedStable, fun C => (⟨C.η, C.θ, C.D_s⟩ : EtaConst)⟩
      (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))).2
    have hisf := (h ⟨includedStableFast, fun C => C.D_f⟩
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))).2
    have hpe := (h ⟨persistOutage,
        fun C => (⟨C.η, C.θ, C.armingLag, C.budget⟩ : OutageConst)⟩
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))).2
    have hpf := (h ⟨persistOutageFast,
        fun C => (⟨C.η, C.θ, C.fastArmingLag, C.budget⟩ : OutageConst)⟩
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))).2
    have hrc := (h ⟨recovered, fun C =>
        (⟨C.θrec, C.recoveryFull, C.proposerGap, C.recoveryBound, C.D_c, C.D_s⟩ :
          RecoveryConst)⟩
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
        (.head _)))))))))).2
    exact {
      constants := hC
      confirmedSafe := fun rho t₀ hr => hsc W ⟨E, rho⟩ hE t₀ hr
      stableSafe := fun rho t₀ hr => hss W ⟨E, rho⟩ hE t₀ hr
      monotone := fun rho t₀ hr =>
        ⟨(hsc W ⟨E, rho⟩ hE t₀ hr).monotone, (hss W ⟨E, rho⟩ hE t₀ hr).monotone⟩
      nested := fun rho => hpo W ⟨E, rho⟩ hE () trivial
      confirmedIncluded := fun rho t₀ hr => hic W ⟨E, rho⟩ hE t₀ hr
      stableIncluded := fun rho t₀ hr =>
        his W ⟨E, rho⟩ hE t₀ (stableSleepyRegime_iff.1 hr)
      stableIncludedFast := fun rho t₀ hr => hisf W ⟨E, rho⟩ hE t₀ hr
      stableResilient := fun rho T b₀ b₁ hr =>
        hpe W ⟨E, rho⟩ hE (T, b₀, b₁) (outageRegime_iff.1 hr)
      stableResilientFast := fun rho T b₀ b₁ hr =>
        hpf W ⟨E, rho⟩ hE (T, b₀, b₁) (fastOutageRegime_iff.1 hr)
      recovered := fun rho hr =>
        recoveredAt_iff.2 (hrc W ⟨E, rho⟩ hE () (recoveryRegime_iff.1 hr)) }

/-- Review Focus 3: a cross-claim condition of `ac-4.3` is checked once, by
the profile. -/
theorem ac43_valid_cross (C : Constants) (h : ac43.valid C) :
    C.fastArmingLag ≤ C.armingLag := h.fastArmingLag_le

/-! ### `strong-1` -/

/-- The profile `strong-1`: the five claims of the bundle `StrongClaims`, at
the projections of one pair `(C, SC)`. `valid` is `SC.Valid` only, as in the
bundle; the recovery fields of `C` have no condition (see `Catalog/Strong`). -/
def strong1 : Profile ClaimDomain.strong where
  id := `«strong-1»
  Shared := Constants × StrongConstants
  valid := fun C => C.2.Valid
  entries :=
    [⟨strongSafe, fun C => C.2.faultCap⟩,
     ⟨strongIncluded, fun C => (⟨C.2.faultCap, C.2.strongDelay⟩ : StrongIncConst)⟩,
     ⟨strongPersist, fun C => C.2.faultCap⟩,
     ⟨strongRecoveredSafe, fun C =>
       (⟨C.2.faultCap, C.1.θrec, C.1.recoveryFull, C.1.proposerGap, C.1.recoveryBound⟩ :
         StrongRecConst)⟩,
     ⟨strongRecoveredIncluded, fun C =>
       (⟨⟨C.2.faultCap, C.1.θrec, C.1.recoveryFull, C.1.proposerGap, C.1.recoveryBound⟩,
         C.2.strongDelay⟩ : StrongRecIncConst)⟩]

/-- `strong-1` is today's `StrongClaims`. -/
theorem strong1_iff (I : StrongInstance) (C : Constants) (SC : StrongConstants) :
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → StrongClaims I.P E I.sface C SC) ↔
      strong1.holdsAt I (C, SC) := by
  constructor
  · intro h
    -- One environment with the instance's Δ gives `SC.Valid` (Review Focus 5).
    have hSC : SC.Valid :=
      (h ⟨Fin 1, inferInstance, inferInstance⟩
        ⟨I.Δ, I.Δ_pos, 0, le_rfl, fun _ _ => true⟩ rfl).constants
    refine ⟨hSC, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨trivial, fun W x hx t₀ hr => (h W x.E hx).strongSafe x.rho t₀ hr.1 hr.2⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hSC.delay_nonneg, fun W x hx t₀ hr =>
        (h W x.E hx).strongIncluded x.rho t₀ hr.1 hr.2.1 hr.2.2⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨trivial, fun W x hx p hr => (h W x.E hx).strongResilient x.rho p.1 p.2 hr⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨trivial, fun W x hx _ hr =>
        (h W x.E hx).strongRecoveredSafe x.rho (recoveryRegime_iff.2 hr.1) hr.2⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hSC.delay_nonneg, fun W x hx _ hr =>
        (h W x.E hx).strongRecoveredIncluded x.rho (recoveryRegime_iff.2 hr.1) hr.2⟩
    exact absurd he List.not_mem_nil
  · rintro ⟨hSC, h⟩ W E hE
    have hs := (h ⟨strongSafe, fun C => C.2.faultCap⟩ (.head _)).2
    have hi := (h ⟨strongIncluded,
        fun C => (⟨C.2.faultCap, C.2.strongDelay⟩ : StrongIncConst)⟩ (.tail _ (.head _))).2
    have hp := (h ⟨strongPersist, fun C => C.2.faultCap⟩ (.tail _ (.tail _ (.head _)))).2
    have hrs := (h ⟨strongRecoveredSafe, fun C =>
        (⟨C.2.faultCap, C.1.θrec, C.1.recoveryFull, C.1.proposerGap, C.1.recoveryBound⟩ :
          StrongRecConst)⟩
      (.tail _ (.tail _ (.tail _ (.head _))))).2
    have hri := (h ⟨strongRecoveredIncluded, fun C =>
        (⟨⟨C.2.faultCap, C.1.θrec, C.1.recoveryFull, C.1.proposerGap, C.1.recoveryBound⟩,
          C.2.strongDelay⟩ : StrongRecIncConst)⟩
      (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))).2
    exact {
      constants := hSC
      strongSafe := fun rho t₀ hr hf => hs W ⟨E, rho⟩ hE t₀ ⟨hr, hf⟩
      strongIncluded := fun rho t₀ hr hf hfull => hi W ⟨E, rho⟩ hE t₀ ⟨hr, hf, hfull⟩
      strongResilient := fun rho T b₀ hr => hp W ⟨E, rho⟩ hE (T, b₀) hr
      strongRecoveredSafe := fun rho hr hf =>
        hrs W ⟨E, rho⟩ hE () ⟨recoveryRegime_iff.1 hr, hf⟩
      strongRecoveredIncluded := fun rho hr hf =>
        hri W ⟨E, rho⟩ hE () ⟨recoveryRegime_iff.1 hr, hf⟩ }

end AvailableChain.Framework.Catalog

end
