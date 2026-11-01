module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetKeep -- shake: keep (J3 fixtures)

set_option linter.privateModule false

/-! Blueprint 21 H.14:2815–2884; plan J3; B1/B13/B15/B17/B18.
Each fixture has a pure/model or conditional package label.
The TDel fixture consumes the discharged admission conclusion. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetKeep
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

-- pure/model: the empty cut has no protected read.
example (w : HealingWitness) : PostResetProtectedKept p c E rho w 0 := by
  rw [PostResetProtectedKept_def]
  intro j hj
  exact False.elim (Nat.not_lt_zero j hj)

private def DeliveryServices : Prop :=
  ∀ y r K, y ∈ rho.honest →
    actionSourceFG p c E rho y r = some (some K) →
    recoveryStart p E ≤ SA.voteTime p.toParams (r * p.R) →
    SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon →
    ∀ x ∈ rho.honest, FGBlock.Preceq
      (rho.stateBeforeTime E (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F K →
    ∀ j z W, z ∈ rho.honest →
    rho.events[j]? = some (.tick z (SA.voteTime p.toParams (r * p.R))) →
    W ∈ (storeAt p c E rho j z).fg.TF →
    FGBlock.Preceq K W →
    FGBlock.Preceq
      (rho.stateBeforeTime E (SA.earlyTime p.toParams (r * p.R)) x).st.fg.F W →
    TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams (r * p.R)) x

-- conditional package: consume the A wrapper's conclusion for the source body itself.
example [Fintype V] {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (hServices : DeliveryServices p c E rho)
    (origin : RQCOrigin p c E rho) (source : TSrc p c E rho) {w : HealingWitness}
    (lowFinality : ∀ {j : Nat} {x : V} {D : FGBlock (Fin p.n)}, x ∈ rho.honest →
      afterTicksIdx rho (p.actionTime w.rStar) ≤ j →
      D ∈ (storeAt p c E rho j x).fg.TF →
      (finalityView p D).F = (storeAt p c E rho j x).fg.F →
      (finalityView p D).h_F ≤ w.M → Block.Preceq (F_at p c E rho j x) w.CStar)
    (highCompat : ∀ j, PostResetHighCompatible p c E rho w j)
    (resetCompat : ∀ j, PostResetResetCompatible p c E rho w j)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (h0r : H0Reset p c E rho w)
    {y x : V} {r l : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hsrc : actionSourceFG p c E rho y r = some (some K))
    (hK : SourceBefore p c E rho l K (r * p.R)) (hhK : high p w K)
    (hhor : SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon) (hx : x ∈ rho.honest) :
    Gen.V2.Duty.HoldsBefore E rho (fun nd =>
      K ∈ nd.st.fg.TF ∨ FGBlock.Preceq K nd.st.fg.F)
      (SA.freezeTime p.toParams (r * p.R)) x := by
  have h := postReset_tDel p c E rho mono origin lowFinality highCompat resetCompat
    hrec source hServices emittedNonempty emittedName h0r hy hsrc hK hhK hhor hx
  rw [Gen.V2.Duty.HoldsBefore_def] at h ⊢
  exact h.imp (fun path => path K (KitFG.preceq_refl K)) id

section Consumers
variable (hs : V2.D.ScheduleWellFormed E rho)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (htransfer : ResetTransferCore p c E rho w)
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {x : V} {X : Finset (FGBlock (Fin p.n))} {C B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF)
    (htick : ∃ t, rho.events[i]? = some (.tick x t) ∧ SA.releaseTime p.toParams w.sStar ≤ t)
    (hC : C ∈ X) (he : eraseFG C = w.CStar)
    (cover : ∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X)
    (hreset : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG K) w.CStar)
    (hhigh : ∀ K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K'))
    (path : ∀ A, FGBlock.Preceq A B → A ∈ X)
    (hBC : Block.Compatible (eraseFG B) w.CStar)
    (hBK : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K))

-- conditional package, anti-vacuity: consume the successor at the new tick i,
-- with a reset copy in X and a protected body whose complete path is in X.
example {s : Slot} (hprotected : ProtectedBody p c E rho w B s) :
    w.M + 1 ≤ (storeAt p c E rho i x).fg.h_max ∧ Kept p c E rho i x X B := by
  have h := postReset_protected_kept_succ (hroots := hroots) p c E rho hs xing origin h0r
      htransfer hinv
  rw [PostResetProtectedKept_def] at h
  obtain ⟨hh, _, _, _, _, hk⟩ :=
    h i (Nat.lt_succ_self i) x X C hx hX htick hC he cover hreset hhigh
  exact ⟨hh, hk B s hprotected path hBC hBK⟩

-- conditional package: the general clause also consumes a body outside ProtectedBody.
example (_houtside : ∀ s, ¬ ProtectedBody p c E rho w B s) : Kept p c E rho i x X B :=
  postReset_general_kept (hroots := hroots) p c E rho xing origin h0r hinv hx hX hC he cover
      path hBC hBK

-- conditional package: consume the internal RKeep body's unrestricted last clause.
example (inv : ∀ j, PostResetInv p c E rho w j) : Kept p c E rho i x X B := by
  obtain ⟨_, _, _, _, _, hk⟩ := postReset_rKeep_body (hroots := hroots) p c E rho xing origin
      h0r inv
    i x X C hx hX htick hC he cover hreset hhigh
  exact hk B path hBC hBK

end Consumers
end AvailableChain.FGSA.Run.Tests.HealingPostResetKeep
end
