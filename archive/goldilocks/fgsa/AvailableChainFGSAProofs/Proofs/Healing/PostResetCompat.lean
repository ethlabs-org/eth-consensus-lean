module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossCause

public section

/-! Blueprint 21 H.13:2668–2813, H.14:2815–2830; plan J2 and
"Induction design"; B1/B13/B15/B17/B18. Compatibility fields at each
prefix and the restricted descent projection for J3/H.14.
DC: SAME high-source compatibility; INTENTIONAL FJ descent causes. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

section Compatibility
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (hScopes : LossServiceScope p c E rho)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec hScopes mono emittedNonempty emittedName writes xing origin h0r

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2668–2674; plan J2 A; B1/B13/B15/B17.
DC: SAME high-source compatibility. The reset bound μ ≤ M makes the
existing H.13 theorem apply at every event-prefix cut. -/
theorem postReset_high_compatible_all (i : Nat) :
    PostResetHighCompatible p c E rho w i := by
  rw [PostResetHighCompatible_def]
  exact healing_high_source_compat_reset p c E rho hrec hScopes mono emittedNonempty emittedName
    writes xing origin h0r i

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2668–2674; plan J2 A, carrier high_compatible;
B1/B13/B15/B17. DC: SAME compatibility. The all-cut result supplies the
successor field; no other field of the prior record is needed. -/
theorem postReset_high_compatible_succ {i : Nat} (_hinv : PostResetInv p c E rho w i) :
    PostResetHighCompatible p c E rho w (i + 1) :=
  postReset_high_compatible_all p c E rho hrec hScopes mono emittedNonempty emittedName
    writes xing origin h0r (i + 1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2668–2674, H.14:2815–2830; plan J2 B;
B1/B13/B15/B17. DC: SAME reset source at height M + 1. Use a larger
cut that contains both rows, even when the reset row is not before i. -/
theorem postReset_reset_compatible_all (i : Nat) :
    PostResetResetCompatible p c E rho w i := by
  rw [PostResetResetCompatible_def]
  intro K s hK hhK
  obtain ⟨j, y, a, C, hrow, -, hsrc, he, hh⟩ := h0r.fresh
  have hC : SourceBefore p c E rho (max i (j + 1)) C w.sStar :=
    ⟨j, y, w.rStar, a, lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _),
      hrow, hsrc, h0r.label⟩
  obtain ⟨k, z, r, b, hk, hb, hsrcK, hs⟩ := hK
  have hK' : SourceBefore p c E rho (max i (j + 1)) K s :=
    ⟨k, z, r, b, lt_of_lt_of_le hk (le_max_left _ _), hb, hsrcK, hs⟩
  have hhC : high p w C := by rw [high_def, hh]
  have hcompat := postReset_high_compatible_all p c E rho hrec hScopes mono emittedNonempty
    emittedName writes xing origin h0r (max i (j + 1))
  rw [PostResetHighCompatible_def] at hcompat
  simpa only [he] using hcompat C K w.sStar s hC hK' hhC hhK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2668–2674, H.14:2815–2830; plan J2 B, carrier
reset_compatible; B1/B13/B15/B17. DC: SAME reset compatibility.
The all-cut result supplies this separate successor field. -/
theorem postReset_reset_compatible_succ {i : Nat} (_hinv : PostResetInv p c E rho w i) :
    PostResetResetCompatible p c E rho w (i + 1) :=
  postReset_reset_compatible_all p c E rho hrec hScopes mono emittedNonempty emittedName
    writes xing origin h0r (i + 1)

end Compatibility

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.13:2785–2813, H.14:2815–2830; plan J2 C;
B1/B13/B15/B17/B18. DC: INTENTIONAL FJ single-source and pair causes.
J3/H.14 uses this restricted descent in the duty's own covered view.
The carrier excludes both causes for a high source or a high copy of C*. -/
theorem postReset_descent_kept (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} {i : Nat} (hinv : PostResetInv p c E rho w i)
    {x : V} {X : Finset (FGBlock (Fin p.n))} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF) (hC : C ∈ X)
    (hhC : high p w C)
    (hsource : (∃ s, SourceBefore p c E rho i C s) ∨ eraseFG C = w.CStar)
    (cover : ∀ K s, SourceBefore p c E rho i K s →
      FGBlock.Preceq (storeAt p c E rho i x).fg.F K → FGBlock.Preceq C K →
      (heightView p C).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho i x).fg.F)
    (hroots : NamedRootCollisionFree p c E rho) :
    Kept p c E rho i x X C := by
  have hhigh := hinv.high_compatible
  have hreset := hinv.reset_compatible
  rw [PostResetHighCompatible_def] at hhigh
  rw [PostResetResetCompatible_def] at hreset
  rcases healing_descent (hroots := hroots) p c E rho xing origin hx hX hC cover with
    hk | ⟨K, s, hK, hn, hh⟩ | ⟨K, K', s, s', hK, hK', hh, hlt, hr⟩
  · exact hk
  · have hhK : high p w K := by
      rw [high_def] at hhC ⊢
      exact hhC.trans hh
    apply False.elim
    apply hn
    rcases hsource with ⟨sC, hsrcC⟩ | he
    · exact hhigh C K sC s hsrcC hK hhC hhK
    · rw [he]
      exact hreset K s hK hhK
  · have hhK : high p w K := by
      rw [high_def] at hhC ⊢
      exact hhC.trans (Nat.le_of_lt hlt)
    have hhK' : high p w K' := by
      rw [high_def] at hhK ⊢
      rwa [← hh]
    exact False.elim (healing_entry_pair_incompatible p hh hr
      (hhigh K K' s s' hK hK' hhK hhK'))

end AvailableChain.FGSA.Run
end
