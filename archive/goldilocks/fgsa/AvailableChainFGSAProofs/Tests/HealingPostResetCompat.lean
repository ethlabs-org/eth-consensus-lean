module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat -- shake: keep (J2 fixtures)

set_option linter.privateModule false

/-! Plan J2; blueprint 21 H.13/H.14; B1/B15/B17/B18.
Each fixture has a pure/model or conditional package label.
The reset consumer uses the conclusion with a source in the duty view. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetCompat
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

-- pure/model: the empty event cut has no source pair.
example (w : HealingWitness) : PostResetHighCompatible p c E rho w 0 := by
  rw [PostResetHighCompatible_def]
  intro K K' s s' hK _ _ _
  obtain ⟨j, y, r, a, hj, -⟩ := hK
  exact False.elim (Nat.not_lt_zero j hj)

-- pure/model: the empty event cut has no reset comparison.
example (w : HealingWitness) : PostResetResetCompatible p c E rho w 0 := by
  rw [PostResetResetCompatible_def]
  intro K s hK _
  obtain ⟨j, y, r, a, hj, -⟩ := hK
  exact False.elim (Nat.not_lt_zero j hj)

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
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec hScopes mono emittedNonempty emittedName writes xing origin h0r

-- conditional package: the high field is produced at the successor cut.
example {i : Nat} (hinv : PostResetInv p c E rho w i) :
    PostResetHighCompatible p c E rho w (i + 1) :=
  postReset_high_compatible_succ p c E rho hrec hScopes mono emittedNonempty emittedName
    writes xing origin h0r hinv

-- conditional package, anti-vacuity: consume the successor reset conclusion
-- for a high source held in X and a held copy C of the reset body.
example {i : Nat} (hinv : PostResetInv p c E rho w i)
    {X : Finset (FGBlock (Fin p.n))} {C K : FGBlock (Fin p.n)} {s : Slot}
    (_hC : C ∈ X) (_hK : K ∈ X) (he : eraseFG C = w.CStar)
    (hsrc : SourceBefore p c E rho (i + 1) K s) (hh : high p w K) :
    Block.Compatible (eraseFG C) (eraseFG K) := by
  have h := postReset_reset_compatible_succ p c E rho hrec hScopes mono emittedNonempty
    emittedName writes xing origin h0r hinv
  rw [PostResetResetCompatible_def] at h
  rw [he]
  exact h K s hsrc hh

-- conditional package: reset compatibility has no reset-row-before-i guard.
example (i : Nat) : PostResetResetCompatible p c E rho w i :=
  postReset_reset_compatible_all p c E rho hrec hScopes mono emittedNonempty emittedName
    writes xing origin h0r i

end Compatibility

section Descent
variable (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} {i : Nat} (hinv : PostResetInv p c E rho w i)
    {x : V} {X : Finset (FGBlock (Fin p.n))} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF) (hC : C ∈ X)
    (hhC : high p w C)
    (cover : ∀ K s, SourceBefore p c E rho i K s →
      FGBlock.Preceq (storeAt p c E rho i x).fg.F K → FGBlock.Preceq C K →
      (heightView p C).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho i x).fg.F)

include xing origin hinv hx hX hC hhC cover

-- conditional package: restricted descent keeps a high emitted source.
example {s : Slot} (hsrc : SourceBefore p c E rho i C s) :
    Kept p c E rho i x X C :=
  postReset_descent_kept (hroots := hroots) p c E rho xing origin hinv hx hX hC hhC
    (Or.inl ⟨s, hsrc⟩) cover

-- conditional package: restricted descent keeps a high copy of the reset body.
example (he : eraseFG C = w.CStar) : Kept p c E rho i x X C :=
  postReset_descent_kept (hroots := hroots) p c E rho xing origin hinv hx hX hC hhC (Or.inr he)
      cover

end Descent
end AvailableChain.FGSA.Run.Tests.HealingPostResetCompat
end
