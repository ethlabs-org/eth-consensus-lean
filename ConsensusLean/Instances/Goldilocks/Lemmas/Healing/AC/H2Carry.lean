module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay

public section

/-! # Goldilocks Healing: H.2, `Carry` from the writer, with catch-up -/

namespace Consensus.Goldilocks.SA

open Compose

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {T : SATrace sp FGP ro}

/-- **`Carry_y` from a writer, after the GST or by catch-up** (`h2-open-items.md` §5;
`Healing.carryAt_of_writer_window` with a third case for a counted head: `y` itself accepted it
at or before its vote and before `t_s + 3Δ`, as `Catch(2Δ)` gives for a head the writer accepted
before `ḡ`): `Compose.carryAt_of_writer_heads`. -/
theorem carryAt_of_writer_catch (hr : ACLocalRun (goldilocksSA sp FGP ro) H U T)
    {a₀ b : Time} (hsync : SyncAC (goldilocksSA sp FGP ro) H U a₀ b T) {s : Nat}
    (ha₀ : a₀ ≤ sp.ts s) (hb : sp.ts s + 2 * sp.Δ ≤ b) {w : Fin sp.n} (hw : w ∈ H) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : SA.CastAt T y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hW : ∀ v ∈ CV, v.slot = s ∧
      (∃ k, T.SendOrAdmit w k v ∧ sp.ts s ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∧
      ∃ Hv ∈ U, Hv.root = v.head ∧ Anc U ℓ.frame.F Hv ∧
        (Hv.root = sp.genesisRoot ∨
          (∃ k, T.AcceptAt w k Hv ∧ a₀ ≤ T.time k ∧ T.time k < sp.ts s + 2 * sp.Δ) ∨
          ∃ k ≤ i, T.AcceptAt y k Hv ∧ T.time k < sp.ts s + 3 * sp.Δ)) :
    SA.CarryAt T U y i e s CV := by
  refine carryAt_of_writer_heads hr ha₀ hb hw hy hc hs (Or.inl hsync) fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, hacc⟩ := hW v hv
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hFHv, ?_⟩
  rcases hacc with hg | hw' | ⟨ky, -, hky, hkyt⟩
  · exact Or.inr (Or.inl hg)
  · exact Or.inl hw'
  · exact Or.inr (Or.inr ⟨ky, hky, hkyt⟩)

end Consensus.Goldilocks.SA

end
