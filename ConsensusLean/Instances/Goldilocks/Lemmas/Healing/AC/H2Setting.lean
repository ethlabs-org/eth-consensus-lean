module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting

public section

/-! # Goldilocks Healing: the setting of H.2 (healthy driven AC traces with their frames)

H.2's premises over an AC trace of the SA (`InclusionRun`: `ACRun`, `Driven`, `Healthy(g)`,
`Catch(2Δ)`, `t₀ ≥ ḡ` and `Inv(t₀)`; no trivial frames), and the clean raw origins of H.2's
proof: the protected pairs `(B, j)` of kinds P1 (an honest
fast lock write of a slot `j` with `t_j ≥ t₀ + 4Δ`, on the block it selects, before its move
back) and P2 (an honest slow lock write of a slot `j` with `t_{j−k+1} ≥ t₀ + 4Δ`), each at a
node joined at the write. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- **H.2's premises** over an AC trace of the SA: the trace contract with the honest-object
facts, a driven trace, `Healthy(g)`, `Catch(2Δ)`, and `Inv(t₀)` for some `t₀ ≥ ḡ`. -/
structure InclusionRun (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (proposer : Nat → Fin sp.n) (g t₀ : Time) : Prop extends HealthyBase tr H U proposer g where
  le : gbar g ≤ t₀
  inv : Inv proposer tr H U t₀

/-- **A clean raw origin** of label `j` on `B` (the P1/P2 pairs of
`𝒫(t₀)`): an honest fast lock write of slot `j` with `t_j ≥ t₀ + 4Δ` on the block it selects,
or an honest slow lock write of slot `j` with `t_{j−k+1} ≥ t₀ + 4Δ`, at a node joined at the
write. -/
def CleanOrigin (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (t₀ : Time) (B : Blk sp.n FGP)
    (j : Nat) : Prop :=
  (∃ x ∈ H, ∃ i CV, JoinedAt tr x (tr.time i) ∧ FastLockAt tr x i j B CV ∧
    t₀ + 4 * sp.Δ ≤ sp.ts j) ∨
  (∃ x ∈ H, ∃ i, JoinedAt tr x (tr.time i) ∧ SlowLockAt tr x i j B ∧
    t₀ + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))

theorem cleanOrigin_iff {B : Blk sp.n FGP} {j : Nat} : CleanOrigin tr H t₀ B j ↔
    ((∃ x ∈ H, ∃ i CV, JoinedAt tr x (tr.time i) ∧ FastLockAt tr x i j B CV ∧
      t₀ + 4 * sp.Δ ≤ sp.ts j) ∨
    (∃ x ∈ H, ∃ i, JoinedAt tr x (tr.time i) ∧ SlowLockAt tr x i j B ∧
      t₀ + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))) := Iff.rfl

/-- A clean raw origin is protected (kinds P1 and P2 of `𝒫(t₀)`). -/
theorem CleanOrigin.protected {proposer : Nat → Fin sp.n} {B : Blk sp.n FGP} {j : Nat}
    (h : CleanOrigin tr H t₀ B j) : Protected proposer tr H t₀ B j := by
  rcases h with h | h
  exacts [Or.inl h, Or.inr (Or.inl h)]


end Consensus.Goldilocks.SA

end
