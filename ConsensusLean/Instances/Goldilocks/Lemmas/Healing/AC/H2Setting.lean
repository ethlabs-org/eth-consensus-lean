module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting

public section

/-! # Goldilocks Healing: the setting of H.2 (healthy driven AC traces with their frames)

H.2's premises over an AC trace of the SA (`InclusionRun`: `ACRun`, `Driven`, `Healthy(g)`,
`Catch(2Δ)`, `t₀ ≥ ḡ` and `Inv(t₀)`; no trivial frames), and the clean raw origins of H.2's
proof (workbench `h2-open-items.md` §6.1): the protected pairs `(B, j)` of kinds P1 (an honest
fast lock write of a slot `j` with `t_j ≥ t₀ + 4Δ`, on the block it selects, before its move
back) and P2 (an honest slow lock write of a slot `j` with `t_{j−k+1} ≥ t₀ + 4Δ`), each at a
node joined at the write. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- **H.2's premises** over an AC trace of the SA: the trace contract with the honest-object
facts, a driven trace, `Healthy(g)`, `Catch(2Δ)`, and `Inv(t₀)` for some `t₀ ≥ ḡ`. -/
structure InclusionRun (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (g t₀ : Time) : Prop where
  run : ACRun tr H U
  driven : Driven tr H
  healthy : HealthyAC tr H U g
  catchUp : CatchAC tr H U g (2 * sp.Δ)
  le : gbar g ≤ t₀
  inv : Inv tr H U t₀

/-- **A clean raw origin** of label `j` on `B` (`h2-open-items.md` §6.1, the P1/P2 pairs of
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
theorem CleanOrigin.protected {B : Blk sp.n FGP} {j : Nat} (h : CleanOrigin tr H t₀ B j) :
    Protected tr H t₀ B j := by
  rcases h with h | h
  exacts [Or.inl h, Or.inr (Or.inl h)]

namespace InclusionRun

variable (hI : InclusionRun tr H U g t₀)
include hI

/-- An honest node is awake from `ḡ` on. -/
theorem awake {y : Fin sp.n} (hy : y ∈ H) {t : Time} (ht : gbar g ≤ t) : tr.awake y t :=
  hI.healthy.2.2.1 y hy t ht

/-- **No restart after `ḡ`**: a restart is a wake, and an honest node is awake from `ḡ` on. -/
theorem restart_le {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hk : tr.RestartAt y k) :
    tr.time k ≤ gbar g := by
  by_contra hlt
  rw [not_le] at hlt
  have hr := hI.run.localRun
  obtain ⟨ℓ, hc, hcall⟩ := hk
  obtain ⟨u, hu0, -, hna, hbefore⟩ := hr.sleep_of_restart y hy k ℓ hc hcall
  have hug : u < gbar g := by
    by_contra h
    exact hna (hI.awake hy (not_lt.mp h))
  obtain ⟨k', ⟨ℓ', hc', -⟩, huk', hk'g⟩ :=
    hr.restart_at_wake y hy u (gbar g) hu0 hug hna (hI.awake hy le_rfl)
  have hk'k : k' < k := by
    by_contra h
    have := hr.time_mono (not_lt.mp h)
    linarith
  have := hbefore k' hk'k ℓ' hc'
  linarith

/-- An honest node is joined at every `t` with `ḡ ≤ t_{slot(t)−1}`. -/
theorem joinedAt {y : Fin sp.n} (hy : y ∈ H) {t : Time}
    (ht : gbar g ≤ sp.ts ((sp.slot t : Int) - 1)) : JoinedAt tr y t :=
  fun _ hk _ => (hI.restart_le hy hk).trans ht

end InclusionRun

end Consensus.Goldilocks.SA

end
