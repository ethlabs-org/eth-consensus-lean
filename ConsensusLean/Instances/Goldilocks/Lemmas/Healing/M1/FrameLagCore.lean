module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # The key lag between two reachable stores

A source store `x` and a receiver store `z` whose trees lie in a coherent `U`. If every block of
`x` at or above `h_max(z)` reaches `z` (relay), then the milestone key of `x` is at most that of
`z` (`key_le_of_relay`): the `h_max` carrier reaches `z`, so `h_max(z) = h_max(x)` when
`h_max(z) ≤ h_max(x)`; at a top frame of `x` the block caching `h_j(x)` and its `J` reach `z`, and
a lower `h_j(z)` would put `Σ.F(z)` below `J(x)` (store-level G1.2), against `JMax`.

Run facts enter only as premises (held-attestation safety, the relay, and the parent closure of
the receiver's tree inside `U`), so readers honest at different cuts instantiate the same proof. -/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {A : NodeAC P}

open Classical in
/-- **The key lag of a relay**, for the milestone key `2·h_max + [h_max = h_j + 1]`
(`Generic.frameKey''`): only the maximum-height and `J` carriers are needed. -/
theorem key_le_of_relay {acp₀ : A.Payload} {stx stz : Store P A.Payload}
    (hRx : stx.Reachable acp₀) (hRz : stz.Reachable acp₀)
    {U : Set (NodeBlock P A.Payload)} (hU : Coherent U)
    (hsubx : stx.tree ⊆ U) (hsubz : stz.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    (hsafe : ∀ a b, (∃ Y ∈ stz.tree, a ∈ Y.fgPayload) →
      (∃ Y ∈ stx.tree, b ∈ Y.fgPayload) → a.val ∈ V → ¬ FG.slashable a b)
    (hancz : ∀ A C, Anc U A C → C ∈ stz.tree → stz.Anc A C)
    (hheld : ∀ B ∈ stx.tree, stz.hmax ≤ (stx.σ B.root).h → B ∈ stz.tree) :
    2 * stx.hmax + (if stx.hmax = stx.hj + 1 then 1 else 0) ≤
      2 * stz.hmax + (if stz.hmax = stz.hj + 1 then 1 else 0) := by
  classical
  obtain ⟨-, hJx, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, ⟨Bh, hBh, hBhh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ hRx
  obtain ⟨-, -, -, -, hgez, -, -⟩ := Store.cache_invariants _ _ _ _ hRz
  by_cases hlt : stx.hmax < stz.hmax
  · split_ifs <;> omega
  have hle : stz.hmax ≤ stx.hmax := not_lt.mp hlt
  have hheld' : ∀ {B : NodeBlock P A.Payload}, B ∈ stx.tree → stx.hmax ≤ (stx.σ B.root).h →
      B ∈ stz.tree := fun hB hh => hheld _ hB (hle.trans hh)
  have hσ : ∀ {B : NodeBlock P A.Payload}, B ∈ stz.tree → B ∈ stx.tree →
      stz.σ B.root = stx.σ B.root :=
    fun hBz hBx => Healing.Store.σ_eq_of_mem hRz hRx hU.1 hsubz hsubx hBz hBx
  have hBhz := hheld' hBh hBhh.ge
  have heq : stz.hmax = stx.hmax := by
    have := hgez Bh hBhz
    rw [hσ hBhz hBh] at this
    omega
  have hjz := Healing.Store.hj_lt_hmax_of_reachable hRz
  have htop : stx.hmax = stx.hj + 1 → stz.hmax = stz.hj + 1 := by
    intro htx
    have hBjh := Healing.Store.hj_lt_h hRx hBj
    have hBjz := hheld' hBj (by omega)
    obtain ⟨E, hE, hEr, hEB, -⟩ := Goldilocks.Store.J_entry_hj P A.Payload hRx hBj
    obtain rfl : E = stx.J := hU.1 (hsubx hE) (hsubx hJx) (hEr.trans hBjJ)
    have hJz : stx.J ∈ stz.tree := mem_of_anc (hancz _ _ (hEB.mono hsubx) hBjz) hBjz
    have hJh := Healing.Store.J_height_le hRx hBj hJx hBjJ.symm
    by_contra hn
    have hzlt : stz.hj < stx.hj := by omega
    have hFJ := hancz _ _ ((Healing.Store.F_anc_of_hj_lt_of_safe hRz hRx hU hsubz hsubx
      hV hsafe hJx (by rw [hBjhj] at hJh; omega)).mono hsubx) hJz
    have hσj := hσ hBjz hBj
    have := (jMax_iff _).mp (jMax_of_reachable hRz) Bj hBjz _ hJz (by rw [hσj, hBjJ]) hFJ
    rw [hσj] at this
    omega
  split_ifs <;> omega

end Consensus.Goldilocks.Healing

end
