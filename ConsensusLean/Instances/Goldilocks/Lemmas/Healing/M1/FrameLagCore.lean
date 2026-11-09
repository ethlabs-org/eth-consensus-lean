module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo

public section

/-! # The frame-key lag between two reachable stores

A source store `x` and a receiver store `z` whose trees lie in a coherent `U`. If every block of
`x` at or above `h_max(z)` reaches `z` (relay), then `frameKey x ≤ frameKey z`
(`frameKey_le_of_relay`). Each trigger block of `x` is carried to `z`:

* the `h_max` carrier: it reaches `z`, so `h_max(z) = h_max(x)` when `h_max(z) ≤ h_max(x)`;
* the `J` carrier, the block caching `h_j(x)` at `h_max(x) = h_j(x) + 1`: it and its `J` reach
  `z`; a lower `h_j(z)` would put `Σ.F(z)` below `J(x)` (store-level G1.2), and `J(x)` is then
  a justification of `z` above `h_j(z)`, against `JMax`;
* the contest witness: it reaches `z`, with `Σ.F(z)` below it (G1.2 at `h_max`) and `J(z) = J(x)`
  (equal `h_j`) not below it.

Run facts enter only as premises (the held-attestation safety premise of `Healing/HeldSafety`,
the relay, and the parent closure of the two trees inside `U`), so readers honest at different
cuts, under constant or growing faults, instantiate the same proof. -/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- **The frame-key lag of a relay.** -/
theorem frameKey_le_of_relay {stx stz : Store P ACP} (hRx : stx.Reachable acp₀)
    (hRz : stz.Reachable acp₀) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsubx : stx.tree ⊆ U) (hsubz : stz.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of the receiver and of the source, or of the receiver
    -- twice, with a signer in `V` are not slashable.
    (hsafex : ∀ a b, (∃ Y ∈ stz.tree, a ∈ Y.fgPayload) → (∃ Y ∈ stx.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    (hsafez : ∀ a b, (∃ Y ∈ stz.tree, a ∈ Y.fgPayload) → (∃ Y ∈ stz.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    -- Parent closure: ancestry inside `U` below a held block is ancestry in the store.
    (hancx : ∀ A C, Anc U A C → C ∈ stx.tree → stx.Anc A C)
    (hancz : ∀ A C, Anc U A C → C ∈ stz.tree → stz.Anc A C)
    -- Relay: a block of the source at or above the receiver's `h_max` is held by the receiver.
    (hheld : ∀ B ∈ stx.tree, stz.hmax ≤ (stx.σ B.root).h → B ∈ stz.tree) :
    frameKey stx ≤ frameKey stz := by
  obtain ⟨-, hJx, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, ⟨Bh, hBh, hBhh⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hRx
  obtain ⟨-, -, -, -, hgez, -, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hRz
  have hbx := frameKey_bounds stx
  have hbz := frameKey_bounds stz
  by_cases hlt : stx.hmax < stz.hmax
  · omega
  have hle : stz.hmax ≤ stx.hmax := not_lt.1 hlt
  have hheld' : ∀ {B : NodeBlock P ACP}, B ∈ stx.tree → stx.hmax ≤ (stx.σ B.root).h →
      B ∈ stz.tree := fun hB hh => hheld _ hB (hle.trans hh)
  have hσ : ∀ {B : NodeBlock P ACP}, B ∈ stz.tree → B ∈ stx.tree →
      stz.σ B.root = stx.σ B.root :=
    fun hBz hBx => Store.σ_eq_of_mem hRz hRx hU.1 hsubz hsubx hBz hBx
  -- the `h_max` carrier
  have hBhz := hheld' hBh hBhh.ge
  have heq : stz.hmax = stx.hmax := by
    have := hgez Bh hBhz
    rw [hσ hBhz hBh] at this
    omega
  -- the `J` carrier
  have hjz := Store.hj_lt_hmax_of_reachable hRz
  have hjx := Store.hj_lt_hmax_of_reachable hRx
  have hb : stx.hmax = stx.hj + 1 → stz.hmax = stz.hj + 1 := by
    intro hbx'
    have hBjh := Store.hj_lt_h hRx hBj
    have hBjz := hheld' hBj (by omega)
    obtain ⟨E, hE, hEr, hEB, -⟩ := Store.J_entry_of_reachable hRx hBj
    obtain rfl : E = stx.J := hU.1 (hsubx hE) (hsubx hJx) (hEr.trans hBjJ)
    have hJz : stx.J ∈ stz.tree := mem_of_anc (hancz _ _ (hEB.mono hsubx) hBjz) hBjz
    have hJh := Store.J_height_le hRx hBj hJx hBjJ.symm
    by_contra hn
    have hzlt : stz.hj < stx.hj := by omega
    have hFJ := hancz _ _ ((Store.F_anc_of_hj_lt_of_safe hRz hRx hU hsubz hsubx hV hsafex hJx
      (by rw [hBjhj] at hJh; omega)).mono hsubx) hJz
    have hσj := hσ hBjz hBj
    have := (jMax_iff _).1 (jMax_of_reachable hRz) Bj hBjz _ hJz (by rw [hσj, hBjJ]) hFJ
    rw [hσj] at this
    omega
  -- the contest witness
  have hC : stx.Contest → stz.Contest := by
    rintro ⟨hbx', W, hW, -, hWh, hJW⟩
    have hbz' := hb hbx'
    have hWz := hheld' hW hWh.ge
    have hσW := hσ hWz hW
    have hJ := Store.J_eq_of_cache_hj_eq_of_safe hRz hRx hU hsubz hsubx hV hsafex (by omega)
    refine ⟨hbz', W, hWz, ?_, by rw [hσW]; omega, ?_⟩
    · exact Goldilocks.Store.F_anc_of_hmax_le_of_safe hRz hRz hU hsubz hsubz hV hsafez hWz
        (by rw [hσW]; omega)
    · intro hJW'
      rw [hJ] at hJW'
      exact hJW (hancx _ _ (hJW'.mono hsubz) hW)
  rw [frameKey_def, frameKey_def]
  split_ifs <;> first | omega | tauto

end Consensus.Goldilocks.Healing

end
