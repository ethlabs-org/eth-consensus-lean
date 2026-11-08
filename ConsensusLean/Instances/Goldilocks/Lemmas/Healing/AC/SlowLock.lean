module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProvenance

public section

/-! # Goldilocks Healing: where a node's slow locks come from

Every lock that is not fast and that an honest node holds sits below (inside `U`) the block of a
slow lock of its slot that the node itself wrote at an earlier cut (`SlowLockAt`, the update of
that slot writing the lock block of `update_confirmation` that is not the fast test's block):
the SA's lock functions only move locks back and keep their slot and fast bit (A0.4 (c)), a
restart keeps the locks (A0.7), an optimistic confirmation writes only fast locks, and an update
writes a lock that is not fast only as its slow lock. `fast_lock_provenance` (A1.5) is the fast
case. The slow one is the stored slow-lock provenance `slow_lock_provenance_stored`
(`Healing/DrainProvenance`), weakened from the stored block `Φ.viableAncestor D` to the selection
`D` itself, which the stored block is an ancestor of. Over a run at a write mode `wm` the origin
is a slow lock of width `wm.width` (`slow_lock_provenanceM`, `SlowLockAtW`), and `SlowLockAt` at a
mode of width `k` (`slow_lock_provenanceU`). -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {U : Set (Blk sp.n FGP)}
variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SATrace sp FGP ro}

/-- **Slow lock provenance at width `wm.width`**: every lock that is not fast and that an honest
node holds before cut `i` sits below (inside `U`) the block of a slow lock of width `wm.width` of
its slot that the node wrote at an earlier cut. -/
theorem slow_lock_provenanceM
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state y i).locks, l.fast = false →
      ∃ j < i, ∃ B, SlowLockAtW wm.width tr y j l.slot B ∧
        ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  intro l hl hf
  obtain ⟨j, hj, ℓ, D, hc, hsl, L, hL, hLr, hLA⟩ := slow_lock_provenance_storedM hr hy i l hl hf
  obtain ⟨ℓ', C, hu, hC, hD⟩ := slowLockAtW_iff.1 hsl
  obtain rfl : ℓ = ℓ' := Option.some.inj (hc.2.symm.trans hu.1.2)
  have hΦ := frameIn_of_callAtU hr hy hc
  exact ⟨j, hj, D, hsl, L, hL, hLr,
    hLA.trans ((viableAncestor_anc hΦ.1 (deepest_mem hD).1.1.1).2.mono hΦ.2)⟩

/-- `slow_lock_provenance` with the unlock given, at a mode of width `k`. -/
theorem slow_lock_provenanceU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) (hw : wm.width = sp.k) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = false →
      ∃ j < i, ∃ B, SlowLockAt tr x j l.slot B ∧ ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  intro l hl hf
  have h := slow_lock_provenanceM hr hx i l hl hf
  rw [hw] at h
  simpa only [slowLockAtW_k] using h

/-- **Slow lock provenance** (every stored lock has such an origin, the slow case):
every lock that is not fast and that an honest node holds before cut `i` sits below (inside `U`)
the block of a slow lock of its slot that the node wrote at an earlier cut. -/
theorem slow_lock_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = false →
      ∃ j < i, ∃ B, SlowLockAt tr x j l.slot B ∧ ∃ L ∈ U, L.root = l.block ∧ Anc U L B :=
  slow_lock_provenanceU (hr := hr.toU) rfl (x := x) (hx := hx) (i := i)

end Consensus.Goldilocks.SA

end
