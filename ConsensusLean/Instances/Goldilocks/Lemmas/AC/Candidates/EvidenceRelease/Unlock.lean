module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockTargetSelf

public section

/-! # Candidate `evidence-release`: the weighted unlock and its step properties

A candidate variant of the AC unlock that keeps each lock's counted weight. The SA is Goldilocks'
except for one step: after the parent's `unlock`, a lock of a slot below `s` moves further back, to
the deepest block `Y` at or below the parent's target whose **evidence** in the view is below the
lock's **weight** at `Y`, or to `Φ.F`. The evidence against `Y` is the equivocators of the view's
votes and the validators with a slot-`s` support vote whose head (in the tree) does not extend `Y`.
The weight is fixed at the lock's write (the validators its confirmation counted for each block)
and travels with the lock.

Modelling rationale: a lock written from a partial view weighs only the support that wrote it, so
signed votes that do not extend it and outnumber that support are positive evidence to release it,
while silence counts for nothing. The parent's threshold, half of the committee as opponents, is
kept as the first stage, so the candidate's lock is never above the parent's.

The definitions and the step properties, with nothing of the parent's spec or proofs changed:

* `WLock`, a lock with an origin and a weight, and `WLock.lock`, the forgetful map to `SA.Lock`
  (two writes with the same lock tuple and different weights are distinct `WLock`s);
* `liveLocksW` and `unlockW` (`E ∘ unlock`); `evidence`, `evidenceTarget`;
* (B) `unlockW_backward`: every lock of `unlockW` is a lock of the parent's `unlock` (of the
  forgotten set) moved to an ancestor in the tree, with the same slot, fast bit and expiry, and its
  own origin and weight; `unlockW_covers`: every lock of the parent's `unlock` has such an image
  (the evidence stage removes no lock);
* (S) `unlockW_slot_ge`: a lock of a slot at or above `s` is the parent's;
* (K) `evidenceTarget_keeps`: the weighted keep. If the evidence against `Y ⪯ T` lies in a set of
  fewer validators than the lock's weight at `Y`, the evidence stage keeps the lock at or above `Y`;
  `evidence_subset` gives that inclusion from "every support vote of slot `s` by a validator outside
  `O` extends `Y`" and "the equivocators lie in `O`";
* `unlockW_keeps`: (K) composed with the parent's keep, at the level of a lock of `unlockW`.

Idempotence of `unlockW`, and the candidate as an instance of the lock-rule interface, are in
`EvidenceRelease.Rule`. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable (sp : SAParams) {FGP : Type}

/-- A lock with its weight: the lock, the root of the block it was written on, and the weight by
block root (the validators its formation counted for that block; `0` off the origin's chain). -/
structure WLock where
  /-- The lock as the parent stores it. -/
  lock : Lock
  /-- The root of the block the lock was written on. -/
  origin : Nat
  /-- The weight, by block root. -/
  weight : Nat → Nat

/-- `live_locks` on weighted locks: each live lock moved back to its viable ancestor, keeping its
origin and weight. -/
def liveLocksW (L : Set WLock) (Φ : Frm sp.n FGP) (t : Time) : Set WLock :=
  {w' | ∃ w ∈ L, ∃ B ∈ Φ.tree, B.root = w.lock.block ∧ w.lock.LiveAt sp t ∧
    w' = { w with lock := { w.lock with block := (Φ.viableAncestor B).root } }}

/-- The evidence against `Y` in a view against the slot-`s` votes: the equivocators of its votes
and the validators with a slot-`s` support vote whose head (in the tree) does not extend `Y`. -/
def evidence (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (Y : Blk sp.n FGP) : Set (Fin sp.n) :=
  equivocators V.votes ∪ {i | ∃ x ∈ V.support, x.val = i ∧ (x.slot : Int) = s ∧
    ∃ H ∈ Φ.tree, H.root = x.head ∧ ¬ Φ.Anc Y H}

/-- The blocks the evidence stage may keep a lock of weight `w` on, below `T`. -/
def keepable (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock) (T : Blk sp.n FGP) :
    Set (Blk sp.n FGP) :=
  {Y | Y ∈ Φ.tree ∧ Φ.Anc Y T ∧ (evidence sp Φ V s Y).ncard < w.weight Y.root}

/-- Where the evidence stage moves a lock of weight `w` from `T`: the deepest keepable block below
`T`, or `Φ.F`. -/
noncomputable def evidenceTarget (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock)
    (T : Blk sp.n FGP) : Blk sp.n FGP :=
  (deepest Φ (keepable sp Φ V s w T)).getD Φ.F

/-- The candidate's `unlock` (`E ∘ unlock`): every live lock of a slot below `s` moves to the
evidence target of its parent unlock target; the others keep their place. -/
noncomputable def unlockW (L : Set WLock) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) : Set WLock :=
  {w' | ∃ w ∈ liveLocksW sp L Φ t, ∃ B ∈ Φ.tree, B.root = w.lock.block ∧
    w' = if (w.lock.slot : Int) < s then
      { w with lock := { w.lock with
        block := (evidenceTarget sp Φ V s w (unlockTarget sp Φ V s B)).root } } else w}

variable {sp}

theorem mem_keepable {Φ : Frm sp.n FGP} {V : View sp.n} {s : Int} {w : WLock}
    {T Y : Blk sp.n FGP} :
    Y ∈ keepable sp Φ V s w T ↔
      Y ∈ Φ.tree ∧ Φ.Anc Y T ∧ (evidence sp Φ V s Y).ncard < w.weight Y.root :=
  Iff.rfl

theorem mem_evidence {Φ : Frm sp.n FGP} {V : View sp.n} {s : Int} {Y : Blk sp.n FGP}
    {i : Fin sp.n} :
    i ∈ evidence sp Φ V s Y ↔ i ∈ equivocators V.votes ∨ ∃ x ∈ V.support, x.val = i ∧
      (x.slot : Int) = s ∧ ∃ H ∈ Φ.tree, H.root = x.head ∧ ¬ Φ.Anc Y H :=
  Iff.rfl

theorem mem_liveLocksW {L : Set WLock} {Φ : Frm sp.n FGP} {t : Time} {w' : WLock} :
    w' ∈ liveLocksW sp L Φ t ↔ ∃ w ∈ L, ∃ B ∈ Φ.tree, B.root = w.lock.block ∧ w.lock.LiveAt sp t ∧
      w' = { w with lock := { w.lock with block := (Φ.viableAncestor B).root } } :=
  Iff.rfl

theorem evidenceTarget_eq (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : WLock)
    (T : Blk sp.n FGP) :
    evidenceTarget sp Φ V s w T = (deepest Φ (keepable sp Φ V s w T)).getD Φ.F := by
  rfl

/-- The keepable set depends on the lock only through its weight. -/
theorem keepable_weight {Φ : Frm sp.n FGP} {V : View sp.n} {s : Int} {w w' : WLock}
    (h : w.weight = w'.weight) (T : Blk sp.n FGP) :
    keepable sp Φ V s w T = keepable sp Φ V s w' T := by
  ext Y
  rw [mem_keepable, mem_keepable, h]

/-- The forgotten live weighted locks are the parent's live locks of the forgotten set. -/
theorem lock_image_liveLocksW (L : Set WLock) (Φ : Frm sp.n FGP) (t : Time) :
    WLock.lock '' liveLocksW sp L Φ t = liveLocks sp (WLock.lock '' L) Φ t := by
  ext l
  constructor
  · rintro ⟨_, ⟨w, hw, B, hB, hr, hlive, rfl⟩, rfl⟩
    exact ⟨w.lock, ⟨w, hw, rfl⟩, B, hB, hr, hlive, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, B, hB, hr, hlive, rfl⟩
    exact ⟨_, ⟨w, hw, B, hB, hr, hlive, rfl⟩, rfl⟩

/-- The evidence target is in the tree, below `T`, when `T` is in the tree of a well-formed
frame. -/
theorem evidenceTarget_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    (w : WLock) {T : Blk sp.n FGP} (hT : T ∈ Φ.tree) :
    evidenceTarget sp Φ V s w T ∈ Φ.tree ∧ Φ.Anc (evidenceTarget sp Φ V s w T) T := by
  rw [evidenceTarget_eq]
  cases h : deepest Φ (keepable sp Φ V s w T) with
  | none => exact ⟨hΦ.rooted.1, hΦ.rooted.2 T hT⟩
  | some D => exact ⟨(deepest_mem h).1.1, (deepest_mem h).1.2.1⟩

/-- **(K), the weighted keep.** If `Y ⪯ T` is in the tree and the evidence against `Y` lies in a
set `O` of fewer validators than the lock's weight at `Y`, the evidence stage keeps the lock at or
above `Y`. -/
theorem evidenceTarget_keeps {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    (w : WLock) {T Y : Blk sp.n FGP} (hY : Y ∈ Φ.tree) (hYT : Φ.Anc Y T)
    {O : Set (Fin sp.n)} (hO : evidence sp Φ V s Y ⊆ O) (hOw : O.ncard < w.weight Y.root) :
    Φ.Anc Y (evidenceTarget sp Φ V s w T) := by
  have hS : keepable sp Φ V s w T ⊆ Φ.tree := fun X hX => hX.1
  have hYS : Y ∈ keepable sp Φ V s w T :=
    ⟨hY, hYT, lt_of_le_of_lt (Set.ncard_le_ncard hO O.toFinite) hOw⟩
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨Y, hYS⟩
  have hYD := anc_deepest hΦ hS (fun X hX C hC => anc_total hΦ.coherent hX.2.1 hC.2.1) hD Y hYS
  rw [evidenceTarget_eq, hD, Option.getD_some]
  exact hYD

/-- **The evidence inclusion.** If the equivocators of the view lie in `O` and every slot-`s`
support vote of a validator outside `O` has its head (in the tree) above `Y`, the evidence against
`Y` lies in `O`. -/
theorem evidence_subset {Φ : Frm sp.n FGP} {V : View sp.n} {s : Int} {Y : Blk sp.n FGP}
    {O : Set (Fin sp.n)} (heq : equivocators V.votes ⊆ O)
    (hext : ∀ x ∈ V.support, x.val ∉ O → (x.slot : Int) = s →
      ∀ H ∈ Φ.tree, H.root = x.head → Φ.Anc Y H) :
    evidence sp Φ V s Y ⊆ O := by
  rintro i (hi | ⟨x, hx, rfl, hs, H, hH, hHr, hnot⟩)
  · exact heq hi
  · by_contra hO
    exact hnot (hext x hx hO hs H hH hHr)

/-- A weighted lock of `unlockW`, written out: the live lock it comes from, its block in the
tree, and the move. -/
theorem mem_unlockW {L : Set WLock} {Φ : Frm sp.n FGP} {t : Time} {s : Int}
    {V : View sp.n} {w' : WLock} :
    w' ∈ unlockW sp L Φ t s V ↔ ∃ w ∈ liveLocksW sp L Φ t, ∃ B ∈ Φ.tree,
      B.root = w.lock.block ∧ w' = if (w.lock.slot : Int) < s then
        { w with lock := { w.lock with
          block := (evidenceTarget sp Φ V s w (unlockTarget sp Φ V s B)).root } } else w :=
  Iff.rfl

/-- **(B), backward.** Every lock of `unlockW` is a lock of the parent's `unlock` of the forgotten
set, moved to an ancestor in the tree, with the same slot, fast bit and expiry, and with the origin
and weight of a stored weighted lock. -/
theorem unlockW_backward {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set WLock) (t : Time)
    (s : Int) (V : View sp.n) :
    ∀ w' ∈ unlockW sp L Φ t s V, ∃ l ∈ unlock sp (WLock.lock '' L) Φ t s V,
      w'.lock.slot = l.slot ∧ w'.lock.fast = l.fast ∧ w'.lock.expiry = l.expiry ∧
      (∃ w ∈ L, w'.origin = w.origin ∧ w'.weight = w.weight) ∧
      ∃ T ∈ Φ.tree, T.root = l.block ∧ ∃ Y ∈ Φ.tree, Y.root = w'.lock.block ∧ Φ.Anc Y T := by
  rintro w' ⟨_, ⟨w, hw, B₀, hB₀, hr₀, hlive, rfl⟩, B, hB, hBr, rfl⟩
  have hl : (⟨(Φ.viableAncestor B₀).root, w.lock.slot, w.lock.fast, w.lock.expiry⟩ : Lock) ∈
      liveLocks sp (WLock.lock '' L) Φ t :=
    ⟨w.lock, ⟨w, hw, rfl⟩, B₀, hB₀, hr₀, hlive, rfl⟩
  have hu : ∀ l', l' = (if (w.lock.slot : Int) < s then
      (⟨(unlockTarget sp Φ V s B).root, w.lock.slot, w.lock.fast, w.lock.expiry⟩ : Lock) else
      ⟨(Φ.viableAncestor B₀).root, w.lock.slot, w.lock.fast, w.lock.expiry⟩) →
      l' ∈ unlock sp (WLock.lock '' L) Φ t s V :=
    fun l' hl' => ⟨_, hl, B, hB, hBr, hl'⟩
  by_cases hlt : (w.lock.slot : Int) < s
  · obtain ⟨hTt, -⟩ := unlockTarget_anc sp hΦ V s hB
    obtain ⟨hEt, hET⟩ := evidenceTarget_anc hΦ V s
      { w with lock := { w.lock with block := (Φ.viableAncestor B₀).root } } hTt
    refine ⟨_, hu _ (ite_eq_left hlt).symm, ?_⟩
    rw [ite_eq_left hlt]
    exact ⟨rfl, rfl, rfl, ⟨w, hw, rfl, rfl⟩, _, hTt, rfl, _, hEt, rfl, hET⟩
  · refine ⟨_, hu _ (ite_eq_right hlt).symm, ?_⟩
    rw [ite_eq_right hlt]
    exact ⟨rfl, rfl, rfl, ⟨w, hw, rfl, rfl⟩, B, hB, hBr, B, hB, hBr, .refl⟩

/-- **No removal.** Every lock of the parent's `unlock` of the forgotten set is the forgotten
image, up to the block, of a lock of `unlockW`: the evidence stage drops no lock. -/
theorem unlockW_covers (L : Set WLock) (Φ : Frm sp.n FGP) (t : Time) (s : Int) (V : View sp.n) :
    ∀ l ∈ unlock sp (WLock.lock '' L) Φ t s V, ∃ w' ∈ unlockW sp L Φ t s V,
      w'.lock.slot = l.slot ∧ w'.lock.fast = l.fast ∧ w'.lock.expiry = l.expiry := by
  rintro _ ⟨_, ⟨_, ⟨w, hw, rfl⟩, B₀, hB₀, hr₀, hlive, rfl⟩, B, hB, hBr, rfl⟩
  refine ⟨_, ⟨_, ⟨w, hw, B₀, hB₀, hr₀, hlive, rfl⟩, B, hB, hBr, rfl⟩, ?_⟩
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- **(S), the slot exemption.** A lock of `unlockW` that comes from a live lock of a slot at or
above `s` is that live lock, unchanged. -/
theorem unlockW_slot_ge {L : Set WLock} {Φ : Frm sp.n FGP} {t : Time} {s : Int}
    {V : View sp.n} {w : WLock} (hw : w ∈ liveLocksW sp L Φ t) (hs : s ≤ (w.lock.slot : Int))
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBr : B.root = w.lock.block) :
    w ∈ unlockW sp L Φ t s V := by
  refine ⟨w, hw, B, hB, hBr, ?_⟩
  rw [ite_eq_right (not_lt.2 hs)]

/-- **The keep at the level of `unlockW`.** A live weighted lock of a slot below `s` on `B`, whose
parent unlock target is at or above `Y` (the parent's keep), and whose evidence against `Y` lies
in a set of fewer validators than its weight at `Y`, stays at or above `Y` in `unlockW`. -/
theorem unlockW_keeps {L : Set WLock} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {s : Int}
    {V : View sp.n} {w : WLock} (hw : w ∈ liveLocksW sp L Φ t) {B Y : Blk sp.n FGP}
    (hB : B ∈ Φ.tree) (hBr : B.root = w.lock.block) (hY : Y ∈ Φ.tree)
    (hpar : Φ.Anc Y (unlockTarget sp Φ V s B))
    {O : Set (Fin sp.n)} (hO : evidence sp Φ V s Y ⊆ O) (hOw : O.ncard < w.weight Y.root) :
    ∃ w' ∈ unlockW sp L Φ t s V, w'.origin = w.origin ∧ w'.weight = w.weight ∧
      w'.lock.slot = w.lock.slot ∧ w'.lock.expiry = w.lock.expiry ∧
      ∃ Z ∈ Φ.tree, Z.root = w'.lock.block ∧ Φ.Anc Y Z := by
  by_cases hlt : (w.lock.slot : Int) < s
  · have hT := (unlockTarget_anc sp hΦ V s hB).1
    refine ⟨_, ⟨w, hw, B, hB, hBr, rfl⟩, ?_⟩
    rw [ite_eq_left hlt]
    exact ⟨rfl, rfl, rfl, rfl, _, (evidenceTarget_anc hΦ V s w hT).1, rfl,
      evidenceTarget_keeps hΦ V s w hY hpar hO hOw⟩
  · refine ⟨w, unlockW_slot_ge hw (not_lt.1 hlt) hB hBr, rfl, rfl, rfl, rfl, B, hB, hBr, ?_⟩
    exact hpar.trans (unlockTarget_anc sp hΦ V s hB).2

end Consensus.Goldilocks.EvidenceRelease

end
