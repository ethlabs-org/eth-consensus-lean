module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.2: stored slow-lock provenance

Every lock that is not fast and that an honest node holds sits below (inside `U`) the **stored**
block `Φ.viableAncestor D` of a slow lock of its slot that the node itself wrote at an earlier cut
(`D` the slow selection of `SlowLockAt`, `Φ` the frame of the writing call): `add_locks` stores
exactly that block (`liveLocks` moves the new lock to its viable ancestor), the lock functions
only move locks back and keep their slot and fast bit (A0.4 (c)), a restart keeps the locks
(A0.7), an optimistic confirmation writes only fast locks, and an update writes a lock that is
not fast only as its slow lock. This is the slow case of the induction of `fast_lock_provenance`
(`AC/Steps/Provenance`, whose per-function helpers are private there and repeated here with the
slow write tracked; the shared `FromP` toolkit is `Lemmas/AC/LockProvenance`), with the stored
block of HR.4's `stored_fast_lock_provenance` (`Retention/Provenance`)
(every lock image retains its original label).
`slow_lock_provenance` (`AC/SlowLock`) is its corollary for the raw selection `D`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

private theorem FromP.of_addLocks {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {L : Set Lock} {t : Time} {s : Nat}
    {N : Set (Nat × Bool × Nat)} {New : Nat → Bool → Blk sp.n FGP → Prop} {L₀ : Set Lock}
      (hL : L₀ = L)
    (hN : ∀ r f e, (r, f, e) ∈ N → ∃ D ∈ Φ.tree, D.root = r ∧ New s f (Φ.viableAncestor D)) :
    FromP U L (addLocks sp L₀ Φ t s N) New := by
  subst hL
  rw [fromP_iff]
  rintro l' ⟨l, hl, B, hB, hBr, -, rfl⟩
  obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l, hl, rfl, rfl,
      sitsBelow_iff.2 (Or.inr ⟨_, hΦU hvt, rfl, B, hΦU hB, hBr, hva.mono hΦU⟩)⟩
  · obtain ⟨D, hD, hDr, hND⟩ := hN p.1 p.2.1 p.2.2 hp
    obtain rfl : B = D := hU.1 (hΦU hB) (hΦU hD) (hBr.trans hDr.symm)
    exact Or.inr ⟨_, hND, below_iff.2 ⟨_, hΦU hvt, rfl, .refl⟩⟩

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

/-- An optimistic confirmation writes only fast locks. -/
private theorem FromP.of_optimistic (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (A : SAState sp.n) (t : Time) :
    FromP U A.locks (optimisticConfirmation sp A Φ t).locks (fun _ f _ => f = true) := by
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact FromP.of_eq rfl
  · rw [updateLatestConfirmed_keeps_locks]
    refine FromP.of_addLocks hU hΦ hΦU rfl fun r f e hr => ?_
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
    have hB := h
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    exact ⟨B, (deepest_mem hB).1.1, rfl, rfl⟩

private theorem FromP.of_tryVote
    {L : Set Lock} (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time)
    (hL : UnlockRel sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t)) L) :
    FromP U A.locks (tryVoteWith sp x L A Φ t).1.locks (fun _ f _ => f = true) := by
  have hopt : ∀ (A' : SAState sp.n) (v : Vote sp.n) (L : Set Lock), A'.locks = L →
      FromP U L (optimisticConfirmation sp (admitVote sp A' t v) Φ t).locks
        (fun _ f _ => f = true) := fun A' v L hL => by
    have := FromP.of_optimistic hU hΦ hΦU (admitVote sp A' t v) t
    rwa [admitVote_locks_eq, hL] at this
  unfold tryVoteWith
  dsimp only
  split_ifs
  · exact FromP.of_eq rfl
  · exact FromP.of_eq rfl
  · exact FromP.trans hU (FromP.of_movesBack hΦU (hL.movesBack hΦ)) (hopt _ _ _ rfl)
  · exact hopt _ _ _ rfl

/-- The slow lock that the update of slot `s` at `(A, Φ, t)` writes on `B` (vetoed or not). -/
private def SlowW (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) (B : Blk sp.n FGP) :
    Prop :=
  ∃ C, getConfirmation sp A Φ s = some C ∧
    deepest Φ {X | X ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t X ∧
      ∀ j : Int, (s : Int) - sp.k < j → j < s →
        ∃ S ∈ Φ.tree, A.saved j = some S.root ∧ Φ.Anc X S} = some B

/-- An update writes a lock that is not fast only as its slow lock. -/
private theorem FromP.of_updateConfirmation (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (t : Time) (s : Nat) :
    FromP U A.locks (updateConfirmation sp A Φ t s).locks
      (fun s' f O => s' = s ∧ (f = false → ∃ D, SlowW A Φ t s D ∧ O = Φ.viableAncestor D)) := by
  unfold updateConfirmation
  dsimp only
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact FromP.of_eq rfl
  · dsimp only
    refine FromP.of_addLocks hU hΦ hΦU (by
        split_ifs
        · rfl
        · exact updateLatestConfirmed_keeps_locks _ _ _)
      fun r f e hr => ?_
    rcases hr with ⟨D, hD, hr⟩ | ⟨D, hD, hr⟩
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      exact ⟨D, (deepest_mem hD).1.1.1.1, rfl, rfl, fun h => absurd h (by simp)⟩
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      refine ⟨D, (deepest_mem hD).1.1.1.1, rfl, rfl, fun _ => ⟨D, ⟨C, hC, ?_⟩, rfl⟩⟩
      rw [← hD]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq, and_assoc]
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun j =>
        imp_congr_right fun _ => imp_congr_right fun hj => ?_
      rw [Function.update_of_ne (ne_of_lt hj)]

private theorem FromP.of_onTick
    {L : Set Lock} (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time)
    (hL : UnlockRel sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t)) L) :
    FromP U A.locks (acOnTickWith sp x L A Φ t).1.locks
      (fun s f B => f = true ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ joined sp A t ∧
          s = sp.slot t - 1 ∧ (f = false → ∃ D, SlowW A Φ t s D ∧ B = Φ.viableAncestor D))) := by
  unfold acOnTickWith
  dsimp only
  split_ifs with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · refine (FromP.of_updateConfirmation hU hΦ hΦU A t _).mono fun s f B h => ?_
    obtain ⟨rfl, h2⟩ := h
    exact Or.inr ⟨ht.1, ht.2, hj, rfl, h2⟩
  · exact (FromP.of_tryVote hU hΦ hΦU x A t hL).mono fun s f B h => Or.inl h
  · exact FromP.of_eq rfl
  · exact FromP.of_eq rfl

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SATrace sp FGP ro}

/-- `call_fromP` with the unlock given. -/
private theorem call_fromPU
    {u : Nat → Set Lock} (hr : ACLocalRunU u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f O => f = false → ∃ D, SlowLockAt tr x i s D ∧ O = ℓ.frame.viableAncestor D) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  have hU := hr.coherent
  have fast : ∀ s (f : Bool) (O : Blk sp.n FGP), f = true → f = false →
      ∃ D, SlowLockAt tr x i s D ∧ O = ℓ.frame.viableAncestor D :=
    fun _ _ _ h1 h2 => absurd (h1.symm.trans h2) (by simp)
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  simp only at hpost
  rw [← hpost]
  have hlaw := hr.lawfulAt hx hc hΦ
  generalize hA : tr.state x i = A at hpost hlaw
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hlaw
    refine (FromP.of_onTick (L := u i) hU hΦ hΦU x A _ hlaw).mono fun s f B h hf => ?_
    rcases h with h | ⟨ht, hs0, hj, hs, hW⟩
    · exact fast s f B h hf
    · have hu : UpdateAt tr x i s ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        rw [hs]
        conv_lhs => rw [ht]
        simp only [SAParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      obtain ⟨D, ⟨C, h1, h2⟩, rfl⟩ := hW hf
      exact ⟨D, ⟨ℓ, C, hu, hA ▸ h1, hA ▸ h2⟩, rfl⟩
  | proposal => rw [hcall] at hlaw; exact FromP.of_proposalWith hΦ hΦU A _ hlaw
  | toFG => exact FromP.of_eq (toFG_locks A _)
  | message m =>
    rw [hcall] at hlaw
    have h₁ := FromP.of_optimistic hU hΦ hΦU (admitVote sp A (tr.time i) m) (tr.time i)
    rw [admitVote_locks_eq] at h₁
    exact (FromP.trans hU h₁ (FromP.of_tryVote (L := u i) hU hΦ hΦU x _ _ hlaw)).mono
      fun s f B h hf => fast s f B h hf
  | block B =>
    rw [hcall] at hlaw
    have h₁ := FromP.of_optimistic hU hΦ hΦU (blockReceipt sp A (tr.time i) B) (tr.time i)
    rw [blockReceipt_locks] at h₁
    exact (FromP.trans hU h₁ (FromP.of_tryVote (L := u i) hU hΦ hΦU x _ _ hlaw)).mono
      fun s f B h hf => fast s f B h hf
  | restart =>
    exact FromP.of_eq ((restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.1

/-- A call of an honest node keeps its locks below earlier ones, or writes fast locks, or writes
a slow lock of the slot of its update. -/
private theorem call_fromP (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f O => f = false → ∃ D, SlowLockAt tr x i s D ∧ O = ℓ.frame.viableAncestor D) :=
  call_fromPU (hr := hr.toU) (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc)

/-- `slow_lock_provenance_stored` with the unlock given. -/
theorem slow_lock_provenance_storedU
    {u : Nat → Set Lock} (hr : ACLocalRunU u H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = false →
      ∃ j < i, ∃ ℓ D, tr.CallAt x j ℓ ∧ SlowLockAt tr x j l.slot D ∧
        ∃ L ∈ U, L.root = l.block ∧ Anc U L (ℓ.frame.viableAncestor D) := by
  induction i with
  | zero =>
    intro l hl
    change l ∈ (tr.init x).locks at hl
    rw [hr.init x hx] at hl
    exact absurd hl (Set.notMem_empty l)
  | succ i ih =>
    intro l hl hf
    rw [Trace.state] at hl
    split_ifs at hl with hnode
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hnode.2
      rcases fromP_iff.1 (call_fromPU hr hx ⟨hnode.1, hℓ⟩) l hl with
        ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨O, h, hB⟩
      · obtain ⟨j, hj, ℓ', D, hc, h, hB⟩ := ih l₀ hl₀ (hf₀.trans hf)
        exact ⟨j, hj.trans (Nat.lt_succ_self i), ℓ', D, hc, hs ▸ h,
          below_iff.1 (Below.of_sitsBelow hr.coherent hb (below_iff.2 hB))⟩
      · obtain ⟨D, hD, rfl⟩ := h hf
        exact ⟨i, Nat.lt_succ_self i, ℓ, D, ⟨hnode.1, hℓ⟩, hD, below_iff.1 hB⟩
    · obtain ⟨j, hj, h⟩ := ih l hl hf
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

/-- **Stored slow-lock provenance**: every lock that is not fast and that an honest node holds
before cut `i` sits below (inside `U`) the stored block `ℓ.frame.viableAncestor D` of a slow lock
of its slot (selection `D`) that the node wrote at an earlier cut `j` (call label `ℓ`). -/
theorem slow_lock_provenance_stored (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = false →
      ∃ j < i, ∃ ℓ D, tr.CallAt x j ℓ ∧ SlowLockAt tr x j l.slot D ∧
        ∃ L ∈ U, L.root = l.block ∧ Anc U L (ℓ.frame.viableAncestor D) :=
  slow_lock_provenance_storedU (hr := hr.toU) (x := x) (hx := hx) (i := i)

end Consensus.Goldilocks.SA

end
