module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks Healing, HS.2: stored slow-lock provenance

Every lock that is not fast and that an honest node holds sits below (inside `U`) the **stored**
block `Φ.viableAncestor D` of a slow lock of its slot that the node itself wrote at an earlier cut
(`D` the slow selection of `SlowLockAt`, `Φ` the frame of the writing call): `add_locks` stores
exactly that block (`liveLocks` moves the new lock to its viable ancestor), the lock functions
only move locks back and keep their slot and fast bit (A0.4 (c)), a restart keeps the locks
(A0.7), an optimistic confirmation writes only fast locks, and an update writes a lock that is
not fast only as its slow lock. This is `slow_lock_provenance` (`AC/SlowLock`, which keeps only
the raw selection `D`) with the stored block of HR.4's `stored_fast_lock_provenance`
(`Retention/Provenance`); their helpers are private there and repeated here
(`hs234-exact-interface.md` §3: "every lock image retains its original label"). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- The block of `l'` is an ancestor (inside `U`) of the block of `l`, or `l' = l`. -/
private def SitsBelow (U : Set (Blk sp.n FGP)) (l' l : Lock) : Prop :=
  l' = l ∨ ∃ L₁ ∈ U, L₁.root = l'.block ∧ ∃ L₂ ∈ U, L₂.root = l.block ∧ Anc U L₁ L₂

/-- The block of `l` is in `U` and an ancestor of `B` there. -/
private def Below (U : Set (Blk sp.n FGP)) (l : Lock) (B : Blk sp.n FGP) : Prop :=
  ∃ L ∈ U, L.root = l.block ∧ Anc U L B

/-- Every lock of `L'` sits below a lock of `L` with its slot and fast bit, or below a block `B`
with `New l'.slot l'.fast B`. -/
private def FromP (U : Set (Blk sp.n FGP)) (L L' : Set Lock)
    (New : Nat → Bool → Blk sp.n FGP → Prop) : Prop :=
  ∀ l' ∈ L', (∃ l ∈ L, l.fast = l'.fast ∧ l'.slot = l.slot ∧ SitsBelow U l' l) ∨
    ∃ B, New l'.slot l'.fast B ∧ Below U l' B

private theorem FromP.of_eq {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} (h : L' = L) : FromP U L L' New := by
  subst h
  exact fun l hl => Or.inl ⟨l, hl, rfl, rfl, Or.inl rfl⟩

private theorem FromP.mono {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New New' : Nat → Bool → Blk sp.n FGP → Prop} (h : FromP U L L' New)
    (hN : ∀ s f B, New s f B → New' s f B) : FromP U L L' New' := fun l hl =>
  (h l hl).imp_right fun ⟨B, h1, h2⟩ => ⟨B, hN _ _ _ h1, h2⟩

private theorem FromP.trans {U : Set (Blk sp.n FGP)} (hU : Coherent U) {L₁ L₂ L₃ : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} (h₁ : FromP U L₁ L₂ New) (h₂ : FromP U L₂ L₃ New) :
    FromP U L₁ L₃ New := by
  intro l₃ hl₃
  rcases h₂ l₃ hl₃ with ⟨l₂, hl₂, hf₂, hs₂, hb₂⟩ | ⟨B, hN, hB⟩
  · rcases h₁ l₂ hl₂ with ⟨l₁, hl₁, hf₁, hs₁, hb₁⟩ | ⟨B, hN, L, hL, hLr, hLB⟩
    · refine Or.inl ⟨l₁, hl₁, hf₁.trans hf₂, hs₂.trans hs₁, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact hb₁
      rcases hb₁ with rfl | ⟨C₁, hC₁, hC₁r, C₂, hC₂, hC₂r, hC⟩
      · exact Or.inr ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      have : A₂ = C₁ := hU.1 hA₂ hC₁ (hA₂r.trans hC₁r.symm)
      subst this
      exact Or.inr ⟨A₁, hA₁, hA₁r, C₂, hC₂, hC₂r, hA.trans hC⟩
    · refine Or.inr ⟨B, hs₂ ▸ hf₂ ▸ hN, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact ⟨L, hL, hLr, hLB⟩
      have : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
      subst this
      exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩
  · exact Or.inr ⟨B, hN, hB⟩

private theorem FromP.of_movesBack {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}
    (hΦ : Φ.tree ⊆ U) {L L' : Set Lock} {New : Nat → Bool → Blk sp.n FGP → Prop}
    (h : MovesBack sp Φ L L') : FromP U L L' New := by
  intro l' hl'
  obtain ⟨l, hl, hs, hfa, B, hB, hBr, B', hB', hB'r, hA⟩ := h l' hl'
  exact Or.inl ⟨l, hl, hfa.symm, hs, Or.inr ⟨B', hΦ hB', hB'r, B, hΦ hB, hBr, hA.mono hΦ⟩⟩

private theorem FromP.of_addLocks {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {L : Set Lock} {t : Time} {s : Nat}
    {N : Set (Nat × Bool)} {New : Nat → Bool → Blk sp.n FGP → Prop} {L₀ : Set Lock} (hL : L₀ = L)
    (hN : ∀ r f, (r, f) ∈ N → ∃ D ∈ Φ.tree, D.root = r ∧ New s f (Φ.viableAncestor D)) :
    FromP U L (addLocks sp L₀ Φ t s N) New := by
  subst hL
  rintro l' ⟨l, hl, B, hB, hBr, -, rfl⟩
  obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l, hl, rfl, rfl, Or.inr ⟨_, hΦU hvt, rfl, B, hΦU hB, hBr, hva.mono hΦU⟩⟩
  · obtain ⟨D, hD, hDr, hND⟩ := hN p.1 p.2 hp
    obtain rfl : B = D := hU.1 (hΦU hB) (hΦU hD) (hBr.trans hDr.symm)
    exact Or.inr ⟨_, hND, _, hΦU hvt, rfl, .refl⟩

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

/-- An optimistic confirmation writes only fast locks. -/
private theorem FromP.of_optimistic (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (A : SAState sp.n) (t : Time) :
    FromP U A.locks (optimisticConfirmation sp A Φ t).locks (fun _ f _ => f = true) := by
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact FromP.of_eq rfl
  · rw [updateLatestConfirmed_locks_eq]
    refine FromP.of_addLocks hU hΦ hΦU rfl fun r f hr => ?_
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hB := h
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    exact ⟨B, (deepest_mem hB).1.1, rfl, rfl⟩

private theorem FromP.of_tryVote (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    FromP U A.locks (tryVote sp x A Φ t).1.locks (fun _ f _ => f = true) := by
  have hopt : ∀ (A' : SAState sp.n) (v : Vote sp.n),
      FromP U A'.locks (optimisticConfirmation sp (admitVote sp A' t v) Φ t).locks
        (fun _ f _ => f = true) := fun A' v => by
    have := FromP.of_optimistic hU hΦ hΦU (admitVote sp A' t v) t
    rwa [admitVote_locks_eq] at this
  unfold tryVote
  dsimp only
  split_ifs
  · exact FromP.of_eq rfl
  · exact FromP.of_eq rfl
  · exact FromP.trans hU (FromP.of_movesBack hΦU
      (((locks_move_back sp) FGP Φ A.locks t hΦ).2.2 ((sp.slot t : Int) - 1)
        (mergedVoteView sp A Φ (sp.slot t)))) (hopt _ _)
  · exact hopt _ _

/-- The slow lock that the update of slot `s` at `(A, Φ, t)` writes on `B`. -/
private def SlowW (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) (B : Blk sp.n FGP) :
    Prop :=
  ∃ C, getConfirmation sp A Φ s = some C ∧ ¬ conflictsWithLock sp A.locks Φ t C ∧
    deepest Φ {X | X ∈ confirmationPath sp Φ C ∧ (FastTest sp A Φ s X ∨
      ∀ j : Int, (s : Int) - sp.k < j → j < s →
        ∃ S ∈ Φ.tree, A.saved j = some S.root ∧ Φ.Anc X S)} = some B ∧
    fastSelect sp A Φ s C ≠ some B

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
    split_ifs with hconf
    · exact FromP.of_eq rfl
    · refine FromP.of_addLocks hU hΦ hΦU (updateLatestConfirmed_locks_eq _ _ _) fun r f hr => ?_
      rcases hr with ⟨D, hD, hr⟩ | ⟨hne, D, hD, hr⟩
      · simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨D, (deepest_mem hD).1.1.1, rfl, rfl, fun h => absurd h (by simp)⟩
      · simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        refine ⟨D, (deepest_mem hD).1.1.1, rfl, rfl, fun _ => ⟨D, ⟨C, hC, hconf, ?_, ?_⟩, rfl⟩⟩
        · rw [← hD]
          congr 1
          ext X
          simp only [Set.mem_ofPred_eq]
          refine and_congr_right fun _ => or_congr_right (forall_congr' fun j =>
            imp_congr_right fun _ => imp_congr_right fun hj => ?_)
          rw [Function.update_of_ne (ne_of_lt hj)]
        · rw [← hD]
          exact Ne.symm hne

private theorem FromP.of_onTick (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    FromP U A.locks (acOnTick sp x A Φ t).1.locks
      (fun s f B => f = true ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ joined sp A t ∧
          s = sp.slot t - 1 ∧ (f = false → ∃ D, SlowW A Φ t s D ∧ B = Φ.viableAncestor D))) := by
  unfold acOnTick
  dsimp only
  split_ifs with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · refine (FromP.of_updateConfirmation hU hΦ hΦU A t _).mono fun s f B h => ?_
    obtain ⟨rfl, h2⟩ := h
    exact Or.inr ⟨ht.1, ht.2, hj, rfl, h2⟩
  · exact (FromP.of_tryVote hU hΦ hΦU x A t).mono fun s f B h => Or.inl h
  · exact FromP.of_eq rfl
  · exact FromP.of_eq rfl

private theorem FromP.of_proposal (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n)
    (t : Time) {New : Nat → Bool → Blk sp.n FGP → Prop} :
    FromP U A.locks (acProposal sp A Φ t).1.locks New := by
  unfold acProposal
  dsimp only
  split_ifs
  · exact FromP.of_movesBack hΦU (((locks_move_back sp) FGP Φ A.locks t hΦ).2.2 _ _)
  · exact FromP.of_eq rfl

private theorem toFG_locks (A : SAState sp.n) (t : Time) :
    (acToFG sp A Φ t).1.locks = A.locks := by
  unfold acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SATrace sp FGP ro}

/-- A call of an honest node keeps its locks below earlier ones, or writes fast locks, or writes
a slow lock of the slot of its update. -/
private theorem call_fromP (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f O => f = false → ∃ D, SlowLockAt tr x i s D ∧ O = ℓ.frame.viableAncestor D) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hU := hr.coherent
  have fast : ∀ s (f : Bool) (O : Blk sp.n FGP), f = true → f = false →
      ∃ D, SlowLockAt tr x i s D ∧ O = ℓ.frame.viableAncestor D :=
    fun _ _ _ h1 h2 => absurd (h1.symm.trans h2) (by simp)
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  simp only at hpost
  rw [← hpost]
  generalize hA : tr.state x i = A at hpost
  cases hcall : ℓ.call with
  | tick =>
    refine (FromP.of_onTick hU hΦ hΦU x A _).mono fun s f B h hf => ?_
    rcases h with h | ⟨ht, hs0, hj, hs, hW⟩
    · exact fast s f B h hf
    · have hu : UpdateAt tr x i s ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        rw [hs]
        conv_lhs => rw [ht]
        simp only [SAParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      obtain ⟨D, ⟨C, h1, h2, h3, h4⟩, rfl⟩ := hW hf
      exact ⟨D, ⟨ℓ, C, hu, hA ▸ h1, hA ▸ h2, hA ▸ h3, hA ▸ h4⟩, rfl⟩
  | proposal => exact FromP.of_proposal hΦ hΦU A _
  | toFG => exact FromP.of_eq (toFG_locks A _)
  | message m =>
    have h₁ := FromP.of_optimistic hU hΦ hΦU (admitVote sp A (tr.time i) m) (tr.time i)
    rw [admitVote_locks_eq] at h₁
    exact (FromP.trans hU h₁ (FromP.of_tryVote hU hΦ hΦU x _ _)).mono fun s f B h hf =>
      fast s f B h hf
  | block B =>
    have h₁ := FromP.of_optimistic hU hΦ hΦU (blockReceipt sp A (tr.time i) B) (tr.time i)
    rw [blockReceipt_locks] at h₁
    exact (FromP.trans hU h₁ (FromP.of_tryVote hU hΦ hΦU x _ _)).mono fun s f B h hf =>
      fast s f B h hf
  | restart =>
    exact FromP.of_eq ((restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.1

private theorem Below.of_sitsBelow (hU : Coherent U) {l' l : Lock} {B : Blk sp.n FGP}
    (h : SitsBelow U l' l) (hB : Below U l B) : Below U l' B := by
  rcases h with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
  · exact hB
  obtain ⟨L, hL, hLr, hLB⟩ := hB
  have : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
  subst this
  exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩

/-- **Stored slow-lock provenance**: every lock that is not fast and that an honest node holds
before cut `i` sits below (inside `U`) the stored block `ℓ.frame.viableAncestor D` of a slow lock
of its slot (selection `D`) that the node wrote at an earlier cut `j` (call label `ℓ`). -/
theorem slow_lock_provenance_stored (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
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
      rcases call_fromP hr hx ⟨hnode.1, hℓ⟩ l hl with ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨O, h, hB⟩
      · obtain ⟨j, hj, ℓ', D, hc, h, hB⟩ := ih l₀ hl₀ (hf₀.trans hf)
        exact ⟨j, hj.trans (Nat.lt_succ_self i), ℓ', D, hc, hs ▸ h,
          Below.of_sitsBelow hr.coherent hb hB⟩
      · obtain ⟨D, hD, rfl⟩ := h hf
        exact ⟨i, Nat.lt_succ_self i, ℓ, D, ⟨hnode.1, hℓ⟩, hD, hB⟩
    · obtain ⟨j, hj, h⟩ := ih l hl hf
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

end Consensus.Goldilocks.SA

end
