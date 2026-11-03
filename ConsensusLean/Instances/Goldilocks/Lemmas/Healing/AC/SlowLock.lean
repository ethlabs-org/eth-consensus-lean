module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks Healing: where a node's slow locks come from (T1 §1)

Every lock that is not fast and that an honest node holds sits below (inside `U`) the block of a
slow lock of its slot that the node itself wrote at an earlier cut (`SlowLockAt`, the update of
that slot writing the lock block of `update_confirmation` that is not the fast test's block):
the SA's lock functions only move locks back and keep their slot and fast bit (A0.4 (c)), a
restart keeps the locks (A0.7), an optimistic confirmation writes only fast locks, and an update
writes a lock that is not fast only as its slow lock. `fast_lock_provenance` (A1.5) is the fast
case; this is the slow one, by the same induction over the calls (`Lemmas/AC/Steps/Provenance`,
whose helpers are private there and repeated here with the slow write tracked). -/

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
  obtain ⟨l, hl, hs, hfa, -, B, hB, hBr, B', hB', hB'r, hA⟩ := h l' hl'
  exact Or.inl ⟨l, hl, hfa.symm, hs, Or.inr ⟨B', hΦ hB', hB'r, B, hΦ hB, hBr, hA.mono hΦ⟩⟩

private theorem FromP.of_addLocks {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {L : Set Lock} {t : Time} {s : Nat}
    {N : Set (Nat × Bool × Nat)} {New : Nat → Bool → Blk sp.n FGP → Prop} {L₀ : Set Lock}
      (hL : L₀ = L)
    (hN : ∀ r f e, (r, f, e) ∈ N → ∃ B ∈ Φ.tree, B.root = r ∧ New s f B) :
    FromP U L (addLocks sp L₀ Φ t s N) New := by
  subst hL
  intro l' hl'
  obtain ⟨l, hl, hs, hfa, -, B, hB, hBr, B', hB', hB'r, hA⟩ :=
    ((locks_move_back sp) FGP Φ L₀ t hΦ).2.1 s N l' hl'
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l, hl, hfa.symm, hs, Or.inr ⟨B', hΦU hB', hB'r, B, hΦU hB, hBr,
      Goldilocks.Anc.mono hΦU hA⟩⟩
  · obtain ⟨r, b, e⟩ := p
    simp only at hfa hs hBr
    obtain ⟨D, hD, hDr, hND⟩ := hN r b e hp
    have : B = D := hU.1 (hΦU hB) (hΦU hD) (hBr.trans hDr.symm)
    subst this
    exact Or.inr ⟨B, hs ▸ hfa ▸ hND, B', hΦU hB', hB'r, Goldilocks.Anc.mono hΦU hA⟩

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

/-- An optimistic confirmation writes only fast locks. -/
private theorem FromP.of_optimistic (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (A : SAState sp.n) (t : Time) :
    FromP U A.locks (optimisticConfirmation sp A Φ t).locks (fun _ f _ => f = true) := by
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact FromP.of_eq rfl
  · rw [updateLatestConfirmed_locks_eq]
    refine FromP.of_addLocks hU hΦ hΦU rfl fun r f e hr => ?_
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
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
  ∃ C, getConfirmation sp A Φ s = some C ∧
    deepest Φ {X | X ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t X ∧
      ∀ j : Int, (s : Int) - sp.k < j → j < s →
        ∃ S ∈ Φ.tree, A.saved j = some S.root ∧ Φ.Anc X S} = some B

/-- An update writes a lock that is not fast only as its slow lock. -/
private theorem FromP.of_updateConfirmation (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (t : Time) (s : Nat) :
    FromP U A.locks (updateConfirmation sp A Φ t s).locks
      (fun s' f B => s' = s ∧ (f = false → SlowW A Φ t s B)) := by
  unfold updateConfirmation
  dsimp only
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact FromP.of_eq rfl
  · dsimp only
    refine FromP.of_addLocks hU hΦ hΦU ?_ fun r f e hr => ?_
    · split_ifs
      · rfl
      · exact updateLatestConfirmed_locks_eq _ _ _
    rcases hr with ⟨D, hD, hr⟩ | ⟨D, hD, hr⟩
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      exact ⟨D, (deepest_mem hD).1.1.1.1, rfl, rfl, fun h => absurd h (by simp)⟩
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      refine ⟨D, (deepest_mem hD).1.1.1.1, rfl, rfl, fun _ => ⟨C, hC, ?_⟩⟩
      rw [← hD]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq, and_assoc]
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun j =>
        imp_congr_right fun _ => imp_congr_right fun hj => ?_
      rw [Function.update_of_ne (ne_of_lt hj)]

private theorem FromP.of_onTick (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    FromP U A.locks (acOnTick sp x A Φ t).1.locks
      (fun s f B => f = true ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ joined sp A t ∧
          s = sp.slot t - 1 ∧ (f = false → SlowW A Φ t s B))) := by
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
      (fun s f B => f = false → SlowLockAt tr x i s B) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hU := hr.coherent
  have fast : ∀ s (f : Bool) (B : Blk sp.n FGP), f = true → f = false → SlowLockAt tr x i s B :=
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
      obtain ⟨C, h1, h2⟩ := hW hf
      exact ⟨ℓ, C, hu, hA ▸ h1, hA ▸ h2⟩
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

/-- **T1 §1, slow lock provenance** ("every stored lock has such an origin", the slow case):
every lock that is not fast and that an honest node holds before cut `i` sits below (inside `U`)
the block of a slow lock of its slot that the node wrote at an earlier cut. -/
theorem slow_lock_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = false →
      ∃ j < i, ∃ B, SlowLockAt tr x j l.slot B ∧ ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
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
      rcases call_fromP hr hx ⟨hnode.1, hℓ⟩ l hl with ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨B, h, hB⟩
      · obtain ⟨j, hj, B, h, hB⟩ := ih l₀ hl₀ (hf₀.trans hf)
        exact ⟨j, hj.trans (Nat.lt_succ_self i), B, hs ▸ h, Below.of_sitsBelow hr.coherent hb hB⟩
      · exact ⟨i, Nat.lt_succ_self i, B, h hf, hB⟩
    · obtain ⟨j, hj, h⟩ := ih l hl hf
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

end Consensus.Goldilocks.SA

end
