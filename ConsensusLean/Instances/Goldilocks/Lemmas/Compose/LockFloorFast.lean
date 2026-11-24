module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal

public section

/-! # Goldilocks: the lock floor keeps the fast bit

The lock floor of `AC.exists_step_locks_floor` and `Compose.floor_run_view` with the fast bit
of the floor lock kept. Every lock function moves a lock to a block (its viable ancestor or its
unlock target) and keeps its slot, fast bit and expiry, so a fast floor lock stays fast. This is
what makes the moved lock a candidate of `ac_to_fg`, which reads fast locks only. -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams} {Φ : Frm sp.n FGP} {t : Time} {j m : Nat}
  {B₀ : Blk sp.n FGP}

/-- `live_locks` keeps the fast floor. -/
theorem fastFloor_liveLocks {L : Set Lock} (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree)
    (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ L, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ liveLocks sp L Φ t, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  obtain ⟨l, hl, hj, hf, he, B, hB, hBr, hB0B⟩ := h
  subst hj
  exact ⟨_, ⟨l, hl, B, hB, hBr, hk.trans he, rfl⟩, rfl, hf, he, _,
    (viableAncestor_anc hΦ hB).1, rfl, anc_viableAncestor_of_floor hΦ hB0 hva0 hB hB0B⟩

/-- `add_locks` keeps the fast floor. -/
theorem fastFloor_addLocks {L : Set Lock} {s : Nat} {N : Set (Nat × Bool × Nat)}
    (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀)
    (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ L, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ addLocks sp L Φ t s N, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  obtain ⟨l, hl, h⟩ := h
  exact fastFloor_liveLocks hΦ hB0 hva0 hk ⟨l, Set.subset_union_left hl, h⟩

/-- `unlock` against the slot-`s` votes of `V` keeps the fast floor when `s ≤ j` or the unlock
target of `B₀` is `B₀`. -/
theorem fastFloor_unlock {L : Set Lock} {s : Int} {V : View sp.n} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : s ≤ j ∨ unlockTarget sp Φ V s B₀ = B₀)
    (h : ∃ l ∈ L, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ unlock sp L Φ t s V, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  obtain ⟨l, hl, hj, hf, he, B, hB, hBr, hB0B⟩ := fastFloor_liveLocks hΦ hB0 hva0 hk h
  subst hj
  by_cases hs : (l.slot : Int) < s
  · have hu' := hu.resolve_left (by omega)
    exact ⟨⟨(unlockTarget sp Φ V s B).root, l.slot, l.fast, l.expiry⟩,
      ⟨l, hl, B, hB, hBr, by simp only [hs, ↓reduceIte]⟩, rfl, hf, he, _,
      (unlockTarget_anc sp hΦ V s hB).1, rfl, anc_unlockTarget_of_floor hΦ V s hB0 hB hB0B hu'⟩
  · exact ⟨l, ⟨l, hl, B, hB, hBr, by simp only [hs, ↓reduceIte]⟩, rfl, hf, he, B, hB, hBr,
      hB0B⟩

/-- The optimistic confirmation keeps the fast floor. -/
theorem fastFloor_optimisticConfirmation {A : ACState sp.n} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (optimisticConfirmation sp A Φ t).locks, l.slot = j ∧ l.fast = true ∧
      m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold optimisticConfirmation
  split
  · exact h
  · rw [updateLatestConfirmed_keeps_locks]
    exact fastFloor_addLocks hΦ hB0 hva0 hk h

/-- The confirmation update keeps the fast floor. -/
theorem fastFloor_updateConfirmation {A : ACState sp.n} {s : Nat} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (updateConfirmation sp A Φ t s).locks, l.slot = j ∧ l.fast = true ∧
      m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold updateConfirmation
  dsimp only
  split
  · exact h
  · split_ifs <;>
      first
      | exact fastFloor_addLocks hΦ hB0 hva0 hk h
      | (rw [updateLatestConfirmed_keeps_locks]; exact fastFloor_addLocks hΦ hB0 hva0 hk h)

/-- `try_vote` keeps the fast floor when `unlock` at the merged vote view of its input keeps
`B₀`. -/
theorem fastFloor_tryVote (self : Fin sp.n) {A : ACState sp.n} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨
      unlockTarget sp Φ (mergedVoteView sp A Φ (sp.slot t)) ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (tryVote sp self A Φ t).1.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold tryVote
  dsimp only
  split_ifs <;> first
    | exact h
    | exact fastFloor_unlock hΦ hB0 hva0 hk hu h
    | (apply fastFloor_optimisticConfirmation hΦ hB0 hva0 hk
       rw [admitVote_locks_eq]
       exact fastFloor_unlock hΦ hB0 hva0 hk hu h)
    | (apply fastFloor_optimisticConfirmation hΦ hB0 hva0 hk
       rw [admitVote_locks_eq]
       exact h)

/-- `ac_on_tick` keeps the fast floor. -/
theorem fastFloor_acOnTick (self : Fin sp.n) {A : ACState sp.n} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨
      unlockTarget sp Φ (mergedVoteView sp A Φ (sp.slot t)) ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (acOnTick sp self A Φ t).1.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  have hv := fastFloor_tryVote self hΦ hB0 hva0 hk hu h
  unfold acOnTick
  dsimp only
  split_ifs <;>
    first
    | exact h
    | exact hv
    | exact fastFloor_updateConfirmation hΦ hB0 hva0 hk h
    | exact fastFloor_updateConfirmation hΦ hB0 hva0 hk hv

/-- `ac_proposal` keeps the fast floor. -/
theorem fastFloor_acProposal {A : ACState sp.n} (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree)
    (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨ unlockTarget sp Φ
      (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))
      ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (acProposal sp A Φ t).1.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold acProposal
  dsimp only
  split_ifs <;>
    first
    | exact h
    | exact fastFloor_unlock hΦ hB0 hva0 hk hu h

/-- **The fast floor lemma of an AC call**: `exists_step_locks_floor` with the fast bit kept. -/
theorem exists_step_locks_fastFloor {ro : ReplayOrder sp FGP} (self : Fin sp.n)
    {A : ACState sp.n} (c : (goldilocksAC sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨
      unlockTarget sp Φ (unlockView A Φ t c) ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ ((goldilocksAC sp FGP ro).step self A Φ t c).1.locks, l.slot = j ∧ l.fast = true ∧
      m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  cases c with
  | tick =>
    rw [unlockView_tick] at hu
    exact fastFloor_acOnTick self hΦ hB0 hva0 hk hu h
  | proposal =>
    rw [unlockView_proposal] at hu
    exact fastFloor_acProposal hΦ hB0 hva0 hk hu h
  | toFG =>
    have he : ((goldilocksAC sp FGP ro).step self A Φ t .toFG).1.locks = A.locks :=
      acToFG_locks_eq A
    rw [he]
    exact h
  | message v =>
    rw [unlockView_message] at hu
    refine fastFloor_tryVote self hΦ hB0 hva0 hk hu ?_
    refine fastFloor_optimisticConfirmation hΦ hB0 hva0 hk ?_
    rw [admitVote_locks_eq]
    exact h
  | block C =>
    rw [unlockView_block] at hu
    refine fastFloor_tryVote self hΦ hB0 hva0 hk hu ?_
    refine fastFloor_optimisticConfirmation hΦ hB0 hva0 hk ?_
    rw [blockReceipt_locks]
    exact h
  | restart =>
    have he : ((goldilocksAC sp FGP ro).step self A Φ t .restart).1.locks = A.locks :=
      ((restart_state sp) FGP ro self A Φ t hΦ ht).2.1
    rw [he]
    exact h

end Consensus.Goldilocks.AC

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The fast floor at node `y`, cut `i`: a fast lock of slot `j` and expiry at least `m` on a
block `⪰ B₀` of the frame's tree. -/
abbrev FastFloorAt (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat)
    (B₀ : AC.Blk sp.n (List (FG.Att sp.n))) (j m : Nat) : Prop :=
  ∃ l ∈ (tr.state y i).ac.locks, l.slot = j ∧ l.fast = true ∧ m ≤ l.expiry ∧
    ∃ B ∈ (tr.state y i).fg.toFrame.tree, B.root = l.block ∧ (tr.state y i).fg.toFrame.Anc B₀ B

/-- **The fast floor over one cut**: `floor_run_view` with the fast bit kept. -/
theorem fastFloor_run_view {ini} (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) {B₀ : AC.Blk sp.n (List (FG.Att sp.n))} {j m : Nat}
    (hfl : FastFloorAt tr y i B₀ j m)
    (hk : sp.slot (tr.time i) ≤ m) (hB0 : B₀ ∈ (tr.state y i).fg.toFrame.tree)
    (hB0' : B₀ ∈ (tr.state y (i + 1)).fg.toFrame.tree)
    (hva0 : (tr.state y i).fg.toFrame.viableAncestor B₀ = B₀)
    (hu : ∀ ℓ, tr.CallAt y i (.ac ℓ) → (sp.slot (tr.time i) : Int) - 1 ≤ j ∨
      AC.unlockTarget sp (Node.frame (tr.state y i))
        (AC.unlockView (ro := ro) (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)
          ℓ.call) ((sp.slot (tr.time i) : Int) - 1) B₀ = B₀) :
    FastFloorAt tr y (i + 1) B₀ j m := by
  have hold : ∃ l ∈ (tr.state y (i + 1)).ac.locks, l.slot = j ∧ l.fast = true ∧
      m ≤ l.expiry ∧ ∃ B ∈ (tr.state y i).fg.toFrame.tree, B.root = l.block ∧
        (tr.state y i).fg.toFrame.Anc B₀ B := by
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := hrun.cutLaw y hy i c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        obtain ⟨hfr, hstep, -, -⟩ := hlaw
        rw [hfr] at hstep
        have := AC.exists_step_locks_fastFloor (ro := ro) y ℓ.call
          (frameOK_state hrun.toLocalRun hy i) (hrun.time_nonneg i) hB0 hva0 hk (hu ℓ hc) hfl
        rw [hstep] at this
        exact this
      | fg ℓ =>
        cases ℓ with
        | block C acc =>
          cases acc with
          | true => rw [hlaw.2.2.1]; exact hfl
          | false => rw [hlaw.2]; exact hfl
        | attestation a => rw [hlaw.2.1]; exact hfl
        | attest C s =>
          cases s with
          | none => rw [hlaw.2]; exact hfl
          | some a => rw [hlaw.2.2]; exact hfl
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact hfl
  obtain ⟨l, hl, hj, hf, he, B, hB, hBr, hB0B⟩ := hold
  obtain ⟨hB', hB0B'⟩ := floor_frame_transport hrun hy (Nat.le_succ i) hB0' hB hB0B
  exact ⟨l, hl, hj, hf, he, B, hB', hBr, hB0B'⟩

end Consensus.Goldilocks.Compose

end
