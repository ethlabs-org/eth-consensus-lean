module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: every lock lives at least two and at most `k` slots

`LocksWF`: every lock `l` of a set has `l.slot + 2 ≤ l.expiry ≤ l.slot + k`. It holds at every
state an honest node reaches (`locksWF_state`), at a cast's read point
(`castAt_readPoint_locksWF`) and after each call (`locksWF_post`). The lock functions keep
each lock's slot and expiry (`live_locks`, `unlock` and the move-back; a restart keeps the set),
and `add_locks` writes only expiries in `[s + 2, s + k]`: `fastExpiry` (`le_fastExpiry`,
`fastExpiry_le`), or `s + k` for a slow lock and a slow-qualified update's fast lock (B′). So
`LocksWF` is per lock, independent of the frame and the time, and needs no regime. The cap half
gives "live ⇒ recent" (`LocksWF.slot_le_of_live`), the floor half a fresh fast lock's two slots. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- Every lock of `L` lives at least two slots and at most `k` slots past its slot. -/
def LocksWF (sp : SAParams) (L : Set Lock) : Prop :=
  ∀ l ∈ L, l.slot + 2 ≤ l.expiry ∧ l.expiry ≤ l.slot + sp.k

/-- The floor half: a lock of a well-formed set lives through `slot + 2`. -/
theorem LocksWF.floor {L : Set Lock} (h : LocksWF sp L) {l : Lock} (hl : l ∈ L) :
    l.slot + 2 ≤ l.expiry :=
  (h l hl).1

/-- The cap half: a lock of a well-formed set expires by `slot + k`. -/
theorem LocksWF.cap {L : Set Lock} (h : LocksWF sp L) {l : Lock} (hl : l ∈ L) :
    l.expiry ≤ l.slot + sp.k :=
  (h l hl).2

/-- A subset of a well-formed set is well formed. -/
theorem LocksWF.mono {L L' : Set Lock} (h : LocksWF sp L) (hL : L' ⊆ L) : LocksWF sp L' :=
  fun l hl => h l (hL hl)

/-- `live_locks` keeps `LocksWF`: a live lock keeps its source's slot and expiry. -/
theorem LocksWF.liveLocks {L : Set Lock} (h : LocksWF sp L) (Φ : Frm sp.n FGP) (t : Time) :
    LocksWF sp (SA.liveLocks sp L Φ t) := by
  rintro _ ⟨l, hl, -, -, -, -, rfl⟩
  exact h l hl

/-- **Live ⇒ recent.** A live lock of a well-formed set has `slot(t) ≤ l.slot + k`. -/
theorem LocksWF.slot_le_of_live {L : Set Lock} (h : LocksWF sp L) {Φ : Frm sp.n FGP}
    {t : Time} {l : Lock} (hl : l ∈ SA.liveLocks sp L Φ t) : sp.slot t ≤ l.slot + sp.k := by
  obtain ⟨l₀, hl₀, -, -, -, hlive, rfl⟩ := hl
  exact hlive.trans (h.cap hl₀)

/-- `mem_liveLockBlocks` with the slow-window bound: in a well-formed set, the stored lock of a
live lock block has `slot(t) ≤ l.slot + k` (the cap). -/
theorem mem_liveLockBlocks_of_wf {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set Lock}
    (h : LocksWF sp L) {t : Time} {B : Blk sp.n FGP} (hB : B ∈ liveLockBlocks sp L Φ t) :
    ∃ l ∈ L, ∃ B₀ ∈ Φ.tree, B₀.root = l.block ∧ sp.slot t ≤ l.slot + sp.k ∧
      B = Φ.viableAncestor B₀ := by
  obtain ⟨l, hl, B₀, hB₀, hBr, hlive, rfl⟩ := mem_liveLockBlocks hΦ hB
  exact ⟨l, hl, B₀, hB₀, hBr, hlive.trans (h.cap hl), rfl⟩

/-- `unlock` keeps `LocksWF`: a moved lock keeps its slot and expiry. -/
theorem LocksWF.unlock {L : Set Lock} (h : LocksWF sp L) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) : LocksWF sp (SA.unlock sp L Φ t s V) := by
  rintro _ ⟨l, hl, -, -, -, rfl⟩
  have := h.liveLocks Φ t l hl
  split_ifs <;> exact this

/-- Locks related by the unlock relation keep `LocksWF`: a moved lock keeps its slot and expiry. -/
theorem LocksWF.unlockRel {L L' : Set Lock} (h : LocksWF sp L) {Φ : Frm sp.n FGP} {t : Time}
    {s : Int} {V : View sp.n} (hL : UnlockRel sp L Φ t s V L') : LocksWF sp L' := by
  intro l' hl'
  obtain ⟨l, hl, -, -, -, -, hs, -, he, -, -⟩ := hL l' hl'
  rw [hs, he]
  exact h l hl

/-- `add_locks` keeps `LocksWF` when every new lock of slot `s` has an expiry in
`[s + 2, s + k]`. -/
theorem LocksWF.addLocks {L : Set Lock} (h : LocksWF sp L) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) {N : Set (Nat × Bool × Nat)} (hN : ∀ p ∈ N, s + 2 ≤ p.2.2 ∧ p.2.2 ≤ s + sp.k) :
    LocksWF sp (SA.addLocks sp L Φ t s N) := by
  refine LocksWF.liveLocks (fun l hl => ?_) Φ t
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact h l hl
  · exact hN p hp

/-- The optimistic confirmation keeps `LocksWF` (its lock has expiry `fastExpiry`). -/
theorem LocksWF.optimisticConfirmation {A : SAState sp.n} (h : LocksWF sp A.locks)
    (Φ : Frm sp.n FGP) (t : Time) : LocksWF sp (SA.optimisticConfirmation sp A Φ t).locks := by
  unfold SA.optimisticConfirmation
  split
  · exact h
  · rw [updateLatestConfirmed_keeps_locks]
    refine h.addLocks Φ t _ fun p hp => ?_
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨le_fastExpiry sp _ Φ t _, fastExpiry_le sp _ Φ t _⟩

/-- The confirmation update keeps `LocksWF`: its fast lock on `D` has expiry `s + k` when
the path has a slow-test block (B′) and `fastExpiry` otherwise, its slow lock `s + k`. -/
theorem LocksWF.updateConfirmation {A : SAState sp.n} (h : LocksWF sp A.locks)
    (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    LocksWF sp (SA.updateConfirmation sp A Φ t s).locks := by
  have hk := sp.two_le_k
  unfold SA.updateConfirmation
  dsimp only
  split
  · exact h
  · split_ifs
    all_goals
      refine LocksWF.addLocks ?_ Φ t s fun p hp => ?_
      · first | exact h | (rw [updateLatestConfirmed_keeps_locks]; exact h)
      · rcases hp with ⟨B, -, rfl⟩ | ⟨B, -, rfl⟩
        · exact ⟨le_fastExpiry sp _ Φ t s, fastExpiry_le sp _ Φ t s⟩
        · dsimp only; omega

/-- `LocksWF.tryVote` with the unlock given. -/
theorem LocksWF.tryVoteWith
    {L : Set Lock} {A : SAState sp.n} (h : LocksWF sp A.locks) (x : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time)
    (hL : UnlockRel sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t)) L) :
    LocksWF sp (SA.tryVoteWith sp x L A Φ t).1.locks ∧
      ∀ e ∈ (SA.tryVoteWith sp x L A Φ t).2, LocksWF sp e.readPoint.locks := by
  have hu : LocksWF sp (if 0 < sp.slot t then L else A.locks) := by
    split_ifs
    · exact h.unlockRel hL
    · exact h
  refine ⟨?_, fun e he => by rw [tryVote_readPoint_locks_eqWith he]; exact hu⟩
  unfold SA.tryVoteWith
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact h
  · exact h
  · refine LocksWF.optimisticConfirmation ?_ Φ t
    rw [admitVote_locks_eq]
    exact h.unlockRel hL
  · refine LocksWF.optimisticConfirmation ?_ Φ t
    rw [admitVote_locks_eq]
    exact h

/-- `try_vote` keeps `LocksWF`, in its post-state and in its emissions' read points. -/
theorem LocksWF.tryVote {A : SAState sp.n} (h : LocksWF sp A.locks) (x : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    LocksWF sp (SA.tryVote sp x A Φ t).1.locks ∧
      ∀ e ∈ (SA.tryVote sp x A Φ t).2, LocksWF sp e.readPoint.locks := by
  have hu : LocksWF sp (if 0 < sp.slot t then
      SA.unlock sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t))
      else A.locks) := by
    split_ifs
    · exact h.unlock Φ t _ _
    · exact h
  refine ⟨?_, fun e he => by rw [tryVote_readPoint_locks_eq he]; exact hu⟩
  unfold SA.tryVote
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact h
  · exact h
  · refine LocksWF.optimisticConfirmation ?_ Φ t
    rw [admitVote_locks_eq]
    exact h.unlock Φ t _ _
  · refine LocksWF.optimisticConfirmation ?_ Φ t
    rw [admitVote_locks_eq]
    exact h

/-- `LocksWF.step` with the unlock given. -/
theorem LocksWF.stepWith
    {L : Set Lock} {ro : ReplayOrder sp FGP} {A : SAState sp.n} (h : LocksWF sp A.locks)
    (x : Fin sp.n) {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call)
    (hL : UnlockRel sp (callInput sp A Φ t c).locks Φ t ((sp.slot t : Int) - 1)
      (callView sp A Φ t c) L) :
    LocksWF sp (stepWith sp ro x L A Φ t c).1.locks ∧
      ∀ e ∈ (stepWith sp ro x L A Φ t c).2, LocksWF sp e.readPoint.locks := by
  have hopt : ∀ {A' : SAState sp.n}, A'.locks = A.locks →
      LocksWF sp (SA.optimisticConfirmation sp A' Φ t).locks := fun hA =>
    LocksWF.optimisticConfirmation (hA ▸ h) Φ t
  cases c with
  | tick =>
    change LocksWF sp (acOnTickWith sp x L A Φ t).1.locks ∧
      ∀ e ∈ (acOnTickWith sp x L A Φ t).2, LocksWF sp e.readPoint.locks
    have hv := h.tryVoteWith x Φ t hL
    unfold acOnTickWith
    dsimp only
    split_ifs <;> simp only [List.not_mem_nil, false_imp_iff, imp_true_iff, and_true] <;>
      first
      | exact ⟨hv.1.updateConfirmation Φ t _, hv.2⟩
      | exact hv
      | exact h.updateConfirmation Φ t _
      | exact h
  | proposal =>
    refine ⟨?_, fun e he => by simp at he⟩
    change LocksWF sp (acProposalWith sp L A Φ t).1.locks
    unfold acProposalWith
    dsimp only
    split_ifs <;> first | exact h | exact h.unlockRel hL
  | toFG =>
    refine ⟨?_, fun e he => by simp at he⟩
    change LocksWF sp (acToFG sp A Φ t).1.locks
    rw [acToFG_locks_eq]
    exact h
  | message v =>
    exact (hopt (admitVote_locks_eq A t v)).tryVoteWith x Φ t hL
  | block B =>
    exact (hopt (blockReceipt_locks A t B)).tryVoteWith x Φ t hL
  | restart =>
    obtain ⟨he, hl, -⟩ := (restart_state sp) FGP ro x A Φ t hΦ ht
    change LocksWF sp (acRestart sp ro x A Φ t).1.locks ∧
      ∀ e ∈ (acRestart sp ro x A Φ t).2, LocksWF sp e.readPoint.locks
    refine ⟨?_, fun e he' => ?_⟩
    · rw [hl]; exact h
    · rw [he] at he'; simp at he'

/-- **One SA call keeps `LocksWF`**, in its post-state and in every emission's read point
(a well-formed frame and `t ≥ 0` for the restart). -/
theorem LocksWF.step {ro : ReplayOrder sp FGP} {A : SAState sp.n} (h : LocksWF sp A.locks)
    (x : Fin sp.n) {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) :
    LocksWF sp ((goldilocksSA sp FGP ro).step x A Φ t c).1.locks ∧
      ∀ e ∈ ((goldilocksSA sp FGP ro).step x A Φ t c).2, LocksWF sp e.readPoint.locks := by
  rw [step_eq_stepWith]
  exact h.stepWith x hΦ ht c (unlockRel_unlock hΦ _ _ _ _)

/-! ## Over an SA trace -/

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro}

/-- `locksWF_state` with the unlock given. -/
theorem locksWF_stateU
    {u : Nat → Set Lock} (hr : ACLocalRunU u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) : LocksWF sp (tr.state y i).locks := by
  induction i with
  | zero =>
    rw [Trace.state, hr.init y hy]
    intro l hl
    exact absurd hl (Set.notMem_empty l)
  | succ i ih =>
    rw [Trace.state]
    split
    · next hc =>
      obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hc.2
      have hcall : tr.CallAt y i ℓ := ⟨hc.1, hℓ⟩
      have hx := hr.exec i ℓ hℓ (hc.1 ▸ hy)
      rw [hc.1] at hx
      have hΦ := (frameIn_of_callAtU hr hy hcall).1
      have := (ih.stepWith y hΦ (hr.time_nonneg i) ℓ.call (hr.lawfulAt hy hcall hΦ)).1
      rw [hx] at this
      exact this
    · exact ih

/-- **`LocksWF` at every honest state** of an SA trace. -/
theorem locksWF_state (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) : LocksWF sp (tr.state y i).locks :=
  locksWF_stateU (hr := hr.toU) (y := y) (hy := hy) (i := i)

/-- `castAt_readPoint_locksWF` with the unlock given. -/
theorem castAt_readPoint_locksWFU
    {u : Nat → Set Lock} (hr : ACLocalRunU u H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) : LocksWF sp e.readPoint.locks := by
  obtain ⟨hc, he⟩ := hc
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have hΦ := (frameIn_of_callAtU hr hy hc).1
  have := ((locksWF_stateU hr hy i).stepWith y hΦ (hr.time_nonneg i) ℓ.call
    (hr.lawfulAt hy hc hΦ)).2
  rw [hx] at this
  exact this e he

/-- **`LocksWF` at the read point of an honest cast.** -/
theorem castAt_readPoint_locksWF (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) : LocksWF sp e.readPoint.locks :=
  castAt_readPoint_locksWFU (hr := hr.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc)

end Consensus.Goldilocks.SA

end
