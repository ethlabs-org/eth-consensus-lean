module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockRule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace
public import Mathlib.Data.Int.Interval

public section

/-! # Counting stored locks and saved rows along a node's calls

A generic count for any lawful lock store `S`, read along the calls of one node of an AC trace:

* **a lock step** (`LockStep`): a call leaves the stored locks `W` as they are, or moves them by an
  unlock of any stage (`LockStore.unlockWith`), and then, only at a tick at `t_s + 2Δ` with
  `s > 0`, adds the new locks of the update of slot `s − 1` (`LockStore.addLocksWith`), one per
  fast bit, of slot `s − 1` and expiry at most `s − 1 + k`, and fast only with the fast arm
  (`NewOK`);
* **the invariant** (`HeldLockInv`, `lockInv_of_steps`): the stored locks are one per (slot, fast
  bit) (`KeyInj`), each has expiry at most its slot plus `k`, is fast only with the fast arm, and
  its slot `j` has a tick of the node at `t_{j+1} + 2Δ` before the cut (`TickBefore`: such a tick
  precedes the cut; it is the tick whose update wrote the lock's slot). With one tick per node and
  time, the update of each slot runs once, so its new locks meet no stored lock of their slot;
* **the count** (`held_encard_le`): the stored locks unexpired at a cut are at most
  `(fast arm ? 2 : 1) · k`, one per (slot, fast bit) over the slots `slot(t) − k ≤ j < slot(t)`;
* **saved rows** (`RowStep`, `rowInv_of_steps`, `row_lt_slot`, `rows_encard_le`): a call keeps
  or drops rows and, only at a tick at `t_s + 2Δ` with `s > 0`, adds the row `s − 1`, so every
  row is of a slot before `slot(t)`, and the rows of the slots `slot(t) − w ≤ j` are at most
  `w`. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {S : LockStore}

variable (S) in
/-- The stored locks are one per (slot, fast bit). -/
def KeyInj (L : Set S.Lk) : Prop :=
  ∀ w ∈ L, ∀ w' ∈ L, (S.lock w).slot = (S.lock w').slot → (S.lock w).fast = (S.lock w').fast →
    w = w'

variable (S sp) in
/-- The new locks of the update of slot `j`: of slot `j`, expiry at most `j + k`, fast only with
the fast arm, one per fast bit. -/
def NewOK (fastArm : Bool) (j : Nat) (N : Set S.Lk) : Prop :=
  (∀ w ∈ N, (S.lock w).slot = j ∧ (S.lock w).expiry ≤ j + sp.k ∧
    (fastArm = false → (S.lock w).fast = false)) ∧ KeyInj S N

variable (S sp) in
/-- **A lock step** at a call at `t` (`tick`: the call is a tick): the stored locks `W` become
`W'`, kept or moved by an unlock, then, at a tick at `t_s + 2Δ` with `s > 0`, with the update's
new locks of slot `s − 1` added. -/
def LockStep (fastArm : Bool) (W W' : Set S.Lk) (Φ : Frm sp.n FGP) (t : Time) (tick : Prop) :
    Prop :=
  ∃ X : Set S.Lk, (X = W ∨ ∃ (σ : Type) (E : UnlockStage sp S σ) (c : σ) (s : Int)
      (V : View sp.n), X = S.unlockWith sp E c W Φ t s V) ∧
    (W' = X ∨ (tick ∧ t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧
      ∃ N, NewOK sp S fastArm (sp.slot t - 1) N ∧ W' = S.addLocksWith sp X N Φ t))

theorem keyInj_iff (L : Set S.Lk) : KeyInj S L ↔ ∀ w ∈ L, ∀ w' ∈ L,
    (S.lock w).slot = (S.lock w').slot → (S.lock w).fast = (S.lock w').fast → w = w' :=
  Iff.rfl

theorem newOK_iff (fastArm : Bool) (j : Nat) (N : Set S.Lk) :
    NewOK sp S fastArm j N ↔ (∀ w ∈ N, (S.lock w).slot = j ∧ (S.lock w).expiry ≤ j + sp.k ∧
      (fastArm = false → (S.lock w).fast = false)) ∧ KeyInj S N :=
  Iff.rfl

theorem lockStep_iff (fastArm : Bool) (W W' : Set S.Lk) (Φ : Frm sp.n FGP) (t : Time)
    (tick : Prop) : LockStep sp S fastArm W W' Φ t tick ↔
      ∃ X : Set S.Lk, (X = W ∨ ∃ (σ : Type) (E : UnlockStage sp S σ) (c : σ) (s : Int)
        (V : View sp.n), X = S.unlockWith sp E c W Φ t s V) ∧
      (W' = X ∨ (tick ∧ t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧
        ∃ N, NewOK sp S fastArm (sp.slot t - 1) N ∧ W' = S.addLocksWith sp X N Φ t)) :=
  Iff.rfl

theorem LockStep.mono_tick {fastArm : Bool} {W W' : Set S.Lk} {Φ : Frm sp.n FGP} {t : Time}
    {tk tk' : Prop} (h : LockStep sp S fastArm W W' Φ t tk) (htk : tk → tk') :
    LockStep sp S fastArm W W' Φ t tk' := by
  obtain ⟨X, hX, hW⟩ := (lockStep_iff _ _ _ _ _ _).1 h
  exact (lockStep_iff _ _ _ _ _ _).2 ⟨X, hX, hW.imp id fun ⟨h1, h2⟩ => ⟨htk h1, h2⟩⟩

/-! ### The moves keep the fields and one lock per key -/

private theorem liveLocks_fields (hS : S.Lawful) {L : Set S.Lk} {Φ : Frm sp.n FGP} {t : Time}
    {w' : S.Lk} (h : w' ∈ S.liveLocks sp L Φ t) :
    ∃ w ∈ L, (S.lock w').slot = (S.lock w).slot ∧ (S.lock w').fast = (S.lock w).fast ∧
      (S.lock w').expiry = (S.lock w).expiry := by
  obtain ⟨w, hw, -, -, -, -, rfl⟩ := h
  obtain ⟨-, h1, h2, h3⟩ := LockStore.lock_withBlock_fields hS w _
  exact ⟨w, hw, h1, h2, h3⟩

private theorem keyInj_liveLocks (hS : S.Lawful) {Φ : Frm sp.n FGP}
    (hΦ : Set.InjOn Block.root Φ.tree) {L : Set S.Lk} (hL : KeyInj S L) (t : Time) :
    KeyInj S (S.liveLocks sp L Φ t) := by
  rintro _ ⟨w₁, hw₁, B₁, hB₁, hr₁, -, rfl⟩ _ ⟨w₂, hw₂, B₂, hB₂, hr₂, -, rfl⟩ hs hf
  obtain ⟨-, s₁, f₁, -⟩ := LockStore.lock_withBlock_fields hS w₁ (Φ.viableAncestor B₁).root
  obtain ⟨-, s₂, f₂, -⟩ := LockStore.lock_withBlock_fields hS w₂ (Φ.viableAncestor B₂).root
  obtain rfl := hL w₁ hw₁ w₂ hw₂ (s₁.symm.trans (hs.trans s₂)) (f₁.symm.trans (hf.trans f₂))
  obtain rfl := hΦ hB₁ hB₂ (hr₁.trans hr₂.symm)
  rfl

private theorem unlockWith_fields (hS : S.Lawful) {σ : Type} {E : UnlockStage sp S σ} {c : σ}
    {L : Set S.Lk} {Φ : Frm sp.n FGP} {t : Time} {s : Int} {V : View sp.n} {w' : S.Lk}
    (h : w' ∈ S.unlockWith sp E c L Φ t s V) :
    ∃ w ∈ L, (S.lock w').slot = (S.lock w).slot ∧ (S.lock w').fast = (S.lock w).fast ∧
      (S.lock w').expiry = (S.lock w).expiry := by
  obtain ⟨w, hw, B, -, -, rfl⟩ := h
  obtain ⟨w₀, hw₀, e1, e2, e3⟩ := liveLocks_fields hS hw
  refine ⟨w₀, hw₀, ?_⟩
  split_ifs
  · obtain ⟨-, h1, h2, h3⟩ := LockStore.lock_withBlock_fields hS w _
    exact ⟨h1.trans e1, h2.trans e2, h3.trans e3⟩
  · exact ⟨e1, e2, e3⟩

private theorem keyInj_unlockWith (hS : S.Lawful) {σ : Type} {E : UnlockStage sp S σ} {c : σ}
    {Φ : Frm sp.n FGP} (hΦ : Set.InjOn Block.root Φ.tree) {L : Set S.Lk} (hL : KeyInj S L)
    (t : Time) (s : Int) (V : View sp.n) : KeyInj S (S.unlockWith sp E c L Φ t s V) := by
  have hL' := keyInj_liveLocks hS hΦ hL t
  have key : ∀ w B, (S.lock (if ((S.lock w).slot : Int) < s then
      S.withBlock w (E.target c Φ V s w (unlockTarget sp Φ V s B)).root else w)).slot =
        (S.lock w).slot ∧ (S.lock (if ((S.lock w).slot : Int) < s then
      S.withBlock w (E.target c Φ V s w (unlockTarget sp Φ V s B)).root else w)).fast =
        (S.lock w).fast := by
    intro w B
    split_ifs
    · obtain ⟨-, h1, h2, -⟩ := LockStore.lock_withBlock_fields hS w _
      exact ⟨h1, h2⟩
    · exact ⟨rfl, rfl⟩
  rintro _ ⟨w₁, hw₁, B₁, hB₁, hr₁, rfl⟩ _ ⟨w₂, hw₂, B₂, hB₂, hr₂, rfl⟩ hs hf
  obtain ⟨s₁, f₁⟩ := key w₁ B₁
  obtain ⟨s₂, f₂⟩ := key w₂ B₂
  obtain rfl := hL' w₁ hw₁ w₂ hw₂ (s₁.symm.trans (hs.trans s₂)) (f₁.symm.trans (hf.trans f₂))
  obtain rfl := hΦ hB₁ hB₂ (hr₁.trans hr₂.symm)
  rfl

/-! ### The invariant along a node's calls -/

variable {A : ACInterface sp.toParams FGP} {tr : ACTrace A} {y : Fin sp.n}

/-- The tick of node `y` at a cut before `i` at `t_{j+1} + 2Δ`. -/
def TickBefore (tr : ACTrace A) (y : Fin sp.n) (i j : Nat) : Prop :=
  ∃ i' < i, ∃ ℓ' : ACLabel A, tr.CallAt y i' ℓ' ∧ ℓ'.call = .tick ∧
    tr.time i' = sp.ts ((j + 1 : Nat) : Int) + 2 * sp.Δ

private theorem TickBefore.mono {i i' j : Nat} (h : TickBefore tr y i j) (hi : i ≤ i') :
    TickBefore tr y i' j := by
  obtain ⟨k, hk, ℓ', h1, h2, h3⟩ := h
  exact ⟨k, by omega, ℓ', h1, h2, h3⟩

variable (S) in
/-- **The lock invariant** of the stored locks `W` before cut `i` of node `y`. -/
def HeldLockInv (tr : ACTrace A) (y : Fin sp.n) (fastArm : Bool) (i : Nat) (W : Set S.Lk) : Prop :=
  KeyInj S W ∧ ∀ w ∈ W, (S.lock w).expiry ≤ (S.lock w).slot + sp.k ∧
    (fastArm = false → (S.lock w).fast = false) ∧ TickBefore tr y i (S.lock w).slot

private theorem state_succ_of_call' {i : Nat} {ℓ : ACLabel A} (hc : tr.CallAt y i ℓ) :
    tr.state y (i + 1) = tr.post i := by
  simp [Trace.state, hc.1, hc.2]

private theorem state_succ_of_not' {i : Nat} (hn : ∀ ℓ, ¬ tr.CallAt y i ℓ) :
    tr.state y (i + 1) = tr.state y i := by
  rw [Trace.state]
  split_ifs with h
  · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 h.2
    exact absurd ⟨h.1, hℓ⟩ (hn ℓ)
  · rfl

/-- **The lock invariant holds at every cut** of a node whose calls are lock steps, from no
stored lock, with one tick per time. -/
theorem lockInv_of_steps (hS : S.Lawful) (st : A.State → Set S.Lk) (fastArm : Bool)
    (h0 : st (tr.state y 0) = ∅)
    (hstep : ∀ i ℓ, tr.CallAt y i ℓ → ∃ Φ : Frm sp.n FGP, Set.InjOn Block.root Φ.tree ∧
      LockStep sp S fastArm (st (tr.state y i)) (st (tr.post i)) Φ (tr.time i)
        (ℓ.call = .tick))
    (hone : ∀ i j (ℓ ℓ' : ACLabel A), tr.CallAt y i ℓ → tr.CallAt y j ℓ' → ℓ.call = .tick →
      ℓ'.call = .tick → tr.time i = tr.time j → i = j) :
    ∀ i, HeldLockInv S tr y fastArm i (st (tr.state y i)) := by
  intro i
  induction i with
  | zero =>
    rw [h0]
    exact ⟨fun _ h => absurd h (Set.notMem_empty _), fun _ h => absurd h (Set.notMem_empty _)⟩
  | succ i ih =>
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      rw [state_succ_of_call' hc]
      obtain ⟨Φ, hΦ, X, hX, hW'⟩ := hstep i ℓ hc
      -- the moved locks keep the invariant, with the witnesses before `i`
      have hXi : HeldLockInv S tr y fastArm i X := by
        rcases hX with rfl | ⟨σ, E, c, s, V, rfl⟩
        · exact ih
        · refine ⟨keyInj_unlockWith hS hΦ ih.1 _ _ _, fun w' hw' => ?_⟩
          obtain ⟨w, hw, e1, e2, e3⟩ := unlockWith_fields hS hw'
          obtain ⟨h1, h2, h3⟩ := ih.2 w hw
          refine ⟨by rw [e1, e3]; exact h1, fun hf => by rw [e2]; exact h2 hf, by rw [e1]; exact h3⟩
      have hX1 : HeldLockInv S tr y fastArm (i + 1) X :=
        ⟨hXi.1, fun w hw => let h := hXi.2 w hw; ⟨h.1, h.2.1, h.2.2.mono (by omega)⟩⟩
      rcases hW' with h | ⟨htick, ht, hs, N, hN, h⟩
      · rw [h]; exact hX1
      · rw [h, LockStore.addLocksWith_eq]
        -- the new locks are of slot `slot(t) − 1`; no moved lock is of that slot
        have hdis : ∀ w ∈ X, (S.lock w).slot ≠ sp.slot (tr.time i) - 1 := by
          intro w hw he
          obtain ⟨-, -, i', hi', ℓ', hc', hk', ht'⟩ := hXi.2 w hw
          have hti : tr.time i' = tr.time i := by
            rw [ht', he, Nat.sub_add_cancel hs]
            exact ht.symm
          exact absurd (hone i' i ℓ' ℓ hc' hc hk' htick hti) (by omega)
        have hU : KeyInj S (X ∪ N) := by
          rintro w₁ (h₁ | h₁) w₂ (h₂ | h₂) hsl hf
          · exact hXi.1 w₁ h₁ w₂ h₂ hsl hf
          · exact absurd (hsl.trans (hN.1 w₂ h₂).1) (hdis w₁ h₁)
          · exact absurd (hsl.symm.trans (hN.1 w₁ h₁).1) (hdis w₂ h₂)
          · exact hN.2 w₁ h₁ w₂ h₂ hsl hf
        refine ⟨keyInj_liveLocks hS hΦ hU _, fun w' hw' => ?_⟩
        obtain ⟨w, hw, e1, e2, e3⟩ := liveLocks_fields hS hw'
        rw [e1, e2, e3]
        rcases hw with hw | hw
        · exact hX1.2 w hw
        · obtain ⟨hsl, hex, hfa⟩ := hN.1 w hw
          refine ⟨by rw [hsl]; exact hex, hfa, ⟨i, by omega, ℓ, hc, htick, ?_⟩⟩
          rw [hsl, Nat.sub_add_cancel hs]
          exact ht
    · push Not at hc
      rw [state_succ_of_not' hc]
      exact ⟨ih.1, fun w hw => let h := ih.2 w hw; ⟨h.1, h.2.1, h.2.2.mono (by omega)⟩⟩

theorem heldLockInv_iff (fastArm : Bool) (i : Nat) (W : Set S.Lk) :
    HeldLockInv S tr y fastArm i W ↔ KeyInj S W ∧ ∀ w ∈ W,
      (S.lock w).expiry ≤ (S.lock w).slot + sp.k ∧ (fastArm = false → (S.lock w).fast = false) ∧
      TickBefore tr y i (S.lock w).slot :=
  Iff.rfl

/-- A slot with a tick of the node at `t_{j+1} + 2Δ` before cut `i` is before `slot(t_i)`. -/
theorem lt_slot_of_tickBefore (hmono : Monotone tr.time) {i : Nat} (ht : 0 ≤ tr.time i) {j : Nat}
    (h : TickBefore tr y i j) : j < sp.slot (tr.time i) := by
  obtain ⟨i', hi', -, -, -, hti'⟩ := h
  have hle : sp.ts ((j + 1 : Nat) : Int) ≤ tr.time i := by
    have := hmono hi'.le
    have hΔ := sp.toParams.hΔ
    linarith
  have := (ts_le_iff_le_slot sp ht _).1 hle
  omega

/-- **The count**: under the lock invariant, the stored locks unexpired at `t_i` are at most
`(fast arm ? 2 : 1) · k`. -/
theorem held_encard_le (hmono : Monotone tr.time) {i : Nat} (ht : 0 ≤ tr.time i)
    {fastArm : Bool} {W : Set S.Lk} (h : HeldLockInv S tr y fastArm i W) :
    {w | w ∈ W ∧ (S.lock w).LiveAt sp (tr.time i)}.encard ≤
      ((if fastArm then 2 else 1) * sp.k : ℕ) := by
  classical
  set T := sp.slot (tr.time i)
  let bits : Finset Bool := if fastArm then {false, true} else {false}
  let K : Finset (Nat × Bool) := Finset.Ico (T - sp.k) T ×ˢ bits
  have hK : K.card ≤ (if fastArm then 2 else 1) * sp.k := by
    rw [Finset.card_product, Nat.card_Ico, mul_comm]
    refine Nat.mul_le_mul ?_ (by omega)
    dsimp only [bits]
    split_ifs <;> simp
  calc {w | w ∈ W ∧ (S.lock w).LiveAt sp (tr.time i)}.encard
      ≤ (K : Set (Nat × Bool)).encard := by
        refine Set.encard_le_encard_of_injOn (f := fun w => ((S.lock w).slot, (S.lock w).fast))
          ?_ ?_
        · rintro w ⟨hw, hlive⟩
          obtain ⟨hex, hfa, htb⟩ := h.2 w hw
          have hlt := lt_slot_of_tickBefore hmono ht htb
          have hlive' : T ≤ (S.lock w).expiry := hlive
          simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Ico, Set.mem_Ico,
            Finset.mem_coe, K, bits]
          refine ⟨⟨by omega, hlt⟩, ?_⟩
          split_ifs with hf
          · cases (S.lock w).fast <;> simp
          · simp [hfa (by simpa using hf)]
        · rintro w₁ ⟨h₁, -⟩ w₂ ⟨h₂, -⟩ he
          simp only [Prod.mk.injEq] at he
          exact h.1 w₁ h₁ w₂ h₂ he.1 he.2
    _ = (K.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard K
    _ ≤ _ := by exact_mod_cast hK

/-! ### Saved rows -/

/-- **A row step** at a call at `t`: the rows `R'` after are among the rows `R` before and, at a
tick at `t_s + 2Δ` with `s > 0`, the row `s − 1`. -/
def RowStep (R R' : Set Int) (t : Time) (tick : Prop) : Prop :=
  ∀ j ∈ R', j ∈ R ∨ (tick ∧ t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧
    j = ((sp.slot t - 1 : Nat) : Int))

theorem rowStep_iff (R R' : Set Int) (t : Time) (tick : Prop) :
    RowStep (sp := sp) R R' t tick ↔ ∀ j ∈ R', j ∈ R ∨ (tick ∧ t = sp.ts (sp.slot t) + 2 * sp.Δ ∧
      0 < sp.slot t ∧ j = ((sp.slot t - 1 : Nat) : Int)) :=
  Iff.rfl

theorem RowStep.mono_tick {R R' : Set Int} {t : Time} {tk tk' : Prop}
    (h : RowStep (sp := sp) R R' t tk) (htk : tk → tk') : RowStep (sp := sp) R R' t tk' :=
  (rowStep_iff _ _ _ _).2 fun j hj =>
    ((rowStep_iff _ _ _ _).1 h j hj).imp id fun ⟨h1, h2⟩ => ⟨htk h1, h2⟩

/-- **The row invariant holds at every cut** of a node whose calls are row steps, from no row:
every row is of a slot `j ≥ 0` with a tick of the node at `t_{j+1} + 2Δ` before. -/
theorem rowInv_of_steps (rows : A.State → Set Int) (h0 : rows (tr.state y 0) = ∅)
    (hstep : ∀ i ℓ, tr.CallAt y i ℓ →
      RowStep (sp := sp) (rows (tr.state y i)) (rows (tr.post i)) (tr.time i) (ℓ.call = .tick)) :
    ∀ i, ∀ j ∈ rows (tr.state y i), ∃ j' : Nat, j = j' ∧ TickBefore tr y i j' := by
  intro i
  induction i with
  | zero => rw [h0]; exact fun _ h => absurd h (Set.notMem_empty _)
  | succ i ih =>
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      rw [state_succ_of_call' hc]
      intro j hj
      rcases hstep i ℓ hc j hj with hj | ⟨htick, ht, hs, rfl⟩
      · obtain ⟨j', rfl, h⟩ := ih j hj
        exact ⟨j', rfl, h.mono (by omega)⟩
      · refine ⟨_, rfl, i, by omega, ℓ, hc, htick, ?_⟩
        rw [Nat.sub_add_cancel hs]
        exact ht
    · push Not at hc
      rw [state_succ_of_not' hc]
      intro j hj
      obtain ⟨j', rfl, h⟩ := ih j hj
      exact ⟨j', rfl, h.mono (by omega)⟩

/-- **No future rows.** -/
theorem row_lt_slot (hmono : Monotone tr.time) {i : Nat} (ht : 0 ≤ tr.time i) {R : Set Int}
    (h : ∀ j ∈ R, ∃ j' : Nat, j = j' ∧ TickBefore tr y i j') :
    ∀ j ∈ R, j < sp.slot (tr.time i) := by
  intro j hj
  obtain ⟨j', rfl, htb⟩ := h j hj
  exact_mod_cast lt_slot_of_tickBefore hmono ht htb

/-- **The working rows**: rows of slots before `slot(t)` in the window `slot(t) − w ≤ j` are at
most `w`. -/
theorem rows_encard_le {R : Set Int} {T : Nat} (hR : ∀ j ∈ R, j < T) (w : Nat) :
    {j | (T : Int) - (w : Nat) ≤ j ∧ j ∈ R}.encard ≤ (w : ℕ) := by
  calc {j | (T : Int) - (w : Nat) ≤ j ∧ j ∈ R}.encard
      ≤ (Finset.Ico ((T : Int) - w) T : Set Int).encard := by
        refine Set.encard_le_encard fun j ⟨h1, h2⟩ => ?_
        simp only [Finset.coe_Ico, Set.mem_Ico]
        exact ⟨h1, hR j h2⟩
    _ = ((Finset.Ico ((T : Int) - w) T).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (w : ℕ) := by
        rw [Int.card_Ico]
        exact_mod_cast (show ((T : Int) - (T - w)).toNat ≤ w by omega)

end Consensus.Goldilocks.SA

end
