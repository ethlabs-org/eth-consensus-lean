module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepGlobal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service

public section

/-! # Outage lock safety under growing faults: the premise package and the cut invariant

The vocabulary of `Obligations/OutageLockSafety/Defs` for a time-indexed honest set
`H : Time → Set (Fin n)`. Every node quantifier reads honesty at the cut of the event it
constrains (`HVoteAt`, `y ∈ H (tr.time k)` for the state at cut `k`).

* `OutageLockPremises`: the premise package. The cohort is retained at the window end `z`
  (`A₀ ⊆ H z`, `W ⊆ H z`, `|(H z)ᶜ ∪ W| < |A₀|`); a validator honest at `z` and awake in `[a, z]`
  is in `A₀ ∪ W` (`hawake`). The fault bound is the two count shapes of `SleepyBounds` through
  every horizon that an honest call reaches (`hB`). Every cohort count runs at a time `≤ z`: a
  time up to `t_{j₀+k} + 6Δ` that an honest call reaches is at or before `z` (`hzc`).
* `two_mul_lt`: `2·|(H z)ᶜ ∪ W| < n`; `cohort_classify`: a vote cast in `[a, z]` by a node
  honest then is by `A₀`, by `W`, or by a validator compromised by `z`.
* `OutageVoteInv`, `OutageLockInv`, `OutageS5StepAt`: the cut invariant, with every event field at
  the cut of its event, and the per-node state fields (`locks`, `caches`, `viable`) at a read
  time: a time at which the node is honest and after every cut before the state's cut (a reader
  ready at `t` reads the state of the first cut after `t`, at which it may already be
  compromised; `OutageLockInv.locks_at_cut` and the like give the cut form). The protections
  `protPrev`, `protCover` constrain the state of a member of `A₀` at cuts at which it is honest.
* `ExtendingMajorityAt tr H B q d`: the extending majority of label `q`, with the opponents
  charged at `d` (`(H d)ᶜ` and the slot-`q` casters honest at `d` whose vote does not extend `B`).

The receiver service after GST, `ReceiverServiceAfterAt`, is in `Outage/Service`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The base of the label-`(j₀ − 1)` protection at `x`'s update at cut `c`: root cover, or a
fresh lock of label `j` and expiry `j + k` on a frame block above `P`. -/
def PrevBaseAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (P : SA.Blk sp.n (List (FG.Att sp.n)))
    (j : Nat) (x : Fin sp.n) (c : Nat) (ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) :
    Prop :=
  Anc (tr.HonestBlocksAt H) P (tr.state x c).fg.F ∨
    ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc P L ∧
      (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks

/-- The base of the label-`j₀` protection at `x`'s first label-`j₀` update at cut `c`: root
cover, or a fresh label-`j` lock of expiry `j + k` on a frame block above `P`. -/
def CoverBaseAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (P : SA.Blk sp.n (List (FG.Att sp.n)))
    (j : Nat) (x : Fin sp.n) (c : Nat) (ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) :
    Prop :=
  Anc (tr.HonestBlocksAt H) P (tr.state x c).fg.F ∨
    ∃ L f, ℓ.frame.Anc P L ∧
      (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks

theorem prevBaseAt_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat} {x : Fin sp.n} {c : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} :
    PrevBaseAt tr H P j x c ℓ ↔ Anc (tr.HonestBlocksAt H) P (tr.state x c).fg.F ∨
      ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc P L ∧
        (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks :=
  Iff.rfl

theorem coverBaseAt_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat} {x : Fin sp.n} {c : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} :
    CoverBaseAt tr H P j x c ℓ ↔ Anc (tr.HonestBlocksAt H) P (tr.state x c).fg.F ∨
      ∃ L f, ℓ.frame.Anc P L ∧
        (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks :=
  Iff.rfl

/-- **The premise package of the outage lock module under growing faults**, at trace level. -/
structure OutageLockPremises (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) where
  /-- The outage start and stop. -/
  b₀ : Time
  b₁ : Time
  /-- The no-sleep window `[a, z]`; `z` is also the time the cohort is retained at. -/
  a : Time
  z : Time
  /-- The protected block. -/
  P : SA.Blk sp.n (List (FG.Att sp.n))
  /-- The label of `P` as an origin, the last early label `j₀`, the first restored label `r`. -/
  σ : Nat
  j₀ : Nat
  r : Nat
  /-- The cohort awake at `a`, and the late wakers, both honest at `z`. -/
  A₀ : Set (Fin sp.n)
  W : Set (Fin sp.n)
  hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
  hnc : NoCollRun dg tr
  hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀ ∧ b₀ < sp.ts (j₀ + 1 : Nat) + 2 * sp.Δ
  hr : b₁ ≤ sp.ts r + sp.Δ ∧ ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → r ≤ s
  hσ : σ + sp.k < j₀
  hrk : j₀ + 1 ≤ r ∧ r ≤ j₀ + sp.k
  hgap : b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ
  hb₀ : b₀ ≤ b₁
  /-- `P` is held while honest: genesis, or an origin within `b₀` of label `σ`. -/
  hP : P ∈ tr.HonestBlocksAt H ∧ (P.root = sp.genesisRoot ∨ OriginWithin tr H P σ b₀)
  /-- The Sleepy invariant up to `b₀`. -/
  hpre : SleepyInvariantUpTo tr H b₀
  /-- The pre-`b₀` service. -/
  hpreSvc : SleepyServiceBefore tr H sp.Δ b₀
  /-- The two count shapes through every horizon that an honest call reaches. -/
  hB : ∀ b, (∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ b ≤ tr.time i) → SleepyBounds tr H b
  /-- The cohort, retained at `z`. -/
  hA₀ : A₀ ⊆ H z
  hW : W ⊆ H z ∧ Disjoint A₀ W
  hcohort : ((H z)ᶜ ∪ W).ncard < A₀.ncard
  /-- Every validator honest at `z` and awake in `[a, z]` is in `A₀` or a late waker. -/
  hawake : ∀ x t, a ≤ t → t ≤ z → x ∈ H z → tr.awake x t → x ∈ A₀ ∪ W
  /-- `A₀` is awake throughout `[a, z]`; a restart of `A₀` up to `z` is at most `a + Δ`. -/
  hA₀awake : ∀ x ∈ A₀, ∀ t, a ≤ t → t ≤ z → tr.awake x t
  hA₀join : ∀ x ∈ A₀, ∀ k, tr.RestartAt x k → tr.time k ≤ z → tr.time k ≤ a + sp.Δ
  ha : a + sp.Δ ≤ sp.ts j₀
  /-- Every cohort consumption is inside the window: a time up to `t_{j₀+k} + 6Δ` that an honest
  call reaches is at or before `z`. -/
  hzc : ∀ t, t ≤ sp.ts (j₀ + sp.k : Nat) + 6 * sp.Δ →
    (∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ t ≤ tr.time i) → t ≤ z
  /-- Arming: the label-`(j₀ − 1)` lock of every member of `A₀`, when `P` is not genesis and the
  gate is reached by an honest call. -/
  lockPrev : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y i, y ∈ H (tr.time i) ∧ tr.IsCall y i ∧ sp.ts j₀ + 2 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, SA.UpdateAt tr.projAC x c (j₀ - 1) ℓ ∧ PrevBaseAt tr H P (j₀ - 1) x c ℓ
  /-- Arming: the label-`j₀` cover at the first label-`j₀` update of every member of `A₀`, given
  (F), (VA) and (N), when `P` is not genesis and the gate is reached by an honest call. -/
  lockCover : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y i, y ∈ H (tr.time i) ∧ tr.IsCall y i ∧ sp.ts j₀ + 6 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, SA.UpdateAt tr.projAC x c j₀ ℓ ∧
    (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt tr.projAC x k j₀ ℓ') ∧
    (Compatible (tr.HonestBlocksAt H) (tr.state x c).fg.F P →
     (Anc (tr.HonestBlocksAt H) (tr.state x c).fg.F P → ℓ.frame.AncestorCandidate P) →
     (∀ y ∈ A₀, ∀ j e, HVoteAt tr H y j e → e.msg.slot = j₀ + 1 → j < c →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg P) →
     CoverBaseAt tr H P j₀ x c ℓ)
  /-- Post-GST pool delivery: an update of a restored label by a node honest at it holds every
  vote of that slot cast by a node honest at its cast. -/
  PG : ∀ w c m ℓ, w ∈ H (tr.time c) → SA.UpdateAt tr.projAC w c m ℓ → r ≤ m →
    ∀ x i e, HVoteAt tr H x i e → e.msg.slot = m → e.msg ∈ (tr.state w c).ac.pool m

variable {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

namespace OutageLockPremises

/-- **N6 at the window end**: `2·|(H z)ᶜ ∪ W| < n`. -/
theorem two_mul_lt (D : OutageLockPremises tr H proposer dg) :
    2 * ((H D.z)ᶜ ∪ D.W).ncard < sp.n := by
  have hdisj : Disjoint D.A₀ ((H D.z)ᶜ ∪ D.W) := by
    rw [Set.disjoint_union_right]
    exact ⟨Set.disjoint_left.2 fun x hx hxc => hxc (D.hA₀ hx), D.hW.2⟩
  have h1 := Set.ncard_union_eq hdisj
  have h2 : (D.A₀ ∪ ((H D.z)ᶜ ∪ D.W)).ncard ≤ sp.n := by
    calc (D.A₀ ∪ ((H D.z)ᶜ ∪ D.W)).ncard ≤ (Set.univ : Set (Fin sp.n)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = sp.n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := D.hcohort
  omega

/-- **The cohort classification**: a vote cast in `[a, z]` by a node honest at its cast is by a
member of `A₀`, by a late waker, or by a validator compromised by `z`. -/
theorem cohort_classify (D : OutageLockPremises tr H proposer dg) {x : Fin sp.n} {k : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e) (hka : D.a ≤ tr.time k)
    (hkz : tr.time k ≤ D.z) : x ∈ D.A₀ ∨ x ∈ D.W ∨ x ∉ H D.z := by
  by_cases hxz : x ∈ H D.z
  · obtain ⟨hx, ℓ, hc, -⟩ := hVoteAt_iff.1 hv
    have haw := D.hrun.awake_of_call x k hx ⟨_, projAC_callAt.1 hc⟩
    rcases D.hawake x (tr.time k) hka hkz hxz haw with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hxz)

end OutageLockPremises

/-- The protection of `x` at cut `i` with label `j` through slot `m`: a lock of label `j` and
expiry at least `m` on a frame block above `P`, or root cover (`P ⪯ Σ.F`). -/
def Prot (D : OutageLockPremises tr H proposer dg) (x : Fin sp.n) (i j m : Nat) : Prop :=
  FloorAt tr x i D.P j m ∨ Anc (tr.HonestBlocksAt H) D.P (tr.state x i).fg.F

theorem prot_iff {D : OutageLockPremises tr H proposer dg} {x : Fin sp.n} {i j m : Nat} :
    Prot D x i j m ↔ FloorAt tr x i D.P j m ∨ Anc (tr.HonestBlocksAt H) D.P (tr.state x i).fg.F :=
  Iff.rfl

/-- The vote half of the invariant at the cuts before `i`: (H) and S5V, over votes cast by nodes
honest at their cast. -/
structure OutageVoteInv (D : OutageLockPremises tr H proposer dg) (i : Nat) : Prop where
  /-- (H) votes of slots in `(σ, j₀ + k]` cast at or before `b₀` or by `A₀` extend `P`. -/
  votes : ∀ x k, k < i → ∀ e, HVoteAt tr H x k e → D.σ < e.msg.slot →
    e.msg.slot ≤ D.j₀ + sp.k → (tr.time k ≤ D.b₀ ∨ x ∈ D.A₀) →
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P
  /-- S5V at the cuts before `i`: head compatibility with `P` past the lock lifetime. -/
  late : ∀ x k, k < i → ∀ e, HVoteAt tr H x k e → D.j₀ + sp.k < e.msg.slot →
    VoteCompat (tr.HonestBlocksAt H) e.msg D.P

/-- **The outage lock invariant** at the cuts before `i`, every field at the cut of its event or
state. -/
structure OutageLockInv (D : OutageLockPremises tr H proposer dg) (i : Nat) : Prop
    extends OutageVoteInv D i where
  /-- (R) results at unpolluted labels, by nodes honest at their update, are compatible with
  `P`. -/
  results : ∀ y k, k < i → y ∈ H (tr.time k) → ∀ m C CV, SA.ResultAt tr.projAC y k m C CV →
    (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocksAt H) C D.P
  /-- (L) every lock stored at a cut `k`, read at a time `t` at which its node is honest and after
  every cut before `k`, names a held block compatible with `P`. -/
  locks : ∀ y k t, k ≤ i → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
    ∀ l ∈ (tr.state y k).ac.locks,
      ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocksAt H) L D.P
  /-- (SRC) every FG source of a node honest at its call is compatible with `P`. -/
  sources : ∀ y k, k < i → y ∈ H (tr.time k) → ∀ ℓ C, SA.ToFGAt tr.projAC y k ℓ C →
    Compatible (tr.HonestBlocksAt H) C D.P
  /-- (OB-F) the caches at a cut `k`, read at a time `t` at which their node is honest and after
  every cut before `k`, are compatible with `P`. -/
  caches : ∀ y k t, k ≤ i → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F D.P ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J D.P
  /-- (VA) `P`, when in the frame of a node at a cut `k` read at a time `t` at which it is honest
  and after every cut before `k`, is a viable-ancestor candidate. -/
  viable : ∀ y k t, k ≤ i → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
    D.P ∈ (Node.frame (tr.state y k)).tree →
    (Node.frame (tr.state y k)).AncestorCandidate D.P
  /-- (Prot) `A₀` keeps its label-`(j₀ − 1)` lock, or root cover, through its lifetime, at the
  cuts at which it is honest. -/
  protPrev : ∀ x ∈ D.A₀, ∀ c ℓ, SA.UpdateAt tr.projAC x c (D.j₀ - 1) ℓ →
    PrevBaseAt tr H D.P (D.j₀ - 1) x c ℓ →
    ∀ k, c < k → k ≤ i → x ∈ H (tr.time k) → sp.slot (tr.time (k - 1)) ≤ D.j₀ - 1 + sp.k →
      Prot D x k (D.j₀ - 1) (D.j₀ - 1 + sp.k)
  /-- (Prot) `A₀` keeps its label-`j₀` lock, or root cover, through slot `j₀ + k`, after a
  label-`j₀` update with the cover base, at the cuts at which it is honest. -/
  protCover : ∀ x ∈ D.A₀, ∀ c ℓ, SA.UpdateAt tr.projAC x c D.j₀ ℓ →
    CoverBaseAt tr H D.P D.j₀ x c ℓ →
    ∀ k, c < k → k ≤ i → x ∈ H (tr.time k) → sp.slot (tr.time (k - 1)) ≤ D.j₀ + sp.k →
      Prot D x k D.j₀ (D.j₀ + sp.k)

namespace OutageLockInv

variable {D : OutageLockPremises tr H proposer dg} {i : Nat}

/-- The lock field read at the cut's own time. -/
theorem locks_at_cut (hinv : OutageLockInv D i) {y : Fin sp.n} {k : Nat} (hk : k ≤ i)
    (hy : y ∈ H (tr.time k)) : ∀ l ∈ (tr.state y k).ac.locks,
      ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocksAt H) L D.P :=
  hinv.locks y k (tr.time k) hk (D.hrun.time_nonneg k) (fun _ hk' => D.hrun.time_mono hk'.le) hy

/-- The cache field read at the cut's own time. -/
theorem caches_at_cut (hinv : OutageLockInv D i) {y : Fin sp.n} {k : Nat} (hk : k ≤ i)
    (hy : y ∈ H (tr.time k)) : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F D.P ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J D.P :=
  hinv.caches y k (tr.time k) hk (D.hrun.time_nonneg k) (fun _ hk' => D.hrun.time_mono hk'.le) hy

/-- The viability field read at the cut's own time. -/
theorem viable_at_cut (hinv : OutageLockInv D i) {y : Fin sp.n} {k : Nat} (hk : k ≤ i)
    (hy : y ∈ H (tr.time k)) : D.P ∈ (Node.frame (tr.state y k)).tree →
      (Node.frame (tr.state y k)).AncestorCandidate D.P :=
  hinv.viable y k (tr.time k) hk (D.hrun.time_nonneg k) (fun _ hk' => D.hrun.time_mono hk'.le) hy

end OutageLockInv

/-- The restored-vote step that the lock module consumes: from the invariant at `i`, the votes
of cut `i` past the lock lifetime, by nodes honest then, have heads compatible with `P`. -/
def OutageS5StepAt (D : OutageLockPremises tr H proposer dg) : Prop :=
  ∀ i, OutageLockInv D i → ∀ y e, HVoteAt tr H y i e →
    D.j₀ + sp.k < e.msg.slot → VoteCompat (tr.HonestBlocksAt H) e.msg D.P

theorem outageS5StepAt_iff {D : OutageLockPremises tr H proposer dg} :
    OutageS5StepAt D ↔ ∀ i, OutageLockInv D i → ∀ y e, HVoteAt tr H y i e →
      D.j₀ + sp.k < e.msg.slot → VoteCompat (tr.HonestBlocksAt H) e.msg D.P :=
  Iff.rfl

/-! ### The extending majority, charged at a time -/

/-- The slot-`q` casters still honest at `d` (and honest at their cast) whose vote extends `B`. -/
def ExtendingCastersAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (B : SA.Blk sp.n (List (FG.Att sp.n))) (q : Nat) (d : Time) : Set (Fin sp.n) :=
  {x | x ∈ H d ∧ ∃ k e, HVoteAt tr H x k e ∧ e.msg.slot = q ∧
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B}

/-- The validators compromised by `d`, and the slot-`q` casters still honest at `d` whose vote
does not extend `B`. -/
def OpponentsAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (B : SA.Blk sp.n (List (FG.Att sp.n))) (q : Nat) (d : Time) : Set (Fin sp.n) :=
  (H d)ᶜ ∪ {x | x ∈ H d ∧ ∃ k e, HVoteAt tr H x k e ∧ e.msg.slot = q ∧
    ¬ SA.VoteExtends (tr.HonestBlocksAt H) e.msg B}

/-- **The extending majority of label `q` charged at `d`**: the extending casters still honest
at `d` outnumber the opponents at `d`. -/
def ExtendingMajorityAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (B : SA.Blk sp.n (List (FG.Att sp.n))) (q : Nat) (d : Time) : Prop :=
  (OpponentsAt tr H B q d).ncard < (ExtendingCastersAt tr H B q d).ncard

theorem extendingCastersAt_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} {d : Time}
    {x : Fin sp.n} :
    x ∈ ExtendingCastersAt tr H B q d ↔ x ∈ H d ∧ ∃ k e, HVoteAt tr H x k e ∧
      e.msg.slot = q ∧ SA.VoteExtends (tr.HonestBlocksAt H) e.msg B :=
  Iff.rfl

theorem opponentsAt_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} {d : Time}
    {x : Fin sp.n} :
    x ∈ OpponentsAt tr H B q d ↔ x ∈ (H d)ᶜ ∨ (x ∈ H d ∧ ∃ k e, HVoteAt tr H x k e ∧
      e.msg.slot = q ∧ ¬ SA.VoteExtends (tr.HonestBlocksAt H) e.msg B) :=
  Iff.rfl

theorem extendingMajorityAt_iff {B : SA.Blk sp.n (List (FG.Att sp.n))} {q : Nat} {d : Time} :
    ExtendingMajorityAt tr H B q d ↔
      (OpponentsAt tr H B q d).ncard < (ExtendingCastersAt tr H B q d).ncard :=
  Iff.rfl

end Consensus.Goldilocks.Compose.Growing

end
