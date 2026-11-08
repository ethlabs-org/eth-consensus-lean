module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Counts

public section

/-! # Tier A protection, the joint invariant over AC traces: the premise package and the cut
invariant (definitions)

The outage lock invariant (`Obligations/OutageLockSafety/Defs`) over an AC trace of the SA with
the unlock given by a lawful oracle `u` at a write mode `wm` (`ACRunU wm u`), with trivial frames
and ancestry inside `U`. `P` is the protected block: genesis or an origin within `b₀` of label
`σ`; `j₀` is the last label whose early cutoff is at or before `b₀`, `r` the first label whose
last cast time is at or after `b₁`.

* `OutagePremisesAC`: the premise package (`Compose.OutageLockPremises` over the AC trace). The
  pre-`b₀` frontier `FrontierAC` replaces the Sleepy invariant up to `b₀`, the deadline-cut service
  `SyncUntilAC` the pre-`b₀` service, and the tick duty the run's tick at awake public times. The
  FG fields of the composite package (and `NoCollRun`) have no AC counterpart.
* `PrevBaseAC`, `CoverBaseAC`: the bases of the protections over call frames: a fresh lock of
  label `j` and expiry `j + k` on a frame block above `P`. The root-cover disjunct `P ⪯ Σ.F` of the
  composite bases drops: under trivial frames `Φ.F` is genesis, so it would make `P` genesis, and
  every arming field assumes `P` is not genesis.
* `FloorAtAC`, `ProtAC`: a lock of label `j` and expiry at least `m` on a block of `U` above `P`,
  or `P` genesis.
* `OutageVoteInvAC`, `OutageInvAC`: the cut invariant at the cuts before `i`, with the composite's
  fields and index conventions but for its FG fields (`sources`, `caches`, `viable`); the stored
  lock compatibility (`locks`) names a block of `U`.
* `OutageS5StepAC`: the restored-vote step the invariant consumes (`Compose.OutageS5StepAt`).
* `FloorKeepAC`: the per-call lock retention, the one input that reads the oracle: at an honest
  call of the cohort holding a floor of label `j₀ − 1` or `j₀` within its life, when every honest
  vote of slot `slot(t_k) − 1` cast before the call by a validator outside the late wakers extends
  `P` and `2·|Hᶜ ∪ W| < n`, the locks `u k` the call executes with hold such a floor. Each lock
  rule discharges it on its own. -/

namespace Consensus.Goldilocks.Comparison

open SA
open Compose (VoteCompat)

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- The base of the label-`(j₀ − 1)` protection at `x`'s update at cut `c` with label `ℓ`: a fresh
lock of label `j` and expiry `j + k` on a block of the call's frame above `P`. -/
def PrevBaseAC (tr : SATrace sp FGP ro) (P : Blk sp.n FGP) (j : Nat) (x : Fin sp.n) (c : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) : Prop :=
  ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc P L ∧
    (⟨L.root, j, f, j + sp.k⟩ : Lock) ∈ (tr.state x (c + 1)).locks

/-- The base of the label-`j₀` protection at `x`'s first label-`j₀` update at cut `c`: a fresh
lock of label `j` and expiry `j + k` on a block above `P` in the call's frame. -/
def CoverBaseAC (tr : SATrace sp FGP ro) (P : Blk sp.n FGP) (j : Nat) (x : Fin sp.n) (c : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) : Prop :=
  ∃ L f, ℓ.frame.Anc P L ∧ (⟨L.root, j, f, j + sp.k⟩ : Lock) ∈ (tr.state x (c + 1)).locks

theorem prevBaseAC_iff {tr : SATrace sp FGP ro} {P : Blk sp.n FGP} {j : Nat} {x : Fin sp.n}
    {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} :
    PrevBaseAC tr P j x c ℓ ↔ ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc P L ∧
      (⟨L.root, j, f, j + sp.k⟩ : Lock) ∈ (tr.state x (c + 1)).locks :=
  Iff.rfl

theorem coverBaseAC_iff {tr : SATrace sp FGP ro} {P : Blk sp.n FGP} {j : Nat} {x : Fin sp.n}
    {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} :
    CoverBaseAC tr P j x c ℓ ↔
      ∃ L f, ℓ.frame.Anc P L ∧ (⟨L.root, j, f, j + sp.k⟩ : Lock) ∈ (tr.state x (c + 1)).locks :=
  Iff.rfl

/-- **The floor** at `x`, cut `i`: a stored lock of slot `j` and expiry at least `m` on a block of
`U` above `P`. -/
def FloorAtAC (tr : SATrace sp FGP ro) (U : Set (Blk sp.n FGP)) (x : Fin sp.n) (i : Nat)
    (P : Blk sp.n FGP) (j m : Nat) : Prop :=
  ∃ l ∈ (tr.state x i).locks, l.slot = j ∧ m ≤ l.expiry ∧
    ∃ Z ∈ U, Z.root = l.block ∧ Anc U P Z

theorem floorAtAC_iff {tr : SATrace sp FGP ro} {U : Set (Blk sp.n FGP)} {x : Fin sp.n}
    {i : Nat} {P : Blk sp.n FGP} {j m : Nat} :
    FloorAtAC tr U x i P j m ↔ ∃ l ∈ (tr.state x i).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ Z ∈ U, Z.root = l.block ∧ Anc U P Z :=
  Iff.rfl

/-- **The premise package of the outage lock module over AC traces**, for the runs with the
unlock given by `u` at the write mode `wm`. -/
structure OutagePremisesAC (wm : WriteMode) (u : Nat → Set Lock) (proposer : Nat → Fin sp.n)
    (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) where
  /-- The run, with the unlock given. -/
  hrun : ACRunU wm u proposer tr H U
  /-- The slow locks are of width `k`. -/
  hw : wm.width = sp.k
  /-- Trivial frames. -/
  htriv : TrivialFrames tr H
  /-- The tick duty. -/
  htick : TickDuty tr H
  /-- The outage start and stop. -/
  b₀ : Time
  b₁ : Time
  /-- The no-sleep window `[a, z]`. -/
  a : Time
  z : Time
  /-- The protected block. -/
  P : Blk sp.n FGP
  /-- The label of `P` as an origin, the last early label `j₀`, the first restored label `r`. -/
  σ : Nat
  j₀ : Nat
  r : Nat
  /-- The cohort awake at `a`, and the late wakers. -/
  A₀ : Set (Fin sp.n)
  W : Set (Fin sp.n)
  hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀ ∧ b₀ < sp.ts (j₀ + 1 : Nat) + 2 * sp.Δ
  hr : b₁ ≤ sp.ts r + sp.Δ ∧ ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → r ≤ s
  hσ : σ + sp.k < j₀
  hrk : j₀ + 1 ≤ r ∧ r ≤ j₀ + sp.k
  hgap : b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ
  hb₀ : b₀ ≤ b₁
  /-- `P` is a block of `U`: genesis, or an origin within `b₀` of label `σ`. -/
  hP : P ∈ U ∧ (P.root = sp.genesisRoot ∨ OriginWithinAC tr H P σ b₀)
  /-- The pre-`b₀` frontier. -/
  hpre : FrontierAC tr H U b₀
  /-- The service before `b₀`, cut at the deadline. -/
  hpreSvc : SyncUntilAC tr H U b₀
  /-- `f < h_t` at every slot point `t_s + Δ` at or before an honest call. -/
  hFB : ∀ s : Nat, (∃ x ∈ H, ∃ i ℓ, tr.CallAt x i ℓ ∧ sp.ts s + sp.Δ ≤ tr.time i) →
    FaultBound tr H (sp.ts s + sp.Δ)
  /-- The cohort. -/
  hA₀ : A₀ ⊆ H
  hW : W ⊆ H ∧ Disjoint A₀ W
  hcohort : (Hᶜ ∪ W).ncard < A₀.ncard
  /-- Every honest validator awake in `[a, z]` is in `A₀` or a late waker. -/
  hawake : ∀ x ∈ H, ∀ t, a ≤ t → t ≤ z → tr.awake x t → x ∈ A₀ ∪ W
  /-- `A₀` is awake throughout `[a, z]`; its restarts up to `z` are by `a + Δ`. -/
  hA₀awake : ∀ x ∈ A₀, ∀ t, a ≤ t → t ≤ z → tr.awake x t
  hA₀join : ∀ x ∈ A₀, ∀ k, tr.RestartAt x k → tr.time k ≤ z → tr.time k ≤ a + sp.Δ
  ha : a + sp.Δ ≤ sp.ts j₀
  /-- A time up to the last cast time of label `j₀ + k` that some honest call reaches is at or
  before `z`. -/
  hz : ∀ t, t ≤ sp.ts (j₀ + sp.k : Nat) + sp.Δ →
    (∃ x ∈ H, ∃ i ℓ, tr.CallAt x i ℓ ∧ t ≤ tr.time i) → t ≤ z
  /-- Arming: the label-`(j₀ − 1)` lock of every member of `A₀`, when `P` is not genesis and the
  gate is reached. -/
  lockPrev : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y ∈ H, ∃ i ℓ, tr.CallAt y i ℓ ∧ sp.ts j₀ + 2 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, UpdateAt tr x c (j₀ - 1) ℓ ∧ PrevBaseAC tr P (j₀ - 1) x c ℓ
  /-- Arming: the label-`j₀` cover at the first label-`j₀` update of every member of `A₀`, given
  (VA) and (N), when `P` is not genesis and the gate is reached ((F) is vacuous under trivial
  frames). -/
  lockCover : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y ∈ H, ∃ i ℓ, tr.CallAt y i ℓ ∧ sp.ts j₀ + 6 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, UpdateAt tr x c j₀ ℓ ∧ (∀ k < c, ∀ ℓ', ¬ UpdateAt tr x k j₀ ℓ') ∧
    (ℓ.frame.AncestorCandidate P →
     (∀ y ∈ A₀, ∀ j e, VoteAt tr y j e → e.msg.slot = j₀ + 1 → j < c →
        VoteExtends U e.msg P) →
     CoverBaseAC tr P j₀ x c ℓ)
  /-- Post-GST pool delivery: an honest update of a restored label holds every honest vote of
  that slot. -/
  PG : ∀ w ∈ H, ∀ c m ℓ, UpdateAt tr w c m ℓ → r ≤ m →
    ∀ x ∈ H, ∀ i e, VoteAt tr x i e → e.msg.slot = m → e.msg ∈ (tr.state w c).pool m

variable {wm : WriteMode} {u : Nat → Set Lock} {proposer : Nat → Fin sp.n}
  {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- **The protection** of `x` at cut `i` with label `j` through slot `m`: the floor, or `P`
genesis. -/
def ProtAC (D : OutagePremisesAC wm u proposer tr H U) (x : Fin sp.n) (i j m : Nat) : Prop :=
  FloorAtAC tr U x i D.P j m ∨ D.P.root = sp.genesisRoot

theorem protAC_iff {D : OutagePremisesAC wm u proposer tr H U} {x : Fin sp.n} {i j m : Nat} :
    ProtAC D x i j m ↔ FloorAtAC tr U x i D.P j m ∨ D.P.root = sp.genesisRoot :=
  Iff.rfl

/-- The vote half of the invariant at the cuts before `i`: (H) and S5V. -/
structure OutageVoteInvAC (D : OutagePremisesAC wm u proposer tr H U) (i : Nat) : Prop where
  /-- (H) honest votes of slots in `(σ, j₀ + k]` cast at or before `b₀` or by `A₀` extend `P`. -/
  votes : ∀ x ∈ H, ∀ k < i, ∀ e, VoteAt tr x k e → D.σ < e.msg.slot →
    e.msg.slot ≤ D.j₀ + sp.k → (tr.time k ≤ D.b₀ ∨ x ∈ D.A₀) → VoteExtends U e.msg D.P
  /-- S5V at the cuts before `i`: head compatibility with `P` past the lock lifetime. -/
  late : ∀ x ∈ H, ∀ k < i, ∀ e, VoteAt tr x k e → D.j₀ + sp.k < e.msg.slot →
    VoteCompat U e.msg D.P

/-- **The outage lock invariant over AC traces** at the cuts before `i`. -/
structure OutageInvAC (D : OutagePremisesAC wm u proposer tr H U) (i : Nat) : Prop
    extends OutageVoteInvAC D i where
  /-- (R) results at unpolluted labels are compatible with `P`. -/
  results : ∀ y ∈ H, ∀ k < i, ∀ m C CV, ResultAt tr y k m C CV → (m ≤ D.j₀ ∨ D.r ≤ m) →
    Compatible U C D.P
  /-- (i) every stored honest lock names a block of `U` compatible with `P`. -/
  locks : ∀ y ∈ H, ∀ k ≤ i, ∀ l ∈ (tr.state y k).locks,
    ∃ L ∈ U, L.root = l.block ∧ Compatible U L D.P
  /-- (Prot) `A₀` keeps its label-`(j₀ − 1)` lock through its lifetime. -/
  protPrev : ∀ x ∈ D.A₀, ∀ c ℓ, UpdateAt tr x c (D.j₀ - 1) ℓ →
    PrevBaseAC tr D.P (D.j₀ - 1) x c ℓ →
    ∀ k, c < k → k ≤ i → sp.slot (tr.time (k - 1)) ≤ D.j₀ - 1 + sp.k →
      ProtAC D x k (D.j₀ - 1) (D.j₀ - 1 + sp.k)
  /-- (Prot) `A₀` keeps its label-`j₀` lock through slot `j₀ + k`, after a label-`j₀` update with
  the cover base. -/
  protCover : ∀ x ∈ D.A₀, ∀ c ℓ, UpdateAt tr x c D.j₀ ℓ → CoverBaseAC tr D.P D.j₀ x c ℓ →
    ∀ k, c < k → k ≤ i → sp.slot (tr.time (k - 1)) ≤ D.j₀ + sp.k →
      ProtAC D x k D.j₀ (D.j₀ + sp.k)

/-- The restored-vote step that the invariant consumes: from the invariant at `i`, the votes of
cut `i` past the lock lifetime have heads compatible with `P`. -/
def OutageS5StepAC (D : OutagePremisesAC wm u proposer tr H U) : Prop :=
  ∀ i, OutageInvAC D i → ∀ y ∈ H, ∀ e, VoteAt tr y i e → D.j₀ + sp.k < e.msg.slot →
    VoteCompat U e.msg D.P

theorem outageS5StepAC_iff {D : OutagePremisesAC wm u proposer tr H U} :
    OutageS5StepAC D ↔ ∀ i, OutageInvAC D i → ∀ y ∈ H, ∀ e, VoteAt tr y i e →
      D.j₀ + sp.k < e.msg.slot → VoteCompat U e.msg D.P :=
  Iff.rfl

/-- **The per-call lock retention** (the keep): at every honest call of `x ∈ A₀` at cut `k`, for
a label `j ∈ {j₀ − 1, j₀}` and the expiry `j + k`, if `x` holds the floor at `k` within its life
(`slot(t_k) ≤ j + k`), every honest vote of slot `slot(t_k) − 1` cast at a cut before `k` by a
validator outside `W` extends `P`, and `2·|Hᶜ ∪ W| < n`, then the locks `u k` that the call
executes with hold a lock of slot `j` and expiry at least `j + k` on a block of `U` above `P`. -/
def FloorKeepAC (D : OutagePremisesAC wm u proposer tr H U) : Prop :=
  ∀ x ∈ D.A₀, ∀ k ℓ, tr.CallAt x k ℓ → ∀ j, (j = D.j₀ - 1 ∨ j = D.j₀) →
    FloorAtAC tr U x k D.P j (j + sp.k) → sp.slot (tr.time k) ≤ j + sp.k →
    (∀ y ∈ H, y ∉ D.W → ∀ k' < k, ∀ e, VoteAt tr y k' e →
      (e.msg.slot : Int) = (sp.slot (tr.time k) : Int) - 1 → VoteExtends U e.msg D.P) →
    2 * (Hᶜ ∪ D.W).ncard < sp.n →
    ∃ l ∈ u k, l.slot = j ∧ j + sp.k ≤ l.expiry ∧ ∃ Z ∈ U, Z.root = l.block ∧ Anc U D.P Z

theorem floorKeepAC_iff {D : OutagePremisesAC wm u proposer tr H U} :
    FloorKeepAC D ↔ ∀ x ∈ D.A₀, ∀ k ℓ, tr.CallAt x k ℓ → ∀ j, (j = D.j₀ - 1 ∨ j = D.j₀) →
      FloorAtAC tr U x k D.P j (j + sp.k) → sp.slot (tr.time k) ≤ j + sp.k →
      (∀ y ∈ H, y ∉ D.W → ∀ k' < k, ∀ e, VoteAt tr y k' e →
        (e.msg.slot : Int) = (sp.slot (tr.time k) : Int) - 1 → VoteExtends U e.msg D.P) →
      2 * (Hᶜ ∪ D.W).ncard < sp.n →
      ∃ l ∈ u k, l.slot = j ∧ j + sp.k ≤ l.expiry ∧ ∃ Z ∈ U, Z.root = l.block ∧ Anc U D.P Z :=
  Iff.rfl

end Consensus.Goldilocks.Comparison

end
