module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal

public section

/-! # Outage lock safety: the premise package and the cut invariant (definitions)

The outage lock-safety card (workbench `repos/consensus-lean/notes/outage/outage_lock_safety.md`
at af18331, §2–§3), at trace level. `P` is the protected block (`OutageArming.origin`): genesis or
an origin within `b₀` of label `σ`. `j₀` is the last label whose early cutoff is at or before
`b₀`, `r` the first label whose last cast time is at or after `b₁`; the labels `≤ j₀` and `≥ r`
are unpolluted.

* `OutageLockPremises`: the premise package (§2). The arming inputs `lockPrev` and `lockCover`
  are fields in trace form; `lockCover` is conditional on (F), (VA) and (N), which the induction
  discharges. The post-GST pool delivery `PG` is a field. The S5 step is not a field: it is the
  hypothesis `hS5` of `outage_lock_inv`, which consumes `OutageLockInv D i`.
* `OutageLockInv D i`: the cut invariant (§3) at the cuts before `i`: honest votes of slots in
  `(σ, j₀ + k]` cast at or before `b₀` or by the cohort `A₀` extend `P` (`votes`); later votes are
  compatible with `P` (`late`, from S5); results at unpolluted labels are compatible with `P`
  (`results`); stored honest locks (`locks`, the card's (i)), FG sources (`sources`) and the
  caches `Σ.F`, `Σ.J` (`caches`, OB-F) are compatible with `P`; `P`, when in the frame, is a
  viable-ancestor candidate (`viable`); and `A₀` keeps its label-`(j₀ − 1)` and label-`j₀` locks
  (or root cover) through their lifetimes (`protPrev`, `protCover`, O2).

Differences in form from the card's §2 listing, each as the card's own proofs or the landed
arming use them:

* the fault bound (`hFB`) is stated at every slot point that precedes an honest call (R-late
  reads it at `t_m + Δ` for `m > j₀ + k`, §5.1, from `EtaSleepyOn`);
* the cohort premises are stated over times (`hA₀awake`, `hA₀join`) and bound the no-sleep window
  end `z` from below at the times of honest calls (`hz`); a restart of `A₀` up to `z` is by
  `a + Δ`, the bound the abstract run interface `GoldilocksRun` gives (the first call after
  waking, at the first public time from `a`; `restart_le_of_awake`), so `ha` is
  `a + Δ ≤ t_{j₀}` (the simulated trace restarts at the wake time itself);
* `lockPrev` and `lockCover` carry the antecedents of the landed `OutageArming`: `P` is not
  genesis, and the gate is reached by an honest call (the horizon bound);
* `protPrev` and `protCover` take the bases `PrevBase` and `CoverBase` as antecedents (no
  uniqueness of the update cut is needed). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

section VoteCompat

variable {FGP : Type} {n : Nat}

/-- The head of the vote `v` is a block of `U` compatible with `B` (the S5 form, read-back F1:
regression votes with head below `B` satisfy it). -/
def VoteCompat (U : Set (SA.Blk n FGP)) (v : Vote n) (B : SA.Blk n FGP) : Prop :=
  ∃ Hd ∈ U, Hd.root = v.head ∧ Compatible U Hd B

theorem voteCompat_iff {U : Set (SA.Blk n FGP)} {v : Vote n} {B : SA.Blk n FGP} :
    VoteCompat U v B ↔ ∃ Hd ∈ U, Hd.root = v.head ∧ Compatible U Hd B :=
  Iff.rfl

/-- A vote that extends `B` is compatible with it. -/
theorem _root_.Consensus.Goldilocks.SA.VoteExtends.voteCompat {sp : SAParams}
    {U : Set (SA.Blk sp.n FGP)} {v : Vote sp.n} {B : SA.Blk sp.n FGP}
    (h : SA.VoteExtends U v B) : VoteCompat U v B :=
  let ⟨Hd, hHd, hr, hB⟩ := h
  ⟨Hd, hHd, hr, Or.inr hB⟩

end VoteCompat

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The base of the label-`(j₀ − 1)` protection at `x`'s update at cut `c`
(`OutageArming.lockPrev`): root cover, or a fresh lock of label `j₀ − 1` on a frame block above
`P`. -/
def PrevBase (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (P : SA.Blk sp.n (List (FG.Att sp.n)))
    (j : Nat) (x : Fin sp.n) (c : Nat) (ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) :
    Prop :=
  Anc (tr.HonestBlocks H) P (tr.state x c).fg.F ∨
    ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc P L ∧
      (⟨L.root, j, f⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks

/-- The base of the label-`j₀` protection at `x`'s first label-`j₀` update at cut `c`
(`OutageArming.lockCover`): root cover, a fresh label-`j₀` lock on a frame block above `P`, or a
live own label-`(j₀ + 1)` lock whose viable ancestor is above `P` (the veto branch). -/
def CoverBase (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (P : SA.Blk sp.n (List (FG.Att sp.n)))
    (j : Nat) (x : Fin sp.n) (c : Nat) (ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) :
    Prop :=
  Anc (tr.HonestBlocks H) P (tr.state x c).fg.F ∨
    (∃ L f, ℓ.frame.Anc P L ∧ (⟨L.root, j, f⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks) ∨
    (∃ V ∈ SA.liveLockBlocks sp (tr.state x c).ac.locks ℓ.frame (tr.time c),
      ℓ.frame.Anc P V ∧ ∃ l ∈ (tr.state x c).ac.locks, l.slot = j + 1 ∧
        ∃ B₀ ∈ ℓ.frame.tree, B₀.root = l.block ∧ V = ℓ.frame.viableAncestor B₀)

theorem prevBase_iff {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat} {x : Fin sp.n} {c : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} :
    PrevBase tr H P j x c ℓ ↔ Anc (tr.HonestBlocks H) P (tr.state x c).fg.F ∨
      ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc P L ∧
        (⟨L.root, j, f⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks :=
  Iff.rfl

theorem coverBase_iff {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat} {x : Fin sp.n} {c : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} :
    CoverBase tr H P j x c ℓ ↔ Anc (tr.HonestBlocks H) P (tr.state x c).fg.F ∨
      (∃ L f, ℓ.frame.Anc P L ∧ (⟨L.root, j, f⟩ : SA.Lock) ∈ (tr.state x (c + 1)).ac.locks) ∨
      (∃ V ∈ SA.liveLockBlocks sp (tr.state x c).ac.locks ℓ.frame (tr.time c),
        ℓ.frame.Anc P V ∧ ∃ l ∈ (tr.state x c).ac.locks, l.slot = j + 1 ∧
          ∃ B₀ ∈ ℓ.frame.tree, B₀.root = l.block ∧ V = ℓ.frame.viableAncestor B₀) :=
  Iff.rfl

/-- **The premise package of the outage lock module** (card §2), at trace level. -/
structure OutageLockPremises (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) where
  /-- The outage start and stop. -/
  b₀ : Time
  b₁ : Time
  /-- The no-sleep window `[a, z]`. -/
  a : Time
  z : Time
  /-- The protected block (`OutageArming.origin`). -/
  P : SA.Blk sp.n (List (FG.Att sp.n))
  /-- The label of `P` as an origin, the last early label `j₀`, the first restored label `r`. -/
  σ : Nat
  j₀ : Nat
  r : Nat
  /-- The cohort awake at `a`, and the late wakers. -/
  A₀ : Set (Fin sp.n)
  W : Set (Fin sp.n)
  hrun : GoldilocksRun proposer dg H tr
  hnc : NoCollRun dg tr
  hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀ ∧ b₀ < sp.ts (j₀ + 1 : Nat) + 2 * sp.Δ
  hr : b₁ ≤ sp.ts r + sp.Δ ∧ ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → r ≤ s
  hσ : σ + sp.k < j₀
  hrk : j₀ + 1 ≤ r ∧ r ≤ j₀ + sp.k
  hgap : b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ
  hb₀ : b₀ ≤ b₁
  /-- `P` is an honest block: genesis, or an origin within `b₀` of label `σ`. -/
  hP : P ∈ tr.HonestBlocks H ∧ (P.root = sp.genesisRoot ∨ OriginWithin tr H P σ b₀)
  /-- The Sleepy invariant up to `b₀`. -/
  hpre : SleepyInvariantUpTo tr H b₀
  /-- The pre-`b₀` service. -/
  hpreSvc : SleepyServiceBefore tr H sp.Δ b₀
  /-- `f < h_t` at every slot point `t_s + Δ` at or before an honest call. -/
  hFB : ∀ s : Nat, (∃ x ∈ H, ∃ i, tr.IsCall x i ∧ sp.ts s + sp.Δ ≤ tr.time i) →
    tr.FaultBound H (sp.ts s + sp.Δ)
  /-- The cohort. -/
  hA₀ : A₀ ⊆ H
  hW : W ⊆ H ∧ Disjoint A₀ W
  hcohort : (Hᶜ ∪ W).ncard < A₀.ncard
  /-- Every honest validator awake in `[a, z]` is in `A₀` or a late waker. -/
  hawake : ∀ x ∈ H, ∀ t, a ≤ t → t ≤ z → tr.awake x t → x ∈ A₀ ∪ W
  /-- `A₀` is awake throughout `[a, z]`; a restart of `A₀` up to `z` is at most `a + Δ`, the
  abstract-interface bound (`GoldilocksRun`: the first call after waking, at the first public
  time from `a`). -/
  hA₀awake : ∀ x ∈ A₀, ∀ t, a ≤ t → t ≤ z → tr.awake x t
  hA₀join : ∀ x ∈ A₀, ∀ k, tr.RestartAt x k → tr.time k ≤ z → tr.time k ≤ a + sp.Δ
  ha : a + sp.Δ ≤ sp.ts j₀
  /-- A time up to the last cast time of label `j₀ + k` that some honest call reaches is at or
  before `z` (the window end clamps at the horizon). -/
  hz : ∀ t, t ≤ sp.ts (j₀ + sp.k : Nat) + sp.Δ → (∃ x ∈ H, ∃ i, tr.IsCall x i ∧ t ≤ tr.time i) →
    t ≤ z
  /-- Arming: the label-`(j₀ − 1)` lock of every member of `A₀`, when `P` is not genesis and the
  gate is reached (`OutageArming.lockPrev`; the horizon bound is a reached honest call). -/
  lockPrev : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y ∈ H, ∃ i, tr.IsCall y i ∧ sp.ts j₀ + 2 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, SA.UpdateAt tr.projAC x c (j₀ - 1) ℓ ∧ PrevBase tr H P (j₀ - 1) x c ℓ
  /-- Arming: the label-`j₀` cover at the first label-`j₀` update of every member of `A₀`, given
  (F), (VA) and (N), when `P` is not genesis and the gate is reached (`OutageArming.lockCover`). -/
  lockCover : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y ∈ H, ∃ i, tr.IsCall y i ∧ sp.ts j₀ + 6 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, SA.UpdateAt tr.projAC x c j₀ ℓ ∧
    (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt tr.projAC x k j₀ ℓ') ∧
    (Compatible (tr.HonestBlocks H) (tr.state x c).fg.F P →
     (Anc (tr.HonestBlocks H) (tr.state x c).fg.F P → ℓ.frame.AncestorCandidate P) →
     (∀ y ∈ A₀, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = j₀ + 1 → j < c →
        SA.VoteExtends (tr.HonestBlocks H) e.msg P) →
     CoverBase tr H P j₀ x c ℓ)
  /-- Post-GST pool delivery (O4): an honest update of a restored label holds every honest vote of
  that slot. -/
  PG : ∀ w ∈ H, ∀ c m ℓ, SA.UpdateAt tr.projAC w c m ℓ → r ≤ m →
    ∀ x ∈ H, ∀ i e, SA.VoteAt tr.projAC x i e → e.msg.slot = m → e.msg ∈ (tr.state w c).ac.pool m

variable {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- The protection of `x` at cut `i` with label `j`: a lock of label `j` on a frame block above
`P` (`FloorAt`), or root cover (`P ⪯ Σ.F`). -/
def Prot (D : OutageLockPremises tr H proposer dg) (x : Fin sp.n) (i j : Nat) : Prop :=
  FloorAt tr x i D.P j ∨ Anc (tr.HonestBlocks H) D.P (tr.state x i).fg.F

/-- The protection of the cover: label `j₀`, or the veto replacement of label `j₀ + 1`. -/
def Prot₀ (D : OutageLockPremises tr H proposer dg) (x : Fin sp.n) (i : Nat) : Prop :=
  Prot D x i D.j₀ ∨ FloorAt tr x i D.P (D.j₀ + 1)

theorem prot_iff {D : OutageLockPremises tr H proposer dg} {x : Fin sp.n} {i j : Nat} :
    Prot D x i j ↔ FloorAt tr x i D.P j ∨ Anc (tr.HonestBlocks H) D.P (tr.state x i).fg.F :=
  Iff.rfl

theorem prot₀_iff {D : OutageLockPremises tr H proposer dg} {x : Fin sp.n} {i : Nat} :
    Prot₀ D x i ↔ Prot D x i D.j₀ ∨ FloorAt tr x i D.P (D.j₀ + 1) :=
  Iff.rfl

/-- The vote half of the invariant at the cuts before `i`: (H) and S5V. -/
structure OutageVoteInv (D : OutageLockPremises tr H proposer dg) (i : Nat) : Prop where
  /-- (H) honest votes of slots in `(σ, j₀ + k]` cast at or before `b₀` or by `A₀` extend `P`. -/
  votes : ∀ x ∈ H, ∀ k < i, ∀ e, SA.VoteAt tr.projAC x k e → D.σ < e.msg.slot →
    e.msg.slot ≤ D.j₀ + sp.k → (tr.time k ≤ D.b₀ ∨ x ∈ D.A₀) →
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P
  /-- S5V at the cuts before `i`: head compatibility with `P` past the lock lifetime. -/
  late : ∀ x ∈ H, ∀ k < i, ∀ e, SA.VoteAt tr.projAC x k e → D.j₀ + sp.k < e.msg.slot →
    VoteCompat (tr.HonestBlocks H) e.msg D.P

/-- **The outage lock invariant** at the cuts before `i` (card §3). -/
structure OutageLockInv (D : OutageLockPremises tr H proposer dg) (i : Nat) : Prop
    extends OutageVoteInv D i where
  /-- (R) results at unpolluted labels are compatible with `P`. -/
  results : ∀ y ∈ H, ∀ k < i, ∀ m C CV, SA.ResultAt tr.projAC y k m C CV →
    (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocks H) C D.P
  /-- (L) = (i): every stored honest lock names a held block compatible with `P`. -/
  locks : ∀ y ∈ H, ∀ k ≤ i, ∀ l ∈ (tr.state y k).ac.locks,
    ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L D.P
  /-- (SRC) every honest FG source is compatible with `P`. -/
  sources : ∀ y ∈ H, ∀ k < i, ∀ ℓ C, SA.ToFGAt tr.projAC y k ℓ C →
    Compatible (tr.HonestBlocks H) C D.P
  /-- (OB-F) the caches are compatible with `P`. -/
  caches : ∀ y ∈ H, ∀ k ≤ i, Compatible (tr.HonestBlocks H) (tr.state y k).fg.F D.P ∧
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.J D.P
  /-- (VA) `P`, when in the frame, is a viable-ancestor candidate. -/
  viable : ∀ y ∈ H, ∀ k ≤ i, D.P ∈ (Node.frame (tr.state y k)).tree →
    (Node.frame (tr.state y k)).AncestorCandidate D.P
  /-- (Prot) `A₀` keeps its label-`(j₀ − 1)` lock, or root cover, through its lifetime. -/
  protPrev : ∀ x ∈ D.A₀, ∀ c ℓ, SA.UpdateAt tr.projAC x c (D.j₀ - 1) ℓ →
    PrevBase tr H D.P (D.j₀ - 1) x c ℓ →
    ∀ k, c < k → k ≤ i → sp.slot (tr.time (k - 1)) ≤ D.j₀ - 1 + sp.k → Prot D x k (D.j₀ - 1)
  /-- (Prot₀) `A₀` keeps its label-`j₀` lock, its label-`(j₀ + 1)` veto replacement, or root
  cover, through slot `j₀ + k`, after a label-`j₀` update with the cover base. -/
  protCover : ∀ x ∈ D.A₀, ∀ c ℓ, SA.UpdateAt tr.projAC x c D.j₀ ℓ →
    CoverBase tr H D.P D.j₀ x c ℓ →
    ∀ k, c < k → k ≤ i → sp.slot (tr.time (k - 1)) ≤ D.j₀ + sp.k → Prot₀ D x k

/-- The S5 step that the lock module consumes (856c1db, restated cut-indexed; read-back F2): from
the invariant at `i`, the votes of cut `i` past the lock lifetime have heads compatible with
`P`. -/
def OutageS5StepAt (D : OutageLockPremises tr H proposer dg) : Prop :=
  ∀ i, OutageLockInv D i → ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e →
    D.j₀ + sp.k < e.msg.slot → VoteCompat (tr.HonestBlocks H) e.msg D.P

theorem outageS5StepAt_iff {D : OutageLockPremises tr H proposer dg} :
    OutageS5StepAt D ↔ ∀ i, OutageLockInv D i → ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e →
      D.j₀ + sp.k < e.msg.slot → VoteCompat (tr.HonestBlocks H) e.msg D.P :=
  Iff.rfl

end Consensus.Goldilocks.Compose

end
