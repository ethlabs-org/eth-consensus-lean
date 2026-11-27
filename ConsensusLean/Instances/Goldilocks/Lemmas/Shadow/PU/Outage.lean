module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.S5Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Geometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count

public section

/-! # P-U shadow, V-B7: the Outage lock premises and the run-level Hi walk

The stock premise package `OutageLockPremises` and the cut invariant `OutageLockInv`
(`Growing/Outage/Defs`) copied over the shadow run: the same fields, with `hrun` a
`Growing.GoldilocksRun'` and the viability field over `Node.frame'`. The shadow trace type is the
stock one (`GoldilocksTrace' = GoldilocksTrace`), so every trace-level notion
(`HVoteAt`, `HonestBlocksAt`, `PrevBaseAt`, `CommitteeFacts`, `HiAt`) is reused.

The run-level Hi walk `anc_getHead_of_hi'` is the snapshot core of `Shadow/PU/S5Walk` with the
shadow run facts it reads. Those facts that are not yet proved are the named stubs of
`Shadow/PU/Outage` section `RunFacts'` (each is the stock fact over `GoldilocksRun'`). -/

namespace Consensus.Goldilocks.Shadow.PU

open Consensus.Goldilocks.Compose Consensus.Goldilocks.Compose.Growing
open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The premise package of the outage lock module under growing faults**, at trace level, from
the starts `ini`. -/
structure OutageLockPremises' (tr : GoldilocksTrace' sp ro) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (ini : Fin sp.n → (goldilocksNode' sp ro).State) where
  /-- The outage start and stop. -/
  b₀ : Time
  b₁ : Time
  /-- The proof window `[a, z]`; `z` is also the time the holders and opponents are
  retained at. -/
  a : Time
  z : Time
  /-- The protected block. -/
  P : AC.Blk sp.n (List (FG.Att sp.n))
  /-- The label of `P` as an origin, the last early label `j₀`, the first restored label `r`. -/
  σ : Nat
  j₀ : Nat
  r : Nat
  /-- The holders `A₀`, awake throughout `[a, z]`, and the look-back opponents `W` (other
  validators awake in the window), both honest at `z`. -/
  A₀ : Set (Fin sp.n)
  W : Set (Fin sp.n)
  hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini
  /-- The slot committees: the run's selection for each slot's vote role. -/
  K : AC.CommitteeDict sp.n
  /-- Size, P, frames and the gate for `K`. -/
  facts : CommitteeFacts tr H K
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
  hB : ∀ b, (∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ b ≤ tr.time i) → SleepyBoundsFrom tr H 0 b
  /-- CS and current-slot CS2 inside the slot committees, through every horizon that an honest
  call reaches. -/
  hBK : ∀ b, (∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ b ≤ tr.time i) →
    CommitteeBoundsFrom tr H K 0 b
  /-- The holders and opponents, retained at `z`. -/
  hA₀ : A₀ ⊆ H z
  hW : W ⊆ H z ∧ Disjoint A₀ W
  /-- Inside each slot committee of the band, the holders outnumber the compromised and the
  look-back opponents, at every label that an honest call reaches. -/
  hopponentsK : ∀ m, j₀ ≤ m → m ≤ j₀ + sp.k →
    (∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ sp.ts m ≤ tr.time i) →
    (K.committee m ∩ ((H z)ᶜ ∪ W)).ncard < (K.committee m ∩ A₀).ncard
  /-- Every validator honest at `z` and awake in `[a, z]` is in `A₀` or in `W`. -/
  hawake : ∀ x t, a ≤ t → t ≤ z → x ∈ H z → tr.awake x t → x ∈ A₀ ∪ W
  /-- `A₀` is awake throughout `[a, z]`; a restart of `A₀` up to `z` is at most `a + Δ`. -/
  hA₀awake : ∀ x ∈ A₀, ∀ t, a ≤ t → t ≤ z → tr.awake x t
  hA₀join : ∀ x ∈ A₀, ∀ k, tr.RestartAt x k → tr.time k ≤ z → tr.time k ≤ a + sp.Δ
  ha : a + sp.Δ ≤ sp.ts j₀
  /-- Every holder and opponent count is inside the window: a time up to `t_{j₀+k} + 6Δ` that an
  honest call reaches is at or before `z`. -/
  hzc : ∀ t, t ≤ sp.ts (j₀ + sp.k : Nat) + 6 * sp.Δ →
    (∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ t ≤ tr.time i) → t ≤ z
  /-- Arming: the label-`(j₀ − 1)` lock of every member of `A₀`, when `P` is not genesis and the
  gate is reached by an honest call. -/
  lockPrev : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y i, y ∈ H (tr.time i) ∧ tr.IsCall y i ∧ sp.ts j₀ + 2 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, AC.UpdateAt tr.projAC x c (j₀ - 1) ℓ ∧ PrevBaseAt tr H P (j₀ - 1) x c ℓ
  /-- Arming: the label-`j₀` cover at the first label-`j₀` update of every member of `A₀`, given
  (F), (VA) and (N), when `P` is not genesis and the gate is reached by an honest call. -/
  lockCover : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y i, y ∈ H (tr.time i) ∧ tr.IsCall y i ∧ sp.ts j₀ + 6 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, AC.UpdateAt tr.projAC x c j₀ ℓ ∧
    (∀ k < c, ∀ ℓ', ¬ AC.UpdateAt tr.projAC x k j₀ ℓ') ∧
    (Compatible (tr.HonestBlocksAt H) (tr.state x c).fg.F P →
     (Anc (tr.HonestBlocksAt H) (tr.state x c).fg.F P → ℓ.frame.AncestorCandidate P) →
     (∀ y ∈ A₀, ∀ j e, HVoteAt tr H y j e → e.msg.slot = j₀ + 1 → j < c →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg P) →
     CoverBaseAt tr H P j₀ x c ℓ)
  /-- Post-GST pool delivery: an update of a restored label by a node honest at it holds every
  vote of that slot cast by a node honest at its cast, or two other votes of that slot by the
  same validator (which may be compromised after its cast). -/
  PG : ∀ w c m ℓ, w ∈ H (tr.time c) → AC.UpdateAt tr.projAC w c m ℓ → r ≤ m →
    ∀ x i e, HVoteAt tr H x i e → e.msg.slot = m → e.msg ∈ (tr.state w c).ac.pool m ∨
      e.msg.val ∈ AC.equivocators {v | v ∈ (tr.state w c).ac.pool m}


variable {tr : GoldilocksTrace' sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode' sp ro).State}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- The protection of `x` at cut `i` with label `j` through slot `m`: a lock of label `j` and
expiry at least `m` on a frame block above `P`, or root cover (`P ⪯ Σ.F`). -/
def Prot' (D : OutageLockPremises' tr H proposer dg ini) (x : Fin sp.n) (i j m : Nat) : Prop :=
  FloorAt tr x i D.P j m ∨ Anc (tr.HonestBlocksAt H) D.P (tr.state x i).fg.F

theorem prot'_iff {D : OutageLockPremises' tr H proposer dg ini} {x : Fin sp.n} {i j m : Nat} :
    Prot' D x i j m ↔ FloorAt tr x i D.P j m ∨ Anc (tr.HonestBlocksAt H) D.P (tr.state x i).fg.F :=
  Iff.rfl

/-- The vote half of the invariant at the cuts before `i`: (H) and S5V, over votes cast by nodes
honest at their cast. -/
structure OutageVoteInv' (D : OutageLockPremises' tr H proposer dg ini) (i : Nat) : Prop where
  /-- (H) votes of slots in `(σ, j₀ + k]` cast at or before `b₀` or by `A₀` extend `P`. -/
  votes : ∀ x k, k < i → ∀ e, HVoteAt tr H x k e → D.σ < e.msg.slot →
    e.msg.slot ≤ D.j₀ + sp.k → (tr.time k ≤ D.b₀ ∨ x ∈ D.A₀) →
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg D.P
  /-- S5V at the cuts before `i`: head compatibility with `P` past the lock lifetime. -/
  late : ∀ x k, k < i → ∀ e, HVoteAt tr H x k e → D.j₀ + sp.k < e.msg.slot →
    VoteCompat (tr.HonestBlocksAt H) e.msg D.P

/-- **The outage lock invariant** at the cuts before `i`, every field at the cut of its event or
state. -/
structure OutageLockInv' (D : OutageLockPremises' tr H proposer dg ini) (i : Nat) : Prop
    extends OutageVoteInv' D i where
  /-- (R) results at unpolluted labels, by nodes honest at their update, are compatible with
  `P`. -/
  results : ∀ y k, k < i → y ∈ H (tr.time k) → ∀ m C CV, AC.ResultAt tr.projAC y k m C CV →
    (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocksAt H) C D.P
  /-- (L) every lock stored at a cut `k`, read at a time `t` at which its node is honest and after
  every cut before `k`, names a held block compatible with `P`. -/
  locks : ∀ y k t, k ≤ i → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
    ∀ l ∈ (tr.state y k).ac.locks,
      ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocksAt H) L D.P
  /-- (SRC) every FG source of a node honest at its call is compatible with `P`. -/
  sources : ∀ y k, k < i → y ∈ H (tr.time k) → ∀ ℓ C, AC.ToFGAt tr.projAC y k ℓ C →
    Compatible (tr.HonestBlocksAt H) C D.P
  /-- (OB-F) the caches at a cut `k`, read at a time `t` at which their node is honest and after
  every cut before `k`, are compatible with `P`. -/
  caches : ∀ y k t, k ≤ i → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F D.P ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J D.P
  /-- (VA) `P`, when in the frame of a node at a cut `k` read at a time `t` at which it is honest
  and after every cut before `k`, is a viable-ancestor candidate. -/
  viable : ∀ y k t, k ≤ i → 0 ≤ t → (∀ k' < k, tr.time k' ≤ t) → y ∈ H t →
    D.P ∈ (Node.frame' (tr.state y k)).tree →
    (Node.frame' (tr.state y k)).AncestorCandidate D.P
  /-- (Prot) `A₀` keeps its label-`(j₀ − 1)` lock, or root cover, through its lifetime, at the
  cuts at which it is honest. -/
  protPrev : ∀ x ∈ D.A₀, ∀ c ℓ, AC.UpdateAt tr.projAC x c (D.j₀ - 1) ℓ →
    PrevBaseAt tr H D.P (D.j₀ - 1) x c ℓ →
    ∀ k, c < k → k ≤ i → x ∈ H (tr.time k) → sp.slot (tr.time (k - 1)) ≤ D.j₀ - 1 + sp.k →
      Prot' D x k (D.j₀ - 1) (D.j₀ - 1 + sp.k)
  /-- (Prot) `A₀` keeps its label-`j₀` lock, or root cover, through slot `j₀ + k`, after a
  label-`j₀` update with the cover base, at the cuts at which it is honest. -/
  protCover : ∀ x ∈ D.A₀, ∀ c ℓ, AC.UpdateAt tr.projAC x c D.j₀ ℓ →
    CoverBaseAt tr H D.P D.j₀ x c ℓ →
    ∀ k, c < k → k ≤ i → x ∈ H (tr.time k) → sp.slot (tr.time (k - 1)) ≤ D.j₀ + sp.k →
      Prot' D x k D.j₀ (D.j₀ + sp.k)

namespace OutageLockInv'

variable {D : OutageLockPremises' tr H proposer dg ini} {i : Nat}

/-- The lock field read at the cut's own time. -/
theorem locks_at_cut (hinv : OutageLockInv' D i) {y : Fin sp.n} {k : Nat} (hk : k ≤ i)
    (hy : y ∈ H (tr.time k)) : ∀ l ∈ (tr.state y k).ac.locks,
      ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocksAt H) L D.P :=
  hinv.locks y k (tr.time k) hk (D.hrun.time_nonneg k) (fun _ hk' => D.hrun.time_mono hk'.le) hy

/-- The cache field read at the cut's own time. -/
theorem caches_at_cut (hinv : OutageLockInv' D i) {y : Fin sp.n} {k : Nat} (hk : k ≤ i)
    (hy : y ∈ H (tr.time k)) : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F D.P ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J D.P :=
  hinv.caches y k (tr.time k) hk (D.hrun.time_nonneg k) (fun _ hk' => D.hrun.time_mono hk'.le) hy

/-- The viability field read at the cut's own time. -/
theorem viable_at_cut (hinv : OutageLockInv' D i) {y : Fin sp.n} {k : Nat} (hk : k ≤ i)
    (hy : y ∈ H (tr.time k)) : D.P ∈ (Node.frame' (tr.state y k)).tree →
      (Node.frame' (tr.state y k)).AncestorCandidate D.P :=
  hinv.viable y k (tr.time k) hk (D.hrun.time_nonneg k) (fun _ hk' => D.hrun.time_mono hk'.le) hy

end OutageLockInv'

/-! ## Run facts over the shadow run (`RunFacts'`)

The stock facts the Hi walk reads, restated over `Growing.GoldilocksRun'`, each with the stock
signature (`Growing/Outage/Local`, `Count`, `S5Geometry`; `Healing/M1/FrameKey`). A proof still to
be written is a `sorry` here; none is assumed elsewhere. -/

section RunFacts'

variable {d : Time} {y : Fin sp.n} {i : Nat}

/-- Stub (V-A4 at a read time): the shadow frame of a node honest at `d` is well formed. -/
theorem frameOK_at' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    FrameOK (Node.frame' (tr.state y i)) := by
  sorry

/-- The shadow store of a node honest at `d` is `Reachable'`: the static fact on the prefix through
`d` (`Growing.GoldilocksRun'.upTo`, lane B0b). -/
theorem reachable_at' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.Reachable' (goldilocksNode' sp ro).genesisPayload := by
  have h := Node.fg_reachable_at' (hrun.upTo hd).toLocalRun' hy i
  rwa [Trace.upTo_state tr y hi] at h

/-- Stub: ancestry in the honest blocks, ending in the tree, is ancestry in the store. -/
theorem held_anc_at' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d)
    {A W : AC.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocksAt H) A W)
    (hW : W ∈ (tr.state y i).fg.tree) : (tr.state y i).fg.Anc A W := by
  sorry

/-- Stub: the honest blocks are coherent. -/
theorem honestBlocksAt_coherent'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) : Coherent (tr.HonestBlocksAt H) := by
  sorry

/-- A shadow-reachable store has a block of state height `h_max` (lane C0's `cache_invariants'`). -/
theorem hmax_block_of_reachable' {acp₀ : Payload sp.n}
    {st : Store sp.toParams (Payload sp.n)} (h : st.Reachable' acp₀) :
    ∃ B ∈ st.tree, (st.σ B.root).h = st.hmax :=
  (Store.cache_invariants' h).2.2.2.2.2.1

/-- `h_j < h_max` at a shadow-reachable store: the cached justification is the state of a held
block, whose `h_j` is below its height, which is at most `h_max`. -/
theorem hj_lt_hmax_of_reachable' {acp₀ : Payload sp.n}
    {st : Store sp.toParams (Payload sp.n)} (h : st.Reachable' acp₀) : st.hj < st.hmax := by
  obtain ⟨-, -, -, ⟨Bj, hBj, -, hBjhj⟩, hge, -, -⟩ := Store.cache_invariants' h
  exact hBjhj ▸ (Store.hj_lt_h_with Store.finalitySpec_updateFinality' h.reachableWith hBj).trans_le
    (hge Bj hBj)

/-- `h_j < h_max` at the shadow store of a node honest at `d`. -/
theorem hj_lt_hmax_at' (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.hj < (tr.state y i).fg.hmax :=
  hj_lt_hmax_of_reachable' (reachable_at' hrun hd hy hi)

end RunFacts'

/-- **G3′ over the shadow run (stub).** Under Hi at cut `k`, read at a time `t` at which the node
is honest after every earlier cut, with `2 f_t < n`, every block of its tree at state height at
least `h_j + 1` is strictly above `P` (stock `above_of_hi_height_at`). Not yet proved. -/
theorem above_of_hi_height_at' (D : OutageLockPremises' tr H proposer dg ini) {i : Nat}
    (hinv : OutageLockInv' D i) {y : Fin sp.n} {k : Nat} {t : Time} (hk : k ≤ i) (ht0 : 0 ≤ t)
    (ht : ∀ k' < k, tr.time k' ≤ t) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n)
    (hHi : HiAt tr H D.P y k) {X : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree)
    (hh : (tr.state y k).fg.hj + 1 ≤ ((tr.state y k).fg.σ X.root).h) :
    Anc (tr.HonestBlocksAt H) D.P X ∧ X.root ≠ D.P.root := by
  sorry

/-- **The Hi walk over the shadow run.** Under Hi at cut `i`, `w` honest at `t_i` with
`2 f_{t_i} < n`, a head walk of the shadow frame over the viable tree of an ancestor-closed domain
extends `P`, when the live lock blocks of the walked state are compatible with `P` and the
domain's viable tree is nonempty or the domain is the whole tree.

The stock `anc_getHead_of_hi` with its `hcond` branch collapsed (`anc_getHead_of_hi'_core`). -/
theorem anc_getHead_of_hi' (D : OutageLockPremises' tr H proposer dg ini) {i : Nat}
    (hinv : OutageLockInv' D i) {w : Fin sp.n} (hw : w ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) (hHi : HiAt tr H D.P w i) (A : AC.ACState sp.n)
    (t : Time) (V : AC.View sp.n) (σ : Int)
    {dom : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    (hdom : dom ⊆ (Node.frame' (tr.state w i)).tree)
    (hdomA : ∀ B ∈ dom, ∀ X, (Node.frame' (tr.state w i)).Anc X B → X ∈ dom)
    (hne : ((Node.frame' (tr.state w i)).viableTree dom).Nonempty ∨
      (Node.frame' (tr.state w i)).tree ⊆ dom)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp A.locks (Node.frame' (tr.state w i)) t,
      Compatible (tr.HonestBlocksAt H) L D.P) :
    Anc (tr.HonestBlocksAt H) D.P
      (AC.getHead sp A (Node.frame' (tr.state w i)) t
        ((Node.frame' (tr.state w i)).viableTree dom) V σ) := by
  have hd := D.hrun.time_nonneg i
  have ht : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => D.hrun.time_mono hk.le
  obtain ⟨hPJ, hJP⟩ := hiAt_iff.1 hHi
  rw [Node.frame'_eq] at hdom hdomA hne hlocks ⊢
  refine anc_getHead_of_hi'_core (honestBlocksAt_coherent' D.hrun D.hnc)
    (by simpa [Node.frame'_eq] using frameOK_at' D.hrun hd hw ht) (tree_held_at hd hw ht)
    (hj_lt_hmax_at' D.hrun hd hw ht) (hmax_block_of_reachable' (reachable_at' D.hrun hd hw ht))
    hPJ hJP (fun hX hh => above_of_hi_height_at' D hinv le_rfl hd ht hw hf hHi hX hh)
    (hinv.caches_at_cut le_rfl hw).1
    (fun hY hXY => held_anc_at' D.hrun D.hnc hd hw ht hXY hY) A t V σ hdom hdomA hne hlocks

end Consensus.Goldilocks.Shadow.PU

end
