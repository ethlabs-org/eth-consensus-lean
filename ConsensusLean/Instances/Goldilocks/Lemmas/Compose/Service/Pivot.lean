module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees

public section

/-! # Goldilocks under `Sleepy`: the pivot of an honest proposal

workbench#12 §2.1, §2.2: for the honest proposal `P` of slot `s`, made from `ac_proposal`'s duty
head `Q = P.parent`, a block `D` on the proposal walk (between its start and `Q`) such that every
honest slot-`s` voter whose earlier honest slot-`s` votes are `P` (the caller's strong induction on
the cut) has a walk that passes a block `X` of the path from `D` through `Q` to `P`: `X` is `P`,
or between `D` and `Q` in the proposer's tree.

`D` is the deepest block of the proposal walk among its start and the *old origins* (`OldOrigin`:
the regular origins of labels at most `s − 2` and the optimistic origins of labels at most
`s − 1`, the events before `t_s`); it is genesis or an old origin, and every old origin is below
it. At a voter, the anchor is `fc_root` or a live lock block. `fc_root` and a lock of a slot other
than `s` sit below an old origin (`lock_origin`, the slot of an origin before the vote), hence
below `D`; a lock of slot `s` sits below an optimistic selection with an honest supporter among
the earlier slot-`s` votes, which are `P`. So the anchor is below `D` (then `X = D`, which the
vote extends by S2), or on `P`'s chain above `D` (then `X` is the anchor).

The proposal walk passes every old origin (`proposal_passes_old`, `SA.anc_getHead`) and its
anchor is below one (`proposal_anchor_old`). Open (private, `sorry`): the proposer holds every old
origin or has it below `Σ.F` (`proposal_holds_old`), the children towards it win the proposal
walk (`proposal_best_toward_old`, the counts of §2.1), no honest optimistic check of slot `s`
precedes the proposal (`proposal_no_optimistic`, so the proposer's stored locks are of slots below
`s`), and `fc_root` is below an old origin at the proposal and at a vote
(`proposal_fcRoot_old`, `vote_fcRoot_old`: the source labels before `t_s`, §2). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ### Blocks and walks -/

section Walk

variable {FGP : Type}

/-- A descendant inside the tree of a block of the tree is in the tree. -/
private theorem mem_of_anc_left {Φ : SA.Frm sp.n FGP} {A B : SA.Blk sp.n FGP} (h : Φ.Anc A B)
    (hA : A ∈ Φ.tree) : B ∈ Φ.tree := by
  by_cases hAB : A = B
  · exact hAB ▸ hA
  · exact (Anc.mem h hAB).2

/-- A block between two blocks of a well-formed frame's tree (ancestry in a coherent `U` holding
the tree) is in the tree. -/
private theorem mem_between {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U) {Φ : SA.Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {A B C : SA.Blk sp.n FGP} (hA : A ∈ Φ.tree)
    (hC : C ∈ Φ.tree) (hAB : Anc U A B) (hBC : Anc U B C) : B ∈ Φ.tree := by
  have hFB : Anc U Φ.F B := (Anc.mono hΦU (hΦ.rooted.2 A hA)).trans hAB
  revert hC
  induction hBC with
  | refl => exact id
  | @tail c d hBc e ih =>
    intro hd
    refine ih ?_
    by_cases hdF : d = Φ.F
    · subst hdF
      have h1 := (Anc.slot_le hU (hFB.trans hBc)).1
      have h2 := hU.2 c e.1 _ e.2.1 e.2.2
      omega
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    obtain rfl : p = c := hU.1 (hΦU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    exact hp.1

/-- A proper ancestor of a block is an ancestor of its parent. -/
private theorem anc_parent {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U)
    {A B Q : SA.Blk sp.n FGP} (h : Anc U A B) (hne : A ≠ B) (hBQ : B.parent = some Q.root)
    (hQ : Q ∈ U) : Anc U A Q := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hAY, hY⟩
  · exact absurd heq.symm hne
  obtain rfl : Y = Q := hU.1 hY.1 hQ (Option.some_injective _ (hY.2.2.symm.trans hBQ))
  exact hAY

/-- The anchor is a live lock block or `fc_root`. -/
private theorem anchor_mem (Φ : SA.Frm sp.n FGP) (A : SA.SAState sp.n) (t : Time) :
    SA.getAnchor sp A Φ t ∈ SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} := by
  unfold SA.getAnchor
  cases hd : SA.deepest Φ (SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
  | none => exact Or.inr rfl
  | some D => exact (SA.deepest_mem hd).1

/-- The anchor of a well-formed frame is in its tree. -/
private theorem anchor_tree {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SA.SAState sp.n)
    (t : Time) : SA.getAnchor sp A Φ t ∈ Φ.tree := by
  rcases anchor_mem Φ A t with h | h
  · exact h.1
  · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem

/-- The duty head of a proposal is the walk of the full viable tree from its start, the anchor
after the proposal's unlocking. -/
private theorem acProposal_walk {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    ∃ A₁ : SA.SAState sp.n,
      A₁.locks = SA.unlock sp A.locks Φ t ((sp.slot t : Int) - 1) (SA.View.ofLists pay) ∧
      d.start = SA.getAnchor sp A₁ Φ t ∧
      d.head = SA.getHead sp A₁ Φ t (Φ.viableTree Φ.tree) (SA.View.ofLists pay)
        ((sp.slot t : Int) - 1) := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl, rfl⟩

/-- The proposal walk goes from its start, in the tree, to the duty head. -/
private theorem start_anc_head {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {t : Time} {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) : d.start ∈ Φ.tree ∧ Φ.Anc d.start d.head := by
  obtain ⟨A₁, -, hst, hhd⟩ := acProposal_walk h
  have hs := anchor_tree hΦ A₁ t
  rw [hhd, hst]
  exact ⟨hs, SA.anc_ghost (fun _ h => h.1) _ hs⟩

/-- Two vote times: a regular origin of label `m` (written at `t_m + 6Δ`) before a slot-`s` vote
(at most `t_s + Δ`) has `m + 2 ≤ s`. -/
private theorem add_two_le_of_time {m s : Nat}
    (h : sp.ts (m : Int) + 6 * sp.Δ ≤ sp.ts (s : Int) + sp.Δ) : m + 2 ≤ s := by
  have hΔ := sp.toParams.hΔ
  simp only [SAParams.ts] at h
  by_contra hc
  have h1 : (s : Int) ≤ m + 1 := by omega
  nlinarith

end Walk

/-! ### Over a run -/

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **The old origins of slot `s`** (workbench#12 §2, the set whose deepest member is `D_s`): the
regular origins of labels at most `s − 2` and the optimistic origins of labels at most `s − 1`,
the origins whose events precede `t_s`. -/
private def OldOrigin (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (s : Nat)
    (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ x ∈ H, ∃ k m CV, (SA.ResultAt tr.projAC x k m O CV ∧ m + 2 ≤ s) ∨
    (SA.OptimisticLockAt tr.projAC x k m O CV ∧ m + 1 ≤ s)

/-- An old origin of slot `s` is an origin of a label below `s`. -/
private theorem OldOrigin.origin {s : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : OldOrigin tr H s O) : ∃ m < s, Origin tr H O m := by
  obtain ⟨x, hx, k, m, CV, ⟨hR, hm⟩ | ⟨hO, hm⟩⟩ := h
  · exact ⟨m, by omega, Origin.of_result hx hR⟩
  · exact ⟨m, by omega, Origin.of_optimistic hx hO⟩

/-- Genesis is an honest block below every honest block. -/
private theorem genesis_anc (hrun : GoldilocksRun dg H tr) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H) :
    sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∈ tr.HonestBlocks H ∧
      Anc (tr.HonestBlocks H)
        (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B := by
  obtain ⟨y, hy, i, hBt⟩ := hB
  obtain ⟨-, -, hg, hanc⟩ :=
    Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
  exact ⟨⟨y, hy, i, hg⟩, (hanc B hBt).mono fun X hX => ⟨y, hy, i, hX⟩⟩

/-- An honest block with the genesis root is below every honest block. -/
private theorem genesis_root_anc (hrun : GoldilocksRun dg H tr)
    (hU : Coherent (tr.HonestBlocks H)) {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H) (hr : B.root = sp.genesisRoot) (hC : C ∈ tr.HonestBlocks H) :
    Anc (tr.HonestBlocks H) B C := by
  rw [hU.1 hB (genesis_anc hrun hB).1 hr]
  exact (genesis_anc hrun hC).2

/-- Blocks with the same fields are equal. -/
private theorem block_eq {X Y : SA.Blk sp.n (List (FG.Att sp.n))} (h0 : X.root = Y.root)
    (h1 : X.parent = Y.parent) (h2 : X.slot = Y.slot) (h3 : X.proposer = Y.proposer)
    (h4 : X.input = Y.input) (h5 : X.fgPayload = Y.fgPayload) (h6 : X.acPayload = Y.acPayload) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-- **An honest block with the root of an honest proposal is that proposal** (`NoColl`): both
roots are digests, of an occurring block, and the slot's proposer made both. -/
private theorem eq_proposal (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ tr.HonestBlocks H) (hr : R.root = P.root) : R = P := by
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, hpp, -⟩ := hP
  rcases blockCall_cases hrun.toLocalRun hp hcB with hg | ⟨j, x, rfl, -, hPr, d, pay, -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hok : P.RootOk dg := by rw [hB]; rfl
  have hpr : P.proposer = sp.toParams.proposer P.slot := by
    rw [hpp, hB]
    exact hPr.2.2.symm
  have hpar : P.parent ≠ none := by rw [hB]; simp [Node.mkBlock]
  have hocc : tr.Occurs P := ⟨p, _, acc, hcB⟩
  obtain ⟨y, hy, i, hRt⟩ := hR
  rcases tree_cases hrun.toLocalRun hy hRt with rfl | ⟨k', -, hk'⟩
  · have := (hnc _ (Set.mem_insert _ _) P (Or.inr hocc)
      (hrun.genesis_root_ok.symm.trans (hr.trans hok))).1
    exact absurd this.symm (by simpa [Params.genesisBlock] using hpar)
  obtain ⟨hRok, hRpr, -⟩ := accept_facts hrun.toLocalRun hy hk'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hnc R (Or.inr ⟨y, k', true, hk'⟩) P (Or.inr hocc)
    (hRok.symm.trans (hr.trans hok))
  exact block_eq hr h1 h2 (by rw [hRpr, hpr, h2]) h3 h4 h5

/-- **The proposer holds every old origin, or it is below its `Σ.F`** (workbench#12 §2.1;
open). For a regular origin of label at most `s − 2` and an optimistic one of label at most
`s − 2`, every honest slot-`(s−1)` vote extends it (S2), and the head of one, cast by
`t_{s−1} + Δ`, is accepted by the proposer (awake and joined at `t_s`) before `t_s` under
`Sync` when `Σ.F` is below it; for an optimistic origin of label `s − 1`, the heads of its at
least `3n/4` triggering seats are held at its writer before `t_s − 2Δ` and relayed. Otherwise
`Σ.F`, on the origin chain, is compatible with the origin (S1) and above it. -/
private theorem proposal_holds_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∀ O, OldOrigin tr H s O → O ∈ ℓp.frame.tree ∨ Anc (tr.HonestBlocks H) O ℓp.frame.F := by
  sorry

/-- **The children towards an old origin win the proposal walk** (workbench#12 §2.1; open): at
every block `X` (of the full viable tree, with the proposal's slot-`(s−1)` pool view `pay`), a
viable child `Cx` of `X` below an old origin held by the proposer is the best eligible child. For
a regular origin of label at most `s − 2` or an optimistic one of label at most `s − 2`, every
honest slot-`(s−1)` vote extends it (S2); the more than `f` of them cast by the validators awake
and joined at `t_{s−1} + Δ` are held and resolved in `pay` (`Sync`, the proposer joined), so
they support `Cx`, and the other voters of `pay` are faulty (`faults_lt_honest_voters`,
`SA.isBest_of_majority`). For an optimistic origin of label `s − 1`, its at least `3n/4`
triggering seats are in `pay` with heads extending `Cx` (relayed before `t_s`), so `Cx` has
Goldfish score at least `3n/4` against at most `n/4 + f` for a sibling, and a strict majority
(sleepy-adoption §2.1, `2|S| ≥ 3n/2 > n + f`). -/
private theorem proposal_best_toward_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∀ O, OldOrigin tr H s O → O ∈ ℓp.frame.tree → ∀ X Cx : SA.Blk sp.n (List (FG.Att sp.n)),
      Cx ∈ ℓp.frame.viableTree ℓp.frame.tree → Cx.parent = some X.root → ℓp.frame.Anc Cx O →
      SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
        {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
          SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1) B}
        Cx := by
  sorry

/-- **No honest optimistic check of slot `s` selects a block before the proposal** (open): it
needs at least `3n/4` slot-`s` votes in a pool, one of an honest validator (`3n/4 > f`), emitted
at a cut no later (`SA.optimisticPoint_pool_vote`) at `t_s`, before `t_s + Δ`, so `vote_ready`:
a slot-`s` proposal in that voter's tree. Its proposer is `p` (the slot's proposer), an honest
maker, which makes its slot-`s` block only at its proposal, after cut `i`. -/
private theorem proposal_no_optimistic (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ SA.OptimisticLockAt tr.projAC x k' s C CV := by
  sorry

/-- **The proposer has no stored lock of slot `s` or later**: a stored lock sits below an origin
of its slot before the proposal (`lock_origin`); a regular one of label at least `s` is written
after `t_s`, an optimistic one has the slot of its time, at most `s`, and not `s`
(`proposal_no_optimistic`). -/
private theorem proposal_locks_slot (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∀ l ∈ (tr.state p i).ac.locks, l.slot < s := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  intro l hl
  obtain ⟨-, -, -, O, hO, -⟩ := lock_origin hrun hnc hp i l hl
  have hii : tr.projAC.time i = tr.time i := rfl
  obtain ⟨x, hx, k', hki, CV, hR | hOp⟩ := originBefore_iff.1 hO
  · obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
    have := hr.time_mono hki.le
    have := add_two_le_of_time (sp := sp) (m := l.slot) (s := s) (by linarith [sp.toParams.hΔ])
    omega
  · have hsl_i : sp.slot (tr.time i) = s := by
      rw [hti]
      simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
    have hle := SA.slot_mono sp (hr.time_nonneg k') (hr.time_mono hki.le)
    obtain ⟨-, -, -, hsk, -⟩ := id hOp
    rcases Nat.lt_or_ge l.slot s with h | h
    · exact h
    have hls : l.slot = s := by rw [hii, hsl_i] at hle; omega
    exact absurd (hls ▸ hOp)
      (proposal_no_optimistic hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ x hx k' hki O CV)

/-- **The proposer's `fc_root` is below an old origin, or genesis** (workbench#12 §2,
`F ≤ fc_root ≤ D_s` at the proposal read; open). `fc_root` is `Σ.J` or `Σ.F`, named by a quorum
with an honest row whose source is on the origin chain (`row_on_chain`); before `t_s` every
source the proposer's FG has seen has origin label at most `s − 1` and is not a regular origin of
label `s − 1` (written at `t_s + 2Δ`) (sleepy-record-invariant §3, the source labels). -/
private theorem proposal_fcRoot_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ℓp.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot O := by
  sorry

/-- A live lock block of the proposal's anchor sits below an origin, of the slot of a stored
lock, before the proposal (`lock_origin`; unlocking and `live_locks` only move locks back). -/
private theorem proposal_lock_below (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {i : Nat} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ tr.HonestBlocks H) {t : Time} {σ : Int}
    {V : SA.View sp.n} {A₁ : SA.SAState sp.n}
    (hA₁ : A₁.locks = SA.unlock sp (tr.projAC.state p i).locks Φ t σ V) :
    ∀ L ∈ SA.liveLockBlocks sp A₁.locks Φ t, ∃ l ∈ (tr.state p i).ac.locks, ∃ O,
      OriginBefore tr H O l.slot i ∧ Anc (tr.HonestBlocks H) L O := by
  have hU := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun.coherent
  rintro L ⟨hL, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hlL⟩
  obtain rfl : L = Φ.viableAncestor B :=
    hΦ.coherent.1 hL (SA.viableAncestor_anc hΦ hB).1 hlL.symm
  rw [hA₁] at hl
  obtain ⟨l₁, hl₁, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hB'B₁⟩ :=
    ((SA.locks_move_back sp) _ Φ _ t hΦ).2.2 σ V l hl
  obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
  rw [projAC_state hrun.toLocalRun hp i] at hl₁
  obtain ⟨L₁, hL₁, hL₁r, O, hO, hL₁O⟩ := lock_origin hrun hnc hp i l₁ hl₁
  obtain rfl : L₁ = B₁ := hU.1 ⟨p, hp, i, hL₁⟩ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
  exact ⟨l₁, hl₁, O, hO,
    (Anc.mono hΦU ((SA.anc_viableAncestor Φ _).trans hB'B₁)).trans hL₁O⟩

/-- **The proposal walk passes every old origin** (workbench#12 §2.1): the origin is held by the
proposer (or below its `Σ.F`, below the walk's start), so viable or at or below `fc_root`
(`held_origin_viable`); the proposer's live locks sit below origins, compatible with it (S1);
and the children towards it win (`SA.anc_getHead`). -/
private theorem proposal_passes_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O d.head := by
  intro O hO
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hinv := sleepy_invariant hrun hnc hsl
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hstart, hsQ⟩ := start_anc_head hΦ hd
  obtain ⟨A₁, hA₁, -, hhd⟩ := acProposal_walk hd
  obtain ⟨m, -, hOm⟩ := hO.origin
  rcases proposal_holds_old hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ O hO with hOt | hOF
  swap
  · exact hOF.trans (Anc.mono hΦU ((hΦ.rooted.2 _ hstart).trans hsQ))
  have hfr := frame_of_projAC hrun hp hc
  have hviab := held_origin_viable hrun hnc hsl (fun m => (frontier hrun hnc hsl m).1) hp i
    (fun C m' hC => hinv.origins_compatible O m C m' hOm hC.origin) (hfr ▸ hOt)
  rw [← hfr] at hviab
  have hsl_i : sp.slot (tr.time i) = s := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  have hbest := proposal_best_toward_old hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ O hO hOt
  rw [← hsl_i] at hbest
  rw [hhd]
  refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A₁ (tr.time i) _ _ (fun _ h => h)
    (fun B hB X hXB => SA.mem_of_anc hXB hB) hviab.symm ?_ hbest)
  intro L hL
  obtain ⟨l, -, O', hO', hLO'⟩ := proposal_lock_below hrun hnc hp hΦ hΦU hA₁ L hL
  rcases hinv.origins_compatible O' l.slot O m hO'.origin hOm with h | h
  · exact Or.inl (hLO'.trans h)
  · exact SA.anc_total hU hLO' h

/-- **The proposal's anchor is below an old origin, or genesis** (workbench#12 §2, "both
unlocked anchors are `≤ D_s`"): a live lock block sits below an origin before `t_s` of a slot
below `s` (`proposal_locks_slot`), which is old (a regular origin of label `s − 1` is written at
`t_s + 2Δ`); `fc_root` by `proposal_fcRoot_old`. -/
private theorem proposal_anchor_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    d.start.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) d.start O := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨A₁, hA₁, hst, -⟩ := acProposal_walk hd
  rw [hst]
  rcases anchor_mem ℓp.frame A₁ (tr.time i) with hL | hf
  · right
    obtain ⟨l, hl, O, hO, hLO⟩ := proposal_lock_below hrun hnc hp hΦ hΦU hA₁ _ hL
    have hls := proposal_locks_slot hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ l hl
    refine ⟨O, ?_, hLO⟩
    obtain ⟨x, hx, k', hki, CV, hR | hOp⟩ := originBefore_iff.1 hO
    · refine ⟨x, hx, k', l.slot, CV, Or.inl ⟨hR, add_two_le_of_time (sp := sp) ?_⟩⟩
      obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
      have := hr.time_mono hki.le
      have hii : tr.projAC.time i = tr.time i := rfl
      linarith [sp.toParams.hΔ]
    · exact ⟨x, hx, k', l.slot, CV, Or.inr ⟨hOp, by omega⟩⟩
  · rw [Set.mem_singleton_iff.1 hf]
    exact proposal_fcRoot_old hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ

/-- **A voter's `fc_root` is below an old origin, or genesis** (workbench#12 §2, `F ≤ fc_root ≤
D_s` at the vote reads; open). `fc_root` is `Σ.J` or `Σ.F`, named by a quorum with an honest row
whose source is on the origin chain (`row_on_chain`); before a slot-`s` vote every source the
voter's FG has seen has origin label at most `s − 1` (a label-`s` source is reported at the
earliest at the tick at `t_s + Δ`, after the vote there; sleepy-record-invariant §3, the private
`vote_row_source` of `Sleepy/Frame`), and a regular origin of label `s − 1` is written at
`t_s + 2Δ`, after the vote. -/
private theorem vote_fcRoot_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hs : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ℓ e) (hes : e.msg.slot = s) :
    ℓ.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) ℓ.frame.fcRoot O := by
  sorry

/-- **A voter's anchor is below `D`, or on `P`'s chain above `D`**: for a block `D` above every
old origin and below `Q = P.parent`, at an honest slot-`s` vote whose earlier honest slot-`s`
votes are `P`. -/
private theorem vote_anchor_cases (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P Q D : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hs0 : 0 < s) (hPQ : P.parent = some Q.root) (hQU : Q ∈ tr.HonestBlocks H)
    (hDQ : Anc (tr.HonestBlocks H) D Q) (hDU : D ∈ tr.HonestBlocks H)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O D)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
      e'.msg.head = P.root) :
    Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocks H) D (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
        Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
        P ∈ tr.HonestBlocks H) := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hslj : e.msg.slot = sp.slot (tr.time j) := (SA.castAt_spec hr hy hcy).2.1
  have htj : tr.time j ≤ sp.ts s + sp.Δ := hes ▸ (cast_head_fcRoot hr hy hcy).2
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have haS := anchor_mem ℓy.frame e.readPoint (tr.time j)
  generalize SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = a at hat haS ⊢
  rcases haS with ⟨-, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hl'r⟩ | haf
  swap
  · -- `fc_root` is below an old origin, or genesis
    left
    rw [Set.mem_singleton_iff.1 haf]
    rcases vote_fcRoot_old hrun hnc hsl hs0 hy hcy hes with hg | ⟨O, hO, hfO⟩
    · exact genesis_root_anc hrun hU (hΦU hΦ.fcRoot_mem) hg hDU
    · exact hfO.trans (hDold O hO)
  -- a live lock block: the viable ancestor of the block of a read-point lock
  obtain rfl : a = ℓy.frame.viableAncestor B :=
    hΦ.coherent.1 hat (SA.viableAncestor_anc hΦ hB).1 hl'r.symm
  have haB : Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor B) B :=
    Anc.mono hΦU (SA.anc_viableAncestor _ B)
  by_cases hls : l.slot = s
  · -- a lock of slot `s`: below an optimistic selection with an honest earlier supporter
    obtain ⟨Φ', A', D', -, hΦ'U, -, h34, hpool, -, L, hLU, hLr, hLD'⟩ :=
      SA.lock_origin_readPoint hrun' hy hcy l hl (by rw [hes, hls]; omega)
    obtain rfl : L = B := hU.1 hLU (hΦU hB) (hLr.trans hBr.symm)
    have hf := two_faults_lt_of_sleepy hsl
    obtain ⟨x, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A' Φ' l.slot D') (by omega)
    have hvH : v.val ∈ H := not_not.1 hxH
    obtain ⟨hvs, j', hj', e', hv', rfl⟩ := hpool v hv hvH
    have hRP : R = P := eq_proposal hrun hnc hp hP (hΦ'U hR)
      (hRr.trans (hE _ hvH j' hj' e' hv' (hvs.trans hls)))
    rw [hRP] at hR hDR
    have hPU : P ∈ tr.HonestBlocks H := hΦ'U hR
    have haP := haB.trans (hLD'.trans (Anc.mono hΦ'U hDR))
    have hDP : Anc (tr.HonestBlocks H) D P :=
      hDQ.trans (Relation.ReflTransGen.single ⟨hQU, hPU, hPQ⟩)
    rcases Anc.total hU haP hDP with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haP, hPU⟩
  · -- a lock of another slot: below a stored lock, below an old origin
    left
    obtain ⟨l₁, hl₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hB'B₁⟩ :=
      SA.readPoint_locks_below_stored hr hy hcy (hslj ▸ hes ▸ hs0) l hl
        (by change l.slot ≠ sp.slot (tr.time j); rw [← hslj, hes]; exact hls)
    obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
    rw [projAC_state hrun.toLocalRun hy j] at hl₁
    obtain ⟨L₁, hL₁, hL₁r, O, hO, hL₁O⟩ := lock_origin hrun hnc hy j l₁ hl₁
    obtain rfl : L₁ = B₁ := hU.1 ⟨y, hy, j, hL₁⟩ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
    have hOld : OldOrigin tr H s O := by
      obtain ⟨x, hx, k', hkj, CV, hR | hOp⟩ := originBefore_iff.1 hO
      · refine ⟨x, hx, k', l₁.slot, CV, Or.inl ⟨hR, add_two_le_of_time (sp := sp) ?_⟩⟩
        obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
        have := hr.time_mono hkj.le
        have hjj : tr.projAC.time j = tr.time j := rfl
        linarith
      · refine ⟨x, hx, k', l₁.slot, CV, Or.inr ⟨hOp, ?_⟩⟩
        obtain ⟨-, -, -, hsk, -⟩ := hOp
        have := SA.slot_mono sp (hr.time_nonneg k') (hr.time_mono hkj.le)
        have hjj : sp.slot (tr.projAC.time j) = sp.slot (tr.time j) := rfl
        omega
    exact (haB.trans (Anc.mono hΦU hB'B₁)).trans (hL₁O.trans (hDold O hOld))

/-- **The pivot** (workbench#12 §2.1, §2.2). For a voter, the earlier honest slot-`s` votes are
assumed to be `P` (the caller's strong induction on the cut: a current-slot optimistic lock of the
voter sits below one of them). -/
theorem pivot {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      ∀ y ∈ H, ∀ j ℓy e, SA.CastAt tr.projAC y j ℓy e → e.msg.slot = s →
        (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
          e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hinv := sleepy_invariant hrun hnc hsl
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  have hs0 : 0 < s := by
    obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, -⟩ := hP
    rcases blockCall_cases hrun.toLocalRun hp hcB with hg | ⟨j, x, rfl, -, hPr, d', pay', -, hB, -⟩
    · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
    rw [← hPs, hB]
    exact hPr.1
  -- the proposal walk, from its start to `Q`
  obtain ⟨hstart, hsQ⟩ := start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hstart
  have hpass := proposal_passes_old hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ
  have hanch := proposal_anchor_old hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ
  -- `D`: the deepest of the start and the old origins on the proposal walk
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦp (S := {X | X ∈ ℓp.frame.tree ∧
      ℓp.frame.Anc d.start X ∧ ℓp.frame.Anc X d.head ∧ (X = d.start ∨ OldOrigin tr H s X)})
    (fun X hX => hX.1) ⟨d.start, hstart, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hΦp (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hΦp.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O D := by
    intro O hO
    have hOQ := hpass O hO
    rcases Anc.total hU hOQ (Anc.mono hΦpU hsQ) with h | h
    · exact h.trans (Anc.mono hΦpU hsD)
    have hOt := mem_between hU hΦp hΦpU hstart hQt h hOQ
    exact Anc.mono hΦpU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hΦp hΦpU hstart h hOt,
      SA.anc_tree_of_anc_U hU hΦp hΦpU hOt hOQ hQt, Or.inr hO⟩)
  -- `D` is genesis or an old origin
  have hDkind : D.root = sp.genesisRoot ∨ OldOrigin tr H s D := by
    rcases hDk with rfl | h
    · rcases hanch with h | ⟨O, hO, hsO⟩
      · exact Or.inl h
      · rw [Anc.antisymm hU hsO (hDold O hO)]
        exact Or.inr hO
    · exact Or.inr h
  refine ⟨D, hsD, hDQ, fun y hy j ℓy e hcy hes hE => ?_⟩
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hhead := (SA.castAt_spec hr hy hcy).2.2.2
  rw [hes] at hhead
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have hah : ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) :=
    SA.anc_ghost (fun B hB => hB.1.1) _ hat
  have hht := mem_of_anc_left hah hat
  -- the vote's head extends `D` (S2, or genesis)
  have hDh : Anc (tr.HonestBlocks H) D (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
      (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
    rcases hDkind with hg | hO
    · exact genesis_root_anc hrun hU (hΦpU hDt) hg (hΦU hht)
    obtain ⟨m, hm, hO⟩ := hO.origin
    obtain ⟨Hd, hHd, hHdr, hDHd⟩ :=
      hinv.vote_extends D m hO y hy j e ⟨ℓy, hcy.1, hcy.2⟩ (by omega)
    rwa [hU.1 hHd (hΦU hht) (hHdr.trans hhead)] at hDHd
  rcases vote_anchor_cases hrun hnc hsl hp hP hs0 hPQ (hΦpU hQt) (Anc.mono hΦpU hDQ) (hΦpU hDt)
      hDold hy hcy hes hE with haD | ⟨hDa, haP, hPU⟩
  · have hDt' := mem_between hU hΦ hΦU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hΦ hΦU hat haD hDt',
      SA.anc_tree_of_anc_U hU hΦ hΦU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := anc_parent hU haP haPe hPQ (hΦpU hQt)
  have hat' := mem_between hU hΦp hΦpU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hΦp hΦpU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hΦp hΦpU hat' haQ hQt⟩, .refl, hah⟩

end Consensus.Goldilocks.Compose

end
