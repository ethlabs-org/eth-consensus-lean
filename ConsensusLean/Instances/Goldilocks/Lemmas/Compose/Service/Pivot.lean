module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

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

The proposal walk passes every old origin (`proposal_walk_passes_old`, `SA.anc_getHead`): the
proposer holds it or has it below `Σ.F` (`proposal_holds_old`: an honest supporting head is
relayed to the proposer, `proposer_relay`), and the children towards it win the walk
(`proposal_best_toward_old`, the counts of §2.1: the honest slot-`(s−1)` batch, or the `3n/4`
votes of an optimistic origin of label `s − 1`, relayed into the proposer's pool and resolved).
Its anchor is below one (`proposal_anchor_old`): no honest optimistic check of slot `s` precedes
the proposal (`proposal_no_optimistic`, so the proposer's stored locks are of slots below `s`),
and `fc_root` is below an old origin at the proposal and at a vote (`proposal_fcRoot_old`,
`vote_fcRoot_old`: the source labels of the honest rows held before `t_s`, §2). The path from
`D` to `Q` is through viable heads of the proposal's frame (`proposal_suffix_viable`, §2: the
head height floor is at most the height of `D`, and `fc_root` is below `D`). -/

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
theorem acProposal_start_anc_head {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {t : Time} {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) : d.start ∈ Φ.tree ∧ Φ.Anc d.start d.head := by
  obtain ⟨A₁, -, hst, hhd⟩ := acProposal_walk h
  have hs := anchor_tree hΦ A₁ t
  rw [hhd, hst]
  exact ⟨hs, SA.anc_ghost (fun _ h => h.1) _ hs⟩

/-- Two vote times: a regular origin of label `m` (written at `t_m + 6Δ`) before a slot-`s` vote
(at most `t_s + Δ`) has `m + 2 ≤ s`. -/
theorem ts_add_two_le {m s : Nat}
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
def OldOrigin (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (s : Nat)
    (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ x ∈ H, ∃ k m CV, (SA.ResultAt tr.projAC x k m O CV ∧ m + 2 ≤ s) ∨
    (SA.OptimisticLockAt tr.projAC x k m O CV ∧ m + 1 ≤ s)

theorem oldOrigin_iff {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {s : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} : OldOrigin tr H s O ↔
      ∃ x ∈ H, ∃ k m CV, (SA.ResultAt tr.projAC x k m O CV ∧ m + 2 ≤ s) ∨
        (SA.OptimisticLockAt tr.projAC x k m O CV ∧ m + 1 ≤ s) := Iff.rfl

/-- An old origin of slot `s` is an origin of a label below `s`. -/
private theorem OldOrigin.origin {s : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : OldOrigin tr H s O) : ∃ m < s, Origin tr H O m := by
  obtain ⟨x, hx, k, m, CV, ⟨hR, hm⟩ | ⟨hO, hm⟩⟩ := h
  · exact ⟨m, by omega, Origin.of_result hx hR⟩
  · exact ⟨m, by omega, Origin.of_optimistic hx hO⟩

/-- An honest block with the genesis root is below every honest block. -/
theorem honest_genesis_root_anc (hrun : GoldilocksRun dg H tr)
    (hU : Coherent (tr.HonestBlocks H)) {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H) (hr : B.root = sp.genesisRoot) (hC : C ∈ tr.HonestBlocks H) :
    Anc (tr.HonestBlocks H) B C := by
  rw [honest_eq_genesis hrun hU hB hr]
  exact (honest_genesis_anc hrun hC).2

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

/-- The proposer's restarts up to its proposal are at or before `t_{s−1}`: `ac_proposal` runs
joined, and keeps the restart time. -/
theorem proposal_call_restarts (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay)) :
    ∀ c ≤ i, tr.projAC.RestartAt p c →
      tr.projAC.time c ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hx := hr.exec i ℓp hc.2 (hc.1 ▸ hp)
  rw [hc.1, hcall] at hx
  have hpost : tr.projAC.post i =
      (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).1 :=
    (congrArg Prod.fst hx).symm
  have hj : SA.joined sp (tr.projAC.post i) (tr.projAC.time i) := by
    rw [hpost]
    unfold SA.acProposal at hd ⊢
    split_ifs at hd ⊢ with hj
    exact hj
  exact ((SA.joined_awake sp) _ ro H _ tr.projAC hr p hp i ℓp hc hj).2

/-- **A block an honest node accepts before `t_{s−1} + 2Δ` reaches the proposer** of slot `s`
(`Sync`, the proposer awake since its last restart at or before `t_{s−1}`): when the proposer's
`Σ.F` is below it, it is in the proposal's frame, accepted before `t_{s−1} + 3Δ`. -/
private theorem proposer_relay (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hacc : B.root = sp.genesisRoot ∨ ∃ kx, tr.projAC.AcceptAt x kx B ∧
      tr.projAC.time kx < sp.ts ((s : Int) - 1) + 2 * sp.Δ)
    (hFB : Anc (tr.HonestBlocks H) ℓp.frame.F B) :
    B ∈ ℓp.frame.tree ∧ SA.AcceptedBefore tr.projAC p B (sp.ts ((s : Int) - 1) + 3 * sp.Δ) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  rcases hacc with hg | ⟨kx, hacc, hkxt⟩
  · refine ⟨?_, Or.inl hg⟩
    have h2 := (honest_genesis_anc hrun (hΦU hΦ.rooted.1)).2
    rw [← honest_eq_genesis hrun hU hB hg] at h2
    rw [← Anc.antisymm hU hFB h2]
    exact hΦ.rooted.1
  have hsi : sp.slot (tr.time i) = s := by
    rw [hti]; simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  have hts : sp.ts (s : Int) = sp.ts ((s : Int) - 1) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  have hrs := proposal_call_restarts hrun hnc hp hc hcall hd
  rw [hsi] at hrs
  have hdl : ∀ c ≤ i, tr.projAC.deadline p c (tr.projAC.time kx) ≤
      sp.ts ((s : Int) - 1) + 3 * sp.Δ := fun c hc' => by
    have h1 := ac_deadline_le_of_restarts (T := tr.projAC)
      (fun k hk hrk => hrs k (hk.trans hc') hrk) (tr.projAC.time kx)
    have h2 := max_le hkxt.le (show sp.ts ((s : Int) - 1) ≤ sp.ts ((s : Int) - 1) + 2 * sp.Δ by
      linarith)
    linarith
  have hii : tr.projAC.time i = tr.time i := rfl
  obtain ⟨k', hk'i, hAp, hk't⟩ := (syncAC_of_sleepy hrun hsl (a := 0)
    (b := tr.projAC.time kx) le_rfl).2 x hx kx B hacc (hr.time_nonneg kx) le_rfl p hp i ℓp hc
    (by have := hdl i le_rfl; linarith) hFB
  exact ⟨SA.mem_tree_of_acceptAt sp hr hp hAp hk'i hc hFB,
    Or.inr ⟨k', hAp, lt_of_lt_of_le hk't (hdl k' hk'i)⟩⟩

/-- **The head of an honest vote of a slot before `s` reaches the proposer** of slot `s`: its
voter accepted it (or it is genesis) by `t_{s−1} + Δ` (`frame_anc_accepted`), and
`proposer_relay`. -/
private theorem proposer_accepts_head (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt tr.projAC x j e) (hes : e.msg.slot + 1 ≤ s)
    {Hd : SA.Blk sp.n (List (FG.Att sp.n))} (hHd : Hd ∈ tr.HonestBlocks H)
    (hHdr : Hd.root = e.msg.head) (hFHd : Anc (tr.HonestBlocks H) ℓp.frame.F Hd) :
    Hd ∈ ℓp.frame.tree ∧ SA.AcceptedBefore tr.projAC p Hd (sp.ts ((s : Int) - 1) + 3 * sp.Δ) ∧
      Hd.slot ≤ e.msg.slot := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨ℓx, hcx, hex⟩ := hv
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hjt⟩ := cast_head_fcRoot hr hx ⟨hcx, hex⟩
  have hHdeq : Hd' = Hd :=
    hU.1 ((SA.frameIn_of_callAt hr hx hcx).2 hHd't) hHd (hHd'r.trans hHdr.symm)
  rw [hHdeq] at hHd't
  have hjt' : tr.projAC.time j ≤ sp.ts ((s : Int) - 1) + sp.Δ := by
    have : sp.ts (e.msg.slot : Int) ≤ sp.ts ((s : Int) - 1) := by
      simp only [SAParams.ts]
      exact mul_le_mul_of_nonneg_left (show (e.msg.slot : Int) ≤ (s : Int) - 1 by omega)
        (by linarith)
    linarith
  have hslot : Hd.slot ≤ e.msg.slot := by
    rw [(SA.castAt_spec hr hx ⟨hcx, hex⟩).2.1]
    exact SA.frame_slot_le sp hr hx hcx Hd hHd't
  have hacc : Hd.root = sp.genesisRoot ∨ ∃ kx, tr.projAC.AcceptAt x kx Hd ∧
      tr.projAC.time kx < sp.ts ((s : Int) - 1) + 2 * sp.Δ := by
    rcases frame_anc_accepted hr hx j ℓx hcx Hd hHd't Hd .refl with hg | ⟨kx, hkx, hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨kx, hacc, lt_of_le_of_lt (hr.time_mono hkx) (by linarith)⟩
  obtain ⟨h1, h2⟩ := proposer_relay hrun hnc hsl hp hc hcall hd hti hx hHd hacc hFHd
  exact ⟨h1, h2, hslot⟩

/-- **The proposer holds every old origin, or it is below its `Σ.F`** (workbench#12 §2.1): an
old origin has an honest supporting vote of a slot before `s` (`honest_supporter`), whose head
reaches the proposer when `Σ.F` is below the origin (`proposer_accepts_head`); otherwise `Σ.F`,
on the origin chain, is compatible with it (S1) and above it. -/
private theorem proposal_holds_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    ∀ O, OldOrigin tr H s O → O ∈ ℓp.frame.tree ∨ Anc (tr.HonestBlocks H) O ℓp.frame.F := by
  intro O hO
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hinv := sleepy_invariant hrun hnc hsl
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨m, hm, hOm⟩ := hO.origin
  obtain ⟨x, hx, j, e, hv, hes, Hd, hHd, hHdr, hOHd⟩ := honest_supporter hrun hnc hsl hOm
  have hOU : O ∈ tr.HonestBlocks H := by
    by_cases h : O = Hd
    · exact h ▸ hHd
    · exact (Anc.mem hOHd h).1
  have hFc : OnOriginChain tr H ℓp.frame.F := by
    rw [frame_of_projAC hrun hp hc]
    exact (hinv.caches p hp i).1
  rcases OnOriginChain.compatible hrun hnc hinv.origins_compatible (hΦU hΦ.rooted.1) hOU hFc
      (onOriginChain_iff.2 (Or.inr ⟨O, m, hOm, .refl⟩)) with hFO | hOF
  · left
    have hHdt := (proposer_accepts_head hrun hnc hsl hp hc hcall hd hti hx hv (by omega) hHd hHdr
      (hFO.trans hOHd)).1
    exact mem_between hU hΦ hΦU hΦ.rooted.1 hHdt hFO hOHd
  · exact Or.inr hOF

/-- **The children towards an old origin win the proposal walk** (workbench#12 §2.1): at every
block `X` (of the full viable tree, with the proposal's slot-`(s−1)` pool view `pay`), a viable
child `Cx` of `X` below an old origin held by the proposer is the best eligible child. A vote of
the proposer's pool is held with a finite stamp; an honest validator has one vote in it
(`one_vote_per_slot`). For an origin of label below `s − 1`, every honest slot-`(s−1)` vote
extends it (S2), is relayed to the proposer (`SA.sync_forward`) and resolved there (its head is
relayed too, `proposer_accepts_head`), so the honest slot-`(s−1)` voters support it, and the
other voters are faulty (`faults_lt_honest_voters`, `SA.isBest_of_majority`). For an optimistic
origin of label `s − 1`, the at least `3n/4` votes it counted (`optimistic_writer_votes`) are
relayed likewise, so each of its seats supports it or equivocates, and the equivocators and the
voters outside are fewer (`2f < n`, `SA.isBest_of_cover`). -/
private theorem proposal_best_toward_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    ∀ O, OldOrigin tr H s O → O ∈ ℓp.frame.tree → ∀ X Cx : SA.Blk sp.n (List (FG.Att sp.n)),
      Cx ∈ ℓp.frame.viableTree ℓp.frame.tree → Cx.parent = some X.root → ℓp.frame.Anc Cx O →
      SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
        {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
          SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1) B}
        Cx := by
  intro O hO hOt X Cx hCx hpar hCxO
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hinv := sleepy_invariant hrun hnc hsl
  have hΔ := sp.toParams.hΔ
  have hf := two_faults_lt_of_sleepy hsl
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := by
    obtain ⟨m, hm, -⟩ := hO.origin
    exact ⟨s - 1, by omega⟩
  have hσ : (((s' + 1 : Nat) : Int) - 1) = (s' : Int) := by push_cast; ring
  have hsi : sp.slot (tr.time i) = s' + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s' + 1)).1 0 (by omega)
  have hts : sp.ts ((s' + 1 : Nat) : Int) = sp.ts (s' : Int) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hii : tr.projAC.time i = tr.time i := rfl
  rw [hσ]
  set A := tr.projAC.state p i with hA
  -- the payload is the proposer's slot-`(s−1)` pool
  have hpay : pay = SA.voteViewList A ℓp.frame (s' : Int) ⊤ := by
    have h := hd
    unfold SA.acProposal at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2, hsi, hσ]
  have hvotes : ∀ v, v ∈ (SA.View.ofLists pay).votes ↔ v ∈ A.pool s' ∧ A.voteStamp v < ⊤ := by
    intro v
    rw [hpay]
    simp [SA.View.ofLists, SA.voteViewList, SA.SAState.poolAt]
  have hsupv : ∀ v, v ∈ (SA.View.ofLists pay).support ↔
      (v ∈ A.pool s' ∧ A.voteStamp v < ⊤) ∧ SA.resolutionTime A ℓp.frame v < ⊤ := by
    intro v
    rw [hpay]
    simp [SA.View.ofLists, SA.voteViewList, SA.SAState.poolAt]
    tauto
  have hsub : (SA.View.ofLists pay).support ⊆ (SA.View.ofLists pay).votes := fun v hv =>
    (hvotes v).2 ((hsupv v).1 hv).1
  -- the pool's votes have finite stamps
  have hstamp : ∀ v ∈ A.pool s', A.voteStamp v < ⊤ := by
    intro v hv
    have hvs : v.slot = s' := SA.state_pool_slot sp hr hp i s' v hv
    rcases SA.pool_origin hr hp i v (by rw [hvs]; exact hv) with
      ⟨k, -, -, hst, -⟩ | ⟨k, -, -, -, -, hst, -⟩ <;>
    · rw [hst]; exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  have hvotes' : ∀ v, v ∈ (SA.View.ofLists pay).votes ↔ v ∈ A.pool s' := fun v =>
    ⟨fun h => ((hvotes v).1 h).1, fun h => (hvotes v).2 ⟨h, hstamp v h⟩⟩
  -- an honest validator has at most one vote in the pool
  have hnoeq : ∀ w ∈ H, w ∉ SA.equivocators {v | v ∈ A.pool s'} := by
    rintro w hw ⟨v₁, hv₁, v₂, hv₂, hne, rfl, h2⟩
    obtain ⟨j₁, -, e₁, hve₁, rfl⟩ := hrun'.honest.pool_vote p hp i s' v₁ hv₁ hw
    obtain ⟨j₂, -, e₂, hve₂, rfl⟩ := hrun'.honest.pool_vote p hp i s' v₂ hv₂ (h2 ▸ hw)
    have hs₁ := SA.state_pool_slot sp hr hp i s' _ hv₁
    have hs₂ := SA.state_pool_slot sp hr hp i s' _ hv₂
    obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr _ hw j₁ j₂ e₁ e₂ hve₁
      (h2 ▸ hve₂) (hs₁.trans hs₂.symm)
    exact hne rfl
  have hequiv : SA.equivocators (SA.View.ofLists pay).votes ⊆ Hᶜ := by
    rintro w ⟨v₁, hv₁, v₂, hv₂, hne, h1, h2⟩ hw
    exact hnoeq w hw ⟨v₁, (hvotes' v₁).1 hv₁, v₂, (hvotes' v₂).1 hv₂, hne, h1, h2⟩
  -- the proposer's restarts, and the relay window
  have hrs := proposal_call_restarts hrun hnc hp hc hcall hd
  rw [hsi, hσ] at hrs
  have hsync := syncAC_of_sleepy hrun hsl (a := 0) (b := sp.ts (s' : Int) + 2 * sp.Δ) le_rfl
  have hts0 : (0 : Time) ≤ sp.ts (s' : Int) := by
    simp only [SAParams.ts]; positivity
  -- a vote sent or admitted by an honest node in `[t_{s−1}, t_{s−1} + 2Δ)` is in the pool
  have hfwd : ∀ x ∈ H, ∀ kx v, tr.projAC.SendOrAdmit x kx v → v.slot = s' →
      sp.ts (s' : Int) ≤ tr.projAC.time kx → tr.projAC.time kx < sp.ts (s' : Int) + 2 * sp.Δ →
      v ∈ A.pool s' ∨ v.val ∈ SA.equivocators {w | w ∈ A.pool s'} := by
    intro x hx kx v hsend hvs hk1 hk2
    have h := SA.sync_forward hr hsync hx hsend (hts0.trans hk1) hk2.le hp hc
      (fun k' hk' hrk' => (hrs k' hk' hrk').trans hk1) (by rw [hii, hti, hts]; linarith)
      (fun t ht1 ht2 => by
        have := SA.slot_of_mem sp s' (hk1.trans ht1) (by rw [hts]; linarith)
        omega)
    rwa [hvs] at h
  -- a vote of the pool whose head, of a slot at most its own, the proposer accepted is resolved
  have hres : ∀ v ∈ A.pool s', ∀ Hv ∈ ℓp.frame.tree, Hv.root = v.head → Hv.slot ≤ v.slot →
      SA.AcceptedBefore tr.projAC p Hv (sp.ts (s' : Int) + 3 * sp.Δ) →
      v ∈ (SA.View.ofLists pay).support := by
    intro v hv Hv hHv hHvr hHvs hacc
    refine (hsupv v).2 ⟨⟨hv, hstamp v hv⟩, ?_⟩
    have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hp hc hHv hacc
      (fun k hk hrk => lt_of_le_of_lt (hrs k hk hrk) (by linarith))
      (Or.inl (by rw [hii, hti, hts]; linarith))
    unfold SA.resolutionTime
    split
    · rename_i hl
      exact absurd ⟨Hv, hHv, hHvr⟩ (SA.lookup_eq_none hl)
    · rename_i Hd' hl
      obtain ⟨hHd', hr'⟩ := SA.lookup_eq_some hl
      obtain rfl : Hd' = Hv := hΦ.coherent.1 hHd' hHv (hr'.trans hHvr.symm)
      split_ifs with hlt
      · omega
      · rw [← hHvr]
        exact max_lt (hstamp v hv) (lt_trans hbs (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)))
  have hFO : Anc (tr.HonestBlocks H) ℓp.frame.F O := Anc.mono hΦU (hΦ.rooted.2 O hOt)
  have hcase : (∃ m < s', Origin tr H O m) ∨
      ∃ x ∈ H, ∃ k CV, SA.OptimisticLockAt tr.projAC x k s' O CV := by
    obtain ⟨x, hx, k, m, CV, ⟨hR, hm⟩ | ⟨hOp, hm⟩⟩ := hO
    · exact Or.inl ⟨m, by omega, Origin.of_result hx hR⟩
    rcases Nat.lt_or_ge m s' with hm' | hm'
    · exact Or.inl ⟨m, hm', Origin.of_optimistic hx hOp⟩
    obtain rfl : s' = m := by omega
    exact Or.inr ⟨x, hx, k, CV, hOp⟩
  rcases hcase with ⟨m, hml, hOm⟩ | ⟨x, hx, k, CV, hOp⟩
  · -- an origin of label below `s − 1`: every honest slot-`(s−1)` vote extends it
    refine SA.isBest_of_majority hΦ hsub (fun B hB => hB.1)
      (SX := {w | w ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC w j e ∧ e.msg.slot = s'})
      (VX := {w | w ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC w j e ∧ e.msg.slot = s'} ∪ Hᶜ) ?_ ?_ ?_
      hCx hpar hCxO
    · rintro w ⟨hw, j, e, hv, hes⟩
      obtain ⟨Hd, hHd, hHdr, hOHd⟩ := hinv.vote_extends O m hOm w hw j e hv (by omega)
      obtain ⟨hHdt, hacc, hHds⟩ := proposer_accepts_head hrun hnc hsl hp hc hcall hd hti hw hv
        (by omega) hHd hHdr (hFO.trans hOHd)
      obtain ⟨ℓw, hcw, hew⟩ := hv
      have hvw : e.msg.val = w := (SA.castAt_spec hr hw ⟨hcw, hew⟩).1
      have hjt := (cast_head_fcRoot hr hw ⟨hcw, hew⟩).2
      have hj1 : sp.ts (s' : Int) ≤ tr.projAC.time j := by
        rw [← hes, (SA.castAt_spec hr hw ⟨hcw, hew⟩).2.1]
        exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 le_rfl
      have hvp : e.msg ∈ A.pool s' := by
        rcases hfwd w hw j e.msg ⟨ℓw, hcw, Or.inl ⟨e, hew, rfl⟩⟩ hes hj1
          (by rw [hes] at hjt; linarith) with h | h
        · exact h
        · exact absurd (hvw ▸ h) (hnoeq w hw)
      refine ⟨fun h => hnoeq w hw (by
          obtain ⟨v₁, hv₁, v₂, hv₂, hne, h1, h2⟩ := h
          exact ⟨v₁, (hvotes' v₁).1 hv₁, v₂, (hvotes' v₂).1 hv₂, hne, h1, h2⟩),
        e.msg, hres e.msg hvp Hd hHdt hHdr hHds (by rw [← hσ]; exact hacc), hvw, by rw [hes],
        Hd, hHdt, hHdr, SA.anc_tree_of_anc_U hU hΦ hΦU hOt hOHd hHdt⟩
    · rintro w ⟨v, hv, rfl⟩
      by_cases hw : v.val ∈ H
      · obtain ⟨j, -, e, hve, rfl⟩ := hrun'.honest.pool_vote p hp i s' v ((hvotes' v).1 hv) hw
        exact Or.inl ⟨hw, j, e, hve, SA.state_pool_slot sp hr hp i s' _ ((hvotes' _).1 hv)⟩
      · exact Or.inr hw
    · have := faults_lt_honest_voters hrun hnc hsl s'
      have := Set.ncard_union_le {w | w ∈ H ∧ ∃ j e, SA.VoteAt tr.projAC w j e ∧ e.msg.slot = s'}
        Hᶜ
      omega
  · -- an optimistic origin of label `s − 1`: its counted votes
    have hW := optimistic_writer_votes hr hx hOp
    obtain ⟨ℓx, Ax, hpt, hslx, hsel, rfl⟩ := hOp
    have hsel' := hsel
    unfold SA.optimisticSelect at hsel'
    dsimp only at hsel'
    split_ifs at hsel'
    have h34 := (SA.deepest_mem hsel').1.2.1
    rw [hslx] at h34
    have hΦxU := (SA.frameIn_of_callAt hr hx hpt.1).2
    refine SA.isBest_of_cover hΦ hsub (fun B hB => hB.1) (SX := SA.optimisticVoters sp Ax ℓx.frame
      s' O) ?_ ?_ hCx hpar hCxO
    · rintro u ⟨v, hvA, rfl, R, hR, hRr, hOR⟩
      obtain ⟨hvs, ⟨kx, hsend, hk1, hk2⟩, Hv, hHv, hHvr, hOHv, hacc⟩ :=
        hW v ⟨hvA, R, hR, hRr, hOR⟩
      have hRHv : R = Hv := hU.1 (hΦxU hR) hHv (hRr.trans hHvr.symm)
      rw [← hRHv] at hHv hOHv hacc
      by_cases heq : v.val ∈ SA.equivocators (SA.View.ofLists pay).votes
      · exact Or.inr heq
      left
      rcases hfwd x hx kx v hsend hvs hk1 hk2 with hvp | ⟨a₁, ha₁, a₂, ha₂, hne, h1, h2⟩
      swap
      · exact absurd ⟨a₁, (hvotes' a₁).2 ha₁, a₂, (hvotes' a₂).2 ha₂, hne, h1, h2⟩ heq
      obtain ⟨hRt, hacc'⟩ := proposer_relay hrun hnc hsl hp hc hcall hd hti hx hHv
        (by rw [hσ]; exact hacc) (hFO.trans hOHv)
      have hRs : R.slot ≤ v.slot := by
        rw [hvs, ← hslx]
        exact SA.frame_slot_le sp hr hx hpt.1 R hR
      exact ⟨heq, v, hres v hvp R hRt hRr hRs (by rw [← hσ]; exact hacc'), rfl,
        by rw [hvs], R, hRt, hRr, SA.anc_tree_of_anc_U hU hΦ hΦU hOt hOHv hRt⟩
    · have hle : (SA.voters (SA.View.ofLists pay).votes \ SA.optimisticVoters sp Ax ℓx.frame s'
          O).ncard + (SA.optimisticVoters sp Ax ℓx.frame s' O).ncard ≤ sp.n := by
        rw [← Set.ncard_union_eq Set.disjoint_sdiff_left]
        exact (Set.ncard_le_ncard (Set.subset_univ _)).trans (by simp)
      have := Set.ncard_le_ncard hequiv (Set.toFinite _)
      omega

/-- An AC call with the proposal label is a cut of a tick. -/
theorem acProposal_in_tick {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)}
    {t : Time} {e : Node.Event (goldilocksNode sp ro)} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : Cut.ac ℓ ∈ (Node.exec dg y st t e).2) (hm : ℓ.call = .proposal) : ∃ x, e = .tick x := by
  cases e with
  | tick x => exact ⟨x, rfl⟩
  | message m =>
    simp only [Node.exec, Node.onMessage, Node.acCall, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    cases hm
  | attestation a => simp [Node.exec, Node.onAttestation] at h
  | restart =>
    simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at h
    subst h
    cases hm
  | block B =>
    simp only [Node.exec, Node.onBlock] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp [Node.acCall] at h
      subst h
      cases hm

/-- **The AC cuts of a tick by position** (C0.4): `ac_on_tick` first, then for the slot's
proposer `ac_proposal` second and its own block's `ac_on_block` later, and `ac_to_fg`. -/
private theorem tick_ac_positions {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)}
    {t : Time} {x c : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : (Node.exec dg y st t (.tick x)).2[c]? = some (Cut.ac ℓ)) :
    (ℓ.call = .tick ∧ c = 0) ∨ ℓ.call = .toFG ∨
      (Node.Proposes y t ∧ ((ℓ.call = .proposal ∧ c = 1) ∨ (ℓ.call ≠ .proposal ∧ 2 ≤ c))) := by
  obtain ⟨ℓt, pc, uc, hlt, hcs, hpc, ℓu, hlu, huc⟩ :=
    @tick_order sp.toParams (goldilocksNode sp ro) dg y st t x
  have huc' : ∀ ℓ', Cut.ac ℓ' ∈ uc → ℓ'.call = .toFG := by
    intro ℓ' hm
    rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;> simp at hm <;> (rw [hm]; exact hlu)
  change (Node.onTick dg y st t x).2[c]? = _ at h
  rw [hcs] at h
  rcases c with _ | c
  · simp only [List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at h
    exact Or.inl ⟨h ▸ hlt, rfl⟩
  rw [List.getElem?_cons_succ] at h
  rcases hpc with ⟨-, rfl⟩ | ⟨hpr, ℓ₀, hℓ₀, hpc⟩
  · exact Or.inr (Or.inl (huc' ℓ (by simpa using List.mem_of_getElem? h)))
  obtain ⟨rest, rfl, hrest⟩ : ∃ rest, pc = Cut.ac ℓ₀ :: rest ∧
      ∀ ℓ', Cut.ac ℓ' ∈ rest → ℓ'.call ≠ .proposal := by
    rcases hpc with rfl | ⟨B, -, -, rfl | ⟨ℓ', hℓ', rfl⟩⟩
    · exact ⟨[], rfl, by simp⟩
    · exact ⟨_, rfl, by simp⟩
    · refine ⟨_, rfl, fun ℓ'' hm => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, Cut.ac.injEq, reduceCtorEq, false_or,
        or_false] at hm
      rw [hm, hℓ']
      simp
  rcases c with _ | c
  · simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at h
    exact Or.inr (Or.inr ⟨hpr, Or.inl ⟨h ▸ hℓ₀, rfl⟩⟩)
  rw [List.cons_append, List.getElem?_cons_succ] at h
  rcases List.mem_append.1 (List.mem_of_getElem? h) with hm | hm
  · exact Or.inr (Or.inr ⟨hpr, Or.inr ⟨hrest ℓ hm, by omega⟩⟩)
  · exact Or.inr (Or.inl (huc' ℓ hm))

/-- **No honest optimistic check of slot `s` selects a block before the proposal**: its at least
`3n/4` voters include an honest one (`2f < n`), whose slot-`s` vote is in the checker's pool, cast
at a cut no later (`SA.optimisticPoint_pool_vote`), at `t_s`. A vote at `t_s` is cast in a call
whose group precedes the proposer's tick at `t_s` or is it (phase order), so in a tick, where only
the slot's proposer's own block casts it (C0.4), after `ac_proposal`: in the proposer's tick
(`tick_unique`), after cut `i`. -/
private theorem proposal_no_optimistic (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ SA.OptimisticLockAt tr.projAC x k' s C CV := by
  intro z hz c hci C CV hO
  have hr' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hr'.localRun
  have hl := hrun.toLocalRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  -- the proposal call is the second cut of the proposer's tick at `t_s`
  obtain ⟨gi, ei, ki, hgi, rfl, hki⟩ := call_in_group hl hp (projAC_callAt.1 hc)
  rw [hti] at hgi hki
  obtain ⟨xi, rfl⟩ := acProposal_in_tick (List.mem_of_getElem? hki) hcall
  obtain ⟨hpr, hki1⟩ : Node.Proposes p (sp.ts s) ∧ ki = 1 := by
    rcases tick_ac_positions hki with ⟨h, -⟩ | h | ⟨hpr, ⟨-, h⟩ | ⟨h, -⟩⟩
    · rw [hcall] at h; cases h
    · rw [hcall] at h; cases h
    · exact ⟨hpr, h⟩
    · exact absurd hcall h
  have hlen := (List.getElem?_eq_some_iff.1 hki).1
  -- the selection is at `t_s`
  obtain ⟨ℓO, AO, hpt, hslc, hsel, -⟩ := hO
  have hct : tr.time c ≤ sp.ts s := hti ▸ hrun.time_mono hci.le
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (SA.deepest_mem hsel).1.2.1
  rw [hslc] at h34
  -- no honest validator is among its voters
  have hnoH : SA.optimisticVoters sp AO ℓO.frame s C ⊆ Hᶜ := by
    rintro u ⟨v, hv, rfl, -⟩ huH
    obtain ⟨hvs, j', hj', e', ⟨ℓ', hc', he'⟩, rfl⟩ :=
      SA.optimisticPoint_pool_vote hr' hz hpt hv huH
    have hsl' : sp.slot (tr.projAC.time j') = s :=
      (SA.castAt_spec hr huH ⟨hc', he'⟩).2.1.symm.trans hvs
    have htj : tr.time j' = sp.ts s := le_antisymm ((hrun.time_mono hj').trans hct)
      ((SA.ts_le_iff_le_slot sp (hr.time_nonneg j') (s : Int)).2 (by rw [hsl']))
    obtain ⟨g, eu, k₁, hg, hjeq, hk₁⟩ := call_in_group hl huH (projAC_callAt.1 hc')
    rw [htj] at hg hk₁
    obtain ⟨htick, hnp, hnt, hnr⟩ := honest_vote_call hrun hnc huH ⟨hc', he'⟩
    have hph : eu.phase ≤ 1 := by
      rcases lt_trichotomy g gi with h | rfl | h
      · have := hl.phase_order _ huH _ hp g gi (sp.ts s) eu _ hg hgi h
        simpa [Node.Event.phase] using this
      · obtain ⟨_, hn₁⟩ := (group_call hg).1
        obtain ⟨_, hn₂⟩ := (group_call hgi).1
        have hnode : e'.msg.val = p := hn₁.1.symm.trans hn₂.1
        rw [hnode] at hg
        rw [group_phase hg hgi]
        simp [Node.Event.phase]
      · exact absurd (group_start hgi hg h.le (by omega)) h.ne'
    cases eu with
    | tick xu =>
      rcases tick_ac_positions hk₁ with ⟨h, -⟩ | h | ⟨hpu, ⟨h, -⟩ | ⟨-, hk₁2⟩⟩
      · have h5 := htick h
        have hslts : sp.slot (sp.ts s) = s := by
          simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
        rw [htj, hslts] at h5
        linarith
      · exact hnt h
      · exact hnp h
      have hup : e'.msg.val = p := hpu.2.2.symm.trans hpr.2.2
      rw [hup] at hg
      have := hl.tick_unique p hp g gi (sp.ts s) ⟨xu, hg⟩ ⟨xi, hgi⟩
      omega
    | restart =>
      have hmem := List.mem_of_getElem? hk₁
      simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hmem
      exact hnr (by rw [hmem])
    | _ => simp [Node.Event.phase] at hph
  have hf := two_faults_lt_of_sleepy hsl
  have := Set.ncard_le_ncard hnoH (Set.toFinite _)
  omega

/-- **The proposer has no stored lock of slot `s` or later**: a stored lock sits below an origin
of its slot before the proposal (`lock_origin`); a regular one of label at least `s` is written
after `t_s`, an optimistic one has the slot of its time, at most `s`, and not `s`
(`proposal_no_optimistic`). -/
private theorem proposal_locks_slot (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    ∀ l ∈ (tr.state p i).ac.locks, l.slot < s := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  intro l hl
  obtain ⟨-, -, -, O, hO, -⟩ := lock_origin hrun hnc hp i l hl
  have hii : tr.projAC.time i = tr.time i := rfl
  obtain ⟨x, hx, k', hki, CV, hR | hOp⟩ := originBefore_iff.1 hO
  · obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
    have := hr.time_mono hki.le
    have := ts_add_two_le (sp := sp) (m := l.slot) (s := s) (by linarith [sp.toParams.hΔ])
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
      (proposal_no_optimistic hrun hnc hsl hp hc hcall hd hti x hx k' hki O CV)

/-- **`fc_root` below the old origins, from the sources**: at an honest node's cut whose honest
rows all have sources below old origins, `Σ.J` is genesis (`h_j = 0`) or the entry of such a
source (`justified_honest_source`, `honest_source_entry`), and `Σ.F` is below `Σ.J`. -/
private theorem fcRoot_old_of_rows (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    (hsrc : HonestRowsSourced tr H
      (fun D => ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) D O) y j) :
    (Node.frame (tr.state y j)).fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) (Node.frame (tr.state y j)).fcRoot O := by
  have hU : Coherent (tr.HonestBlocks H) :=
    (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun.coherent
  have hR := fg_reachable hrun.toLocalRun hy j
  obtain ⟨hFt, hJt, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hsU : (tr.state y j).fg.tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨y, hy, j, hZ⟩
  have hJ : (tr.state y j).fg.J.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) (tr.state y j).fg.J O := by
    by_cases h0 : (tr.state y j).fg.hj = 0
    · left
      rw [justified_genesis hrun h0 hy]
      rfl
    obtain ⟨-, -, D, ⟨O, hO, hDO⟩, hDs⟩ :=
      justified_honest_source hrun hnc hsl hy hsrc (by omega)
    obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, j, hJt⟩ rfl
    exact Or.inr ⟨O, hO,
      (Anc.mono (T := tr.HonestBlocks H) (fun Z hZ => ⟨x, hx, k, hZ⟩) hJD).trans hDO⟩
  change (tr.state y j).fg.fcRoot.root = _ ∨ ∃ O, _ ∧ Anc _ (tr.state y j).fg.fcRoot O
  unfold Store.fcRoot
  split_ifs
  · exact hJ
  rcases hJ with hg | ⟨O, hO, hJO⟩
  · left
    have h2 := (honest_genesis_anc hrun (hsU hFt)).2
    rw [← honest_eq_genesis hrun hU (hsU hJt) hg] at h2
    rw [Anc.antisymm hU (Anc.mono hsU hFJ) h2]
    exact hg
  · exact Or.inr ⟨O, hO, (Anc.mono hsU hFJ).trans hJO⟩

/-- **The proposer's honest rows have sources below old origins** (workbench#12 §2): every honest
row the proposer holds was signed before cut `i`, with a source below an origin before the
signing (`attestation_source`); a regular one of label `l` is written at `t_l + 6Δ ≤ t_s`, so
`l ≤ s − 2`; an optimistic one has label at most `s`, and not `s` (`proposal_no_optimistic`). -/
private theorem proposal_rows_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    HonestRowsSourced tr H
      (fun D => ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) D O) p i := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hΔ := sp.toParams.hΔ
  refine honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmi, -, k', hkm, hsg⟩ := honest_row_signed_before hrun hnc hp hX ha hav
  obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  refine ⟨D, ⟨C, ?_, hDC⟩, hDs⟩
  have hii : tr.projAC.time i = tr.time i := rfl
  obtain ⟨z, hz, c, hck, CV, hR | hOp⟩ := originBefore_iff.1 hC
  · refine ⟨z, hz, c, l, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
    obtain ⟨-, ⟨-, -, htc, -⟩, -⟩ := hR
    have := hr.time_mono (show c ≤ i by omega)
    linarith
  · refine ⟨z, hz, c, l, CV, Or.inr ⟨hOp, ?_⟩⟩
    obtain ⟨-, -, -, hsc, -⟩ := id hOp
    have hle := SA.slot_mono sp (hr.time_nonneg c) (hr.time_mono (show c ≤ i by omega))
    have hsi : sp.slot (tr.projAC.time i) = s := by
      rw [hii, hti]
      simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
    rcases Nat.lt_or_ge l s with h | h
    · omega
    obtain rfl : l = s := by omega
    exact absurd hOp
      (proposal_no_optimistic hrun hnc hsl hp hc hcall hd hti z hz c (by omega) C CV)

/-- **The proposer's `fc_root` is below an old origin, or genesis** (workbench#12 §2,
`F ≤ fc_root ≤ D_s` at the proposal read), from the sources of its honest rows
(`proposal_rows_old`, `fcRoot_old_of_rows`). -/
private theorem proposal_fcRoot_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    ℓp.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot O := by
  rw [frame_of_projAC hrun hp hc]
  exact fcRoot_old_of_rows hrun hnc hsl hp (proposal_rows_old hrun hnc hsl hp hc hcall hd hti)

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
theorem proposal_walk_passes_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O d.head := by
  intro O hO
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hinv := sleepy_invariant hrun hnc hsl
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦ hd
  obtain ⟨A₁, hA₁, -, hhd⟩ := acProposal_walk hd
  obtain ⟨m, -, hOm⟩ := hO.origin
  rcases proposal_holds_old hrun hnc hsl hp hc hcall hd hti O hO with hOt | hOF
  swap
  · exact hOF.trans (Anc.mono hΦU ((hΦ.rooted.2 _ hstart).trans hsQ))
  have hfr := frame_of_projAC hrun hp hc
  have hviab := held_origin_viable hrun hnc hsl (fun m => (frontier hrun hnc hsl m).1) hp i
    (fun C m' hC => hinv.origins_compatible O m C m' hOm hC.origin) (hfr ▸ hOt)
  rw [← hfr] at hviab
  have hsl_i : sp.slot (tr.time i) = s := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  have hbest := proposal_best_toward_old hrun hnc hsl hp hc hcall hd hti O hO hOt
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
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) :
    d.start.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) d.start O := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨A₁, hA₁, hst, -⟩ := acProposal_walk hd
  rw [hst]
  rcases anchor_mem ℓp.frame A₁ (tr.time i) with hL | hf
  · right
    obtain ⟨l, hl, O, hO, hLO⟩ := proposal_lock_below hrun hnc hp hΦ hΦU hA₁ _ hL
    have hls := proposal_locks_slot hrun hnc hsl hp hc hcall hd hti l hl
    refine ⟨O, ?_, hLO⟩
    obtain ⟨x, hx, k', hki, CV, hR | hOp⟩ := originBefore_iff.1 hO
    · refine ⟨x, hx, k', l.slot, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
      obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
      have := hr.time_mono hki.le
      have hii : tr.projAC.time i = tr.time i := rfl
      linarith [sp.toParams.hΔ]
    · exact ⟨x, hx, k', l.slot, CV, Or.inr ⟨hOp, by omega⟩⟩
  · rw [Set.mem_singleton_iff.1 hf]
    exact proposal_fcRoot_old hrun hnc hsl hp hc hcall hd hti

/-- **A voter's `fc_root` is below an old origin, or genesis** (workbench#12 §2,
`F ≤ fc_root ≤ D_s` at the vote reads): every honest row the voter holds was signed before the
vote, with a source below an origin before the signing (`attestation_source`); a regular one of
label `l` is written at `t_l + 6Δ ≤ t_s + Δ`, so `l ≤ s − 2`; an optimistic one has label at most
`s`, and not `s` (`no_optimistic_before_held_row`). -/
theorem vote_fcRoot_old (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hs : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ℓ e) (hes : e.msg.slot = s) :
    ℓ.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) ℓ.frame.fcRoot O := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hΔ := sp.toParams.hΔ
  have htj : tr.time j ≤ sp.ts ((s' + 1 : Nat) : Int) + sp.Δ :=
    hes ▸ (cast_head_fcRoot hr hy hc).2
  have hsj : sp.slot (tr.projAC.time j) = s' + 1 := (SA.castAt_spec hr hy hc).2.1.symm.trans hes
  rw [frame_of_projAC hrun hy hc.1]
  refine fcRoot_old_of_rows hrun hnc hsl hy (honestRowsSourced_iff.2 fun X hX a ha hav => ?_)
  obtain ⟨m, hmj, hm, k, hkm, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  refine ⟨D, ⟨C, ?_, hDC⟩, hDs⟩
  have hjj : tr.projAC.time j = tr.time j := rfl
  obtain ⟨z, hz, c, hck, CV, hR | hOp⟩ := originBefore_iff.1 hC
  · refine ⟨z, hz, c, l, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
    obtain ⟨-, ⟨-, -, htc, -⟩, -⟩ := hR
    have := hr.time_mono (show c ≤ j by omega)
    linarith
  · refine ⟨z, hz, c, l, CV, Or.inr ⟨hOp, ?_⟩⟩
    obtain ⟨-, -, -, hsc, -⟩ := id hOp
    have hle := SA.slot_mono sp (hr.time_nonneg c) (hr.time_mono (show c ≤ j by omega))
    rcases Nat.lt_or_ge l (s' + 1) with h | h
    · omega
    obtain rfl : l = s' + 1 := by omega
    exact (no_optimistic_before_held_row hrun hnc hsl hy hc hes hm hmj hav hkm hsg hz hck hOp).elim

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
    · exact honest_genesis_root_anc hrun hU (hΦU hΦ.fcRoot_mem) hg hDU
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
      · refine ⟨x, hx, k', l₁.slot, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
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

/-- **The proposal walk from `D` to `Q` is through viable heads** (workbench#12 §2: at `t_s`,
`F ⪯ fc_root ⪯ D_s` and the head height floor is at most `ht(D_s)`, heights increase along the
path), for `D` above every old origin. `fc_root` is genesis or below an old origin
(`proposal_fcRoot_old`), so below `D ⪯ X`. The proposer's honest rows have sources below old
origins, hence below `D` and pairwise compatible (`proposal_rows_old`), so with no contest the
floor is reached by `X`, or a crossing entry `E ⪰ X` of the floor's height is below its source,
below `D ⪯ X`, and `E = X` (`floor_or_crossing`). -/
private theorem proposal_suffix_viable (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) {D : SA.Blk sp.n (List (FG.Att sp.n))} (hDt : D ∈ ℓp.frame.tree)
    (hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O D) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads := by
  intro X hDX _
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  have hXt : X ∈ ℓp.frame.tree := mem_of_anc_left hDX hDt
  have hDXU : Anc (tr.HonestBlocks H) D X := Anc.mono hΦU hDX
  -- `fc_root` is genesis or below an old origin, below `D`
  have hfX : ℓp.frame.Anc ℓp.frame.fcRoot X := by
    refine SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem ?_ hXt
    rcases proposal_fcRoot_old hrun hnc hsl hp hc hcall hd hti with hg | ⟨O, hO, hfO⟩
    · exact honest_genesis_root_anc hrun hU (hΦU hΦ.fcRoot_mem) hg (hΦU hXt)
    · exact (hfO.trans (hDold O hO)).trans hDXU
  -- the sources of the proposer's honest rows are below old origins, below `D ⪯ X`
  have hsrc := proposal_rows_old hrun hnc hsl hp hc hcall hd hti
  rw [frame_of_projAC hrun hp hc] at hXt hfX ⊢
  obtain ⟨hXs, hFX⟩ := hXt
  refine ⟨hXs, hFX, Anc.mono (fun _ h => h.1) hfX, ?_⟩
  rcases floor_or_crossing hrun hnc hsl hp hsrc
      (fun D₁ D₂ ⟨O₁, hO₁, h₁⟩ ⟨O₂, hO₂, h₂⟩ =>
        Anc.total hU (h₁.trans (hDold O₁ hO₁)) (h₂.trans (hDold O₂ hO₂)))
      (fun D' ⟨O, hO, h⟩ => Or.inl ((h.trans (hDold O hO)).trans hDXU)) hXs with
    hle | ⟨D', E, -, ⟨O, hO, hD'O⟩, hD's, hE, hXE, hEh, -⟩
  · exact hle
  -- a crossing entry `E ⪰ X` is below its source, below `D ⪯ X`: `E = X`
  obtain ⟨x, hx, k', -, -, hED', -, -⟩ := honest_source_entry hrun hnc hD's ⟨p, hp, i, hE⟩ rfl
  obtain rfl : X = E := Anc.antisymm hU
    (Anc.mono (T := tr.HonestBlocks H) (fun _ h => ⟨p, hp, i, h⟩) hXE)
    (((Anc.mono (T := tr.HonestBlocks H) (fun _ h => ⟨x, hx, k', h⟩) hED').trans hD'O).trans
      ((hDold O hO).trans hDXU))
  exact hEh.ge

/-- **The pivot** (workbench#12 §2.1, §2.2). For a voter, the earlier honest slot-`s` votes are
assumed to be `P` (the caller's strong induction on the cut: a current-slot optimistic lock of the
voter sits below one of them). -/
theorem pivot {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (_hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      (∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads) ∧
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
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hstart
  have hpass := proposal_walk_passes_old hrun hnc hsl hp hc hcall hd hti
  have hanch := proposal_anchor_old hrun hnc hsl hp hc hcall hd hti
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
  refine ⟨D, hsD, hDQ, proposal_suffix_viable hrun hnc hsl hp hc hcall hd hti hDt hDold,
    fun y hy j ℓy e hcy hes hE => ?_⟩
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
    · exact honest_genesis_root_anc hrun hU (hΦpU hDt) hg (hΦU hht)
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
