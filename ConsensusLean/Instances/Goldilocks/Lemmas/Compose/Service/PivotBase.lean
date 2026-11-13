module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the old origins of a slot and the proposal's anchor facts

The run facts the pivot of an honest proposal (`Compose/Service/Pivot`) builds on: walks and
anchors of a frame, the old origins of slot `s` (`OldOrigin`), the honest genesis root, the
restarts of a proposer (`proposal_call_restarts`), no honest optimistic check of slot `s` before
the proposal (`proposal_no_optimistic_of`), the slots of the proposer's stored locks
(`proposal_locks_slot_of`), and `fc_root` below an old origin from the row sources
(`fcRoot_of_rows_of`, `vote_fcRoot_old_of`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ### Blocks and walks -/

section Walk

variable {FGP : Type}

/-- A descendant inside the tree of a block of the tree is in the tree. -/
theorem mem_of_anc_left {Φ : SA.Frm sp.n FGP} {A B : SA.Blk sp.n FGP} (h : Φ.Anc A B)
    (hA : A ∈ Φ.tree) : B ∈ Φ.tree := by
  by_cases hAB : A = B
  · exact hAB ▸ hA
  · exact (Anc.mem h hAB).2

/-- A block between two blocks of a well-formed frame's tree (ancestry in a coherent `U` holding
the tree) is in the tree. -/
theorem mem_between {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U) {Φ : SA.Frm sp.n FGP}
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
theorem anc_parent {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U)
    {A B Q : SA.Blk sp.n FGP} (h : Anc U A B) (hne : A ≠ B) (hBQ : B.parent = some Q.root)
    (hQ : Q ∈ U) : Anc U A Q := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hAY, hY⟩
  · exact absurd heq.symm hne
  obtain rfl : Y = Q := hU.1 hY.1 hQ (Option.some_injective _ (hY.2.2.symm.trans hBQ))
  exact hAY

/-- The anchor is a live lock block or `fc_root`. -/
theorem anchor_mem (Φ : SA.Frm sp.n FGP) (A : SA.SAState sp.n) (t : Time) :
    SA.getAnchor sp A Φ t ∈ SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} := by
  unfold SA.getAnchor
  cases hd : SA.deepest Φ (SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
  | none => exact Or.inr rfl
  | some D => exact (SA.deepest_mem hd).1

/-- The anchor of a well-formed frame is in its tree. -/
theorem anchor_tree {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SA.SAState sp.n)
    (t : Time) : SA.getAnchor sp A Φ t ∈ Φ.tree := by
  rcases anchor_mem Φ A t with h | h
  · exact h.1
  · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem

/-- The duty head of a proposal is the walk of the full viable tree from its start, the anchor
after the proposal's unlocking. -/
theorem acProposal_walk {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP} {t : Time}
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
  linarith only [h, sp.toParams.hΔ, mul_le_mul_of_nonneg_left h1 sp.toParams.hΔ.le]

end Walk

/-! ### Over a run -/

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **The old origins of slot `s`** (the set whose deepest member is `D_s`): the
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

/-- Old origins are within every horizon containing the slot's proposal time. -/
theorem OldOrigin.within (hrun : GoldilocksRun proposer dg H tr)
    {s : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))} {b : Time}
    (h : OldOrigin tr H s O) (hb : sp.ts s ≤ b) :
    ∃ m < s, OriginWithin tr H O m b := by
  obtain ⟨x, hx, k, m, CV, ⟨hR, hm⟩ | ⟨hO, hm⟩⟩ := oldOrigin_iff.1 h
  · refine ⟨m, by omega, originWithin_iff.2 ⟨x, hx, k, CV, ?_, Or.inl hR⟩⟩
    obtain ⟨ℓ, hu, -⟩ := hR
    have ht : tr.time k = sp.ts m + 6 * sp.Δ := hu.2.2.1
    have hs : (m : Int) + 2 ≤ s := by exact_mod_cast hm
    have hΔ := sp.toParams.hΔ
    simp only [SAParams.ts] at hb ht
    linarith only [hb, ht, sp.toParams.hΔ, mul_le_mul_of_nonneg_left hs sp.toParams.hΔ.le]
  · refine ⟨m, by omega, originWithin_iff.2 ⟨x, hx, k, CV, ?_, Or.inr hO⟩⟩
    obtain ⟨ℓ, A, _, hs, _⟩ := hO
    change sp.slot (tr.time k) = m at hs
    have ht : tr.time k < sp.ts s := by
      by_contra ht
      have hle := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) (s : Int)).1 (le_of_not_gt ht)
      rw [hs] at hle
      omega
    exact ht.le.trans hb

/-- An honest block with the genesis root is below every honest block. -/
theorem honest_genesis_root_anc (hrun : GoldilocksRun proposer dg H tr)
    (hU : Coherent (tr.HonestBlocks H)) {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H) (hr : B.root = sp.genesisRoot) (hC : C ∈ tr.HonestBlocks H) :
    Anc (tr.HonestBlocks H) B C := by
  rw [honest_eq_genesis hrun hU hB hr]
  exact (honest_genesis_anc hrun hC).2

/-- The proposer's restarts up to its proposal are at or before `t_{s−1}`: `ac_proposal` runs
joined, and keeps the restart time. -/
theorem proposal_call_restarts (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay)) :
    ∀ c ≤ i, tr.projAC.RestartAt p c →
      tr.projAC.time c ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
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

/-- An AC call with the proposal label is a cut of a tick. -/
theorem acProposal_in_tick {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)}
    {t : Time} {e : Node.Event (goldilocksNode sp ro)} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : Cut.ac ℓ ∈ (Node.exec proposer dg y st t e).2) (hm : ℓ.call = .proposal) :
    ∃ x, e = .tick x := by
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
    (h : (Node.exec proposer dg y st t (.tick x)).2[c]? = some (Cut.ac ℓ)) :
    (ℓ.call = .tick ∧ c = 0) ∨ ℓ.call = .toFG ∨
      (Node.Proposes proposer y t ∧
        ((ℓ.call = .proposal ∧ c = 1) ∨ (ℓ.call ≠ .proposal ∧ 2 ≤ c))) := by
  obtain ⟨ℓt, pc, uc, hlt, hcs, hpc, ℓu, hlu, huc⟩ :=
    @tick_order sp.toParams (goldilocksNode sp ro) proposer dg y st t x
  have huc' : ∀ ℓ', Cut.ac ℓ' ∈ uc → ℓ'.call = .toFG := by
    intro ℓ' hm
    rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;> simp at hm <;> (rw [hm]; exact hlu)
  change (Node.onTick proposer dg y st t x).2[c]? = _ at h
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
theorem proposal_no_optimistic_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal) (hti : tr.time i = sp.ts s)
    (hstock : sp.committeeSize = sp.n) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ SA.OptimisticLockAt tr.projAC x k' s C CV := by
  intro z hz c hci C CV hO
  have hr' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hr'.localRun
  have hl := hrun.toLocalRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  -- the proposal call is the second cut of the proposer's tick at `t_s`
  obtain ⟨gi, ei, ki, hgi, rfl, hki⟩ := call_in_group hl hp (projAC_callAt.1 hc)
  rw [hti] at hgi hki
  obtain ⟨xi, rfl⟩ := acProposal_in_tick (List.mem_of_getElem? hki) hcall
  obtain ⟨hpr, hki1⟩ : Node.Proposes proposer p (sp.ts s) ∧ ki = 1 := by
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
        linarith only [h5, hΔ]
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
  have := Set.ncard_le_ncard hnoH (Set.toFinite _)
  omega

set_option linter.unusedVariables false in
/-- **The proposer has no stored lock of slot `s` or later**: a stored lock sits below an origin
of its slot before the proposal (`lock_origin`); a regular one of label at least `s` is written
after `t_s`, an optimistic one has the slot of its time, at most `s`, and not `s`
(`proposal_no_optimistic`). -/
theorem proposal_locks_slot_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hstock : sp.committeeSize = sp.n) :
    ∀ l ∈ (tr.state p i).ac.locks, l.slot < s := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro l hl
  obtain ⟨-, -, -, O, hO, -⟩ := lock_origin hrun hnc hp i l hl
  have hii : tr.projAC.time i = tr.time i := rfl
  obtain ⟨x, hx, k', hki, CV, hR | hOp⟩ := originBefore_iff.1 hO
  · obtain ⟨-, ⟨-, -, htk, -⟩, -⟩ := hR
    have := hr.time_mono hki.le
    have := ts_add_two_le (sp := sp) (m := l.slot) (s := s)
      (by linarith only [htk, this, hii, hti, sp.toParams.hΔ])
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
      (proposal_no_optimistic_of hrun hnc hf hp hc hcall hti hstock x hx k' hki O CV)

/-- **`fc_root` in a downward-closed set, from the sources**: at an honest node's cut whose honest
attestations all have sources in a set `R` closed under ancestors, `Σ.J` is genesis (`h_j = 0`) or
the entry of such a source (`justified_honest_source`, `honest_source_entry`), so in `R`, and `Σ.F`
is below `Σ.J`. -/
theorem fcRoot_of_rows_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hRc : ∀ A B, Anc (tr.HonestBlocks H) A B → R B → R A)
    (hsrc : HonestRowsSourced tr H R y j) :
    (Node.frame (tr.state y j)).fcRoot.root = sp.genesisRoot ∨
      R (Node.frame (tr.state y j)).fcRoot := by
  have hU : Coherent (tr.HonestBlocks H) :=
    (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hR := fg_reachable hrun.toLocalRun hy j
  obtain ⟨hFt, hJt, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hsU : (tr.state y j).fg.tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨y, hy, j, hZ⟩
  have hJ : (tr.state y j).fg.J.root = sp.genesisRoot ∨ R (tr.state y j).fg.J := by
    by_cases h0 : (tr.state y j).fg.hj = 0
    · left
      rw [justified_genesis hrun h0 hy]
      rfl
    obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_before hrun hnc hf hy hsrc (by omega)
    obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, j, hJt⟩ rfl
    exact Or.inr (hRc _ _ (Anc.mono (T := tr.HonestBlocks H) (fun Z hZ => ⟨x, hx, k, hZ⟩) hJD) hD)
  change (tr.state y j).fg.fcRoot.root = _ ∨ R (tr.state y j).fg.fcRoot
  unfold Store.fcRoot
  split_ifs
  · exact hJ
  rcases hJ with hg | hJR
  · left
    have h2 := (honest_genesis_anc hrun (hsU hFt)).2
    rw [← honest_eq_genesis hrun hU (hsU hJt) hg] at h2
    rw [Anc.antisymm hU (Anc.mono hsU hFJ) h2]
    exact hg
  · exact Or.inr (hRc _ _ (Anc.mono hsU hFJ) hJR)

/-- **A voter's `fc_root` is below an old origin, or genesis**
(`F ≤ fc_root ≤ D_s` at the vote reads): every honest attestation the voter holds was signed before
the vote, with a source below an origin before the signing (`attestation_source`); a regular one of
label `l` is written at `t_l + 6Δ ≤ t_s + Δ`, so `l ≤ s − 2`; an optimistic one has label at most
`s`, and not `s` (`no_optimistic_before_held_row`, at the full committee: `hstock`, §S.2
scope-(ii) item). -/
theorem vote_fcRoot_old_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} (hs : 0 < s) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ℓ e) (hes : e.msg.slot = s)
    (hstock : sp.committeeSize = sp.n) :
    ℓ.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldOrigin tr H s O ∧ Anc (tr.HonestBlocks H) ℓ.frame.fcRoot O := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ := sp.toParams.hΔ
  have htj : tr.time j ≤ sp.ts ((s' + 1 : Nat) : Int) + sp.Δ :=
    hes ▸ (cast_head_fcRoot hr hy hc).2
  have hsj : sp.slot (tr.projAC.time j) = s' + 1 := (SA.castAt_spec hr hy hc).2.1.symm.trans hes
  rw [frame_of_projAC hrun hy hc.1]
  refine fcRoot_of_rows_of hrun hnc hf hy (j := j)
    (R := fun B => ∃ O, OldOrigin tr H (s' + 1) O ∧ Anc (tr.HonestBlocks H) B O)
    (fun _ _ hAB ⟨O, hO, hBO⟩ => ⟨O, hO, hAB.trans hBO⟩)
    (honestRowsSourced_iff.2 fun X hX a ha hav => ?_)
  obtain ⟨m, hmj, hm, k, hkm, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  refine ⟨D, ⟨C, ?_, hDC⟩, hDs⟩
  have hjj : tr.projAC.time j = tr.time j := rfl
  obtain ⟨z, hz, c, hck, CV, hR | hOp⟩ := originBefore_iff.1 hC
  · refine ⟨z, hz, c, l, CV, Or.inl ⟨hR, ts_add_two_le (sp := sp) ?_⟩⟩
    obtain ⟨-, ⟨-, -, htc, -⟩, -⟩ := hR
    have := hr.time_mono (show c ≤ j by omega)
    linarith only [htc, this, hjj, htj]
  · refine ⟨z, hz, c, l, CV, Or.inr ⟨hOp, ?_⟩⟩
    obtain ⟨-, -, -, hsc, -⟩ := id hOp
    have hle := SA.slot_mono sp (hr.time_nonneg c) (hr.time_mono (show c ≤ j by omega))
    rcases Nat.lt_or_ge l (s' + 1) with h | h
    · omega
    obtain rfl : l = s' + 1 := by omega
    exact (no_optimistic_before_held_row_of hrun hnc _ SA.CommitteeP.full
      (SA.size_binding_full hstock) (SA.cs2_full hstock hf) hy (SA.mem_full _ _) hc hes
      hm hmj hav hkm hsg hz hck hOp).elim

end Consensus.Goldilocks.Compose

end
