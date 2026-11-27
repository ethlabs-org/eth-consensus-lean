module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Shadow P-U: where the locks come from

A copy of stock `Compose/Sleepy/Provenance` (`lock_origin`, through `good_state`) over the shadow
run law `GoldilocksRun'`: every stored lock of an honest node sits below an origin of its own slot
from an earlier cut. The AC handler facts (`Good`, `Down`, `good_*`) are copied verbatim; the cut
induction reads the shadow cut law, the shadow frame (`Compose.frameOK_state'`) and the shadow
honest-tree coherence (`Coherence.honest_blocks_coherent'`). `Origin` and `OriginBefore` are the
stock ones (the shadow trace is a `RunTrace` of the stock AC). -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

section Handlers

variable {FGP : Type}

/-- The record satisfies `R` and every stored lock `G`. -/
private def Good (R : Nat → Prop) (G : AC.Lock → Prop) (A : AC.ACState sp.n) : Prop :=
  R A.latestConfirmed ∧ ∀ l ∈ A.locks, G l

/-- `G` is closed under moving a lock back to an ancestor (of the frame), keeping its slot. -/
private def Down (Φ : AC.Frm sp.n FGP) (G : AC.Lock → Prop) : Prop :=
  ∀ l l' : AC.Lock, l'.slot = l.slot → ∀ B ∈ Φ.tree, B.root = l.block → ∀ B' ∈ Φ.tree,
    B'.root = l'.block → Φ.Anc B' B → G l → G l'

variable {R : Nat → Prop} {G : AC.Lock → Prop} {Φ : AC.Frm sp.n FGP}

private theorem good_movesBack (hD : Down Φ G) {L L' : Set AC.Lock} (hm : AC.MovesBack sp Φ L L')
    (h : ∀ l ∈ L, G l) : ∀ l ∈ L', G l := by
  intro l' hl'
  obtain ⟨l, hl, hs, -, -, B, hB, hBr, B', hB', hB'r, hA⟩ := hm l' hl'
  exact hD l l' hs B hB hBr B' hB' hB'r hA (h l hl)

private theorem good_addLocks (hΦ : FrameOK Φ) (hD : Down Φ G) {L : Set AC.Lock} {t : Time}
    {s : Nat} {N : Set (Nat × Bool × Nat)} (h : ∀ l ∈ L, G l) (hN : ∀ p
        ∈ N, G ⟨p.1, s, p.2.1, p.2.2⟩) :
    ∀ l ∈ AC.addLocks sp L Φ t s N, G l :=
  good_movesBack hD ((AC.locks_move_back sp FGP Φ L t hΦ).2.1 s N) (by
    rintro l (hl | ⟨p, hp, rfl⟩)
    exacts [h l hl, hN p hp])

private theorem good_admitVote {A : AC.ACState sp.n} (h : Good R G A) (t : Time) (v : Vote sp.n) :
    Good R G (AC.admitVote sp A t v) := by
  refine ⟨?_, by rw [AC.admitVote_locks_eq]; exact h.2⟩
  have : (AC.admitVote sp A t v).latestConfirmed = A.latestConfirmed := by
    unfold AC.admitVote
    split_ifs <;> rfl
  rw [this]
  exact h.1

private theorem good_blockReceipt {A : AC.ACState sp.n} (h : Good R G A) (t : Time)
    (B : AC.Blk sp.n FGP) : Good R G (AC.blockReceipt sp A t B) :=
  h

private theorem good_optimistic (hΦ : FrameOK Φ) (hD : Down Φ G) {A : AC.ACState sp.n}
    (h : Good R G A) {t : Time}
    (hnew : ∀ B, AC.optimisticSelect sp A Φ t = some B → R B.root ∧
      ∀ e, G ⟨B.root, sp.slot t, true, e⟩) :
    Good R G (AC.optimisticConfirmation sp A Φ t) := by
  unfold AC.optimisticConfirmation
  rcases hsel : AC.optimisticSelect sp A Φ t with _ | B
  · exact h
  dsimp only
  have hl := good_addLocks (t := t) (s := sp.slot t)
    (N := {(B.root, true, AC.fastExpiry sp A.locks Φ t (sp.slot t))}) hΦ hD h.2
    (by rintro p rfl; exact (hnew B hsel).2 _)
  unfold AC.updateLatestConfirmed
  split_ifs
  exacts [⟨h.1, hl⟩, ⟨(hnew B hsel).1, hl⟩]

private theorem good_tryVote (hΦ : FrameOK Φ) (hD : Down Φ G) (x : Fin sp.n)
    {A : AC.ACState sp.n} (h : Good R G A) {t : Time}
    (hnew : ∀ e ∈ (AC.tryVote sp x A Φ t).2, ∀ B,
      AC.optimisticSelect sp (AC.admitVote sp e.readPoint t e.msg) Φ t = some B →
        R B.root ∧ ∀ e, G ⟨B.root, sp.slot t, true, e⟩) :
    Good R G (AC.tryVote sp x A Φ t).1 := by
  revert hnew
  unfold AC.tryVote
  lift_lets
  extract_lets s V A₁ dom H A₂ vote A₃
  have hA₁ : Good R G A₁ := by
    simp only [A₁]
    split
    · exact ⟨h.1, good_movesBack hD ((AC.locks_move_back sp FGP Φ A.locks t hΦ).2.2 _ _) h.2⟩
    · exact h
  have hA₂ : Good R G A₂ := hA₁
  split_ifs with h₁ h₂ h₃ <;> intro hnew
  · exact h
  · exact h
  · simp only [List.mem_singleton, forall_eq] at hnew
    simp only [A₃, h₃, ↓reduceIte]
    exact good_optimistic hΦ hD (good_admitVote hA₂ _ _) hnew
  · simpa only [A₃, h₃, Bool.false_eq_true, ↓reduceIte] using hA₂

private theorem good_updateConfirmation (hΦ : FrameOK Φ) (hD : Down Φ G) {A : AC.ACState sp.n}
    (h : Good R G A) {t : Time} {s : Nat}
    (hnew : ∀ C, AC.getConfirmation sp A Φ s = some C →
      R C.root ∧ ∀ D ∈ Φ.tree, Φ.Anc D C → ∀ f e, G ⟨D.root, s, f, e⟩) :
    Good R G (AC.updateConfirmation sp A Φ t s) := by
  unfold AC.updateConfirmation
  dsimp only
  rcases hC : AC.getConfirmation sp A Φ s with _ | C
  · exact h
  dsimp only
  obtain ⟨hR, hG⟩ := hnew C hC
  -- a veto keeps the record; the locks are written either way, on blocks of `C`'s path
  split_ifs with hconf
  all_goals
    refine ⟨?_, good_addLocks hΦ hD (by
      first | exact h.2 | (rw [AC.updateLatestConfirmed_keeps_locks]; exact h.2)) ?_⟩
    · first
        | exact h.1
        | (change R (AC.updateLatestConfirmed sp _ Φ C).latestConfirmed
           unfold AC.updateLatestConfirmed
           split_ifs
           exacts [h.1, hR])
    · rintro p (⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩) <;>
      · obtain ⟨⟨⟨hDt, -, hDC⟩, -⟩, -⟩ := (AC.deepest_mem hD).1
        exact hG D hDt hDC _ _

private theorem good_onTick (hΦ : FrameOK Φ) (hD : Down Φ G) (x : Fin sp.n) {A : AC.ACState sp.n}
    (h : Good R G A) {t : Time}
    (hopt : ∀ e ∈ (AC.acOnTick sp x A Φ t).2, ∀ B,
      AC.optimisticSelect sp (AC.admitVote sp e.readPoint t e.msg) Φ t = some B →
        R B.root ∧ ∀ e, G ⟨B.root, sp.slot t, true, e⟩)
    (hupd : t = sp.ts (sp.slot t) + 2 * sp.Δ → 0 < sp.slot t → AC.joined sp A t → ∀ C,
      AC.getConfirmation sp A Φ (sp.slot t - 1) = some C →
        R C.root ∧ ∀ D ∈ Φ.tree, Φ.Anc D C → ∀ f e, G ⟨D.root, sp.slot t - 1, f, e⟩) :
    Good R G (AC.acOnTick sp x A Φ t).1 := by
  unfold AC.acOnTick at hopt ⊢
  dsimp only at hopt ⊢
  split_ifs at hopt ⊢ with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · exact good_updateConfirmation hΦ hD h (hupd ht.1 ht.2 hj)
  · exact good_tryVote hΦ hD x h hopt
  · exact h
  · exact h

private theorem good_proposal (hΦ : FrameOK Φ) (hD : Down Φ G) {A : AC.ACState sp.n}
    (h : Good R G A) (t : Time) : Good R G (AC.acProposal sp A Φ t).1 := by
  unfold AC.acProposal
  dsimp only
  split_ifs
  all_goals first
    | exact h
    | exact ⟨h.1, good_movesBack hD ((AC.locks_move_back sp FGP Φ A.locks t hΦ).2.2 _ _) h.2⟩

private theorem good_toFG {A : AC.ACState sp.n} (h : Good R G A) (t : Time) :
    Good R G (AC.acToFG sp A Φ t).1 := by
  unfold AC.acToFG
  split_ifs
  · split
    · exact h
    · split_ifs
      · exact h
      · exact h
  · exact h

end Handlers


/-! ### The record and the locks at the cuts of an honest node -/

private def RecOK (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (T : Set (AC.Blk sp.n (List (FG.Att sp.n)))) (i : Nat) (r : Nat) : Prop :=
  ∃ C ∈ T, C.root = r ∧ (C.root = sp.genesisRoot ∨ ∃ s, OriginBefore tr H C s i)

private def LockOK (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (T : Set (AC.Blk sp.n (List (FG.Att sp.n)))) (i : Nat) (l : AC.Lock) : Prop :=
  ∃ L ∈ T, L.root = l.block ∧ ∃ C, OriginBefore tr H C l.slot i ∧ Anc (tr.HonestBlocks H) L C

private theorem good_mono {T T' : Set (AC.Blk sp.n (List (FG.Att sp.n)))} {i i' : Nat}
    {A : AC.ACState sp.n} (h : Good (RecOK tr H T i) (LockOK tr H T i) A) (hT : T ⊆ T')
    (hi : i ≤ i') : Good (RecOK tr H T' i') (LockOK tr H T' i') A := by
  obtain ⟨⟨C, hC, h1, h2⟩, hl⟩ := h
  have hmono : ∀ {C s}, OriginBefore tr H C s i → OriginBefore tr H C s i' := fun hs => by
    obtain ⟨x, hx, k, hk, CV, hO⟩ := originBefore_iff.1 hs
    exact originBefore_iff.2 ⟨x, hx, k, hk.trans_le hi, CV, hO⟩
  refine ⟨⟨C, hT hC, h1, h2.imp_right fun ⟨s, hs⟩ => ⟨s, hmono hs⟩⟩, fun l hl' => ?_⟩
  obtain ⟨L, hL, hLr, C, hC, hLC⟩ := hl l hl'
  exact ⟨L, hT hL, hLr, C, hmono hC, hLC⟩

private theorem down_lockOK {T : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    {Φ : AC.Frm sp.n (List (FG.Att sp.n))} (hU : Coherent (tr.HonestBlocks H))
    (hTU : T ⊆ tr.HonestBlocks H) (hΦT : Φ.tree ⊆ T) (i : Nat) : Down Φ (LockOK tr H T i) := by
  rintro l l' hs B hB hBr B' hB' hB'r hA ⟨L, hL, hLr, C, hC, hLC⟩
  obtain rfl : B = L := hU.1 (hTU (hΦT hB)) (hTU hL) (hBr.trans hLr.symm)
  exact ⟨B', hΦT hB', hB'r, C, hs ▸ hC, (hA.mono (hΦT.trans hTU)).trans hLC⟩

/-- At an AC call of an honest node, `Good` passes from the state before to the state after,
with the origins of the call's own selections (a copy of `good_acCall`). -/
private theorem good_acCall {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.CallAt y i (.ac ℓ))
    (h : Good (RecOK tr H (tr.state y i).fg.tree (i + 1))
      (LockOK tr H (tr.state y i).fg.tree (i + 1)) (tr.state y i).ac) :
    Good (RecOK tr H (tr.state y i).fg.tree (i + 1))
      (LockOK tr H (tr.state y i).fg.tree (i + 1)) (tr.post i).ac := by
  obtain ⟨hfr, hstep, -, -⟩ := (Node.cutStep_ac _ _ _ _ _).1 (hrun.cutLaw y hy i _ hc)
  have hΦ : FrameOK ℓ.frame := hfr ▸ frameOK_state hrun.toLocalRun hy i
  have hΦT : ℓ.frame.tree ⊆ (tr.state y i).fg.tree := by
    rw [hfr, Node.frame_eq, Store.toFrame_tree]
    exact fun X hX => hX.1
  have hTU : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX⟩
  have hD := down_lockOK (Coherence.honest_blocks_coherent hrun.toLocalRun hnc) hTU hΦT (i + 1)
  have hpc : tr.projAC.CallAt y i ℓ := ⟨hc.1, by simp [RunTrace.projAC, hc.2, RunTrace.acLabel]⟩
  have hps : tr.projAC.state y i = (tr.state y i).ac := projAC_state' hrun.toLocalRun hy i
  -- the optimistic selections of the call
  have opt : ∀ A₀, AC.OptimisticPoint tr.projAC y i ℓ A₀ → ∀ B,
      AC.optimisticSelect sp A₀ ℓ.frame (tr.time i) = some B →
      RecOK tr H (tr.state y i).fg.tree (i + 1) B.root ∧
        ∀ e, LockOK tr H (tr.state y i).fg.tree (i + 1) ⟨B.root, sp.slot (tr.time i), true, e⟩ := by
    intro A₀ hpt B hsel
    have hB : B ∈ ℓ.frame.tree := by
      have h' := hsel
      unfold AC.optimisticSelect at h'
      dsimp only at h'
      split_ifs at h'
      exact (AC.deepest_mem h').1.1
    have hO : AC.OptimisticLockAt tr.projAC y i (sp.slot (tr.time i)) B _ :=
      ⟨ℓ, A₀, hpt, rfl, hsel, rfl⟩
    have hOb : OriginBefore tr H B (sp.slot (tr.time i)) (i + 1) :=
      originBefore_iff.2 ⟨y, hy, i, Nat.lt_succ_self i, _, Or.inr hO⟩
    exact ⟨⟨B, hΦT hB, rfl, Or.inr ⟨_, hOb⟩⟩,
      fun _ => ⟨B, hΦT hB, rfl, B, hOb, Relation.ReflTransGen.refl⟩⟩
  have emit : ∀ e ∈ ℓ.emits, ∀ B, AC.optimisticSelect sp
      (AC.admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame (tr.time i) = some B →
      RecOK tr H (tr.state y i).fg.tree (i + 1) B.root ∧
        ∀ e, LockOK tr H (tr.state y i).fg.tree (i + 1) ⟨B.root, sp.slot (tr.time i), true, e⟩ :=
    fun e he => opt _ ⟨hpc, Or.inr (Or.inr ⟨e, he, rfl⟩)⟩
  have hpost := congrArg Prod.fst hstep
  have hem := congrArg Prod.snd hstep
  dsimp only at hpost hem
  rw [← hpost]
  generalize hA : (tr.state y i).ac = A at h hpost hem hps
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hem
    refine good_onTick hΦ hD y h (fun e he => emit e (hem ▸ he)) ?_
    intro ht hs0 hj C hC
    have hu : AC.UpdateAt tr.projAC y i (sp.slot (tr.time i) - 1) ℓ := by
      refine ⟨hpc, hcall, ?_, hps ▸ hj⟩
      change tr.time i = _
      conv_lhs => rw [ht]
      simp only [ACParams.ts]
      push_cast [Nat.cast_sub hs0]
      ring
    have hr : AC.ResultAt tr.projAC y i (sp.slot (tr.time i) - 1) C _ :=
      ⟨ℓ, hu, hps ▸ hC, rfl⟩
    have hCt : C ∈ ℓ.frame.tree := (AC.deepest_mem hC).1.1
    have hOb : OriginBefore tr H C (sp.slot (tr.time i) - 1) (i + 1) :=
      originBefore_iff.2 ⟨y, hy, i, Nat.lt_succ_self i, _, Or.inl hr⟩
    exact ⟨⟨C, hΦT hCt, rfl, Or.inr ⟨_, hOb⟩⟩, fun D hD hDC f e =>
      ⟨D, hΦT hD, rfl, C, hOb, hDC.mono (hΦT.trans hTU)⟩⟩
  | proposal => exact good_proposal hΦ hD h _
  | toFG => exact good_toFG h _
  | message m =>
    rw [hcall] at hem
    exact good_tryVote hΦ hD y (good_optimistic hΦ hD (good_admitVote h _ _)
      (opt _ ⟨hpc, Or.inl ⟨m, hcall, by rw [hps]; rfl⟩⟩))
      fun e he => emit e (hem ▸ he)
  | block B =>
    rw [hcall] at hem
    exact good_tryVote hΦ hD y (good_optimistic hΦ hD (good_blockReceipt h _ _)
      (opt _ ⟨hpc, Or.inr (Or.inl ⟨B, hcall, by rw [hps]; rfl⟩)⟩))
      fun e he => emit e (hem ▸ he)
  | restart =>
    obtain ⟨-, hl, hr, -⟩ := AC.restart_state sp _ ro y A ℓ.frame (tr.time i) hΦ
      (hrun.time_nonneg i)
    refine ⟨?_, ?_⟩
    · change RecOK _ _ _ _ (AC.acRestart sp ro y A ℓ.frame (tr.time i)).1.latestConfirmed
      rw [hr]
      exact h.1
    · change ∀ l ∈ (AC.acRestart sp ro y A ℓ.frame (tr.time i)).1.locks, _
      rw [hl]
      exact h.2

/-- An FG cut of an honest node leaves its AC state (a copy of `ac_of_fg`). -/
private theorem ac_of_fg {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : FGLabel sp.toParams (Payload sp.n)} (hc : tr.CallAt y i (.fg ℓ)) :
    (tr.post i).ac = (tr.state y i).ac := by
  have hlaw := hrun.cutLaw y hy i _ hc
  cases ℓ with
  | block B acc =>
    cases acc
    · rw [((Node.cutStep_block_false _ _ _ _ _).1 hlaw).2]
    · exact ((Node.cutStep_block_true _ _ _ _ _).1 hlaw).2.2.1
  | attestation a => exact ((Node.cutStep_attestation _ _ _ _ _).1 hlaw).2.1
  | attest C s =>
    cases s
    · rw [((Node.cutStep_attest_none _ _ _ _ _).1 hlaw).2]
    · exact ((Node.cutStep_attest_some _ _ _ _ _ _).1 hlaw).2.2

/-- `Good` at every cut of an honest node (a copy of `good_state`). -/
private theorem good_state {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    Good (RecOK tr H (tr.state y i).fg.tree i) (LockOK tr H (tr.state y i).fg.tree i)
      (tr.state y i).ac := by
  induction i with
  | zero =>
    have h0 : tr.state y 0 = Node.initWith _ (ini y) := hrun.init y hy
    obtain ⟨m, hm⟩ := AC.voteStart_iff.1 (hrun.vstart y)
    obtain ⟨-, -, hg, -⟩ := Store.accepted_tree_with Store.finalitySpec_updateFinality
      (Node.fg_reachable_at hrun.toLocalRun hy 0).reachableWith
    refine ⟨⟨_, hg, ?_, Or.inl rfl⟩, ?_⟩
    · rw [h0, hm]
      rfl
    · rw [h0, hm]
      exact fun l hl => absurd hl (Set.notMem_empty l)
  | succ i ih =>
    have ih' := good_mono ih (Coherence.tree_mono hrun.toLocalRun hy (Nat.le_succ i))
      (Nat.le_succ i)
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc] at ih' ⊢
      cases c with
      | ac ℓ =>
        have hfg := ((Node.cutStep_ac _ _ _ _ _).1 (hrun.cutLaw y hy i _ hc)).2.2.1
        rw [hfg] at ih' ⊢
        exact good_acCall hrun hnc hy hc ih'
      | fg ℓ =>
        rw [ac_of_fg hrun hy hc]
        exact ih'
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩] at ih' ⊢
      exact ih'

/-- **Every stored lock sits below an origin of its slot** whose event precedes the cut, and names
a block of the node's tree (a copy of `lock_origin`). -/
end Consensus.Goldilocks.Compose

end
