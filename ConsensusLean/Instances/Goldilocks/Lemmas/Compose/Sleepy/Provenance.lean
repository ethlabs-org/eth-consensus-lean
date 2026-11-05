module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
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

/-! # Goldilocks under `Sleepy`: where records, locks, sources, attestations and caches come from

The provenance part of S1, which needs no
comparability: it holds of every Goldilocks run, by the handlers alone.

* The record `latest_confirmed` is written only by `update_latest_confirmed`, with the result of a
  non-vetoed update or an optimistic selection; restarts keep it. So it names genesis or an
  origin, a block of the node's tree (`record_origin`).
* Every stored lock sits below an origin of its own slot from an earlier cut (`lock_origin`): the
  update of slot `s` locks blocks on its result's path, an optimistic check locks its selection,
  and the lock functions only move locks back (`SA.locks_move_back`). `SA.lock_provenance` does
  not tie an update's locks to its result, so both facts come from one induction over the cuts
  of the node (`good_state`), which follows each SA handler (`Good`, `Down`).
* Every FG source is a live fast lock block, so on the chain (`source_on_chain`); every honest
  attestation names the entry of its source's state, an ancestor of the source
  (`row_on_chain`); every `Σ.F` and `Σ.J` is genesis or an entry with a target quorum, which has
  an honest attestation since `q > f` (`caches_on_chain`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-! ### The SA functions write the record and the locks only from selections

`Good R G A`: the record of `A` satisfies `R` and each stored lock `G`. When `G` is closed under
moving a lock back in the frame (`Down`), every SA function keeps `Good`, given `R` and `G` of the
blocks it newly selects: an optimistic selection (a fast lock of the current slot) and the result
of a non-vetoed update (locks of its slot on ancestors of the result). -/

section Handlers

variable {FGP : Type}

/-- The record satisfies `R` and every stored lock `G`. -/
private def Good (R : Nat → Prop) (G : SA.Lock → Prop) (A : SA.SAState sp.n) : Prop :=
  R A.latestConfirmed ∧ ∀ l ∈ A.locks, G l

/-- `G` is closed under moving a lock back to an ancestor (of the frame), keeping its slot. -/
private def Down (Φ : SA.Frm sp.n FGP) (G : SA.Lock → Prop) : Prop :=
  ∀ l l' : SA.Lock, l'.slot = l.slot → ∀ B ∈ Φ.tree, B.root = l.block → ∀ B' ∈ Φ.tree,
    B'.root = l'.block → Φ.Anc B' B → G l → G l'

variable {R : Nat → Prop} {G : SA.Lock → Prop} {Φ : SA.Frm sp.n FGP}

private theorem good_movesBack (hD : Down Φ G) {L L' : Set SA.Lock} (hm : SA.MovesBack sp Φ L L')
    (h : ∀ l ∈ L, G l) : ∀ l ∈ L', G l := by
  intro l' hl'
  obtain ⟨l, hl, hs, -, -, B, hB, hBr, B', hB', hB'r, hA⟩ := hm l' hl'
  exact hD l l' hs B hB hBr B' hB' hB'r hA (h l hl)

private theorem good_addLocks (hΦ : FrameOK Φ) (hD : Down Φ G) {L : Set SA.Lock} {t : Time}
    {s : Nat} {N : Set (Nat × Bool × Nat)} (h : ∀ l ∈ L, G l) (hN : ∀ p
        ∈ N, G ⟨p.1, s, p.2.1, p.2.2⟩) :
    ∀ l ∈ SA.addLocks sp L Φ t s N, G l :=
  good_movesBack hD ((SA.locks_move_back sp FGP Φ L t hΦ).2.1 s N) (by
    rintro l (hl | ⟨p, hp, rfl⟩)
    exacts [h l hl, hN p hp])

private theorem good_admitVote {A : SA.SAState sp.n} (h : Good R G A) (t : Time) (v : Vote sp.n) :
    Good R G (SA.admitVote sp A t v) := by
  refine ⟨?_, by rw [SA.admitVote_locks_eq]; exact h.2⟩
  have : (SA.admitVote sp A t v).latestConfirmed = A.latestConfirmed := by
    unfold SA.admitVote
    split_ifs <;> rfl
  rw [this]
  exact h.1

private theorem good_blockReceipt {A : SA.SAState sp.n} (h : Good R G A) (t : Time)
    (B : SA.Blk sp.n FGP) : Good R G (SA.blockReceipt sp A t B) := by
  unfold SA.blockReceipt
  generalize SA.blockVotes B = l
  suffices ∀ A' : SA.SAState sp.n, Good R G A' →
      Good R G (l.foldl (fun A v => SA.admitVote sp A t v) A') from this _ h
  induction l with
  | nil => exact fun _ h => h
  | cons v l ih => exact fun A' h => ih _ (good_admitVote h t v)

private theorem good_optimistic (hΦ : FrameOK Φ) (hD : Down Φ G) {A : SA.SAState sp.n}
    (h : Good R G A) {t : Time}
    (hnew : ∀ B, SA.optimisticSelect sp A Φ t = some B → R B.root ∧
      ∀ e, G ⟨B.root, sp.slot t, true, e⟩) :
    Good R G (SA.optimisticConfirmation sp A Φ t) := by
  unfold SA.optimisticConfirmation
  rcases hsel : SA.optimisticSelect sp A Φ t with _ | B
  · exact h
  dsimp only
  have hl := good_addLocks (t := t) (s := sp.slot t)
    (N := {(B.root, true, SA.fastExpiry sp A.locks Φ t (sp.slot t))}) hΦ hD h.2
    (by rintro p rfl; exact (hnew B hsel).2 _)
  unfold SA.updateLatestConfirmed
  split_ifs
  exacts [⟨h.1, hl⟩, ⟨(hnew B hsel).1, hl⟩]

private theorem good_tryVote (hΦ : FrameOK Φ) (hD : Down Φ G) (x : Fin sp.n)
    {A : SA.SAState sp.n} (h : Good R G A) {t : Time}
    (hnew : ∀ e ∈ (SA.tryVote sp x A Φ t).2, ∀ B,
      SA.optimisticSelect sp (SA.admitVote sp e.readPoint t e.msg) Φ t = some B →
        R B.root ∧ ∀ e, G ⟨B.root, sp.slot t, true, e⟩) :
    Good R G (SA.tryVote sp x A Φ t).1 := by
  revert hnew
  unfold SA.tryVote
  dsimp only
  split_ifs <;> intro hnew
  · exact h
  · exact h
  all_goals
    simp only [List.mem_singleton, forall_eq] at hnew
    refine good_optimistic hΦ hD (good_admitVote ?_ _ _) hnew
    first
      | exact h
      | exact ⟨h.1, good_movesBack hD ((SA.locks_move_back sp FGP Φ A.locks t hΦ).2.2 _ _) h.2⟩

private theorem good_updateConfirmation (hΦ : FrameOK Φ) (hD : Down Φ G) {A : SA.SAState sp.n}
    (h : Good R G A) {t : Time} {s : Nat}
    (hnew : ∀ C, SA.getConfirmation sp A Φ s = some C →
      R C.root ∧ ∀ D ∈ Φ.tree, Φ.Anc D C → ∀ f e, G ⟨D.root, s, f, e⟩) :
    Good R G (SA.updateConfirmation sp A Φ t s) := by
  unfold SA.updateConfirmation
  dsimp only
  rcases hC : SA.getConfirmation sp A Φ s with _ | C
  · exact h
  dsimp only
  obtain ⟨hR, hG⟩ := hnew C hC
  -- a veto keeps the record; the locks are written either way, on blocks of `C`'s path
  split_ifs with hconf
  all_goals
    refine ⟨?_, good_addLocks hΦ hD (by
      first | exact h.2 | (rw [SA.updateLatestConfirmed_locks_eq]; exact h.2)) ?_⟩
    · first
        | exact h.1
        | (change R (SA.updateLatestConfirmed sp _ Φ C).latestConfirmed
           unfold SA.updateLatestConfirmed
           split_ifs
           exacts [h.1, hR])
    · rintro p (⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩) <;>
      · obtain ⟨⟨⟨hDt, -, hDC⟩, -⟩, -⟩ := (SA.deepest_mem hD).1
        exact hG D hDt hDC _ _

private theorem good_onTick (hΦ : FrameOK Φ) (hD : Down Φ G) (x : Fin sp.n) {A : SA.SAState sp.n}
    (h : Good R G A) {t : Time}
    (hopt : ∀ e ∈ (SA.acOnTick sp x A Φ t).2, ∀ B,
      SA.optimisticSelect sp (SA.admitVote sp e.readPoint t e.msg) Φ t = some B →
        R B.root ∧ ∀ e, G ⟨B.root, sp.slot t, true, e⟩)
    (hupd : t = sp.ts (sp.slot t) + 2 * sp.Δ → 0 < sp.slot t → SA.joined sp A t → ∀ C,
      SA.getConfirmation sp A Φ (sp.slot t - 1) = some C →
        R C.root ∧ ∀ D ∈ Φ.tree, Φ.Anc D C → ∀ f e, G ⟨D.root, sp.slot t - 1, f, e⟩) :
    Good R G (SA.acOnTick sp x A Φ t).1 := by
  unfold SA.acOnTick at hopt ⊢
  dsimp only at hopt ⊢
  split_ifs at hopt ⊢ with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · exact good_updateConfirmation hΦ hD h (hupd ht.1 ht.2 hj)
  · exact good_tryVote hΦ hD x h hopt
  · exact h
  · exact h

private theorem good_proposal (hΦ : FrameOK Φ) (hD : Down Φ G) {A : SA.SAState sp.n}
    (h : Good R G A) (t : Time) : Good R G (SA.acProposal sp A Φ t).1 := by
  unfold SA.acProposal
  dsimp only
  split_ifs
  all_goals first
    | exact h
    | exact ⟨h.1, good_movesBack hD ((SA.locks_move_back sp FGP Φ A.locks t hΦ).2.2 _ _) h.2⟩

private theorem good_toFG {A : SA.SAState sp.n} (h : Good R G A) (t : Time) :
    Good R G (SA.acToFG sp A Φ t).1 := by
  unfold SA.acToFG
  split_ifs
  · split
    · exact h
    · split_ifs
      · exact h
      · exact h
  · exact h

end Handlers

/-! ### The record and the locks at the cuts of an honest node -/

/-- The block `r` names in `T` is genesis or an origin from a cut before `i`. -/
private def RecOK (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (T : Set (SA.Blk sp.n (List (FG.Att sp.n)))) (i : Nat) (r : Nat) : Prop :=
  ∃ C ∈ T, C.root = r ∧ (C.root = sp.genesisRoot ∨ ∃ s, OriginBefore tr H C s i)

/-- The lock `l` names a block of `T` below an origin of its slot from a cut before `i`. -/
private def LockOK (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (T : Set (SA.Blk sp.n (List (FG.Att sp.n)))) (i : Nat) (l : SA.Lock) : Prop :=
  ∃ L ∈ T, L.root = l.block ∧ ∃ C, OriginBefore tr H C l.slot i ∧ Anc (tr.HonestBlocks H) L C

private theorem good_mono {T T' : Set (SA.Blk sp.n (List (FG.Att sp.n)))} {i i' : Nat}
    {A : SA.SAState sp.n} (h : Good (RecOK tr H T i) (LockOK tr H T i) A) (hT : T ⊆ T')
    (hi : i ≤ i') : Good (RecOK tr H T' i') (LockOK tr H T' i') A := by
  obtain ⟨⟨C, hC, h1, h2⟩, hl⟩ := h
  have hmono : ∀ {C s}, OriginBefore tr H C s i → OriginBefore tr H C s i' := fun hs => by
    obtain ⟨x, hx, k, hk, CV, hO⟩ := originBefore_iff.1 hs
    exact originBefore_iff.2 ⟨x, hx, k, hk.trans_le hi, CV, hO⟩
  refine ⟨⟨C, hT hC, h1, h2.imp_right fun ⟨s, hs⟩ => ⟨s, hmono hs⟩⟩, fun l hl' => ?_⟩
  obtain ⟨L, hL, hLr, C, hC, hLC⟩ := hl l hl'
  exact ⟨L, hT hL, hLr, C, hmono hC, hLC⟩

/-- The AC projection of a Goldilocks run is an AC trace with the contract. -/
private theorem ac_run (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) :
    ACLocalRun (goldilocksNode sp ro) H (tr.HonestBlocks H) tr.projAC :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  ac_projection _ _ dg H _ tr proposer
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.toLocalRun hnc

private theorem down_lockOK {T : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hU : Coherent (tr.HonestBlocks H))
    (hTU : T ⊆ tr.HonestBlocks H) (hΦT : Φ.tree ⊆ T) (i : Nat) : Down Φ (LockOK tr H T i) := by
  rintro l l' hs B hB hBr B' hB' hB'r hA ⟨L, hL, hLr, C, hC, hLC⟩
  obtain rfl : B = L := hU.1 (hTU (hΦT hB)) (hTU hL) (hBr.trans hLr.symm)
  exact ⟨B', hΦT hB', hB'r, C, hs ▸ hC, (hA.mono (hΦT.trans hTU)).trans hLC⟩

/-- At an AC call of an honest node, `Good` passes from the state before to the state after,
with the origins of the call's own selections. -/
private theorem good_acCall (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.CallAt y i (.ac ℓ))
    (h : Good (RecOK tr H (tr.state y i).fg.tree (i + 1))
      (LockOK tr H (tr.state y i).fg.tree (i + 1)) (tr.state y i).ac) :
    Good (RecOK tr H (tr.state y i).fg.tree (i + 1))
      (LockOK tr H (tr.state y i).fg.tree (i + 1)) (tr.post i).ac := by
  obtain ⟨hfr, hstep, -, -⟩ := hrun.cutLaw y hy i _ hc
  have hΦ : FrameOK ℓ.frame :=
    hfr ▸ (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦT : ℓ.frame.tree ⊆ (tr.state y i).fg.tree := by
    rw [hfr]
    exact fun X hX => hX.1
  have hTU : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX⟩
  have hD := down_lockOK (honest_coherent hrun hnc) hTU hΦT (i + 1)
  have hpc : tr.projAC.CallAt y i ℓ := ⟨hc.1, by simp [RunTrace.projAC, hc.2, RunTrace.acLabel]⟩
  have hps : tr.projAC.state y i = (tr.state y i).ac := projAC_state hrun.toLocalRun hy i
  -- the optimistic selections of the call
  have opt : ∀ A₀, SA.OptimisticPoint tr.projAC y i ℓ A₀ → ∀ B,
      SA.optimisticSelect sp A₀ ℓ.frame (tr.time i) = some B →
      RecOK tr H (tr.state y i).fg.tree (i + 1) B.root ∧
        ∀ e, LockOK tr H (tr.state y i).fg.tree (i + 1) ⟨B.root, sp.slot (tr.time i), true, e⟩ := by
    intro A₀ hpt B hsel
    have hB : B ∈ ℓ.frame.tree := by
      have h' := hsel
      unfold SA.optimisticSelect at h'
      dsimp only at h'
      split_ifs at h'
      exact (SA.deepest_mem h').1.1
    have hO : SA.OptimisticLockAt tr.projAC y i (sp.slot (tr.time i)) B _ :=
      ⟨ℓ, A₀, hpt, rfl, hsel, rfl⟩
    have hOb : OriginBefore tr H B (sp.slot (tr.time i)) (i + 1) :=
      originBefore_iff.2 ⟨y, hy, i, Nat.lt_succ_self i, _, Or.inr hO⟩
    exact ⟨⟨B, hΦT hB, rfl, Or.inr ⟨_, hOb⟩⟩,
      fun _ => ⟨B, hΦT hB, rfl, B, hOb, Relation.ReflTransGen.refl⟩⟩
  have emit : ∀ e ∈ ℓ.emits, ∀ B, SA.optimisticSelect sp
      (SA.admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame (tr.time i) = some B →
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
    have hu : SA.UpdateAt tr.projAC y i (sp.slot (tr.time i) - 1) ℓ := by
      refine ⟨hpc, hcall, ?_, hps ▸ hj⟩
      change tr.time i = _
      conv_lhs => rw [ht]
      simp only [SAParams.ts]
      push_cast [Nat.cast_sub hs0]
      ring
    have hr : SA.ResultAt tr.projAC y i (sp.slot (tr.time i) - 1) C _ :=
      ⟨ℓ, hu, hps ▸ hC, rfl⟩
    have hCt : C ∈ ℓ.frame.tree := (SA.deepest_mem hC).1.1
    have hOb : OriginBefore tr H C (sp.slot (tr.time i) - 1) (i + 1) :=
      originBefore_iff.2 ⟨y, hy, i, Nat.lt_succ_self i, _, Or.inl hr⟩
    exact ⟨⟨C, hΦT hCt, rfl, Or.inr ⟨_, hOb⟩⟩, fun D hD hDC f e =>
      ⟨D, hΦT hD, rfl, C, hOb, hDC.mono (hΦT.trans hTU)⟩⟩
  | proposal => exact good_proposal hΦ hD h _
  | toFG => exact good_toFG h _
  | message m =>
    rw [hcall] at hem
    exact good_tryVote hΦ hD y (good_optimistic hΦ hD (good_admitVote h _ _)
      (opt _ ⟨hpc, Or.inl ⟨m, hcall, by rw [hps]; rfl⟩⟩)) fun e he => emit e (hem ▸ he)
  | block B =>
    rw [hcall] at hem
    exact good_tryVote hΦ hD y (good_optimistic hΦ hD (good_blockReceipt h _ _)
      (opt _ ⟨hpc, Or.inr (Or.inl ⟨B, hcall, by rw [hps]; rfl⟩)⟩)) fun e he => emit e (hem ▸ he)
  | restart =>
    obtain ⟨-, hl, hr, -⟩ := SA.restart_state sp _ ro y A ℓ.frame (tr.time i) hΦ
      (hrun.time_nonneg i)
    refine ⟨?_, ?_⟩
    · change RecOK _ _ _ _ (SA.acRestart sp ro y A ℓ.frame (tr.time i)).1.latestConfirmed
      rw [hr]
      exact h.1
    · change ∀ l ∈ (SA.acRestart sp ro y A ℓ.frame (tr.time i)).1.locks, _
      rw [hl]
      exact h.2

/-- An FG cut of an honest node leaves its AC state. -/
private theorem ac_of_fg (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : FGLabel sp.toParams (Payload sp.n)} (hc : tr.CallAt y i (.fg ℓ)) :
    (tr.post i).ac = (tr.state y i).ac := by
  have hlaw := hrun.cutLaw y hy i _ hc
  cases ℓ with
  | block B acc =>
    cases acc
    · rw [hlaw.2]
    · exact hlaw.2.2.1
  | attestation a => exact hlaw.2.1
  | attest C s =>
    cases s
    · rw [hlaw.2]
    · exact hlaw.2.2

/-- A changed record is an actual selection at this cut, not merely an
origin somewhere in the run. Restarts and FG calls retain the record. -/
theorem record_step_origin (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y (i + 1)).ac.latestConfirmed = (tr.state y i).ac.latestConfirmed ∨
      ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        ∃ s CV, SA.ResultAt tr.projAC y i s C CV ∨
          SA.OptimisticLockAt tr.projAC y i s C CV := by
  let R := fun r => r = (tr.state y i).ac.latestConfirmed ∨
    ∃ C ∈ (tr.state y i).fg.tree, C.root = r ∧
      ∃ s CV, SA.ResultAt tr.projAC y i s C CV ∨ SA.OptimisticLockAt tr.projAC y i s C CV
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    rw [tr.state_succ_of_call hc]
    cases c with
    | fg ℓ => exact Or.inl (congrArg SA.SAState.latestConfirmed (ac_of_fg hrun hy hc))
    | ac ℓ =>
      obtain ⟨hfr, hstep, _, _⟩ := hrun.cutLaw y hy i _ hc
      have hΦ : FrameOK ℓ.frame :=
        hfr ▸ (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
      have hΦT : ℓ.frame.tree ⊆ (tr.state y i).fg.tree := by
        rw [hfr]; exact fun _ h => h.1
      have hpc : tr.projAC.CallAt y i ℓ := ⟨hc.1, by simp [RunTrace.projAC, hc.2, RunTrace.acLabel]⟩
      have hps := projAC_state hrun.toLocalRun hy i
      have h : Good R (fun _ => True) (tr.state y i).ac := ⟨Or.inl rfl, fun _ _ => trivial⟩
      have hD : Down ℓ.frame (fun _ => True) := fun _ _ _ _ _ _ _ _ _ _ _ => trivial
      have opt : ∀ A₀, SA.OptimisticPoint tr.projAC y i ℓ A₀ → ∀ B,
          SA.optimisticSelect sp A₀ ℓ.frame (tr.time i) = some B →
          R B.root ∧ ∀ _ : Nat, True := by
        intro A₀ hpt B hsel
        have hB : B ∈ ℓ.frame.tree := by
          unfold SA.optimisticSelect at hsel
          dsimp only at hsel
          split_ifs at hsel
          exact (SA.deepest_mem hsel).1.1
        exact ⟨Or.inr ⟨B, hΦT hB, rfl, _, _, Or.inr ⟨ℓ, A₀, hpt, rfl, hsel, rfl⟩⟩, fun _ => trivial⟩
      have emit : ∀ e ∈ ℓ.emits, ∀ B, SA.optimisticSelect sp
          (SA.admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame (tr.time i) = some B →
          R B.root ∧ ∀ _ : Nat, True := fun e he => opt _ ⟨hpc, Or.inr (Or.inr ⟨e, he, rfl⟩)⟩
      have hpost := congrArg Prod.fst hstep
      have hem := congrArg Prod.snd hstep
      dsimp only at hpost hem
      change R (tr.post i).ac.latestConfirmed
      rw [← hpost]
      cases hcall : ℓ.call with
      | tick =>
        rw [hcall] at hem
        apply (good_onTick hΦ hD y h (fun e he => emit e (hem ▸ he)) ?_).1
        intro ht hs0 hj C hC
        have hu : SA.UpdateAt tr.projAC y i (sp.slot (tr.time i) - 1) ℓ := by
          refine ⟨hpc, hcall, ?_, hps ▸ hj⟩
          change tr.time i = _
          conv_lhs => rw [ht]
          simp only [SAParams.ts]
          push_cast [Nat.cast_sub hs0]
          ring
        exact ⟨Or.inr ⟨C, hΦT (SA.deepest_mem hC).1.1, rfl, _, _,
          Or.inl ⟨ℓ, hu, hps ▸ hC, rfl⟩⟩, fun _ _ _ _ _ => trivial⟩
      | proposal => exact (good_proposal hΦ hD h _).1
      | toFG => exact (good_toFG h _).1
      | message m =>
        rw [hcall] at hem
        exact (good_tryVote hΦ hD y (good_optimistic hΦ hD (good_admitVote h _ _)
          (opt _ ⟨hpc, Or.inl ⟨m, hcall, by rw [hps]; rfl⟩⟩))
          (fun e he => emit e (hem ▸ he))).1
      | block B =>
        rw [hcall] at hem
        exact (good_tryVote hΦ hD y (good_optimistic hΦ hD (good_blockReceipt h _ _)
          (opt _ ⟨hpc, Or.inr (Or.inl ⟨B, hcall, by rw [hps]; rfl⟩)⟩))
          (fun e he => emit e (hem ▸ he))).1
      | restart =>
        change R (SA.acRestart sp ro y (tr.state y i).ac ℓ.frame (tr.time i)).1.latestConfirmed
        rw [(SA.restart_state sp _ ro y _ ℓ.frame (tr.time i) hΦ (hrun.time_nonneg i)).2.2.1]
        exact Or.inl rfl
  · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
    exact Or.inl rfl

/-- The tree of an honest node only grows across a cut. -/
private theorem tree_succ (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y i).fg.tree ⊆ (tr.state y (i + 1)).fg.tree := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hR := fg_reachable hrun.toLocalRun hy i
    have hlaw := hrun.cutLaw y hy i c hc
    rw [tr.state_succ_of_call hc]
    cases c with
    | ac ℓ => rw [hlaw.2.2.1]
    | fg ℓ =>
      cases ℓ with
      | block B acc =>
        cases acc
        · rw [hlaw.2]
        · rw [(Store.tree_grows _ _ _ _ hR).1 B _ hlaw.2.1]
          exact Set.subset_insert _ _
      | attestation a => rw [hlaw.1, (Store.tree_grows _ _ _ _ hR).2 a]
      | attest C s =>
        cases s
        · rw [hlaw.2]
        · rw [hlaw.2.1]
  · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

/-- `Good` at every cut of an honest node: its record names a block of its tree that is genesis
or an origin, and each stored lock a block of its tree below an origin of its slot from an
earlier cut. -/
private theorem good_state (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    Good (RecOK tr H (tr.state y i).fg.tree i) (LockOK tr H (tr.state y i).fg.tree i)
      (tr.state y i).ac := by
  induction i with
  | zero =>
    have h0 : tr.state y 0 = Node.init _ := hrun.init y hy
    obtain ⟨-, -, hg, -⟩ := Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy 0)
    refine ⟨⟨_, hg, ?_, Or.inl rfl⟩, ?_⟩
    · rw [h0]
      rfl
    · rw [h0]
      exact fun l hl => absurd hl (Set.notMem_empty l)
  | succ i ih =>
    have ih' := good_mono ih (tree_succ hrun hy i) (Nat.le_succ i)
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc] at ih' ⊢
      cases c with
      | ac ℓ =>
        have hfg := (hrun.cutLaw y hy i _ hc).2.2.1
        rw [hfg] at ih' ⊢
        exact good_acCall hrun hnc hy hc ih'
      | fg ℓ =>
        rw [ac_of_fg hrun hy hc]
        exact ih'
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩] at ih' ⊢
      exact ih'

/-- `ac_to_fg` returns one of its candidates. -/
theorem toFG_candidate {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} {C : SA.Blk sp.n (List (FG.Att sp.n))} (h : (SA.acToFG sp A Φ t).2 = some C) :
    C ∈ SA.toFGCandidates sp A Φ t := by
  unfold SA.acToFG at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (SA.deepest_mem hC').1

/-- An attestation names the entry of its entry state. -/
private theorem createAtt_T {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  have hT : ∀ hc T τ, Λ.heightPair σe.h σe.Th = some (hc, T, τ) → T = σe.Th := by
    intro hc T τ hp
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp
    all_goals exact hp.2.1.symm
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨hc, T, τ⟩
  · simp [hp] at h
  · simp only [hp] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hT _ _ _ hp

/-! ### The justified and finalized blocks of a chain have a quorum of attestations -/

/-- Some `q` validators each have an attestation on the chain naming `T`. -/
private def Quorum (gp : FG.FGParams) (c : List (FG.FGBlock gp.n)) (T : Nat) : Prop :=
  ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.T = T

/-- The justified and finalized roots of a chain state and its pending pairs are genesis or named
by a quorum of attestations on the chain; its progress bits by attestations on its entry. -/
private structure Named (gp : FG.FGParams) (c : List (FG.FGBlock gp.n))
    (σ : FG.ChainState gp.n) : Prop where
  prog : ∀ v ∈ σ.prog, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.T = σ.Th
  pending : ∀ p ∈ σ.pending, Quorum gp c p.2
  J : σ.J = gp.genesis ∨ Quorum gp c σ.J
  F : σ.F = gp.genesis ∨ Quorum gp c σ.F

private theorem named_step (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)}
    {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n} (hc : gp.chainState c = some σ)
    (hN : Named gp c σ) (h : gp.stateTransition σ B = some σ') : Named gp (c ++ [B]) σ' := by
  have hatts : gp.chainAtts (c ++ [B]) = gp.chainAtts c ++ B.atts := by
    simp [FG.FGParams.chainAtts]
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    rw [hatts]; exact List.mem_append_left _ h
  have liftQ : ∀ {T}, Quorum gp c T → Quorum gp (c ++ [B]) T := fun ⟨Q, hQ, hv⟩ =>
    ⟨Q, hQ, fun v hv' => let ⟨a, ha, h1⟩ := hv v hv'; ⟨a, liftA ha, h1⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hts⟩ := FG.chain_invariants gp c σ hc
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  have hsub := FG.ChainState.foldl_processAtt_target_subset { σ with s := B.slot } B.atts hts
  have hP := fun v => @Store.mem_foldl_prog _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hsub hP ⊢
  dsimp only at hsub hP ⊢
  have hprog : ∀ v ∈ p, ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.T = σ.Th := by
    intro v hv
    rcases hP v hv with hv | ⟨a, ha, h1, h2⟩
    · obtain ⟨a, ha, h'⟩ := hN.prog v hv
      exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, by rw [hatts]; exact List.mem_append_right _ ha, h1, h2⟩
  obtain ⟨F, hF, σ₁, rfl, hFc, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hpend : ∀ r ∈ σ.pending.filter (fun p => hF < p.1), Quorum gp (c ++ [B]) r.2 :=
    fun r hr => liftQ (hN.pending r (List.mem_of_mem_filter hr))
  have hF₁ : F = gp.genesis ∨ Quorum gp (c ++ [B]) F := by
    rcases hFc with ⟨rfl, -⟩ | ⟨hm, -⟩
    · exact hN.F.imp_right liftQ
    · exact Or.inr (liftQ (hN.pending _ hm))
  rcases hcase with ⟨hj, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · have hQ : Quorum gp (c ++ [B]) σ.Th := ⟨t, hj.1, fun v hv => hprog v (hsub hv)⟩
    refine ⟨by simp [FG.ChainState.advance], fun r hr => ?_, Or.inr hQ, hF₁⟩
    simp only [FG.ChainState.advance] at hr
    rcases List.mem_append.1 (List.mem_of_mem_drop hr) with hr | hr
    · exact hpend r hr
    · rw [List.mem_singleton] at hr
      subst hr
      exact hQ
  · exact ⟨by simp [FG.ChainState.advance], hpend, hN.J.imp_right liftQ, hF₁⟩
  · exact ⟨hprog, hpend, hN.J.imp_right liftQ, hF₁⟩

private theorem named (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)} {σ : FG.ChainState gp.n}
    (h : gp.chainState c = some σ) : Named gp c σ :=
  gp.chainState_induction (P := fun c σ => Named gp c σ)
    ⟨by simp [FG.ChainState.init], by simp [FG.ChainState.init], Or.inl rfl, Or.inl rfl⟩
    (fun _ _ _ _ hc hN hB => named_step gp hc hN hB) h

/-- In an honest store, `Σ.J` and `Σ.F` are genesis or named by a quorum of attestations that
blocks of the tree carry. -/
theorem cache_quorum {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) :
    ∀ X ∈ ({st.J, st.F} : Set (NodeBlock P ACP)), X.root = P.genesisRoot ∨
      ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧ ∀ v ∈ Q,
        ∃ Z ∈ st.tree, ∃ a ∈ Z.fgPayload, a.val = v ∧ a.T = X.root := by
  obtain ⟨-, -, -, ⟨BJ, hBJ, hJ, -⟩, -, -, BF, hBF, hF⟩ := Store.cache_invariants _ _ _ _ hr
  have key : ∀ B ∈ st.tree, ∀ T, ((st.σ B.root).J = T ∨ (st.σ B.root).F = T) →
      T = P.genesisRoot ∨ ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧ ∀ v ∈ Q,
        ∃ Z ∈ st.tree, ∃ a ∈ Z.fgPayload, a.val = v ∧ a.T = T := by
    intro B hB T hT
    obtain ⟨c, hc, -, -, hcs⟩ := Store.chain_state_of_chain _ _ _ _ hr B hB
    have hN := named P.fg hcs
    have lift : Quorum P.fg (c.map Block.fgView) T → ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧
        ∀ v ∈ Q, ∃ Z ∈ st.tree, ∃ a ∈ Z.fgPayload, a.val = v ∧ a.T = T := by
      rintro ⟨Q, hQ, hv⟩
      refine ⟨Q, hQ, fun v hv' => ?_⟩
      obtain ⟨a, ha, h1, h2⟩ := hv v hv'
      simp only [FG.FGParams.chainAtts, List.mem_flatMap] at ha
      obtain ⟨Z', hZ', ha⟩ := ha
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hZ'
      exact ⟨Z, hc Z hZ, a, ha, h1, h2⟩
    rcases hT with rfl | rfl
    · exact hN.J.imp_right lift
    · exact hN.F.imp_right lift
  rintro X (rfl | rfl)
  · exact key BJ hBJ _ (Or.inl hJ)
  · exact key BF hBF _ (Or.inr hF)

/-- With `f < h_t` at some `t`, a quorum has an honest member (`f < n/2 < q`). -/
private theorem honest_of_quorum {t : Time} (hfb : tr.FaultBound H t) {Q : Finset (Fin sp.n)}
    (hQ : sp.toParams.fg.q ≤ Q.card) : ∃ v ∈ Q, v ∈ H := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hHc : (Q : Set (Fin sp.n)).ncard ≤ Hᶜ.ncard :=
    Set.ncard_le_ncard (fun v hv => hno v hv) (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hHc
  have hH : tr.honestAwakeJoined H t ≤ H.ncard :=
    Set.ncard_le_ncard (fun v hv => hv.1) (Set.toFinite _)
  have hsum : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hq : sp.toParams.fg.q = (2 * sp.n + 2) / 3 := rfl
  unfold RunTrace.FaultBound at hfb
  omega

/-- The record names a held genesis or an actual origin strictly before this cut. -/
theorem record_origin_before (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginBefore tr H C s i) :=
  (good_state hrun hnc hy i).1

/-- The time-bounded form of causal record provenance. -/
theorem record_origin_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {b : Time} (hi : ∀ k < i, tr.time k ≤ b) :
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginWithin tr H C s b) :=
  have ⟨C, hC, hCr, h⟩ := (good_state hrun hnc hy i).1
  ⟨C, hC, hCr, h.imp_right fun ⟨s, hs⟩ => ⟨s, hs.within hi⟩⟩

/-- **The record names genesis or an origin**, a block of the node's tree. -/
theorem record_origin (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, Origin tr H C s) :=
  have ⟨C, hC, hCr, h⟩ := (good_state hrun hnc hy i).1
  ⟨C, hC, hCr, h.imp_right fun ⟨s, hs⟩ => ⟨s, hs.origin⟩⟩

/-- **Every stored lock sits below an origin of its slot** whose event precedes the cut, and names
a block of the node's tree. -/
theorem lock_origin (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state y i).ac.locks, ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧
      ∃ C, OriginBefore tr H C l.slot i ∧ Anc (tr.HonestBlocks H) L C :=
  (good_state hrun hnc hy i).2

/-- **Every FG source at a cut within `b` is on the chain of the origins within `b`**: it is the
block of a live fast lock. -/
theorem source_on_chain_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {b : Time} (hi : ∀ k < i, tr.time k ≤ b)
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.ToFGAt tr.projAC y i ℓ C) : OnOriginChainWithin tr H C b := by
  obtain ⟨hpc, -, hC⟩ := h
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt (ac_run hrun hnc) hy hpc
  rw [projAC_state hrun.toLocalRun hy i] at hC
  obtain ⟨hCv, l, ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩, hlC, -, -⟩ := toFG_candidate hC
  obtain ⟨hvt, hva⟩ := SA.viableAncestor_anc hΦ hB
  obtain rfl : C = ℓ.frame.viableAncestor B := hΦ.coherent.1 hCv.1 hvt hlC.symm
  obtain ⟨L, hL, hLr, C', hC', hLC'⟩ := lock_origin hrun hnc hy i l₀ hl₀
  obtain rfl : B = L := (honest_coherent hrun hnc).1 (hΦU hB) ⟨y, hy, i, hL⟩ (hBr.trans hLr.symm)
  exact onOriginChainWithin_iff.2 (Or.inr ⟨C', _, hC'.within hi, (hva.mono hΦU).trans hLC'⟩)

/-- **Every FG source is on the origin chain**: it is the block of a live fast lock. -/
theorem source_on_chain (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (h : SA.ToFGAt tr.projAC y i ℓ C) :
    OnOriginChain tr H C :=
  have ⟨_, _, hi⟩ := exists_horizon hrun i
  (source_on_chain_upTo hrun hnc hy hi h).onOriginChain

/-- **Every honest attestation signed at a cut within `b` names a block on the chain of the origins
within `b`**: an honest attestation's height pair names the entry of its source's state, an
ancestor of the source. -/
theorem row_on_chain_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {a : FG.Att sp.n} (h : tr.SignAt x k a) {b : Time}
    (hk : ∀ k' < k, tr.time k' ≤ b) :
    ∃ E ∈ tr.HonestBlocks H, E.root = a.T ∧ OnOriginChainWithin tr H E b := by
  obtain ⟨src, hc⟩ := h
  obtain ⟨j, rfl, ℓ, hcj, hcall, -, hsrc, hfg⟩ := attest_source hrun.toLocalRun hx hc
  have hpc : tr.projAC.CallAt x j ℓ := ⟨hcj.1, by simp [RunTrace.projAC, hcj.2, RunTrace.acLabel]⟩
  have hch := source_on_chain_upTo hrun hnc hx (fun k' hk' => hk k' (by omega))
    ⟨hpc, hcall, by rw [projAC_state hrun.toLocalRun hx j]; exact hsrc⟩
  have hsrcT : src ∈ (tr.state x (j + 1)).fg.tree := by
    have h' := (toFG_candidate hsrc).1.1
    rw [(hrun.cutLaw x hx j _ hcj).1] at h'
    rw [hfg]
    exact h'.1
  obtain ⟨⟨E, hE, hEr, hEsrc, -, hETh⟩, -, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (fg_reachable hrun.toLocalRun hx (j + 1)) src hsrcT
  have haT : a.T = E.root := by
    rw [createAtt_T (hrun.cutLaw x hx (j + 1) _ hc).1, ← hEr, hETh, hEr]
  have hsub : (tr.state x (j + 1)).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨x, hx, j + 1, hX⟩
  exact ⟨E, hsub hE, haT.symm,
    OnOriginChainWithin.of_anc hrun hnc (hsub hE) (hEsrc.mono hsub) hch⟩

/-- **Every honest attestation names a block on the origin chain**: an honest attestation's height
pair names the entry of its source's state, an ancestor of the source. -/
theorem row_on_chain (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {x : Fin sp.n}
    (hx : x ∈ H) {k : Nat} {a : FG.Att sp.n} (h : tr.SignAt x k a) :
    ∃ E ∈ tr.HonestBlocks H, E.root = a.T ∧ OnOriginChain tr H E :=
  have ⟨_, _, hk⟩ := exists_horizon hrun k
  have ⟨E, hE, hEr, hEc⟩ := row_on_chain_upTo hrun hnc hx h hk
  ⟨E, hE, hEr, hEc.onOriginChain⟩

/-- **Every honest `Σ.F` and `Σ.J` at a cut within `b` is on the chain of the origins within
`b`**, with `f < h_t` at some `t` (`f < n/2 < q`: a target quorum has an honest attestation). -/
theorem caches_on_chain_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {t : Time} (hfb : tr.FaultBound H t) {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {b : Time}
    (hi : ∀ k < i, tr.time k ≤ b) :
    OnOriginChainWithin tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin tr H (tr.state y i).fg.J b := by
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have hfg := fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc
  have hst : tr.projFG.store y i = (tr.state y i).fg := by
    simp only [FGTrace.store, projFG_state hrun.toLocalRun hy i]
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX⟩
  have hX : ∀ X ∈ ({(tr.state y i).fg.J, (tr.state y i).fg.F} :
      Set (SA.Blk sp.n (List (FG.Att sp.n)))), X ∈ (tr.state y i).fg.tree →
      OnOriginChainWithin tr H X b := by
    intro X hXJF hXt
    rcases cache_quorum (fg_reachable hrun.toLocalRun hy i) X hXJF with hg | ⟨Q, hQ, hQv⟩
    · exact onOriginChainWithin_iff.2 (Or.inl hg)
    obtain ⟨v, hvQ, hvH⟩ := honest_of_quorum hfb hQ
    obtain ⟨Z, hZ, a, ha, rfl, haT⟩ := hQv v hvQ
    -- the block carrying the attestation was accepted by `y` at an earlier cut
    rcases Store.tree_accepted hfg hy (hst ▸ hZ) with rfl | ⟨k, hki, hk⟩
    · simp [Params.genesisBlock] at ha
    obtain ⟨hkn, hkl⟩ := hk
    rw [RunTrace.projFG, Option.bind_eq_some_iff] at hkl
    obtain ⟨c, hc, hcl⟩ := hkl
    cases c with
    | ac ℓ => simp [RunTrace.fgLabel] at hcl
    | fg ℓ =>
      simp only [RunTrace.fgLabel, Option.some.injEq] at hcl
      subst hcl
      obtain ⟨j, hjk, hsign⟩ := hrun.att_unforgeable y hy k a
        (Or.inr ⟨Z, ⟨true, hkn, hc⟩, ha⟩) hvH
      obtain ⟨E, hE, hEr, hEc⟩ :=
        row_on_chain_upTo hrun hnc hvH hsign fun k' hk' => hi k' (by omega)
      obtain rfl : X = E := (honest_coherent hrun hnc).1 (hsub hXt) hE (haT.symm.trans hEr.symm)
      exact hEc
  obtain ⟨hFt, hJt, -⟩ := Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
  exact ⟨hX _ (Or.inr rfl) hFt, hX _ (Or.inl rfl) hJt⟩

/-- **Every honest `Σ.F` and `Σ.J` is on the origin chain**, under `Sleepy` (`f < n/2 < q`: a
target quorum has an honest attestation). -/
theorem caches_on_chain (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {ΔF : Time}
    (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    OnOriginChain tr H (tr.state y i).fg.F ∧ OnOriginChain tr H (tr.state y i).fg.J :=
  have ⟨_, _, hi⟩ := exists_horizon hrun i
  have h := caches_on_chain_upTo hrun hnc (hsl.2 0).1 hy hi
  ⟨h.1.onOriginChain, h.2.onOriginChain⟩

end Consensus.Goldilocks.Compose

end
