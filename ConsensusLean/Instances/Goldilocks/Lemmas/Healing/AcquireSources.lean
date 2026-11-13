module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Drain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: current sources above a protected honest proposal

Shared by HS.4 (`Acquire.ready_sources`) and HS.5 (`ConsumeUpper.fixed_upper_rows_of`): over `Γ`
(`GoldilocksRun`, `HSShared`, `Catch(2Δ)`, `SettledIn … w i₀ m c`), let `Y` be an honest proposal
of slot `s` with `t_s ≥ r` on a protected branch (every honest slot-`s` vote is exactly `Y`, later
votes and proposal parents extend it), in the phase through `v = t_s + 6Δ`. Then every honest node
receives, in `[t_s, v]`, an `ac_to_fg` return `C ⪰ Y` (`protected_sources`).

The proof (proved; HS.2 enters as the hypothesis `CleanLockDrain`): `Y` is allowed in the phase
(`proposal_allowed`: its parent is a viable head of the proposer, read with `Geo`'s aligned
readers). At `y`'s tick at `v` (not a slot start, so its cuts are `ac_on_tick`, then `ac_to_fg`)
`y` holds `Y` (relayed by `t_s + Δ`, `F ⪯ Y` by HS.1), as a viable head (HS.1). Every live lock
there compares with `Y` (`update_locks_compatible`: a clean origin of
a label `< s` by HS.2's transfer to an honest slot-`s` vote, which is `Y`; a label `≥ s` through
an honest counted vote or result supporter of slot `s` or `s + 1`). The AC projection is a healthy
driven trace (`DrainCommon.healthyBase_of_hs`), so H.1's `first_update_post` applies: the tick is
the slot-`s` update, its result is `Y`, not vetoed, and `Y` passes the fast test, so it is the
update's fast selection (`SA.fastSelect_eq_result`) and is locked fast with label `s`. At the
`ac_to_fg` that follows, `Y` is a candidate, and every candidate is below a live lock that
compares with `Y`, so the deepest candidate `C` extends `Y`. Either `C` is returned, or the report
record names a block `R ⪰ C`, written by an earlier `ac_to_fg` return of `R`
(`fgReported_origin`), at a time `≥ t_s` (`R` extends the fresh `Y`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-! ## The report record -/

section Report

variable {FGP : Type} {sp : SAParams}

private theorem admitVote_fgr (A : SA.SAState sp.n) (t : Time) (v : SA.Vote sp.n) :
    (SA.admitVote sp A t v).fgReported = A.fgReported := by
  unfold SA.admitVote
  split_ifs <;> rfl

private theorem ulc_fgr (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (C : SA.Blk sp.n FGP) :
    (SA.updateLatestConfirmed sp A Φ C).fgReported = A.fgReported := by
  unfold SA.updateLatestConfirmed
  split_ifs <;> rfl

private theorem optimistic_fgr (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.optimisticConfirmation sp A Φ t).fgReported = A.fgReported := by
  unfold SA.optimisticConfirmation
  split
  · rfl
  · exact ulc_fgr _ _ _

private theorem update_fgr (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) (s : Nat) :
    (SA.updateConfirmation sp A Φ t s).fgReported = A.fgReported := by
  unfold SA.updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs
    · rfl
    all_goals exact ulc_fgr _ _ _

private theorem tryVote_fgr (self : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) : (SA.tryVote sp self A Φ t).1.fgReported = A.fgReported := by
  unfold SA.tryVote
  dsimp only
  split_ifs <;> first | rfl | exact (optimistic_fgr _ _ _).trans (admitVote_fgr _ _ _)

private theorem blockReceipt_fgr (A : SA.SAState sp.n) (t : Time) (B : SA.Blk sp.n FGP) :
    (SA.blockReceipt sp A t B).fgReported = A.fgReported := by
  unfold SA.blockReceipt
  generalize hA' : ({ A with blockStamp := Function.update A.blockStamp B.root (SA.ETime.of t) } :
    SA.SAState sp.n) = A'
  have : A'.fgReported = A.fgReported := by rw [← hA']
  rw [← this]
  clear hA' this
  induction (SA.blockVotes B) generalizing A' with
  | nil => rfl
  | cons v l ih => rw [List.foldl_cons, ih, admitVote_fgr]

/-- `ac_to_fg` keeps the report record, or sets it to the block it returns. -/
private theorem acToFG_fgr (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.acToFG sp A Φ t).1.fgReported = A.fgReported ∨
      ∃ C, (SA.acToFG sp A Φ t).2 = some C ∧ (SA.acToFG sp A Φ t).1.fgReported = C.root := by
  unfold SA.acToFG
  split_ifs
  · split
    · exact Or.inl rfl
    · split_ifs
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl, rfl⟩
  · exact Or.inl rfl

variable {ro : SA.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)}
  {tr : SA.SATrace sp FGP ro}

/-- **The origin of the report record**: the report record of an honest node names genesis (the
initial record, and a restart's), or the block of an earlier `ac_to_fg` return of the node (its
only writer). -/
theorem fgReported_origin (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) : ∀ i, (tr.state y i).fgReported = sp.genesisRoot ∨
      ∃ k < i, ∃ ℓ C, SA.ToFGAt tr y k ℓ C ∧ C.root = (tr.state y i).fgReported
  | 0 => by
    left
    change (tr.init y).fgReported = _
    rw [hr.init y hy]
    rfl
  | i + 1 => by
    have ih := fgReported_origin hr hy i
    have old : (tr.state y (i + 1)).fgReported = (tr.state y i).fgReported →
        (tr.state y (i + 1)).fgReported = sp.genesisRoot ∨
          ∃ k < i + 1, ∃ ℓ C, SA.ToFGAt tr y k ℓ C ∧
            C.root = (tr.state y (i + 1)).fgReported := fun he => by
      rw [he]
      exact ih.imp_right fun ⟨k, hk, h⟩ => ⟨k, by omega, h⟩
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      have hst : tr.state y (i + 1) = tr.post i := by simp [Trace.state, hc.1, hc.2]
      have hΦ := (SA.frameIn_of_callAt hr hy hc).1
      have he := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      have hpost := congrArg Prod.fst he
      simp only at hpost
      cases hcall : ℓ.call with
      | tick =>
        refine old ?_
        rw [hst, ← hpost, hcall]
        change (SA.acOnTick sp y _ _ _).1.fgReported = _
        unfold SA.acOnTick
        dsimp only
        split_ifs <;> first | rfl | exact (update_fgr _ _ _ _).trans (tryVote_fgr _ _ _ _) |
          exact update_fgr _ _ _ _ | exact tryVote_fgr _ _ _ _
      | message m =>
        refine old ?_
        rw [hst, ← hpost, hcall]
        exact ((tryVote_fgr _ _ _ _).trans (optimistic_fgr _ _ _)).trans (admitVote_fgr _ _ _)
      | block B =>
        refine old ?_
        rw [hst, ← hpost, hcall]
        exact ((tryVote_fgr _ _ _ _).trans (optimistic_fgr _ _ _)).trans (blockReceipt_fgr _ _ _)
      | proposal =>
        refine old ?_
        rw [hst, ← hpost, hcall]
        change (SA.acProposal sp _ _ _).1.fgReported = _
        unfold SA.acProposal
        split_ifs <;> rfl
      | toFG =>
        rw [hst, ← hpost, hcall]
        change (SA.acToFG sp (tr.state y i) ℓ.frame (tr.time i)).1.fgReported = _ ∨
          ∃ k < i + 1, ∃ ℓ₁ C, SA.ToFGAt tr y k ℓ₁ C ∧
            C.root = (SA.acToFG sp (tr.state y i) ℓ.frame (tr.time i)).1.fgReported
        rcases acToFG_fgr (tr.state y i) ℓ.frame (tr.time i) with h | ⟨C, hC, h⟩
        · rw [h]
          exact ih.imp_right fun ⟨k, hk, h'⟩ => ⟨k, by omega, h'⟩
        · exact Or.inr ⟨i, by omega, ℓ, C, ⟨hc, hcall, hC⟩, h.symm⟩
      | restart =>
        left
        rw [hst, ← hpost, hcall]
        change (SA.acRestart sp ro y _ _ _).1.fgReported = _
        exact ((SA.restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ
          (hr.time_nonneg i)).2.2.2.2.1
    · refine old ?_
      rw [Trace.state]
      split_ifs with h
      · exact absurd ⟨_, h.1, (Option.ne_none_iff_exists'.1 h.2).choose_spec⟩ hc
      · rfl

end Report

/-! ## The slot-`s` update -/

section Update

variable {FGP : Type} {sp : SAParams}

/-- **The locks after an unvetoed update with result `Y`**: the live locks of the old locks with
new locks on blocks of `Y`'s path, among them the fast selection, fast. -/
private theorem update_locks {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP} {t : Time} {s : Nat}
    {Y : SA.Blk sp.n FGP} (hΦ : FrameOK Φ) (hconf : SA.getConfirmation sp A Φ s = some Y)
    (hnv : ¬ SA.conflictsWithLock sp A.locks Φ t Y) :
    ∃ N : Set (Nat × Bool × Nat),
      (SA.updateConfirmation sp A Φ t s).locks = SA.addLocks sp A.locks Φ t s N ∧
      (∀ p ∈ N, ∃ B ∈ Φ.tree, B.root = p.1 ∧ Φ.Anc B Y) ∧
      ∀ D, SA.fastSelect sp A Φ s Y = some D → ∃ e, s + 2 ≤ e ∧ (D.root, true, e) ∈ N := by
  have path : ∀ {S : Set (SA.Blk sp.n FGP)} {B}, SA.deepest Φ S = some B →
      S ⊆ SA.confirmationPath sp Φ Y → B ∈ Φ.tree ∧ Φ.Anc B Y := fun hB hS =>
    let h := hS (SA.deepest_mem hB).1
    ⟨h.1, h.2.2⟩
  -- below the unvetoed `Y`, no block is vetoed: the filtered path is the whole path
  have hpath : ∀ P : SA.Blk sp.n FGP → Prop,
      SA.deepest Φ {B | B ∈ {B | B ∈ SA.confirmationPath sp Φ Y ∧
        ¬ SA.conflictsWithLock sp A.locks Φ t B} ∧ P B} =
        SA.deepest Φ {B | B ∈ SA.confirmationPath sp Φ Y ∧ P B} := fun P =>
    congrArg _ (Set.ext fun B => ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun ⟨K, hK, hBK⟩ =>
      hnv ⟨K, hK, fun hc => hBK (hc.elim (fun hc => Or.inl (h.1.2.2.trans hc))
        (fun hc => SA.anc_total hΦ.coherent h.1.2.2 hc))⟩⟩, h.2⟩⟩)
  unfold SA.updateConfirmation
  simp only [hconf, hnv, ↓reduceIte]
  refine ⟨_, by rw [SA.updateLatestConfirmed_keeps_locks], ?_, ?_⟩
  swap
  · intro D hD
    exact ⟨_, SA.le_fastExpiry sp _ _ _ _, Or.inl ⟨D, (hpath _).trans hD, rfl⟩⟩
  rintro p (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
  · exact ⟨B, (path hB fun X hX => hX.1.1).1, rfl, (path hB fun X hX => hX.1.1).2⟩
  · exact ⟨B, (path hB fun X hX => hX.1.1).1, rfl, (path hB fun X hX => hX.1.1).2⟩

end Update

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-! ## Run facts -/

/-- `w + 4Δ ≤ r`: `r = t_{a + 2k + 2}` and `t_a ≥ w + 4Δ` (`slotA_spec`). -/
theorem add_le_rTime (sp : SAParams) (w : Time) : w + 4 * sp.Δ ≤ rTime sp w :=
  (slotA_spec sp w).trans ((SA.ts_le_iff sp).2 (by push_cast; omega))

/-- **The cut after a tick's `ac_on_tick` is its `ac_to_fg`** when the tick is not a proposal
duty (the proposal step makes no cut). -/
private theorem tick_toFG_call {y : Fin sp.n} {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt proposer dg y j t (.tick x)) (hP : ¬ Node.Proposes proposer y t) :
    ∃ ℓ' : ACLabel (goldilocksNode sp ro), tr.CallAt y (j + 1) (.ac ℓ') ∧ ℓ'.call = .toFG ∧
      tr.time (j + 1) = t := by
  have h1 : (Node.exec proposer dg y (tr.state y j) t (.tick x)).2[1]? =
      some (Node.acToFG (Node.tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.1 := by
    change (Node.onTick proposer dg y (tr.state y j) t x).2[1]? = _
    rw [onTick_eq]
    simp only [Node.tickStep, hP, ↓reduceIte]
    split <;> simp [Node.acToFG, Node.acCall]
  obtain ⟨hk', hc⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 1 hk'
  exact ⟨_, ⟨hn, hl.trans (congrArg some hc)⟩, rfl, ht⟩

/-- **An honest proposal of the settled phase is allowed** (the
parent's full walk ends at an allowed head (`proposal_head_viable`); `P` is allowed by
`effAllowed_of_anc`): the proposer reads the effective geometry at
its `ac_proposal` cut (`Geo.viableHeads_iff`; it holds the phase's evidence from `w` on, and the
phase's frontier block is a viable head, HS.1), its walk starts in the viable tree and ends at a
viable head, so an allowed parent, and `P` extends it. -/
theorem proposal_allowed (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hset : SettledIn tr H g w i₀ m c) {p : Fin sp.n}
    (hpH : p ∈ H) {kP s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hprop : tr.ProposesAt p kP P) (hPs : P.slot = s) (hws : w ≤ sp.ts s)
    (hon : PhaseOn tr.projFG H i₀ kP m c) :
    EffAllowed (tr.post kP).fg m c P := by
  have hl := hrun.toLocalRun
  have hnc := hs.noColl
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  obtain ⟨iP, ℓp, d, pay, hcP, hcall, hd, ht, hpar, -⟩ := Compose.proposal_data hrun hpH hprop hPs
  -- the `ac_proposal` cut is the cut before the tick's own block call
  have hiPk : iP + 1 = kP := by
    obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, htk⟩ := hprop
    rcases Compose.blockCall_cases hl hpH hcB with hg | ⟨j, x, rfl, hg, -, -⟩
    · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
    obtain ⟨j₀, rfl, h₀⟩ := proposal_call_tick hl hpH (Compose.projAC_callAt.1 hcP) hcall
    have htt : tr.time (j + 2) = tr.time (j₀ + 1) := by
      rw [htk, ht, hPs, sp.slotTime_eq]; rfl
    have := hl.tick_unique p hpH j₀ j _ h₀ (by rw [← htt]; exact ⟨x, hg⟩)
    omega
  have hiP0 : i₀ ≤ iP := le_of_settledIn hset (by rw [ht]; exact hws)
  have hphP := hon iP hiP0 (by omega)
  have hev : HoldsEvidence (tr.state p iP).fg m c := by
    have := hset.1.evidence i₀ hset.2.1 m c hset.2.2 p hpH
    rw [Compose.store_eq hrun hpH] at this
    exact holdsEvidence_mono hrun hnc hpH hiP0 this
  -- the proposer's `fc_root` has a viable head above it: the phase's frontier block
  have hfr₀ : ℓp.frame = Node.frame (tr.state p iP) := Compose.frame_of_projAC hrun hpH hcP
  have hΦ₀ := (SA.frameIn_of_callAt hr hpH hcP).1
  have hfc₀ : ℓp.frame.fcRoot ∈ ℓp.frame.viableTree ℓp.frame.tree := by
    obtain ⟨Bm, hBm, hBmh⟩ : ∃ B ∈ (tr.state p iP).fg.tree,
        ((tr.state p iP).fg.σ B.root).h = m := by
      cases c with
      | gap => exact hev
      | top J => exact hev.1
      | contest J => exact hev.1
    have hBv : Bm ∈ ℓp.frame.viableHeads := by
      rw [hfr₀]
      exact viableHead_of_allowed hrun hs (fun k' h1 h2 => (le_antisymm h2 h1).symm ▸ hphP) hpH
        (effAllowed_of_height hrun hpH hphP hBm hBmh) hpH le_rfl le_rfl hBm
    exact ⟨hΦ₀.fcRoot_mem, .refl, Bm, hΦ₀.viableHeads_subset hBv, hBv,
      hΦ₀.fcRoot_anc_viableHeads Bm hBv⟩
  -- the parent is a viable head of the proposer, so allowed; `P` extends it
  have hPrv : d.head ∈ ℓp.frame.viableHeads := proposal_head_viable hr hpH hcP hcall (σ := s)
    (by rw [sp.slotTime_eq]; exact ht) hd hfc₀
  rw [hfr₀] at hPrv
  have hPrt : d.head ∈ (tr.state p iP).fg.tree := hPrv.1
  obtain ⟨-, hPrE⟩ := (viableHeads_iff hrun hs hc hpH hphP hev hPrt).1 hPrv
  obtain ⟨-, hPt, hpost⟩ := accept_of_proposesAt hrun hnc hpH hprop
  rw [hpost]
  have hR := Compose.fg_reachable hl hpH (kP + 1)
  obtain ⟨Y, hY, hYr, -⟩ := Store.step_σ hR hPt hpar
  obtain rfl : Y = d.head := hU.1 ⟨p, hpH, kP + 1, hY⟩ ⟨p, hpH, iP, hPrt⟩ hYr
  exact effAllowed_of_anc hR (effAllowed_transfer hrun hnc hpH hpH hPrE hY) hPt
    (Relation.ReflTransGen.single ⟨hY, hPt, hpar⟩)

/-! ## Every live lock at the update compares with `Y` -/

/-- **Every live lock at the slot-`s` update compares with the protected proposal**
(compatibility with every live lock
follows from the same cut induction used for transfer): under `Γ` with HS.2 (`hclean`), let `Y`
be an honest proposal of slot `s` with `t_s ≥ r` on a protected branch, in the phase through
`v = t_s + 6Δ`. At an honest node's tick at `v` (the slot-`s` update), every live lock compares
with `Y`: each current image `L` sits below the stored block `B` of its clean origin (labels
survive normalization and unlocking; every live lock is clean, `t_s ≥ r`); for a label `< s`,
HS.2's origin transfer at an honest slot-`s` vote (which is `Y`) gives `B ⪯ Y`, also through a
root `B ⪯ fc_root ⪯ Y`; label `s` compares through the unanimous batch (raw regular and
optimistic comparison); an origin of label `s + 1` has an honest supporting head extending `Y`
(the later vote extension); no slow lock of label `s + 1` exists yet. -/
theorem update_locks_compatible (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ))
    (hset : SettledIn tr H g w i₀ m c) (hclean : CleanLockDrain) {s kY : Nat}
    {Y : SA.Blk sp.n (List (FG.Att sp.n))} (hY : tr.ProposesAt (proposer s) kY Y)
    (hYs : Y.slot = s) (hpH : proposer s ∈ H) (hr : rTime sp w ≤ sp.ts s)
    (hvotes : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = Y.root ∧
      (Y ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) Y ℓ.frame.fcRoot))
    (hlater : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg Y)
    (hparents : ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
      P'.slot = s' → tr.ProposesAt (proposer s') k' P' →
      proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) Y Pr)
    (hon : ∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hck : tr.projAC.CallAt y k ℓ) (htk : tr.time k = sp.ts s + 6 * sp.Δ) :
    ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k),
      Compatible (tr.HonestBlocks H) L Y := by
  have hnc := hs.noColl
  have hr' := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr'.coherent
  have hS := healthyBase_of_hs hrun hs hc
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hg8 : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hset.1.late
  have hw4 := add_le_rTime sp w
  have hts : gbar g + 12 * sp.Δ ≤ sp.ts s := by linarith
  obtain ⟨-, hYt₀, -⟩ := accept_of_proposesAt hrun hnc hpH hY
  have hYU : Y ∈ tr.HonestBlocks H := ⟨_, hpH, kY + 1, hYt₀⟩
  obtain ⟨jv, hjv⟩ := exists_firstCutAfter_of_healthy hrun hs hy (sp.ts s + 6 * sp.Δ)
  have hphv := hon jv hjv
  have hkjv : k < jv := hjv.lt_of_time_le hrun.time_mono htk.le
  have hts2 : sp.ts ((s + 1 : Nat) : Int) + sp.Δ < sp.ts s + 6 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; linarith only [hΔ]
  -- an honest vote of a slot `≤ s + 1` is cast before `v`, in the phase
  have hvphase : ∀ z ∈ H, ∀ k' ℓ' e, SA.CastAt tr.projAC z k' ℓ' e → e.msg.slot ≤ s + 1 →
      PhaseOn tr.projFG H i₀ k' m c := by
    intro z hz k' ℓ' e hv hsl
    have h1 := cast_time_le_slot hrun hnc hz hv
    have h2 : sp.ts e.msg.slot ≤ sp.ts ((s + 1 : Nat) : Int) := (SA.ts_le_iff sp).2 (by omega)
    exact fun k'' h₁ h₂ => hphv k'' h₁
      (h₂.trans (hjv.lt_of_time_le hrun.time_mono (by linarith only [hts2, h1, h2])).le)
  -- the reader's own slot-`s` vote, which is `Y`
  obtain ⟨iv, ev, ⟨ℓv, hcv, hev⟩, hevs⟩ :=
    SA.honest_votes_in_slot hS (m := s) (by linarith only [hΔ, hts]) y hy
  have hcastv : SA.CastAt tr.projAC y iv ℓv ev := ⟨hcv, hev⟩
  have hhead := (hvotes y hy iv ℓv ev hcastv hevs).1
  have hvph := hvphase y hy iv ℓv ev hcastv (by omega)
  have hΦvU := (SA.frameIn_of_callAt hr' hy hcv).2
  -- an origin that HS.2 transfers to that vote is below `Y` (also through its `fc_root`)
  have below : ∀ B, (¬ Anc (tr.HonestBlocks H) B ℓv.frame.fcRoot →
      SA.VoteExtends (tr.HonestBlocks H) ev.msg B) → Anc (tr.HonestBlocks H) B Y := by
    intro B hB
    by_cases hBf : Anc (tr.HonestBlocks H) B ℓv.frame.fcRoot
    · obtain ⟨⟨Hd, hHd, hHdr, hfH⟩, -⟩ := Compose.cast_head_fcRoot hr' hy hcastv
      obtain rfl : Hd = Y := hU.1 (hΦvU hHd) hYU (hHdr.trans hhead)
      exact hBf.trans (Anc.mono hΦvU hfH)
    · obtain ⟨Hd, hHd, hHdr, hBH⟩ := hB hBf
      obtain rfl : Hd = Y := hU.1 hHd hYU (hHdr.trans hhead)
      exact hBH
  obtain ⟨hfast, hslow, -, -⟩ := hclean sp ro proposer dg H tr g ΔF w i₀ m c hrun hs hc hset
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr' hy hck
  rintro L ⟨hLt, l', ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩, hLr⟩
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : L = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hLt) (hΦU hvat) hLr.symm
  have hclean' := live_lock_clean (hr.trans (by
      rw [htk]; linarith only [hΔ])) (SA.locksWF_state hr' hy k)
    ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩
  dsimp only at hclean'
  -- the image is below the stored block `O` of an origin that compares with `Y`
  have down : ∀ O, (∃ L₁ ∈ tr.HonestBlocks H, L₁.root = l₀.block ∧
      Anc (tr.HonestBlocks H) L₁ O) → Compatible (tr.HonestBlocks H) O Y →
      Compatible (tr.HonestBlocks H) (ℓ.frame.viableAncestor B₀) Y := by
    rintro O ⟨L₁, hL₁, hL₁r, hL₁O⟩ h
    obtain rfl : L₁ = B₀ := hU.1 hL₁ (hΦU hB₀) (hL₁r.trans hB₀r.symm)
    have hLO := (Anc.mono hΦU hva).trans hL₁O
    rcases h with h | h
    · exact Or.inl (hLO.trans h)
    · exact SA.anc_total hU hLO h
  have hrt : ∀ r < k, tr.time r ≤ sp.ts s + 6 * sp.Δ := fun r hr => htk ▸ hrun.time_mono hr.le
  by_cases hjs : l₀.slot < s
  · -- an older clean origin: HS.2's transfer to the slot-`s` vote
    cases hf : l₀.fast
    · obtain ⟨r, hrk, ℓw, D, hcw, hsl, hLO⟩ := SA.slow_lock_provenance_stored hr' hy k l₀ hl₀ hf
      have hO : StoredSlowLockAt tr y r l₀.slot (ℓw.frame.viableAncestor D) :=
        ⟨ℓw, D, hcw, hsl, rfl⟩
      have h := (hslow y hy r l₀.slot _ hO (hclean'.2 hf) y hy iv ℓv ev hcastv
        (hevs ▸ hjs) hvph).1
      exact down _ hLO (Or.inl (below _ fun _ => h.1))
    · obtain ⟨r, hrk, CV, ℓw, D, hcw, hfl, hLO⟩ := stored_fast_lock_provenance hr' hy k l₀ hl₀ hf
      have hO : Compose.StoredFastLockAt tr y r l₀.slot (ℓw.frame.viableAncestor D) CV :=
        ⟨ℓw, D, hcw, hfl, rfl⟩
      have h := (hfast y hy r l₀.slot _ CV hO (hclean'.1 hf) y hy iv ℓv ev
        hcastv (hevs ▸ hjs) hvph).1
      exact down _ hLO (Or.inl (below _ fun _ => h.1))
  push Not at hjs
  cases hf : l₀.fast
  · -- a slow origin of a label `≥ s` is the slot-`s` update (no later update yet), whose result
    -- an honest slot-`s` vote, so `Y`, extends
    obtain ⟨r, hrk, ℓw, D, hcw, ⟨ℓu, C, hupd, hC, hD⟩, hLO⟩ :=
      SA.slow_lock_provenance_stored hr' hy k l₀ hl₀ hf
    obtain rfl : ℓw = ℓu := Option.some.inj (hcw.2.symm.trans hupd.1.2)
    have htr := hrt r hrk
    have ht₁ : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := hupd.2.2.1
    rw [ht₁] at htr
    have hjs' : l₀.slot = s := by
      have := (SA.ts_le_iff sp).1 (show sp.ts (l₀.slot : Int) ≤ sp.ts s by linarith only [htr])
      omega
    have hΦwU := (SA.frameIn_of_callAt hr' hy hcw).2
    obtain ⟨z, hz, j', e, ⟨ℓe, hce, hee⟩, hes, Hd, hHd, hHdr, hCHd⟩ :=
      SA.result_extended hS (by rw [hjs']; linarith only [hΔ, hts]) hy hupd.1
        (by rw [hupd.2.2.1]; linarith only [hΔ]) hC
    obtain rfl : Hd = Y :=
      hU.1 hHd hYU (hHdr.trans (hvotes z hz j' ℓe e ⟨hce, hee⟩ (hes.trans hjs')).1)
    have hDC : ℓw.frame.Anc D C := (SA.deepest_mem hD).1.1.2.2
    exact down _ hLO (Or.inl ((Anc.mono hΦwU ((SA.anc_viableAncestor ℓw.frame D).trans hDC)).trans
      hCHd))
  · -- a fast origin of a label `≥ s`: an honest counted vote of its label, `s` or `s + 1`
    obtain ⟨r, hrk, CV, ℓw, D, hcw, hfl, hLO⟩ := stored_fast_lock_provenance hr' hy k l₀ hl₀ hf
    have hΦwU := (SA.frameIn_of_callAt hr' hy hcw).2
    have hwt : sp.ts l₀.slot ≤ tr.time r := by
      rcases hfl with ⟨ℓ₁, C, ⟨-, -, ht₁, -⟩, -⟩ | ⟨ℓ₁, A, -, hsl₁, -⟩
      · have ht₁' : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := ht₁
        rw [ht₁']; linarith only [hΔ]
      · exact (SA.ts_le_iff_le_slot sp (hr'.time_nonneg r) _).2 (by rw [hsl₁])
    have hj2 : l₀.slot ≤ s + 1 := by
      have := hrt r hrk
      have h' : sp.ts (l₀.slot : Int) < sp.ts ((s + 2 : Nat) : Int) := by
        simp only [SAParams.ts] at hwt this ⊢; push_cast at hwt this ⊢; linarith only [hΔ, hwt,
            this]
      have := (SA.ts_lt_iff sp).1 h'
      omega
    obtain ⟨z, hz, j', e, ⟨ℓe, hce, hee⟩, hes, Hd, hHd, hHdr, hDHd⟩ :=
      SA.fastLock_honest_vote hS.run hS.two_faulty_lt hy hfl hs.stock
    have hcz : SA.CastAt tr.projAC z j' ℓe e := ⟨hce, hee⟩
    have hDY : Compatible (tr.HonestBlocks H) D Y := by
      rcases Nat.lt_or_ge l₀.slot (s + 1) with h | h
      · obtain rfl : Hd = Y :=
          hU.1 hHd hYU (hHdr.trans (hvotes z hz j' ℓe e hcz (by omega)).1)
        exact Or.inl hDHd
      · obtain ⟨Hd', hHd', hHd'r, hYHd'⟩ :=
          hlater z hz j' ℓe e hcz (by omega) (hvphase z hz j' ℓe e hcz (by omega))
        obtain rfl : Hd' = Hd := hU.1 hHd' hHd (hHd'r.trans hHdr.symm)
        exact SA.anc_total hU hDHd hYHd'
    rcases hDY with h | h
    · exact down _ hLO (Or.inl ((Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)).trans h))
    · exact down _ hLO (SA.anc_total hU (Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)) h)

/-! ## The sources -/

/-- **Every honest node receives a current source above a protected honest proposal**: under `Γ`
with HS.2 (`hclean`), for an honest proposal `Y` of slot `s` with `t_s ≥ r` on a protected branch,
in the phase through `v = t_s + 6Δ`, every honest `y` has an `ac_to_fg` return `C ⪰ Y` in
`[t_s, v]`: at its tick at `v`, the slot-`s` update has result and fast selection `Y`, not vetoed
(`first_update_post`, `update_locks_compatible`), so `Y` is a candidate of the following
`ac_to_fg`, whose deepest candidate `C` extends `Y`; `C` is returned, or the report record names a
block `R ⪰ C` that an earlier `ac_to_fg` returned (`fgReported_origin`), at a time `≥ t_s`. -/
theorem protected_sources (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ))
    (hset : SettledIn tr H g w i₀ m c) (hclean : CleanLockDrain) {s kY : Nat}
    {Y : SA.Blk sp.n (List (FG.Att sp.n))} (hY : tr.ProposesAt (proposer s) kY Y)
    (hYs : Y.slot = s) (hpH : proposer s ∈ H) (hr : rTime sp w ≤ sp.ts s)
    (hvotes : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = Y.root ∧
      (Y ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) Y ℓ.frame.fcRoot))
    (hlater : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg Y)
    (hparents : ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
      P'.slot = s' → tr.ProposesAt (proposer s') k' P' →
      proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) Y Pr)
    (hon : ∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) :
    ∀ y ∈ H, ∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
      tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) Y C := by
  classical
  intro y hy
  have hl := hrun.toLocalRun
  have hnc := hs.noColl
  have hacr := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr' := hacr.localRun
  have hU := Compose.honest_blocks_coherent hl hnc
  have hS := healthyBase_of_hs hrun hs hc
  -- time
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hg8 : gbar g + 8 * sp.Δ ≤ w := (le_max_right _ _).trans hset.1.late
  have hgb0 := gbar_nonneg g
  have hw4 := add_le_rTime sp w
  have hts : gbar g + 12 * sp.Δ ≤ sp.ts s := by linarith
  have hts1 : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hslot : sp.slot (sp.ts s + 6 * sp.Δ) = s + 1 :=
    SA.slot_of_mem sp (s + 1) (by rw [hts1]; linarith only [hΔ])
      (by simp only [SAParams.ts] at hts1 ⊢; push_cast at hts1 ⊢; linarith only [hΔ])
  have hs1 : 1 ≤ s := by
    by_contra h0
    obtain rfl : s = 0 := by omega
    have : sp.ts ((0 : Nat) : Int) = 0 := by simp [SAParams.ts]
    linarith only [hΔ, hgb0, hts, this]
  -- the proposal and its allowedness
  obtain ⟨hacc, hYt₀, hpost⟩ := accept_of_proposesAt hrun hnc hpH hY
  have hkY : tr.time kY = sp.ts s := by rw [hY.2.2, hYs, sp.slotTime_eq]; rfl
  have hi₀kY : i₀ ≤ kY := le_of_settledIn hset (by rw [hkY]; linarith)
  obtain ⟨jv, hjv⟩ := exists_firstCutAfter_of_healthy hrun hs hy (sp.ts s + 6 * sp.Δ)
  have hphv := hon jv hjv
  have hkYjv : kY < jv := hjv.lt_of_time_le hrun.time_mono (by rw [hkY]; linarith only [hΔ])
  have hall := proposal_allowed hrun hs hc hset hpH hY hYs (by linarith)
    (fun k' h1 h2 => hphv k' h1 (h2.trans hkYjv.le))
  rw [hpost] at hall
  -- `y`'s tick at `v`, not a proposal duty: `ac_on_tick`, then `ac_to_fg`
  obtain ⟨j, x, hg⟩ := hrun.tick_of_awake y hy (sp.ts s + 6 * sp.Δ) (by
      linarith only [hΔ, hts, hgb0])
    ⟨4 * (s : Int) + 6, by simp only [SAParams.ts]; ring⟩
    (hs.healthy.2.1 y hy _ (by change gbar g ≤ _; linarith only [hΔ, hts]))
  have hnP : ¬ Node.Proposes proposer y (sp.ts s + 6 * sp.Δ) := by
    rintro ⟨-, h, -⟩
    rw [show sp.toParams.slotOf (sp.ts s + 6 * sp.Δ) = s + 1 from hslot, sp.slotTime_eq] at h
    simp only [SAParams.ts] at hts1 h
    push_cast at hts1 h
    linarith only [hΔ, h]
  obtain ⟨hcj, htj⟩ := tick_first_cut hg
  obtain ⟨ℓ', hcj1, hcall', htj1⟩ := tick_toFG_call hg hnP
  obtain ⟨ℓ, hcjAC, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.projAC.CallAt y j ℓ ∧ ℓ.call = .tick := ⟨_, Compose.projAC_callAt.2 hcj, rfl⟩
  have hcj1AC : tr.projAC.CallAt y (j + 1) ℓ' := Compose.projAC_callAt.2 hcj1
  have hjjv : j + 1 < jv := hjv.lt_of_time_le hrun.time_mono (by rw [htj1])
  have hi₀j : i₀ ≤ j := le_of_settledIn hset (by rw [htj]; linarith)
  have hkYj : kY < j := by
    by_contra h
    have := hrun.time_mono (not_lt.1 h)
    linarith only [hΔ, hkY, htj, this]
  have hwin : PhaseOn tr.projFG H (kY + 1) (j + 1) m c :=
    fun k' h1 h2 => hphv k' (by omega) (by omega)
  -- `y` holds `Y` at its tick: relayed by `t_s + Δ`, `F ⪯ Y` by HS.1
  have hYj : Y ∈ (tr.state y j).fg.tree := by
    have hex : ∃ k', sp.ts s + 6 * sp.Δ ≤ tr.time k' := ⟨j, htj.ge⟩
    have hjw : tr.FirstCutFrom (Nat.find hex) (sp.ts s + 6 * sp.Δ) :=
      ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
    have hjwj : Nat.find hex ≤ j := Nat.find_min' hex htj.ge
    have hkYw : kY + 1 ≤ Nat.find hex := by
      by_contra h
      have := hrun.time_mono (show Nat.find hex ≤ kY by omega)
      linarith only [hjw.1, hΔ, hkY, this]
    have hF := finalized_anc_of_allowed hrun hs (fun k' h1 h2 => hwin k' h1 (h2.trans (by omega)))
      hpH hall hy hkYw le_rfl
    exact Compose.tree_mono hl hy hjwj (relay_held hl hs.healthy hs.noRestart hc hpH hy hacc
      (by linarith only [hΔ, hts]) (by rw [hkY]; linarith only [hΔ]) hjw hF)
  -- `Y` is a viable head of `y`'s frame at the tick
  have hfr : ℓ.frame = Node.frame (tr.state y j) := Compose.frame_of_projAC hrun hy hcjAC
  have hΦ : FrameOK ℓ.frame := (SA.frameIn_of_callAt hr' hy hcjAC).1
  have hΦU : ℓ.frame.tree ⊆ tr.HonestBlocks H := (SA.frameIn_of_callAt hr' hy hcjAC).2
  have hYv : Y ∈ ℓ.frame.viableHeads := by
    rw [hfr]
    exact viableHead_of_allowed hrun hs hwin hpH hall hy (by omega) (by omega) hYj
  have hYt : Y ∈ ℓ.frame.tree := hΦ.viableHeads_subset hYv
  have hYvt : Y ∈ ℓ.frame.viableTree ℓ.frame.tree :=
    ⟨hYt, hΦ.fcRoot_anc_viableHeads Y hYv, Y, hYt, hYv, .refl⟩
  have hYg : Y.root ≠ sp.genesisRoot := by
    intro hg0
    have hG := Store.genesis_mem (Compose.fg_reachable hl hy j)
    obtain rfl := hU.1 ⟨y, hy, j, hYj⟩ ⟨y, hy, j, hG⟩ hg0
    simp [Params.genesisBlock] at hYs
    omega
  -- the slot-`s` update: result and fast selection `Y`, not vetoed
  have hexact : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      e.msg.head = Y.root := fun x hx j e ⟨ℓ, hc, he⟩ hes => (hvotes x hx j ℓ e ⟨hc, he⟩ hes).1
  have htjAC : tr.projAC.time j = sp.ts s + 6 * sp.Δ := htj
  obtain ⟨hconf, hnv, hfast, hpostj⟩ := SA.first_update_post hS (by
      linarith only [hΔ, hts]) hexact hy hcjAC
    hcall htjAC hYt (update_locks_compatible hrun hs hc hset hclean hY hYs hpH hr hvotes
      hlater hparents hon hy hcjAC htj)
  set A := tr.projAC.state y j with hA
  set t := sp.ts s + 6 * sp.Δ with ht
  have hlocks := update_locks_compatible hrun hs hc hset hclean hY hYs hpH hr hvotes hlater
    hparents hon hy hcjAC htj
  obtain ⟨N, hN, hNY, hND⟩ := update_locks hΦ hconf hnv
  obtain ⟨eY, heY, hD⟩ := hND Y (SA.fastSelect_eq_result hΦ hYt hYg hfast)
  -- the `ac_to_fg` cut: same frame, same time, the state the update left
  have hst1 : tr.projAC.state y (j + 1) = tr.projAC.post j := by
    simp [Trace.state, hcjAC.1, hcjAC.2]
  have hfr' : ℓ'.frame = ℓ.frame := by
    rw [(hrun.cutLaw y hy (j + 1) _ hcj1).1, hfr, tr.state_succ_of_call hcj]
    unfold Node.frame
    rw [(hrun.cutLaw y hy j _ hcj).2.2.1]
  have htj1AC : tr.projAC.time (j + 1) = t := htj1
  have hpostl : (tr.projAC.state y (j + 1)).locks = SA.addLocks sp A.locks ℓ.frame t s N := by
    rw [hst1, hpostj, hN, htjAC]
  have hjoin : SA.joined sp (tr.projAC.state y (j + 1)) t := by
    have := hS.joined_state hy (j + 1) (by
      rw [htj1AC, hslot]; push_cast; simp only [add_sub_cancel_right]
      linarith only [hts, hΔ])
    rwa [htj1AC] at this
  -- every live lock at the `ac_to_fg` compares with `Y`, and `Y` is a fast candidate
  have hlv2 : sp.slot t ≤ s + 2 := by rw [hslot]; omega
  have hlv : sp.slot t ≤ eY := hlv2.trans heY
  have hlive : ∀ B ∈ SA.liveLockBlocks sp (tr.projAC.state y (j + 1)).locks ℓ.frame t,
      Compatible (tr.HonestBlocks H) B Y := by
    rintro B ⟨hB, l, ⟨l₁, hl₁, B₁, hB₁, hB₁r, -, rfl⟩, hlB⟩
    rw [hpostl] at hl₁
    obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, hl₀t, rfl⟩ := hl₁
    obtain ⟨hvat₀, hva₀⟩ := SA.viableAncestor_anc hΦ hB₀
    obtain rfl : B₁ = ℓ.frame.viableAncestor B₀ := hΦ.coherent.1 hB₁ hvat₀ hB₁r
    obtain ⟨-, hva₁⟩ := SA.viableAncestor_anc hΦ hB₁
    obtain rfl : B = ℓ.frame.viableAncestor (ℓ.frame.viableAncestor B₀) :=
      hΦ.coherent.1 hB (SA.viableAncestor_anc hΦ hB₁).1 hlB.symm
    have hBB₀ := hva₁.trans hva₀
    rcases hl₀ with hl₀ | ⟨q, hq, rfl⟩
    · have hcomp := hlocks _ ⟨hvat₀, ⟨(ℓ.frame.viableAncestor B₀).root, l₀.slot, l₀.fast,
        l₀.expiry⟩,
        ⟨l₀, hl₀, B₀, hB₀, hB₀r, by rw [htj]; exact hl₀t, rfl⟩, rfl⟩
      rcases hcomp with h | h
      · exact Or.inl ((Anc.mono hΦU hva₁).trans h)
      · exact (SA.anc_total hU h (Anc.mono hΦU hva₁)).symm
    · obtain ⟨Bq, hBq, hBqr, hBqY⟩ := hNY q hq
      obtain rfl : B₀ = Bq := hΦ.coherent.1 hB₀ hBq (hB₀r.trans hBqr.symm)
      exact Or.inl (Anc.mono hΦU (hBB₀.trans hBqY))
  have hYc : Y ∈ SA.toFGCandidates sp (tr.projAC.state y (j + 1)) ℓ.frame t := by
    refine ⟨hYvt, ⟨Y.root, s, true, eY⟩, ⟨⟨Y.root, s, true, eY⟩, ?_, Y, hYt, rfl, ?_, ?_⟩, rfl,
      rfl, ?_⟩
    · rw [hpostl]
      exact ⟨⟨Y.root, s, true, eY⟩, Or.inr ⟨_, hD, rfl⟩, Y, hYt, rfl, hlv,
        by rw [SA.viableAncestor_self hΦ hYt (Or.inl hYvt)]⟩
    · exact hlv
    · rw [SA.viableAncestor_self hΦ hYt (Or.inl hYvt)]
    · exact hlv2
  -- the deepest candidate extends `Y`
  have hcs : SA.toFGCandidates sp (tr.projAC.state y (j + 1)) ℓ.frame t ⊆ ℓ.frame.tree :=
    fun B hB => hB.1.1
  obtain ⟨C, hC⟩ := SA.exists_deepest hΦ hcs ⟨Y, hYc⟩
  obtain ⟨hCc, hCmax⟩ := SA.deepest_mem hC
  have hYC : ℓ.frame.Anc Y C := by
    obtain ⟨hCv, l, hl, hlC, -⟩ := hCc
    rcases hlive C ⟨hCv.1, l, hl, hlC⟩ with h | h
    · by_cases he : Y = C
      · exact he ▸ .refl
      · have h' := SA.anc_tree_of_anc_U hU hΦ hΦU hCv.1 h hYt
        by_cases he' : C = Y
        · exact absurd he'.symm he
        rcases hCmax Y hYc he with h2 | ⟨h2, -⟩ <;>
          have := SA.depth_lt_of_anc hΦ h' he' hYt <;> omega
    · exact SA.anc_tree_of_anc_U hU hΦ hΦU hYt h hCv.1
  have hYCU : Anc (tr.HonestBlocks H) Y C := hYC.mono hΦU
  -- returned, or suppressed by an earlier return
  by_cases hrep : SA.AncR ℓ.frame C (tr.projAC.state y (j + 1)).fgReported
  · obtain ⟨R, hRt, hRr, hCR⟩ := hrep
    have hYR : Anc (tr.HonestBlocks H) Y R := hYCU.trans (hCR.mono hΦU)
    rcases fgReported_origin hr' hy (j + 1) with hgen | ⟨k', hk', ℓ'', R', hto, hR'r⟩
    · have hG := Store.genesis_mem (Compose.fg_reachable hl hy j)
      have hRG := hU.1 (hΦU hRt) ⟨y, hy, j, hG⟩ (hRr.trans hgen)
      subst hRG
      have := slot_le_of_anc hU hYR
      simp [Params.genesisBlock] at this
      omega
    have hR't := toFG_mem_tree hrun hy hto
    obtain rfl : R' = R := hU.1 ⟨y, hy, k', hR't⟩ (hΦU hRt) (hR'r.trans hRr.symm)
    have hYk' := mem_of_honest_anc hrun hnc hy hYR hR't
    have hk't : tr.time k' ≤ t := by
      rw [← htj1]; exact hrun.time_mono (by omega)
    refine ⟨k', ℓ'', R', hto, ?_, hk't, hYR⟩
    -- `R ⪰ Y` was returned after `Y` was accepted, at `t_s` or later
    rcases Compose.tree_cases hl hy hYk' with hg0 | ⟨a, ha, hacc'⟩
    · exact absurd (by rw [hg0]; rfl) hYg
    have hlaw := (hrun.cutLaw y hy a _ hacc').1
    have hsl : s ≤ sp.slot (tr.time a) := hYs ▸ hlaw
    have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg a) s).2 (by exact_mod_cast hsl)
    exact this.trans (hrun.time_mono ha.le)
  · refine ⟨j + 1, ℓ', C, ⟨hcj1AC, hcall', ?_⟩, by rw [htj1]; linarith only [hΔ], by
      rw [htj1], hYCU⟩
    rw [hfr', htj1AC]
    unfold SA.acToFG
    simp only [hjoin, not_true_eq_false, ↓reduceIte, hC, hrep]

end Consensus.Goldilocks.Healing

end
