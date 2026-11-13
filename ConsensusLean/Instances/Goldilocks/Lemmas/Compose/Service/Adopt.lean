module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Held
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Confirmation
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: an honest proposal is adopted by the update of its slot

A1.7's supplier over the Sleepy invariant: every honest slot-`s` vote is the honest proposal `P` of
slot `s`; at an honest node's joined update of slot `s`, the result is exactly `P` and not vetoed
(`adopt_result_before`: the S1P–S3P bootstrap with the Sleepy step lemmas for a protected block,
`vote_frame`, `later_transfer_step_before`, `vote_locks_compatible_upTo`, `held_origin_viable`). The
update then moves the record to `P`, or keeps an already deeper one (`update_adopts`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

/-- **`P` is in the updater's tree, above its `Σ.F`**: `Σ.F ⪯ P`
(`updater_F_anc_proposal_before`), so the acceptance relay brings `P`, accepted by its proposer at
`t_s`, to the updater, joined (restarts at or before `t_s`), before `t_s + Δ ≤ t_s + 6Δ`
(`relay_mem_before`). -/
theorem proposal_held_at_update_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    P ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F P := by
  have h := hrun.toLocalRun
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hu.1
  -- the frame of the update is the node's frame
  have hfr : ℓ.frame = Node.frame (tr.state y k₀) := by
    obtain ⟨hn, hl⟩ := hu.1
    obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
    obtain rfl : c = .ac ℓ := by
      cases c with
      | ac ℓ' => cases hcl; rfl
      | fg _ => cases hcl
    exact (hrun.cutLaw y hy k₀ (.ac ℓ) ⟨hn, hc⟩).1
  have hF : Anc (tr.HonestBlocks H) ℓ.frame.F P := by
    rw [hfr]
    exact updater_F_anc_proposal_before hrun hnc hb0 hsync hfb hinv hp hP hPs hpj hy hu hb
  -- `P` is accepted by its proposer at `t_s`, and the AC cut of that block follows
  have hacc := proposal_accepted hrun hnc hp hP
  have hPU : P ∈ tr.HonestBlocks H := by
    refine ⟨p, hp, k + 1, ?_⟩
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (fg_reachable h hp _)).1 P _ (h.cutLaw p hp _ _ hacc).2.1]
    exact Set.mem_insert _ _
  obtain ⟨ℓ', hc', hcall', ht'⟩ := accept_next h hp hacc
  have htk : tr.time k = sp.ts s := by
    rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  -- the updater's restarts are at or before `t_s` (joined at `t_s + 6Δ`)
  have hrs : ∀ c ≤ k₀, tr.projAC.RestartAt y c → tr.projAC.time c ≤ sp.ts s := by
    obtain ⟨hc, hcall, ht, hj⟩ := hu
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hts₂ : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have he := hr.exec k₀ ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    have hpost : SA.joined sp (tr.projAC.post k₀) (tr.projAC.time k₀) := by
      have hp' : tr.projAC.post k₀ = ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y
          (tr.projAC.state y k₀) ℓ.frame (tr.projAC.time k₀) ℓ.call).1 := by rw [he]
      unfold SA.joined at hj ⊢
      rw [hp', SA.step_restartTime y _ _ _ _ (by rw [hcall]; simp)]
      exact hj
    have hsl : sp.slot (tr.projAC.time k₀) = s + 1 :=
      SA.slot_of_mem sp (s + 1) (by rw [ht, hts]; linarith) (by rw [ht, hts₂]; linarith)
    intro c hck hrc
    have := ((SA.joined_awake sp) _ ro H _ tr.projAC hr y hy k₀ ℓ hc hpost).2 c hck hrc
    rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this
  have hPt : P ∈ ℓ.frame.tree := by
    refine relay_mem_before hrun hnc hsync.ac
      hp hy hPU hu.1 hb hrs (Or.inr ⟨k + 1,
      ⟨ℓ', projAC_callAt.2 hc', hcall'⟩, ?_⟩) hF
    have htk₀ : tr.projAC.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have : tr.projAC.time (k + 1) = sp.ts s := ht'.trans htk
    rw [htk₀, this, max_self]
    linarith
  exact ⟨hPt, SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.rooted.1 hF hPt⟩

/-- **`P` has a strict majority at the update's test**: every honest slot-`s`
vote is `P` (`honest_votes_eq_proposal_before`) and reaches the updater resolved
(`honest_batch_at_update_before`); an honest validator has one slot-`s` vote in the pool
(unforgeability, A0.8), so the honest slot-`s` voters support `P`; the other voters are faulty, and
they are fewer (the fault bound). -/
theorem proposal_majority_at_update_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    (SA.voters {v | v ∈ (tr.state y k₀).ac.pool s}).ncard <
      2 * SA.confirmationScore sp (tr.state y k₀).ac ℓ.frame s P := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hPt := (proposal_held_at_update_before hrun hnc hb0 hsync hfb hinv
    hp hP hPs hpj hy hu hb).1
  have hall := honest_votes_eq_proposal_at_update_before hrun hnc hb0 hsync hfb hinv
    hp hP hPs hpj (hu.2.2.1 ▸ hb)
  have hbatch := honest_batch_at_update_before hrun hnc
    hsync.ac hy hu hb hPt hall
  rw [← projAC_state hrun.toLocalRun hy]
  set A := tr.projAC.state y k₀
  set Hv := {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = s}
  have hcount : Hᶜ.ncard < Hv.ncard := by
    have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    refine lt_of_lt_of_le (hfb s sp.Δ (by simp)
      (by linarith [sp.toParams.hΔ])) (Set.ncard_le_ncard ?_)
    rintro x ⟨hx, hw, hj⟩
    obtain ⟨j, e, hv, hes, -⟩ :=
      vote_of_awake_joined hrun hnc hx (mayVote_stock hrun hnc hx _) hw hj
    exact ⟨hx, j, e, hv, hes⟩
  -- an honest validator's slot-`s` pool votes are its one slot-`s` vote
  have hone : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      ∀ v ∈ A.pool s, v.val = x → v = e.msg := by
    intro x hx j e hv hs v hvp hvx
    obtain ⟨j', -, e', hv', rfl⟩ := hrun'.honest.pool_vote y hy k₀ s v hvp (hvx ▸ hx)
    have hs' := SA.state_pool_slot sp hr hy k₀ s _ hvp
    rw [hvx] at hv'
    exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
      (SA.one_vote_per_slot sp _ ro H _ _ hr x hx j' j e' e hv' hv (hs'.trans hs.symm)).2
  have hsupp : Hv ⊆ SA.supporters ℓ.frame ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
      SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s P := by
    rintro x ⟨hx, j, e, hv, hs⟩
    obtain ⟨hvp, hres⟩ := hbatch x hx j e hv hs
    obtain ⟨ℓx, hcx, hex⟩ := hv
    have hval := (SA.castAt_spec hr hx ⟨hcx, hex⟩).1
    refine ⟨?_, e.msg, ⟨hvp, hres⟩, hval, by exact_mod_cast hs, P, hPt,
      (hall x hx j e ⟨ℓx, hcx, hex⟩ hs).symm, Relation.ReflTransGen.refl⟩
    rintro ⟨v, hv, v', hv', hne, hvx, hv'x⟩
    exact hne ((hone x hx j e ⟨ℓx, hcx, hex⟩ hs v hv hvx).trans
      (hone x hx j e ⟨ℓx, hcx, hex⟩ hs v' hv' hv'x).symm)
  have hvot : SA.voters {v | v ∈ A.pool s} ⊆ Hv ∪ Hᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e, he, rfl⟩ := hrun'.honest.pool_vote y hy k₀ s _ hv hw
      exact Or.inl ⟨hw, j, e, he, SA.state_pool_slot sp hr hy k₀ s _ hv⟩
    · exact Or.inr hw
  have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
  have h2 := Set.ncard_union_le Hv Hᶜ
  have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
  change _ < 2 * (SA.supporters ℓ.frame _ s P).ncard
  omega

/-- **No result of an honest joined update is vetoed** under `Sleepy`: a live lock
block is an ancestor of a stored lock block, which is on the origin chain (S1); the result is an
origin; blocks on the origin chain are compatible (S1), so the result is compatible with the live
lock block. -/
theorem result_not_vetoed_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {b : Time}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hinv : SleepyInvariantUpTo tr H b) {y : Fin sp.n} (hy : y ∈ H) {k₀ s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k₀ s ℓ)
    (hb : tr.time k₀ ≤ b)
    {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some C) :
    ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) C := by
  have hcoh := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hfr : ℓ.frame = Node.frame (tr.state y k₀) := by
    obtain ⟨⟨hn, hl⟩, -⟩ := hu
    obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
    obtain rfl : c = .ac ℓ := by
      cases c with
      | ac ℓ' => cases hcl; rfl
      | fg _ => cases hcl
    exact (hrun.cutLaw y hy k₀ (.ac ℓ) ⟨hn, hc⟩).1
  have hΦ : FrameOK ℓ.frame := hfr ▸ frameOK_state hrun.toLocalRun hy k₀
  have hHB : ℓ.frame.tree ⊆ tr.HonestBlocks H := fun X hX =>
    ⟨y, hy, k₀, by rw [hfr] at hX; exact hX.1⟩
  have hCt : C ∈ ℓ.frame.tree := (SA.deepest_mem hC).1.1
  have hCo : OriginWithin tr H C s b := originWithin_iff.2
    ⟨y, hy, k₀, _, hb, Or.inl ⟨ℓ, hu,
      by rw [projAC_state hrun.toLocalRun hy]; exact hC, rfl⟩⟩
  rintro ⟨V, hV, hconf⟩
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hV
  obtain ⟨L, hL, hLr, hch⟩ := hinv.locks y hy k₀
    (fun k hk => (hrun.time_mono hk.le).trans hb) l hl
  obtain rfl : L = B₀ := hcoh.1 ⟨y, hy, k₀, hL⟩ (hHB hB₀) (hLr.trans hB₀r.symm)
  have hcomp := OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible
    (hHB hCt) (hHB hB₀)
    (onOriginChainWithin_iff.2 (Or.inr ⟨C, s, hCo, Relation.ReflTransGen.refl⟩)) hch
  obtain ⟨hVt, hVB⟩ := SA.viableAncestor_anc hΦ hB₀
  have hVB' := hVB.mono hHB
  have hCV : Compatible (tr.HonestBlocks H) C (ℓ.frame.viableAncestor L) := by
    rcases hcomp with h | h
    · exact SA.anc_total hcoh h hVB'
    · exact Or.inr (hVB'.trans h)
  apply hconf
  rcases hCV with h | h
  · exact Or.inl (SA.anc_tree_of_anc_U hcoh hΦ hHB hCt h hVt)
  · exact Or.inr (SA.anc_tree_of_anc_U hcoh hΦ hHB hVt h hCt)

/-- **The update of slot `s` returns exactly the honest proposal `P` of slot `s`, not vetoed**:
`P` is held above `Σ.F` with a strict majority, every block with a strict
majority is on one chain with it (A0.3), and no block above it has a resolved slot-`s` supporter;
no result is vetoed (`result_not_vetoed_before`). -/
theorem adopt_result_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some P ∧
      ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) P := by
  suffices hres : SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some P from
    ⟨hres, result_not_vetoed_before hrun hnc hinv hy hu hb hres⟩
  obtain ⟨hPt, hFP⟩ := proposal_held_at_update_before hrun hnc hb0 hsync hfb hinv
    hp hP hPs hpj hy hu hb
  have hmaj := proposal_majority_at_update_before hrun hnc hb0 hsync hfb hinv
    hp hP hPs hpj hy hu hb
  have hΦ : FrameOK ℓ.frame := by
    obtain ⟨⟨hn, hl⟩, -⟩ := hu
    obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
    obtain rfl : c = .ac ℓ := by
      cases c with
      | ac ℓ' => cases hcl; rfl
      | fg _ => cases hcl
    rw [(hrun.cutLaw y hy k₀ (.ac ℓ) ⟨hn, hc⟩).1]
    exact frameOK_state hrun.toLocalRun hy k₀
  exact getConfirmation_eq_of_majority hΦ hPs hPt hFP hmaj

open Classical in
/-- The record after a joined tick at `t_s + 6Δ` whose update of slot `s` has a result `C` that
no live lock vetoes: the old record when `C` is below it in the tree, else `C`. -/
theorem acOnTick_update_record (self : Fin sp.n) {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {t : Time} (ht : t = sp.ts s + 6 * sp.Δ) (hj : SA.joined sp A t)
    (hC : SA.getConfirmation sp A Φ s = some C) (hv : ¬ SA.conflictsWithLock sp A.locks Φ t C) :
    (SA.acOnTick sp self A Φ t).1.latestConfirmed =
      if SA.AncR Φ C A.latestConfirmed then A.latestConfirmed else C.root := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h6 : t = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ := ht.trans (SA.slot_arithmetic sp s).2.2
  have hsl : sp.slot t = s + 1 := by
    have := (SA.slot_arithmetic sp (s + 1)).1 2 (by omega)
    rw [h6]
    simpa using this
  have hne : ¬ t = sp.ts ((s + 1 : Nat) : Int) + sp.Δ := by rw [h6]; intro h; linarith
  unfold SA.acOnTick
  rw [ite_eq_right (not_not.2 hj)]
  simp only [hsl]
  rw [ite_eq_right hne, ite_eq_left ⟨h6, Nat.succ_pos s⟩, Nat.add_sub_cancel]
  simp only [SA.updateConfirmation, hC]
  rw [ite_eq_right hv]
  simp only [SA.updateLatestConfirmed]
  split_ifs <;> rfl

/-- **The update of slot `s` adopts the honest proposal of slot `s`**: after an honest node's
joined update of slot `s`, its record names a block of the honest blocks that extends `P`. -/
theorem update_adopts_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) P E := by
  obtain ⟨hC, hv⟩ := adopt_result_before hrun hnc hb0 hsync hfb hinv hp hP hPs hpj hy hu hb
  obtain ⟨⟨hn, hl⟩, hcall, ht, hj⟩ := hu
  rw [projAC_state hrun.toLocalRun hy] at hj
  -- the cut `k₀` is the run's AC cut `ℓ`
  obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
  obtain rfl : c = .ac ℓ := by
    cases c with
    | ac ℓ' => cases hcl; rfl
    | fg _ => cases hcl
  obtain ⟨hfr, hstep, -, -⟩ := hrun.cutLaw y hy k₀ (.ac ℓ) ⟨hn, hc⟩
  have hpost : tr.state y (k₀ + 1) = tr.post k₀ := by
    rw [Trace.state, ite_eq_left ⟨hn, by rw [hc]; exact Option.some_ne_none _⟩]
  classical
  have hrec : (tr.state y (k₀ + 1)).ac.latestConfirmed =
      if SA.AncR ℓ.frame P (tr.state y k₀).ac.latestConfirmed then
        (tr.state y k₀).ac.latestConfirmed else P.root := by
    rw [hpost, show (tr.post k₀).ac = _ from (congrArg Prod.fst hstep).symm, hcall]
    exact acOnTick_update_record y ht hj hC hv
  have hHB : ∀ X ∈ ℓ.frame.tree, X ∈ tr.HonestBlocks H := fun X hX =>
    ⟨y, hy, k₀, by rw [hfr] at hX; exact hX.1⟩
  have hPt : P ∈ ℓ.frame.tree := (SA.deepest_mem hC).1.1
  split_ifs at hrec with hA
  · obtain ⟨R, hR, hRr, hPR⟩ := hA
    exact ⟨R, hHB R hR, hRr.trans hrec.symm, hPR.mono hHB⟩
  · exact ⟨P, hHB P hPt, hrec.symm, Relation.ReflTransGen.refl⟩

/-- Whole-run adoption is finite adoption at the update horizon. -/
theorem update_adopts {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) P E := by
  have hs : tr.SyncBefore H ΔF (tr.time k₀) :=
    ⟨hsl.1.deltaF, hsl.1.delta_le, fun x hx i m hm h0 y hy j hc _ hd =>
      hsl.1.message x hx i m hm h0 y hy j hc hd,
      fun x hx i B hB h0 y hy j hc _ hd => hsl.1.block x hx i B hB h0 y hy j hc hd,
      fun x hx i B hB h0 y hy j hc _ hd => hsl.1.relay x hx i B hB h0 y hy j hc hd,
      fun x hx i a ha h0 y hy j hc _ hd => hsl.1.attestation x hx i a ha h0 y hy j hc hd⟩
  exact update_adopts_before hrun hnc (hrun.time_nonneg k₀)
    (sleepyServiceBefore_of_sync hrun.toLocalRun hs)
    (sleepyPrefix_iff.1 (hsl.prefix (hrun.time_nonneg k₀))).2.2
    (sleepy_invariant_upTo hrun hnc (hsl.prefix (hrun.time_nonneg k₀))) hp hP hPs hpj hy hu le_rfl

end Consensus.Goldilocks.Compose

end
