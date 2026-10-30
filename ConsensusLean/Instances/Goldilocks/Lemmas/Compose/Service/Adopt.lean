module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Agree

public section

/-! # Goldilocks under `Sleepy`: an honest proposal is adopted by the update of its slot

workbench#12 (`sleepy-proposal-adoption.md`, f42c0ad), A1.7's supplier over the Sleepy
invariant: every honest slot-`s` vote is the honest proposal `P` of slot `s` (§2, §3); at an
honest node's joined update of slot `s`, the result is exactly `P` and not vetoed (§4,
`adopt_result`, open: the S1P–S3P bootstrap with the Sleepy step lemmas for a protected block,
`vote_frame`, `later_transfer_step`, `vote_locks_compatible`, `held_origin_viable`). The update
then moves the record to `P`, or keeps an already deeper one (`update_adopts`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **`P` is in the updater's tree, above its `Σ.F`** (workbench#12 §4: `F ≤ P` through the
update, by the finality-pair sources of labels at most `s + 1`; `P` and its ancestry are accepted by
the joined updater before the deadline; open). -/
theorem proposal_held_at_update {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    P ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F P := by
  sorry

/-- **`P` has a strict majority at the update's test** (workbench#12 §4): every honest slot-`s`
vote is `P` (`honest_votes_eq_proposal`) and reaches the updater resolved
(`honest_batch_at_update`); an honest validator has one slot-`s` vote in the pool (unforgeability,
A0.8), so the honest slot-`s` voters support `P`; the other voters are faulty, and they are fewer
(`faults_lt_honest_voters`). -/
theorem proposal_majority_at_update {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    (SA.voters {v | v ∈ (tr.state y k₀).ac.pool s}).ncard <
      2 * SA.confirmationScore sp (tr.state y k₀).ac ℓ.frame s P := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hrun'.localRun
  have hPt := (proposal_held_at_update hrun hnc hsl hp hP hPs hpj hy hu).1
  have hall := honest_votes_eq_proposal hrun hnc hsl hp hP hPs hpj
  have hbatch := honest_batch_at_update hrun hnc hsl hy hu hPt hall
  rw [← projAC_state hrun.toLocalRun hy]
  set A := tr.projAC.state y k₀
  set Hv := {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = s}
  have hcount : Hᶜ.ncard < Hv.ncard := faults_lt_honest_voters hrun hnc hsl s
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

/-- **No result of an honest joined update is vetoed** under `Sleepy` (workbench#8): a live lock
block is an ancestor of a stored lock block, which is on the origin chain (S1); the result is an
origin; blocks on the origin chain are compatible (S1), so the result is compatible with the live
lock block. -/
theorem result_not_vetoed {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {k₀ s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k₀ s ℓ)
    {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some C) :
    ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) C := by
  have hinv := sleepy_invariant hrun hnc hsl
  have hcoh := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun.coherent
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
  have hCo : Origin tr H C s := Origin.of_result hy
    ⟨ℓ, hu, by rw [projAC_state hrun.toLocalRun hy]; exact hC, rfl⟩
  rintro ⟨V, hV, hconf⟩
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hV
  obtain ⟨L, hL, hLr, hch⟩ := hinv.locks y hy k₀ l hl
  obtain rfl : L = B₀ := hcoh.1 ⟨y, hy, k₀, hL⟩ (hHB hB₀) (hLr.trans hB₀r.symm)
  have hcomp := OnOriginChain.compatible hrun hnc hinv.origins_compatible (hHB hCt) (hHB hB₀)
    (onOriginChain_iff.2 (Or.inr ⟨C, s, hCo, Relation.ReflTransGen.refl⟩)) hch
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

/-- A block strictly above a slot-`s` block has no supporter among the slot-`s` votes resolved by a
cutoff: a vote cannot resolve to a head of a later slot. -/
private theorem confirmationScore_eq_zero {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ) {s : Nat}
    {P B : SA.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = s) (hPB : Φ.Anc P B) (hne : P ≠ B) :
    SA.confirmationScore sp A Φ s B = 0 := by
  have hlt := ((Anc.slot_le hΦ.coherent hPB).2 hne)
  rw [SA.confirmationScore, Set.ncard_eq_zero]
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, x, ⟨-, hx⟩, -, hxs, R, hR, hRr, hBR⟩
  have hin : SA.InTree Φ x.head := ⟨R, hR, hRr⟩
  obtain ⟨R', hl⟩ : ∃ R', SA.lookup Φ x.head = some R' := by
    unfold SA.lookup; rw [dite_eq_left_of_eq_true (eq_true hin)]; exact ⟨_, rfl⟩
  obtain ⟨hR', hR'r⟩ := SA.lookup_eq_some hl
  obtain rfl : R' = R := hΦ.coherent.1 hR' hR (hR'r.trans hRr.symm)
  have hsR := (Anc.slot_le hΦ.coherent hBR).1
  have hxs' : x.slot = s := by exact_mod_cast hxs
  have : SA.resolutionTime A Φ x = ⊤ := by
    unfold SA.resolutionTime
    rw [hl]
    exact ite_eq_left (by omega)
  rw [this] at hx
  exact not_top_lt hx

/-- **The update of slot `s` returns exactly the honest proposal `P` of slot `s`, not vetoed**
(workbench#12 §4): `P` is held above `Σ.F` with a strict majority, every block with a strict
majority is on one chain with it (A0.3), and no block above it has a resolved slot-`s` supporter;
no result is vetoed (`result_not_vetoed`). -/
theorem adopt_result {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some P ∧
      ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) P := by
  suffices hres : SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some P from
    ⟨hres, result_not_vetoed hrun hnc hsl hy hu hres⟩
  obtain ⟨hPt, hFP⟩ := proposal_held_at_update hrun hnc hsl hp hP hPs hpj hy hu
  have hmaj := proposal_majority_at_update hrun hnc hsl hp hP hPs hpj hy hu
  have hΦ : FrameOK ℓ.frame := by
    obtain ⟨⟨hn, hl⟩, -⟩ := hu
    obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
    obtain rfl : c = .ac ℓ := by
      cases c with
      | ac ℓ' => cases hcl; rfl
      | fg _ => cases hcl
    rw [(hrun.cutLaw y hy k₀ (.ac ℓ) ⟨hn, hc⟩).1]
    exact frameOK_state hrun.toLocalRun hy k₀
  set A := (tr.state y k₀).ac
  set S := {B | B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F B ∧
    (SA.voters {v | v ∈ A.pool s}).ncard < 2 * SA.confirmationScore sp A ℓ.frame s B}
  have hS : S ⊆ ℓ.frame.tree := fun X hX => hX.1
  set V : SA.View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hcs : ∀ B, SA.confirmationScore sp A ℓ.frame s B = (SA.supporters ℓ.frame V s B).ncard :=
    fun _ => rfl
  have hsub : V.support ⊆ V.votes := fun _ hv => hv.1
  have hch : ∀ B ∈ S, ∀ C ∈ S, Compatible ℓ.frame.tree B C := fun B hB C hC =>
    SA.majority_chain sp _ ℓ.frame V s B C hΦ hsub hB.1 hC.1 (hcs B ▸ hB.2.2) (hcs C ▸ hC.2.2)
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ hS ⟨P, hPt, hFP, hmaj⟩
  have hPD := SA.anc_deepest hΦ hS hch hD P ⟨hPt, hFP, hmaj⟩
  have hDS := (SA.deepest_mem hD).1
  change SA.deepest ℓ.frame S = some P
  rw [hD]
  by_contra hne
  have h0 := confirmationScore_eq_zero (A := A) hΦ hPs hPD fun h => hne (congrArg some h.symm)
  have := hDS.2.2
  omega

open Classical in
/-- The record after a joined tick at `t_s + 6Δ` whose update of slot `s` has a result `C` that
no live lock vetoes: the old record when `C` is below it in the tree, else `C`. -/
private theorem acOnTick_update_record (self : Fin sp.n) {A : SA.SAState sp.n}
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
theorem update_adopts {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    ∃ E ∈ tr.HonestBlocks H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) P E := by
  obtain ⟨hC, hv⟩ := adopt_result hrun hnc hsl hp hP hPs hpj hy hu
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

end Consensus.Goldilocks.Compose

end
