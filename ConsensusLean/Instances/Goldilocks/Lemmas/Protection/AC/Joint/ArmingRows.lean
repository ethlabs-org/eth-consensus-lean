module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WriteMode
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Viable
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Delivery
import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Joint.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection, the arming over AC traces: the update rows before `b`

The rows of the slow-lock write at an arming update (`Obligations/OutageArmingSteps`), over an AC
trace of the SA with the unlock given at a write mode (`ACRunU wm u`), under trivial frames, with
the pre-`b` frontier `FrontierAC` in place of the Sleepy invariant and the deadline-cut service
`SyncUntilAC` in place of the composite service before `b`:

* D1–D3 before `b` (`accepted_held_before_preAC`, `vote_pooled_before_preAC`,
  `vote_resolved_before_preAC`): the delivery rows of `Rows/Delivery` with the deadline-cut
  service; every delivery read has its receiver's deadline at most `t_q + 2Δ ≤ b`;
* **Lemma P** (`update_result_extends_preAC`, after `Compose.update_result_extends_origin`): an
  honest joined update of a slot `s` whose votes are delivered by `t_s + 2Δ ≤ b` (the update itself
  may be after `b`) has a result extending an origin within `b` of a label below `s`, which is in
  its frame; under trivial frames `Φ.F` is genesis, so no root-cover case arises;
* the post-state of an update at the mode (`state_after_updateAC`) and its saved results
  (`saved_after_updateAC`, `saved_step_of_not_restartAC`: `SA.saved_after_update` and
  `SA.saved_step_of_not_restart` with the unlock given);
* **the slow write at width `k`** (`updateConfirmationM_slow_lock_of`,
  `updateConfirmationM_slow_lock_effective`): `SA.updateConfirmation_slow_lock_of` for the mode's
  `newLocksM`, whose slow arm at width `k` is the parent's. -/

namespace Consensus.Goldilocks.Comparison

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {b : Time}

/-! ### D1–D3 before `b` -/

/-- The deadline of a time `τ ≤ t_q + Δ` at a receiver whose restarts are at or before `t_q` is at
most `t_q + 2Δ`. -/
private theorem deadline_le_twoAC {y : Fin sp.n} {c q : Nat}
    (h : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts q) {τ : Time}
    (hτ : τ ≤ sp.ts q + sp.Δ) : tr.deadline y c τ ≤ sp.ts q + 2 * sp.Δ := by
  have h₁ := Compose.ac_deadline_le_of_restarts h τ
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  linarith [max_le hτ (show sp.ts q ≤ sp.ts q + sp.Δ by linarith)]

/-- **D1 before `b`**: a block that is genesis or that an honest node accepted by `t_q + Δ`, and
that is above the call's `Φ.F`, is in the call's frame and stamped before `t_q + 2Δ`, at every
honest call from `t_q + 2Δ` with no restart after `t_q`, under the deadline-cut service before
`b ≥ t_q + 2Δ`. -/
theorem accepted_held_before_preAC (hr : ACLocalRunU wm u H U tr) (hsy : SyncUntilAC tr H U b)
    {y : Fin sp.n} (hy : y ∈ H) {q c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c)
    (hb : sp.ts q + 2 * sp.Δ ≤ b) (hres : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts q)
    {B : Blk sp.n FGP} (hBU : B ∈ U)
    (hacc : B.root = sp.genesisRoot ∨
      ∃ x ∈ H, ∃ k, tr.AcceptAt x k B ∧ tr.time k ≤ sp.ts q + sp.Δ)
    (hF : Anc U ℓ.frame.F B) :
    B ∈ ℓ.frame.tree ∧ (tr.state y c).blockStamp B.root < ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hy hc
  have hdl : ∀ k ≤ c, ∀ τ, τ ≤ sp.ts q + sp.Δ → tr.deadline y k τ ≤ sp.ts q + 2 * sp.Δ :=
    fun k hk _ hτ => deadline_le_twoAC (fun k' hk' hr' => hres k' (hk'.trans hk) hr') hτ
  have hab : AcceptedBefore tr y B (sp.ts q + 2 * sp.Δ) ∧ B ∈ ℓ.frame.tree := by
    rcases hacc with hgen | ⟨x, hx, k, hax, hkt⟩
    · refine ⟨Or.inl hgen, ?_⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr hy c ℓ hc
      obtain rfl : B = G := hU.1 hBU hGU (hgen.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hF with h | ⟨Q, -, hQ⟩
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    · obtain ⟨ky, hky, hay, hkyt⟩ := hsy.relay x hx k B hax y hy c ℓ hc
        ((hdl c le_rfl _ hkt).trans hct) ((hdl c le_rfl _ hkt).trans (by linarith)) hF
      exact ⟨Or.inr ⟨ky, hay, hkyt.trans_le (hdl ky hky _ hkt)⟩,
        mem_tree_of_acceptAtU sp hr hy hay hky hc hF⟩
  obtain ⟨hab, hBt⟩ := hab
  exact ⟨hBt, blockStamp_lt_of_acceptedBeforeU sp hr hy hc hBt hab
    (fun k hk hrk => by linarith [hres k hk hrk]) (Or.inl hct)⟩

/-- **D2 before `b`**: an honest slot-`q` vote is in the receiver's pool, with a stamp before
`t_q + 2Δ`, at every honest call from `t_q + 2Δ` with no restart after `t_q`, under the
deadline-cut service before `b ≥ t_q + 2Δ`. -/
theorem vote_pooled_before_preAC (hrun : ACRunU wm u proposer tr H U)
    (hsy : SyncUntilAC tr H U b) {y : Fin sp.n} (hy : y ∈ H) {q c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hb : sp.ts q + 2 * sp.Δ ≤ b)
    (hres : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e)
    (hes : e.msg.slot = q) :
    e.msg ∈ (tr.state y c).pool q ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hr := hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hdl : ∀ k ≤ c, ∀ τ, τ ≤ sp.ts q + sp.Δ → tr.deadline y k τ ≤ sp.ts q + 2 * sp.Δ :=
    fun k hk _ hτ => deadline_le_twoAC (fun k' hk' hr' => hres k' (hk'.trans hk) hr') hτ
  obtain ⟨hxv, hxs⟩ := vote_signer_slotAC hr hx hv
  have htj : tr.time j ≤ sp.ts q + sp.Δ := by
    have h := vote_time_leU hr hx hv
    rwa [← hxs, hes] at h
  have hsj : sp.ts q ≤ tr.time j :=
    (ts_le_iff_le_slot sp (hr.time_nonneg j) q).2 (by omega)
  obtain ⟨ℓv, hcv, hev⟩ := id hv
  -- the vote is processed by the receiver before `t_q + 2Δ`
  obtain ⟨k', hk'c, hjk', hp, hk'dl, -⟩ := hsy.message x hx j e.msg
    ⟨ℓv, hcv, Or.inl ⟨e, hev, rfl⟩⟩ y hy c ℓ hc ((hdl c le_rfl _ htj).trans hct)
    ((hdl c le_rfl _ htj).trans (by linarith))
  have hk'lt : tr.time k' < sp.ts q + 2 * sp.Δ := hk'dl.trans_le (hdl k' hk'c _ htj)
  have hk'c' : k' < c := lt_of_le_of_ne hk'c (by rintro rfl; exact hk'lt.not_ge hct)
  have hsk' : sp.slot (tr.time k') = q :=
    slot_of_mem sp q (hsj.trans hjk') (by rw [ts_succ]; linarith only [hk'lt, hΔ])
  have hnr : ∀ r, k' + 1 ≤ r → r < c + 1 → ¬ tr.RestartAt y r := by
    rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
    obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
    obtain ⟨ℓ', hc', -⟩ := hp
    have h₁ := hprev k' (by omega) ℓ' hc'
    have h₂ := hres r (by omega) ⟨ℓr, hcr, hrr⟩
    exact (hsj.trans hjk').not_gt (h₁.trans (hu.trans_le h₂))
  have hpk' : e.msg ∈ (tr.state y (k' + 1)).pool q := by
    rcases held_of_processAtU hr hy hp (by rw [hes, hsk']; omega) (by rw [hes, hsk']) with
      h | ⟨a, ha, b, hb, hab, hav, hbv⟩
    · rwa [hes] at h
    · rw [hes] at ha hb
      obtain ⟨ja, -, ea, hea, hea'⟩ :=
        hrun.honest.pool_vote y hy _ q a ha (by rw [hav, hxv]; exact hx)
      obtain ⟨jb, -, eb, heb, heb'⟩ :=
        hrun.honest.pool_vote y hy _ q b hb (by rw [hbv, hxv]; exact hx)
      rw [hav, hxv] at hea
      rw [hbv, hxv] at heb
      obtain ⟨-, rfl⟩ := one_vote_per_slotU sp FGP ro H U tr hr x hx ja jb ea eb hea heb
        (by rw [hea', heb', state_pool_slotU sp hr hy _ q a ha,
          state_pool_slotU sp hr hy _ q b hb])
      exact absurd (hea'.symm.trans heb') hab
  have hpool : e.msg ∈ (tr.state y c).pool q :=
    pool_monoU hr hy (show k' + 1 ≤ c by omega) (fun r h₁ h₂ => hnr r h₁ (by omega)) q hpk'
  refine ⟨hpool, ?_⟩
  rcases pool_originU hr hy c e.msg (by rw [hes]; exact hpool) with
    ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
  · rw [hst₁, etime_of_lt_of]
    by_cases hk₁k' : k₁ ≤ k'
    · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
    · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, he₁m⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
      · -- the receiver cast the vote itself: it is the voter, and the cast is the vote at `j`
        have hv₁ : VoteAt tr y k₁ e₁ := ⟨ℓ₁, hc₁, he₁⟩
        have hyx : y = x := by
          rw [← (vote_signer_slotAC hr hy hv₁).1, he₁m, hxv]
        rw [hyx] at hv₁
        obtain ⟨rfl, -⟩ := one_vote_per_slotU sp FGP ro H U tr hr x hx k₁ j e₁ e hv₁ hv
          (by rw [he₁m])
        linarith only [htj, hΔ]
      · exact absurd (pool_monoU hr hy (show k' + 1 ≤ k₁ by omega)
          (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hes]; exact hpk')) hn₁
  · rw [hst₁, etime_of_lt_of]
    exact (hres k₁ hk₁.le ⟨ℓ₁, hc₁, hr₁⟩).trans_lt
      (lt_add_of_pos_right _ (mul_pos two_pos hΔ))

/-- **D3 before `b`**: the vote is pooled, its head is in the call's frame, and the vote is
resolved before `t_q + 2Δ`, given the head's slot bound and its acceptance by the voter by
`t_q + Δ` (or genesis). -/
theorem vote_resolved_before_preAC (hrun : ACRunU wm u proposer tr H U)
    (hsy : SyncUntilAC tr H U b) {y : Fin sp.n} (hy : y ∈ H) {q c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y c ℓ)
    (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hb : sp.ts q + 2 * sp.Δ ≤ b)
    (hres : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e)
    (hes : e.msg.slot = q) {Hd : Blk sp.n FGP} (hHdU : Hd ∈ U)
    (hHdr : Hd.root = e.msg.head) (hHds : Hd.slot ≤ q)
    (hHdacc : Hd.root = sp.genesisRoot ∨
      ∃ k, tr.AcceptAt x k Hd ∧ tr.time k ≤ sp.ts q + sp.Δ)
    (hF : Anc U ℓ.frame.F Hd) :
    e.msg ∈ (tr.state y c).pool q ∧ Hd ∈ ℓ.frame.tree ∧
      resolutionTime (tr.state y c) ℓ.frame e.msg < ETime.of (sp.ts q + 2 * sp.Δ) := by
  obtain ⟨hpool, hvst⟩ := vote_pooled_before_preAC hrun hsy hy hc hct hb hres hx hv hes
  obtain ⟨hHdt, hbst⟩ := accepted_held_before_preAC hrun.localRun hsy hy hc hct hb hres hHdU
    (hHdacc.imp_right fun ⟨k, h⟩ => ⟨x, hx, k, h⟩) hF
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hrun.localRun hy hc
  have hHs : Hd.slot ≤ e.msg.slot := by rw [hes]; exact hHds
  refine ⟨hpool, hHdt, ?_⟩
  unfold resolutionTime
  rw [← hHdr, lookup_of_mem hΦ hHdt]
  dsimp only
  simp only [not_lt.2 hHs, ↓reduceIte]
  exact max_lt hvst hbst

/-! ### Lemma P -/

/-- **Lemma P before `b`**: an honest joined update of slot `s`, whose slot's votes are delivered
by `t_s + 2Δ ≤ b` (the update itself may be after `b`), has a result `D` extending an origin `C`
within `b` of a label `σ < s`, and `C` is in its frame. Every honest slot-`s` vote is cast by
`t_s + Δ ≤ b`, so it extends `C` (the frontier), and reaches the update resolved before
`t_s + 2Δ`; the honest voters, more than `f` by the fault bound at `t_s + Δ`, make `C` a majority
block, and the result is the deepest one. -/
theorem update_result_extends_preAC (hrun : ACRunU wm u proposer tr H U)
    (htriv : TrivialFrames tr H) (htick : TickDuty tr H) (hsy : SyncUntilAC tr H U b)
    (hfr : FrontierAC tr H U b) {C : Blk sp.n FGP} {σ : Nat} (hC : OriginWithinAC tr H C σ b)
    {w : Fin sp.n} (hw : w ∈ H) {c s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hσs : σ < s) (hu : UpdateAt tr w c s ℓ) (hsb : sp.ts s + 2 * sp.Δ ≤ b)
    (hfb : FaultBound tr H (sp.ts s + sp.Δ)) :
    C ∈ ℓ.frame.tree ∧ ∃ D, getConfirmation sp (tr.state w c) ℓ.frame s = some D ∧
      ℓ.frame.Anc C D := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hw hu.1
  have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hres := update_restartsAC hr hw hu
  -- `Φ.F ⪯ C`: `C` is in an honest frame, whose `Φ.F` is the shared genesis
  have hFC : Anc U ℓ.frame.F C := by
    obtain ⟨z, hz, k', ℓ', hc', hC'⟩ := origin_frameAC hC
    obtain ⟨hΦ', hΦU'⟩ := frameIn_of_callAtU hr hz hc'
    rw [trivial_F_eqAC hr htriv hw hz hu.1 hc']
    exact (hΦ'.rooted.2 _ hC').mono hΦU'
  -- every honest slot-`s` vote: its head in the frame above `C`, pooled and resolved early
  have hbatch : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = s →
      ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ Anc U C Hd ∧
        e.msg ∈ (tr.state w c).pool s ∧
        resolutionTime (tr.state w c) ℓ.frame e.msg < ETime.of (sp.ts s + 2 * sp.Δ) := by
    intro x hx j e hv hes
    obtain ⟨ℓx, hcx, hex⟩ := id hv
    obtain ⟨-, hte⟩ := ts_le_castAC hr hx hv
    rw [hes] at hte
    obtain ⟨Hd, hHdU, hHdr, hCHd⟩ := hfr.vote_extends C σ hC x hx j e hv (by linarith)
      (by omega)
    obtain ⟨Hd', hHd', hHd'r, hHd's⟩ := honest_head_frameU hr hx ⟨hcx, hex⟩
    obtain ⟨hΦx, hΦxU⟩ := frameIn_of_callAtU hr hx hcx
    obtain rfl : Hd' = Hd := hU.1 (hΦxU hHd') hHdU (hHd'r.trans hHdr.symm)
    have hacc : Hd'.root = sp.genesisRoot ∨
        ∃ k, tr.AcceptAt x k Hd' ∧ tr.time k ≤ sp.ts s + sp.Δ := by
      rcases Compose.frame_anc_acceptedU hr hx j ℓx hcx Hd' hHd' Hd' .refl with
        hg | ⟨k, hk, hak⟩
      · exact Or.inl hg
      · exact Or.inr ⟨k, hak, (hr.time_mono hk).trans hte⟩
    have hFHd : Anc U ℓ.frame.F Hd' := by
      rw [trivial_F_eqAC hr htriv hw hx hu.1 hcx]
      exact (hΦx.rooted.2 _ hHd').mono hΦxU
    obtain ⟨hpool, hHdt, hres'⟩ := vote_resolved_before_preAC hrun hsy hw hu.1 (by linarith)
      hsb hres hx hv hes hHdU hHd'r (hes ▸ hHd's) hacc hFHd
    exact ⟨Hd', hHdt, hHd'r, hCHd, hpool, hres'⟩
  set A := tr.state w c
  set Hv := {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s}
  have hcount : Hᶜ.ncard < Hv.ncard := by
    refine lt_of_lt_of_le hfb (Set.ncard_le_ncard ?_)
    rintro x ⟨hx, hwk, hj⟩
    obtain ⟨j, e, hv, hs, -⟩ := vote_of_awake_joinedAC hr htick hx hwk hj
    exact ⟨hx, j, e, hv, hs⟩
  -- `C` is in the frame, between `Φ.F` and an honest head
  have hCt : C ∈ ℓ.frame.tree := by
    obtain ⟨x, hx, j, e, hv, hes⟩ := Set.nonempty_of_ncard_ne_zero
      (Nat.zero_lt_of_lt hcount).ne'
    obtain ⟨Hd, hHdt, -, hCHd, -⟩ := hbatch x hx j e hv hes
    exact frame_mem_of_between sp hU hΦ hΦU hHdt hCHd hFC
  have hFCΦ : ℓ.frame.Anc ℓ.frame.F C := hΦ.rooted.2 C hCt
  have hone : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = s →
      ∀ v ∈ A.pool s, v.val = x → v = e.msg := by
    intro x hx j e hv hs v hvp hvx
    obtain ⟨j', -, e', hv', rfl⟩ := hrun.honest.pool_vote w hw c s v hvp (hvx ▸ hx)
    have hs' := state_pool_slotU sp hr hw c s _ hvp
    rw [hvx] at hv'
    exact congrArg (fun e : Em sp FGP => e.msg)
      (one_vote_per_slotU sp FGP ro H U tr hr x hx j' j e' e hv' hv (hs'.trans hs.symm)).2
  set V : View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    resolutionTime A ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hcs : ∀ B, confirmationScore sp A ℓ.frame s B = (supporters ℓ.frame V s B).ncard :=
    fun _ => rfl
  have hsupp : Hv ⊆ supporters ℓ.frame V s C := by
    rintro x ⟨hx, j, e, hv, hs⟩
    obtain ⟨Hd, hHdt, hHdr, hCHd, hvp, hres'⟩ := hbatch x hx j e hv hs
    obtain ⟨ℓx, hcx, hex⟩ := hv
    have hval := (castAt_specU hr hx ⟨hcx, hex⟩).1
    refine ⟨?_, e.msg, ⟨hvp, hres'⟩, hval, by exact_mod_cast hs, Hd, hHdt, hHdr,
      anc_tree_of_anc_U hU hΦ hΦU hCt hCHd hHdt⟩
    rintro ⟨v, hv, v', hv', hne, hvx, hv'x⟩
    exact hne ((hone x hx j e ⟨ℓx, hcx, hex⟩ hs v hv hvx).trans
      (hone x hx j e ⟨ℓx, hcx, hex⟩ hs v' hv' hv'x).symm)
  have hvot : voters {v | v ∈ A.pool s} ⊆ Hv ∪ Hᶜ := by
    rintro x ⟨v, hv, rfl⟩
    by_cases hx : v.val ∈ H
    · obtain ⟨j, -, e, he, rfl⟩ := hrun.honest.pool_vote w hw c s _ hv hx
      exact Or.inl ⟨hx, j, e, he, state_pool_slotU sp hr hw c s _ hv⟩
    · exact Or.inr hx
  have hmaj : (voters {v | v ∈ A.pool s}).ncard < 2 * confirmationScore sp A ℓ.frame s C := by
    have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
    have h2 := Set.ncard_union_le Hv Hᶜ
    have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
    rw [hcs]
    omega
  -- the result is the deepest majority block above `Φ.F`, which extends `C`
  set S := {B | B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F B ∧
    (voters {v | v ∈ A.pool s}).ncard < 2 * confirmationScore sp A ℓ.frame s B}
  have hS : S ⊆ ℓ.frame.tree := fun X hX => hX.1
  have hsub : V.support ⊆ V.votes := fun _ hv => hv.1
  have hch : ∀ B ∈ S, ∀ B' ∈ S, Compatible ℓ.frame.tree B B' := fun B hB B' hB' =>
    majority_chain sp _ ℓ.frame V s B B' hΦ hsub hB.1 hB'.1 (hcs B ▸ hB.2.2)
      (hcs B' ▸ hB'.2.2)
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨C, hCt, hFCΦ, hmaj⟩
  exact ⟨hCt, D, hD, anc_deepest hΦ hS hch hD C ⟨hCt, hFCΦ, hmaj⟩⟩

/-! ### The update's post-state and the saved results -/

private theorem saved_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).saved = A.saved := by
  unfold admitVote; split_ifs <;> rfl

private theorem saved_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).saved = A.saved := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

private theorem saved_tryVote {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : (tryVoteWithM sp wm x L A Φ t).1.saved = A.saved := by
  unfold tryVoteWithM; dsimp only
  split_ifs <;> simp only [optimisticConfirmationM_keep _ saved_optimistic, saved_admitVote]

private theorem saved_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).saved = A.saved := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').saved = A'.saved from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => intro A'; simp only [List.foldl_cons]; rw [ih, saved_admitVote]

/-- The parent's update of slot `s` writes `saved[s]` with the root of its result. -/
private theorem saved_update (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (updateConfirmation sp A Φ t s).saved =
      Function.update A.saved s ((getConfirmation sp A Φ s).map Block.root) := by
  unfold updateConfirmation updateLatestConfirmed; dsimp only
  split
  · rfl
  · split_ifs <;> rfl

/-- A call other than a restart keeps the saved results, or is a joined tick at `t_σ + 6Δ` that
writes `saved[σ]` with its update's result. -/
private theorem saved_stepAC {L : Set Lock} (self : Fin sp.n) (A : SAState sp.n)
    {Φ : Frm sp.n FGP} {t : Time} {c : (goldilocksSA sp FGP ro).Call} (hc : c ≠ .restart) :
    let A' := (stepWithM sp ro wm self L A Φ t c).1
    A'.saved = A.saved ∨
      ∃ σ : Nat, c = .tick ∧ t = sp.ts σ + 6 * sp.Δ ∧ joined sp A t ∧
        A'.saved = Function.update A.saved σ ((getConfirmation sp A Φ σ).map Block.root) := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  cases c with
  | tick =>
    change (acOnTickWithM sp wm self L A Φ t).1.saved = _ ∨
      ∃ σ : Nat, _ ∧ _ ∧ _ ∧ (acOnTickWithM sp wm self L A Φ t).1.saved = _
    unfold acOnTickWithM; dsimp only
    by_cases hj : joined sp A t
    swap
    · have hc : (¬ joined sp A t) = True := eq_true hj
      simp only [hc, ↓reduceIte, true_or]
    have hc : (¬ joined sp A t) = False := eq_false (not_not.2 hj)
    simp only [hc, ↓reduceIte]
    by_cases hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
    · have hv : ¬ t = sp.ts (sp.slot t) + sp.Δ := fun h => by linarith [hu.1.symm.trans h]
      have hc₁ : (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) = True := eq_true hu
      have hc₂ : (t = sp.ts (sp.slot t) + sp.Δ) = False := eq_false hv
      simp only [hc₁, hc₂, ↓reduceIte]
      refine Or.inr ⟨sp.slot t - 1, trivial, ?_, hj,
        (updateConfirmationM_field SAState.saved (fun _ _ => rfl) _ _ _ _ _).trans
          (saved_update _ _ _ _)⟩
      have hs1 : ((sp.slot t - 1 : Nat) : Int) = (sp.slot t : Int) - 1 := by omega
      have e := hu.1
      simp only [SAParams.ts] at e ⊢
      rw [hs1]
      linarith
    · have hc₁ : (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) = False := eq_false hu
      simp only [hc₁, ↓reduceIte]
      left
      split_ifs
      · exact saved_tryVote _ _ _ _
      · rfl
  | proposal =>
    left
    change (acProposalWith sp L A Φ t).1.saved = _
    unfold acProposalWith; split_ifs <;> rfl
  | toFG =>
    left
    change (acToFG sp A Φ t).1.saved = _
    unfold acToFG
    split_ifs
    all_goals first | rfl | (split <;> (try split_ifs) <;> rfl)
  | message m =>
    left
    change (tryVoteWithM sp wm self L _ Φ t).1.saved = _
    rw [saved_tryVote, optimisticConfirmationM_keep _ saved_optimistic, saved_admitVote]
  | block B =>
    left
    change (tryVoteWithM sp wm self L _ Φ t).1.saved = _
    rw [saved_tryVote, optimisticConfirmationM_keep _ saved_optimistic, saved_blockReceipt]
  | restart => exact absurd rfl hc

/-- **The state after an update** of slot `s` at cut `c` is the mode's `update_confirmation` of
slot `s` on the state before it. -/
theorem state_after_updateAC (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n} (hx : x ∈ H)
    {c s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr x c s ℓ) :
    tr.state x (c + 1) = updateConfirmationM sp wm (tr.state x c) ℓ.frame (tr.time c) s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have h6 : tr.time c = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ := by rw [ht, ts_succ]; ring
  have hsl : sp.slot (tr.time c) = s + 1 := slot_of_mem sp (s + 1) (by rw [h6]; linarith)
    (by rw [h6, ts_succ (s + 1)]; linarith)
  have hne : ¬ tr.time c = sp.ts ((s + 1 : Nat) : Int) + sp.Δ := by rw [h6]; intro h; linarith
  have he := hr.exec c ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1, hcall] at he
  have h1 : tr.post c = (acOnTickWithM sp wm x (u c) (tr.state x c) ℓ.frame (tr.time c)).1 :=
    (congrArg Prod.fst he).symm
  rw [Trace.state_succ_of_call tr hc, h1]
  unfold acOnTickWithM
  dsimp only
  rw [hsl]
  have hc2 : (tr.time c = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ ∧ 0 < s + 1) = True :=
    eq_true ⟨h6, Nat.succ_pos s⟩
  simp only [hj, not_true_eq_false, hne, hc2, ↓reduceIte, Nat.add_sub_cancel]

/-- **The update writes its slot's saved result**, the other saved results unchanged. -/
theorem saved_after_updateAC (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n} (hx : x ∈ H)
    {c s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr x c s ℓ) :
    (tr.state x (c + 1)).saved = Function.update (tr.state x c).saved s
      ((getConfirmation sp (tr.state x c) ℓ.frame s).map Block.root) := by
  rw [state_after_updateAC hr hx hu,
    updateConfirmationM_field SAState.saved (fun _ _ => rfl), saved_update]

/-- **Without a restart, `saved[j]` changes only at an update of slot `j`.** -/
theorem saved_step_of_not_restartAC (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i j : Nat) (hnr : ¬ tr.RestartAt x i) :
    (tr.state x (i + 1)).saved j = (tr.state x i).saved j ∨
      ∃ ℓ, UpdateAt tr x i j ℓ ∧ (tr.state x (i + 1)).saved j =
        (getConfirmation sp (tr.state x i) ℓ.frame j).map Block.root := by
  by_cases hcall : ∃ ℓ, tr.CallAt x i ℓ
  · obtain ⟨ℓ, hc⟩ := hcall
    have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
    rw [hc.1] at he
    have hpost : tr.state x (i + 1) =
        (stepWithM sp ro wm x (u i) (tr.state x i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [Trace.state_succ_of_call tr hc, he]
    rw [hpost]
    rcases saved_stepAC (wm := wm) (L := u i) (ro := ro) x (tr.state x i) (Φ := ℓ.frame)
        (t := tr.time i) (fun h => hnr ⟨ℓ, hc, h⟩) with hs | ⟨σ, hcl, ht, hj, hs⟩
    · exact Or.inl (congrFun hs j)
    · rw [hs]
      by_cases hjσ : j = σ
      · subst hjσ
        exact Or.inr ⟨ℓ, ⟨hc, hcl, ht, hj⟩, Function.update_self ..⟩
      · exact Or.inl (Function.update_of_ne (by exact_mod_cast hjσ) _ _)
  · push Not at hcall
    exact Or.inl (by rw [Trace.state_succ_of_not tr hcall])

/-! ### The slow write at width `k` -/

/-- **Slow formation at a mode of width `k`**: attestations above `C`, a result `D ⪰ C`, and no
live lock conflicting with `C` store the slow lock of slot `s` and expiry `s + k` on the viable
ancestor of the deepest unvetoed slow-test block `X ⪰ C`. A veto of `D` stops only the record. -/
theorem updateConfirmationM_slow_lock_of (hw : wm.width = sp.k) {A : SAState sp.n}
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {s : Nat} {C D : Blk sp.n FGP}
    (hD : getConfirmation sp A Φ s = some D) (hnvC : ¬ conflictsWithLock sp A.locks Φ t C)
    (hCt : C ∈ Φ.tree) (hCg : C.root ≠ sp.genesisRoot) (hCD : Φ.Anc C D)
    (hrows : ∀ j : Int, (s : Int) - sp.k < j → j < s →
      ∃ S ∈ Φ.tree, A.saved j = some S.root ∧ Φ.Anc C S)
    (hlive : sp.slot t ≤ s + sp.k) :
    ∃ X, X ∈ Φ.tree ∧ Φ.Anc C X ∧
      (⟨(Φ.viableAncestor X).root, s, false, s + sp.k⟩ : Lock) ∈
        (updateConfirmationM sp wm A Φ t s).locks := by
  classical
  rw [updateConfirmationM_locks_of_some hD]
  set S : Set (Blk sp.n FGP) := {B | (B ∈ confirmationPath sp Φ D ∧
      ¬ conflictsWithLock sp A.locks Φ t B) ∧ ∀ j : Int, (s : Int) - wm.width < j → j < s →
        ∃ S ∈ Φ.tree, (Function.update A.saved s (some D.root)) j = some S.root ∧ Φ.Anc B S}
  have hSt : S ⊆ Φ.tree := fun B hB => hB.1.1.1
  have hCS : C ∈ S := by
    refine ⟨⟨⟨hCt, hCg, hCD⟩, hnvC⟩, fun j hj₁ hj₂ => ?_⟩
    rw [hw] at hj₁
    obtain ⟨S', hS', hsv, hCS'⟩ := hrows j hj₁ hj₂
    exact ⟨S', hS', by rw [Function.update_of_ne (by omega)]; exact hsv, hCS'⟩
  have hch : ∀ B ∈ S, ∀ B' ∈ S, Compatible Φ.tree B B' := fun B hB B' hB' =>
    anc_total hΦ.coherent hB.1.1.2.2 hB'.1.1.2.2
  obtain ⟨X, hX⟩ := exists_deepest hΦ hSt ⟨C, hCS⟩
  have hXS := (deepest_mem hX).1
  refine ⟨X, hSt hXS, anc_deepest hΦ hSt hch hX C hCS, ?_⟩
  exact ⟨⟨X.root, s, false, s + sp.k⟩, Or.inr ⟨_, mem_newLocksM.2 (Or.inr ⟨X, hX, rfl⟩), rfl⟩,
    X, hSt hXS, rfl, hlive, rfl⟩

/-- **Effective slow formation at a mode of width `k`**: with `C` a candidate of
`viable_ancestor`, the stored block of the slow lock extends `C`. -/
theorem updateConfirmationM_slow_lock_effective (hw : wm.width = sp.k) {A : SAState sp.n}
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {s : Nat} {C D : Blk sp.n FGP}
    (hD : getConfirmation sp A Φ s = some D) (hnvC : ¬ conflictsWithLock sp A.locks Φ t C)
    (hCt : C ∈ Φ.tree) (hCg : C.root ≠ sp.genesisRoot) (hCD : Φ.Anc C D)
    (hrows : ∀ j : Int, (s : Int) - sp.k < j → j < s →
      ∃ S ∈ Φ.tree, A.saved j = some S.root ∧ Φ.Anc C S)
    (hlive : sp.slot t ≤ s + sp.k) (hcand : Φ.AncestorCandidate C) :
    ∃ L, L ∈ Φ.tree ∧ Φ.Anc C L ∧
      (⟨L.root, s, false, s + sp.k⟩ : Lock) ∈ (updateConfirmationM sp wm A Φ t s).locks := by
  obtain ⟨X, hX, hCX, hl⟩ :=
    updateConfirmationM_slow_lock_of hw hΦ hD hnvC hCt hCg hCD hrows hlive
  exact ⟨Φ.viableAncestor X, (viableAncestor_anc hΦ hX).1,
    anc_viableAncestor_of_candidate hΦ hcand.symm hX hCX, hl⟩

end Consensus.Goldilocks.Comparison

end
