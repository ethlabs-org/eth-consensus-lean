module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the frozen witness

An honest head relayed before the freeze lies in the voter block tree. `Frame` supplies the
honest-store geometry; `FrameLabels` uses this witness for viability at votes. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### The frozen witness: an honest head relayed before the freeze -/

/-- Through the restarts up to cut `c`, the latest wake is at most a bound of those restarts. -/
private theorem lastWake_le {y : Fin sp.n} {a : Time} :
    ∀ {c : Nat}, (∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ a) →
      ∀ w : Time, tr.lastWake y c = (w : WithBot Time) → w ≤ a
  | 0, h, w, hw => by
    unfold RunTrace.lastWake at hw
    split_ifs at hw with hr
    · rw [← WithBot.coe_injective hw]; exact h 0 le_rfl hr
    · simp at hw
  | c + 1, h, w, hw => by
    unfold RunTrace.lastWake at hw
    split_ifs at hw with hr
    · rw [← WithBot.coe_injective hw]; exact h _ le_rfl hr
    · exact lastWake_le (fun k hk => h k (hk.trans (Nat.le_succ c))) w hw

/-- With every restart up to cut `c` at or before `a`, the deadline of `τ` is at most
`max(τ, a) + Δ'`. -/
theorem deadline_le_of_restarts {y : Fin sp.n} {c : Nat} {a : Time}
    (h : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ a) (τ Δ' : Time) :
    tr.deadline y c τ Δ' ≤ max τ a + Δ' := by
  unfold RunTrace.deadline
  rcases hw : tr.lastWake y c with _ | w
  · change τ + Δ' ≤ max τ a + Δ'
    exact add_le_add (le_max_left τ a) le_rfl
  · change max τ w + Δ' ≤ max τ a + Δ'
    exact add_le_add (max_le_max (le_refl τ) (lastWake_le h w hw)) le_rfl

private theorem add_mul_delta_le {x a b : Time} (h : a ≤ b) : x + a * sp.Δ ≤ x + b * sp.Δ :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_right h sp.toParams.hΔ.le)

private theorem add_mul_delta_lt {x a b : Time} (h : a < b) : x + a * sp.Δ < x + b * sp.Δ :=
  add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_right h sp.toParams.hΔ)

private theorem optimistic_stamp (A : SA.SAState sp.n) (Φ : SA.Frm sp.n (List (FG.Att sp.n)))
    (t : Time) : (SA.optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold SA.optimisticConfirmation SA.updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

/-- At an honest slot-`(s+1)` vote, the voter's restarts up to the vote were at or before `t_s`,
and the vote is cast from `t_{s+1} = t_s + 4Δ` on. -/
theorem honest_vote_restarts (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) :
    (∀ c ≤ i, tr.projAC.RestartAt y c → tr.time c ≤ sp.ts s) ∧ sp.ts s + 4 * sp.Δ ≤ tr.time i := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨-, hslot, hjoin, -⟩ := SA.castAt_spec hr hy hc
  have hti : sp.slot (tr.projAC.time i) = s + 1 := hslot ▸ hs
  have hjp : SA.joined sp (tr.projAC.post i) (tr.projAC.time i) := by
    unfold SA.joined; rw [SA.restartTime_of_castAt hr hy hc]; exact hjoin
  refine ⟨fun c hc' hrc => ?_, ?_⟩
  · have h := ((SA.joined_awake sp) _ ro H _ tr.projAC hr y hy i ℓ hc.1 hjp).2 c hc' hrc
    rw [hti, show (((s + 1 : Nat) : Int) - 1) = (s : Int) by push_cast; ring] at h
    exact h
  · have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) ((s : Int) + 1)).2
      (by rw [hti]; push_cast; rfl)
    have e4 : sp.ts ((s : Int) + 1) = sp.ts s + 4 * sp.Δ := by simp only [SAParams.ts]; ring
    rw [e4] at h
    exact h

/-- **An honest head of a slot at most `s` is accepted before the freeze** by an honest
slot-`(s+1)` voter whose `Σ.F` it extends: its voter accepted it (or it is genesis) by
`t_m + Δ ≤ t_s + Δ`, and `Sync` relays the acceptance (from `t_{s₀}` on; an earlier one by
`hold`) to the voter, awake since its last restart at or before `t_s`, by `t_s + 2Δ`. -/
private theorem honest_head_accepted (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s₀ : Nat} {b : Time} (hservice : SleepyWindow tr H ΔF s₀ b ∨ SleepyServiceBefore tr H ΔF b)
    {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {e' : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e')
    (hs' : e'.msg.slot ≤ s) {Hd : SA.Blk sp.n (List (FG.Att sp.n))}
    (hHd : Hd ∈ tr.HonestBlocks H) (hHdr : Hd.root = e'.msg.head)
    (hFHd : Anc (tr.HonestBlocks H) ℓ.frame.F Hd) :
    SA.AcceptedBefore tr.projAC y Hd (sp.ts s + 3 * sp.Δ) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓ', hcx, hex⟩ := hv
  -- the head is in its voter's tree, and the vote is cast by `t_m + Δ ≤ t_s + Δ`
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hkt⟩ := cast_head_fcRoot hr hx ⟨hcx, hex⟩
  rw [frame_of_projAC hrun hx hcx] at hHd't
  obtain rfl : Hd = Hd' :=
    ((projFG_localRun hrun hnc).coherent.1 ⟨x, hx, k, hHd't.1⟩ hHd (hHd'r.trans hHdr.symm)).symm
  have hkt' : tr.time k ≤ sp.ts s + sp.Δ := by
    have h1 : tr.time k ≤ sp.ts (e'.msg.slot : Int) + sp.Δ := hkt
    have h2 : sp.ts (e'.msg.slot : Int) ≤ sp.ts (s : Int) := by
      unfold SAParams.ts
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs') (mul_nonneg (by norm_num) hΔ.le)
    exact h1.trans (add_le_add h2 le_rfl)
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hrs' : ∀ c ≤ i, tr.RestartAt y c → tr.time c ≤ sp.ts s := fun c hc' ⟨ℓr, hcr, hrr⟩ =>
    hrs c hc' ⟨ℓr, projAC_callAt.2 hcr, hrr⟩
  -- its voter accepted it (or it is genesis)
  have hHdx := hHd't.1
  rw [← store_eq hrun hx k] at hHdx
  rcases Store.tree_accepted (projFG_localRun hrun hnc) hx hHdx with hg | ⟨m, hm, hA⟩
  · exact Or.inl (by rw [hg]; rfl)
  have hmt : tr.time m ≤ sp.ts s + sp.Δ := (hrun.time_mono hm.le).trans hkt'
  have hFy : Anc (tr.HonestBlocks H) (tr.state y i).fg.F Hd := by
    rw [frame_of_projAC hrun hy hc.1] at hFHd; exact hFHd
  have hdl : ∀ c ≤ i, tr.deadline y c (tr.time m) sp.Δ ≤ sp.ts s + 2 * sp.Δ := fun c hc' => by
    have := deadline_le_of_restarts (fun k hk hr' => hrs' k (hk.trans hc') hr') (tr.time m) sp.Δ
    refine this.trans ?_
    rw [two_mul, ← add_assoc]
    exact add_le_add (max_le hmt (le_add_of_nonneg_right hΔ.le)) le_rfl
  -- `Sync` relays the acceptance to `y` before `t_s + 2Δ`
  by_cases hm₀ : sp.ts s₀ ≤ tr.time m
  swap
  · exact hold x hx m Hd (projFG_callAt.1 hA) (not_le.1 hm₀) hFHd
  have hdi : tr.deadline y i (tr.time m) sp.Δ ≤ tr.time i :=
    (hdl i le_rfl).trans ((add_mul_delta_le (by norm_num)).trans hti)
  have delivered := hservice.elim
    (fun hwin => (sleepyWindow_iff.1 hwin).2.1.relay x hx m Hd
      (projFG_callAt.1 hA) ⟨hm₀, le_sub_iff_add_le.2 ((add_le_add hmt le_rfl).trans (by
        rw [add_assoc, ← two_mul]; exact (add_mul_delta_le (by norm_num)).trans (hti.trans hib)))⟩
      y hy i ⟨_, projAC_callAt.1 hc.1⟩ hdi hFy)
    (fun hsync => hsync.relay x hx m Hd (projFG_callAt.1 hA) (hrun.time_nonneg m)
      y hy i ⟨_, projAC_callAt.1 hc.1⟩ (hdi.trans hib) hdi hFy)
  obtain ⟨k', hk'i, hAy, hk't⟩ := delivered
  obtain ⟨ℓy, hcy, hby, hty⟩ := accept_next hrun.toLocalRun hy hAy
  have hk't' : tr.time k' < tr.deadline y k' (tr.time m) sp.Δ := hk't
  have := hdl k' hk'i
  exact Or.inr ⟨k' + 1, ⟨ℓy, projAC_callAt.2 hcy, hby⟩, by
    change tr.time (k' + 1) < _; rw [hty]
    exact hk't'.trans_le (this.trans (add_mul_delta_le (by norm_num)))⟩

/-- The emissions of `ac_on_tick` are made at `t_σ + Δ` only. -/
private theorem acOnTick_emits {self : Fin sp.n} {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {t : Time} {e : SA.Em sp (List (FG.Att sp.n))}
    (he : e ∈ (SA.acOnTick sp self A Φ t).2) : t = sp.ts (sp.slot t) + sp.Δ := by
  unfold SA.acOnTick at he
  dsimp only at he
  split_ifs at he <;> first | assumption | simp at he

/-- **The calls that cast an honest vote**: a tick at `t_σ + Δ`, a block or a message; never a
restart, `ac_proposal` or `ac_to_fg`. -/
theorem honest_vote_call (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e) :
    (ℓ.call = .tick → tr.time i = sp.ts (sp.slot (tr.time i)) + sp.Δ) ∧ ℓ.call ≠ .proposal ∧
      ℓ.call ≠ .toFG ∧ ℓ.call ≠ .restart := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hx := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at hx
  have he' : e ∈ ((SA.goldilocksSA sp _ ro).step y (tr.projAC.state y i) ℓ.frame
      (tr.projAC.time i) ℓ.call).2 := by rw [hx]; exact hc.2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at he'
  · exact acOnTick_emits (self := y) (A := tr.projAC.state y i) (Φ := ℓ.frame) he'
  · simp [ACInterface.step] at he'
  · simp [ACInterface.step] at he'
  · change e ∈ (SA.acRestart sp ro y _ ℓ.frame _).2 at he'
    rw [((SA.restart_state sp) _ ro y _ ℓ.frame _ hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- **A block accepted before the freeze is in the voter block tree** of an honest
slot-`(s+1)` vote whose `Σ.F` it extends: it is in the voter's frame, and its stamp at the read
point is below `t_s + 3Δ` (the voter's restarts were before, and this call does not receive
it). -/
theorem accepted_voter_tree (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXU : X ∈ tr.HonestBlocks H) (hacc : SA.AcceptedBefore tr.projAC y X (sp.ts s + 3 * sp.Δ))
    (hFX : Anc (tr.HonestBlocks H) ℓ.frame.F X) :
    X ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hT : sp.ts s + 3 * sp.Δ < tr.projAC.time i := by
    change sp.ts s + 3 * sp.Δ < tr.time i
    exact (add_mul_delta_lt (by norm_num)).trans_le hti
  -- in the voter's frame
  obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy _ _ hc.1
  have hXt : X ∈ ℓ.frame.tree := by
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · obtain rfl : X = G := hU.1 hXU hGU (hg.trans hGr.symm)
      obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFX
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
    · have hki : k ≤ i := by
        by_contra h
        have := hr.time_mono (le_of_not_ge h)
        exact lt_irrefl _ (hT.trans (this.trans_lt hkt))
      exact SA.mem_tree_of_acceptAt sp hr hy hk hki hc.1 hFX
  -- its stamp before the call is below the freeze
  have hbs := SA.blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hXt hacc
    (fun k hk hrk => lt_of_le_of_lt (hrs k hk hrk)
      (lt_add_of_pos_right _ (mul_pos (by norm_num) hΔ))) (Or.inl hT.le)
  -- the call does not receive `X`, so the read point keeps that stamp
  have hne : ∀ B, ℓ.call = .block B → X.root ≠ B.root := by
    intro B hcall hXB
    have hai : tr.projAC.AcceptAt y i B := ⟨ℓ, hc.1, hcall⟩
    obtain rfl : B = X := hΦ.coherent.1 ((SA.accept_new sp hr hy hai).1 ℓ hc.1) hXt hXB.symm
    rcases hacc with hg | ⟨k, hk, hkT⟩
    · exact SA.accept_ne_genesis sp hr hy hai hg
    · obtain rfl := SA.accept_unique sp hr hy hk hai
      exact absurd hkT (not_lt.2 hT.le)
  have hx := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at hx
  have hnr := (honest_vote_call hrun hnc hy hc).2.2.2
  have hrp : e.readPoint.blockStamp X.root = (tr.projAC.state y i).blockStamp X.root := by
    have h1 : (tr.projAC.post i).blockStamp = e.readPoint.blockStamp := by
      rw [SA.post_of_castAt hr hy hc, optimistic_stamp, SA.admitVote_blockStamp]
    have hp : tr.projAC.post i = ((SA.goldilocksSA sp _ ro).step y (tr.projAC.state y i)
        ℓ.frame (tr.projAC.time i) ℓ.call).1 := by rw [hx]
    obtain ⟨hblk, -, hoth⟩ :=
      SA.step_blockStamp_eq ro y (tr.projAC.state y i) hΦ (hr.time_nonneg i) ℓ.call
    rw [← h1, hp]
    by_cases hb : ∃ B, ℓ.call = .block B
    · obtain ⟨B, hB⟩ := hb
      rw [hblk B hB, Function.update_of_ne (hne B hB)]
    · rw [hoth (fun B h => hb ⟨B, h⟩) hnr]
  have hfz : SA.freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by simp [SA.freeze]
  exact ⟨hXt, Or.inl (by rw [hrp, hfz]; exact hbs)⟩

/-- **An honest head of a slot at most `s` is in the voter block tree** of an honest slot-`(s+1)`
vote (the frozen witness): it was accepted by its voter by `t_m + Δ ≤ t_s + Δ`
and relayed to `y` (joined, so awake since `t_s`, with `Σ.F` below it) before the freeze
`t_s + 3Δ`. -/
theorem honest_head_frozen (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s₀ : Nat} {b : Time} (hservice : SleepyWindow tr H ΔF s₀ b ∨ SleepyServiceBefore tr H ΔF b)
    {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H)
    {k : Nat} {e' : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e')
    (hs' : e'.msg.slot ≤ s) {Z : SA.Blk sp.n (List (FG.Att sp.n))}
    (hZ : SA.VoteExtends (tr.HonestBlocks H) e'.msg Z)
    (hFZ : Anc (tr.HonestBlocks H) ℓ.frame.F Z) :
    ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocks H) Z W := by
  obtain ⟨Hd, hHd, hHdr, hZHd⟩ := hZ
  have hFHd := hFZ.trans hZHd
  exact ⟨Hd, accepted_voter_tree hrun hnc hy hc hs hHd
    (honest_head_accepted hrun hnc hservice hy hc hs hib hold hx hv hs' hHd hHdr hFHd) hFHd, hZHd⟩

end Consensus.Goldilocks.Compose

end
