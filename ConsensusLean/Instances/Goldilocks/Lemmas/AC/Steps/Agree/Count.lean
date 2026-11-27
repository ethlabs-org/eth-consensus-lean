module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks AC: an honest voter counts every vote an honest proposal declares

For an honest proposer `p` of slot `s + 1` proposing at `t_{s+1}` and an honest voter `y`
casting its slot-`(s+1)` vote, under `Sync[t_s, t_{s+1}]`: every vote of `p`'s slot-`s` pool
(the declared head votes of the proposal) should be counted at the vote's read point
(`ShouldCountDeclaredVote`: `y` holds it, or two distinct votes of its validator). This is the
exact-or-pair condition at the cast that the merged view needs to reproduce the proposal's view.

* an **early** vote (before `t_{s+1} + Δ`) is ready, so it counts every declared vote of the
  slot's proposals (`voteReady`, `AllDeclaredVotesCounted`);
* a vote at **`t_{s+1} + Δ`**: the proposer admitted each such vote at a time in
  `[t_s, t_{s+1}]` and forwarded it, so `Sync` delivers it to `y` strictly before the vote, and
  admission leaves it, or a pair of its validator, in `y`'s pool (`sync_forwardU`); pools only
  grow up to the read point.

`count_declared_of_syncU`, and the service-window form
`count_declared_of_window_beforeU`. -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP}

private theorem admitVote_pool_sub (A : ACState sp.n) (t : Time) (v : Vote sp.n) (σ : Nat) :
    A.pool σ ⊆ (admitVote sp A t v).pool σ := by
  intro x hx
  unfold admitVote
  split_ifs
  · exact hx
  · exact hx
  · simp only [Function.update_apply]
    split_ifs with h
    · subst h; exact List.mem_append_left _ hx
    · exact hx

/-- The state before a cast's call holds no slot-`σ` vote that the read point lacks. -/
private theorem state_pool_sub_readPointU {ini} {u : Nat → Set Lock}
    (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksAC sp FGP)} {e : Em sp FGP} (hc : CastAt tr y j ℓ e) (σ : Nat) :
    (tr.state y j).pool σ ⊆ e.readPoint.pool σ := by
  obtain ⟨-, hR, -⟩ := voteBranchAt_inputU hr hy (voteBranchAt_of_castAtU hr hy hc)
  have hin : (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call).pool σ ⊆
      e.readPoint.pool σ := by
    rw [hR]
    split_ifs <;> exact fun _ h => h
  refine fun x hx => hin ?_
  have hopt := optimistic_pool_eq (sp := sp) (FGP := FGP)
  cases ℓ.call with
  | message m =>
    change x ∈ (optimisticConfirmation sp _ ℓ.frame (tr.time j)).pool σ
    rw [hopt]
    exact admitVote_pool_sub _ _ _ σ hx
  | block B =>
    change x ∈ (optimisticConfirmation sp _ ℓ.frame (tr.time j)).pool σ
    rw [hopt]
    exact hx
  | _ => exact hx

/-- The proposal's declared head votes are the proposer's slot-`s` pool. -/
private theorem mem_pay_of_pool {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {p : Fin sp.n} (hp : p ∈ H) {i s : Nat}
    {ℓp : ACLabel (goldilocksAC sp FGP)} {pay : Payload sp.n}
    (hprop : ProposalAt tr p i ℓp pay) (hsi : sp.slot (tr.time i) = s + 1) {v : Vote sp.n}
    (hv : v ∈ (tr.state p i).pool s) : v ∈ pay.1 := by
  obtain ⟨-, -, d, hd⟩ := hprop
  have hpay : pay = voteViewList (tr.state p i) ℓp.frame ((sp.slot (tr.time i) : Int) - 1) ⊤ := by
    unfold acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    exact hd.2.symm
  have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hpay, hsi, hcast]
  have hstamp : (tr.state p i).voteStamp v < ⊤ := by
    have hvs := state_pool_slotU sp hr hini hp i s v hv
    obtain ⟨k, -, -, h, -⟩ := pool_origin_sentU hr hini hp i v (hvs ▸ hv)
    exact h ▸ WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  simp [voteViewList, ACState.poolAt, hv, hstamp]

/-- The core: the early case from readiness, the timeout case from the delivery of the
proposer's forwarded admissions, given by `hdeliver` for the admissions inside `[t_s, t_{s+1}]`. -/
private theorem count_declared_coreU {ini} {u : Nat → Set Lock}
    (hr : ACLocalRunU wm u H U tr ini) (hini : ∀ y, VoteStart sp.genesisRoot (ini y))
    {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksAC sp FGP)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H) (hy : y ∈ H)
    (hprop : ProposalAt tr p i ℓp pay) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hc : CastAt tr y j ℓy e) (hes : e.msg.slot = s + 1)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    (hdeliver : ∀ k v, tr.SendOrAdmit p k v → sp.ts s ≤ tr.time k →
      tr.time k ≤ sp.ts (s + 1 : Nat) → v.slot = s →
      (∀ k' ≤ j, tr.RestartAt y k' → tr.time k' ≤ tr.time k) →
      tr.time k + sp.Δ ≤ tr.time j →
      v ∈ (tr.state y j).pool v.slot ∨ v.val ∈ equivocators {w | w ∈ (tr.state y j).pool v.slot}) :
    ∀ v ∈ (tr.state p i).pool s, ShouldCountDeclaredVote sp e.readPoint v := by
  intro v hv
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hsi : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; exact slot_of_mem sp (s + 1) le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  obtain ⟨-, hsl, hjoin, -⟩ := castAt_specU hr hy hc
  have hsj : sp.slot (tr.time j) = s + 1 := hsl ▸ hes
  have hb := voteBranchAt_of_castAtU hr hy hc
  obtain ⟨hcj, -, -, -, hlate, hready, -⟩ := voteBranchAt_iff.1 hb
  rw [hsj] at hlate hready
  obtain ⟨P, hPt, hPs, hPpay⟩ := hP
  by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
  · -- an early vote is ready: every declared vote of the slot's proposals is counted
    have hrd : voteReady sp e.readPoint ℓy.frame (s + 1) := by
      by_contra h
      exact hready ⟨hearly, Or.inr h⟩
    refine hrd.2 P hPt hPs v (Or.inl ?_)
    change v ∈ P.acPayload.1
    rw [hPpay]
    exact mem_pay_of_pool hr hini hp hprop hsi hv
  · -- the vote at `t_{s+1} + Δ`: the proposer's admission reached the voter
    have htj : tr.time j = sp.ts (s + 1 : Nat) + sp.Δ := le_antisymm hlate (not_lt.1 hearly)
    have hvs : v.slot = s := state_pool_slotU sp hr hini hp i s v hv
    obtain ⟨k, hki, hsend, -, hslk⟩ := pool_origin_sentU hr hini hp i v (hvs ▸ hv)
    · have htk : tr.time k ≤ tr.time i := hr.time_mono hki.le
      have hsk : sp.ts s ≤ tr.time k :=
        (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by rw [← hvs]; exact_mod_cast hslk)
      have hpost : joined sp (tr.post j) (tr.time j) := by
        unfold joined at hjoin ⊢
        rw [restartTime_of_castAtU hr hy hc]
        exact hjoin
      have hrsy : ∀ k' ≤ j, tr.RestartAt y k' → tr.time k' ≤ tr.time k := by
        intro k' hk' hr'
        have h := ((joined_awakeU sp) FGP H U tr hr y hy j ℓy hcj hpost).2 k' hk' hr'
        rw [hsj] at h
        have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
        rw [hcast] at h
        exact h.trans hsk
      have hheld := hdeliver k v hsend hsk (htk.trans hti.le) hvs hrsy
        (by rw [htj]; linarith only [htk, hti])
      rw [hvs] at hheld
      have hsub := state_pool_sub_readPointU hr hy hc s
      have hpa : e.readPoint.poolAt v.slot = e.readPoint.pool s := by
        simp [ACState.poolAt, hvs]
      exact backed_mono (P := {w | w ∈ (tr.state y j).pool s})
        (fun w (hw : w ∈ (tr.state y j).pool s) => hpa ▸ hsub hw) hheld

/-- **Every vote an honest proposal declares is counted at an honest slot-`(s+1)` vote** under
`Sync[t_s, t_{s+1}]` (with the unlock given). -/
theorem count_declared_of_syncU {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y))
    {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksAC sp FGP)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H) (hy : y ∈ H)
    (hprop : ProposalAt tr p i ℓp pay) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hc : CastAt tr y j ℓy e) (hes : e.msg.slot = s + 1)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    (hsync : SyncAC (goldilocksAC sp FGP) H U (sp.ts s) (sp.ts (s + 1 : Nat)) tr) :
    ∀ v ∈ (tr.state p i).pool s, ShouldCountDeclaredVote sp e.readPoint v := by
  refine count_declared_coreU hr hini hp hy hprop hti hc hes hP ?_
  intro k v hsend hsk hkb hvs hrs hdl
  exact sync_forwardU hr hsync hp hsend hsk hkb hy hc.1 hrs hdl (by
      rw [hvs]
      have hΔ := sp.toParams.hΔ
      have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      exact slot_window_of_forward (hr.time_nonneg k) hsk le_rfl (by linarith only [hkb, hts, hΔ]))

/-- **Every vote an honest proposal declares is counted at an honest slot-`(s+1)` vote** under
the source service window `[a, b]` with `a ≤ t_s` and the vote at or before `b` (with the unlock
given). -/
theorem count_declared_of_window_beforeU {ini} {u : Nat → Set Lock}
    (hr : ACLocalRunU wm u H U tr ini) (hini : ∀ y, VoteStart sp.genesisRoot (ini y))
    {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksAC sp FGP)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H) (hy : y ∈ H)
    (hprop : ProposalAt tr p i ℓp pay) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hc : CastAt tr y j ℓy e) (hes : e.msg.slot = s + 1)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    {a b : Time} (hsync : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    (hjb : tr.time j ≤ b) :
    ∀ v ∈ (tr.state p i).pool s, ShouldCountDeclaredVote sp e.readPoint v := by
  refine count_declared_coreU hr hini hp hy hprop hti hc hes hP ?_
  intro k v hsend hsk hkb hvs hrs hdl
  exact sync_window_before_forwardU hr hsync hp hsend (ha.trans hsk) (hdl.trans hjb) hy hc.1
    hrs hdl (by
      rw [hvs]
      have hΔ := sp.toParams.hΔ
      have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      exact slot_window_of_forward (hr.time_nonneg k) hsk le_rfl (by linarith only [hkb, hts, hΔ]))

end Consensus.Goldilocks.AC

end
