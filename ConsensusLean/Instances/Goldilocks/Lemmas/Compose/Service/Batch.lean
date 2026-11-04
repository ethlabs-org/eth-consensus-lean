module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the honest batch at an update

workbench#12 §4: when every honest slot-`s` vote names a block `P` of a joined updater's frame,
the honest slot-`s` votes reach the updater of slot `s`, held and resolved before `t_s + 2Δ`
(the update analogue of `honest_batch_carry`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

/-! ### One honest updater over an SA trace -/

section Node

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {T : SA.SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- The restarts of an honest node up to its update of slot `s` (joined) are at or before
`t_s`. -/
theorem update_restarts (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U T)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ s : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)}
    (hu : SA.UpdateAt T y k₀ s ℓ) : ∀ k ≤ k₀, T.RestartAt y k → T.time k ≤ sp.ts s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hts₂ : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have he := hr.exec k₀ ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at he
  have hpost : SA.joined sp (T.post k₀) (T.time k₀) := by
    have hp : T.post k₀ =
        ((SA.goldilocksSA sp FGP ro).step y (T.state y k₀) ℓ.frame (T.time k₀) ℓ.call).1 := by
      rw [he]
    unfold SA.joined at hj ⊢
    rw [hp, SA.step_restartTime y _ _ _ _ (by rw [hcall]; simp)]
    exact hj
  have hsl : sp.slot (T.time k₀) = s + 1 :=
    SA.slot_of_mem sp (s + 1) (by rw [ht, hts]; linarith) (by rw [ht, hts₂]; linarith)
  intro k hk hrk
  have := ((SA.joined_awake sp) FGP ro H U T hr y hy k₀ ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this

/-- **An honest slot-`s` vote at a joined updater of slot `s`**, under `Sync[a₀, t_s + 6Δ]` with
`a₀ ≤ t_s`: the vote, cast by `t_s + Δ` and forwarded, is processed by the updater (awake,
unrestarted since `t_s`) before `t_s + 2Δ` and admitted (its validator has no second slot-`s`
vote), so it is in the updater's pool with a stamp below `t_s + 2Δ`; its head `P`, above the
updater's `Φ.F` and of a slot at most `s`, was accepted by the voter before its vote (at or after
`a₀`, or it is genesis) and relayed to the updater before `t_s + 2Δ`, so it is in the updater's
frame and the vote is resolved before `t_s + 2Δ`. -/
private theorem honest_vote_at_update_of_sync (hrun : SA.ACRun proposer T H U)
    {a₀ : Time} {k₀ s : Nat}
    (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a₀ (T.time k₀) T ∨
      SA.ServiceBefore H U (sp.ts s + 2 * sp.Δ) T) {y : Fin sp.n} (hy : y ∈ H)
    {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt T y k₀ s ℓ)
    (ha₀ : a₀ ≤ sp.ts s) {P : SA.Blk sp.n FGP} (hPU : P ∈ U) (hFP : Anc U ℓ.frame.F P)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = s) (hhead : e.msg.head = P.root)
    (hPa : ∀ kx, T.AcceptAt x kx P → a₀ ≤ T.time kx) :
    P ∈ ℓ.frame.tree ∧ e.msg ∈ (T.state y k₀).pool s ∧
      SA.resolutionTime (T.state y k₀) ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hrsy := update_restarts hr hy hu
  obtain ⟨hcy, -, htk₀, -⟩ := hu
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt hr hy hcy
  -- delivery deadlines at the updater, for objects of times up to `t_s + Δ`
  have hdl : ∀ k ≤ k₀, ∀ τ, τ ≤ sp.ts s + sp.Δ → T.deadline y k τ ≤ sp.ts s + 2 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := ac_deadline_le_of_restarts (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') τ
    change T.deadline y k τ ≤ max τ (sp.ts s) + sp.Δ at h₁
    linarith [max_le hτ (show sp.ts s ≤ sp.ts s + sp.Δ by linarith)]
  obtain ⟨Hd₂, hHd₂, hHd₂r, hHd₂s⟩ := SA.honest_head hrun hx hv
  obtain ⟨ℓv, hcv, hev⟩ := hv
  obtain ⟨hxv, hxs, -, -⟩ := SA.castAt_spec hr hx ⟨hcv, hev⟩
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, htj⟩ := cast_head_fcRoot hr hx ⟨hcv, hev⟩
  rw [hes] at htj
  have hsj : sp.ts s ≤ T.time j := (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) s).2 (by omega)
  -- the vote is processed by the updater before `t_s + 2Δ`
  have hservice : SA.MessageServedBefore T y k₀ (T.time j) e.msg := by
    have hd : T.deadline y k₀ (T.time j) ≤ T.time k₀ := by
      rw [htk₀]; linarith [hdl k₀ le_rfl _ htj]
    rcases hsync with hs | hs
    · apply (SA.messageServedBefore_iff _ _ _ _).mpr
      exact Or.inl (hs.1 x hx j e.msg ⟨ℓv, hcv, Or.inl ⟨e, hev, rfl⟩⟩
        (ha₀.trans hsj) (by rw [htk₀]; linarith) y hy k₀ ℓ hcy hd)
    · exact hs.message x hx j e.msg ⟨ℓv, hcv, Or.inl ⟨e, hev, rfl⟩⟩
        (hr.time_nonneg j) y hy k₀ ℓ hcy (hdl k₀ le_rfl _ htj) hd
  have fresh : (∃ k' ≤ k₀, T.time j ≤ T.time k' ∧ T.ProcessAt y k' e.msg ∧
      T.time k' < T.deadline y k' (T.time j)) →
      e.msg ∈ (T.state y k₀).pool s ∧
        (T.state y k₀).voteStamp e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
    intro hdelivery
    obtain ⟨k', hk'k₀, hjk', hp, hk'dl⟩ := hdelivery
    have hk'lt : T.time k' < sp.ts s + 2 * sp.Δ := hk'dl.trans_le (hdl k' hk'k₀ _ htj)
    have hk'k₀' : k' < k₀ := lt_of_le_of_ne hk'k₀ (by rintro rfl; rw [htk₀] at hk'lt; linarith)
    have hsk' : sp.slot (T.time k') = s :=
      SA.slot_of_mem sp s (hsj.trans hjk') (by rw [hts]; linarith)
    have hnr : ∀ r, k' + 1 ≤ r → r < k₀ + 1 → ¬ T.RestartAt y r := by
      rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
      obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
      obtain ⟨ℓ', hc', -⟩ := hp
      have h₁ := hprev k' (by omega) ℓ' hc'
      have h₂ := hrsy r (by omega) ⟨ℓr, hcr, hrr⟩
      linarith
    have hpk' : e.msg ∈ (T.state y (k' + 1)).pool s := by
      rcases SA.held_of_processAt hr hy hp (by rw [hes, hsk']; omega) (by rw [hes, hsk']) with
        h | ⟨a, ha, b, hb, hab, hav, hbv⟩
      · rwa [hes] at h
      · rw [hes] at ha hb
        obtain ⟨ja, -, ea, hea, hea'⟩ :=
          hrun.honest.pool_vote y hy _ s a ha (by rw [hav, hxv]; exact hx)
        obtain ⟨jb, -, eb, heb, heb'⟩ :=
          hrun.honest.pool_vote y hy _ s b hb (by rw [hbv, hxv]; exact hx)
        rw [hav, hxv] at hea
        rw [hbv, hxv] at heb
        obtain ⟨-, rfl⟩ := SA.one_vote_per_slot sp FGP ro H U T hr x hx ja jb ea eb hea heb
          (by rw [hea', heb', SA.state_pool_slot sp hr hy _ s a ha,
            SA.state_pool_slot sp hr hy _ s b hb])
        exact absurd (hea'.symm.trans heb') hab
    have hpool : e.msg ∈ (T.state y k₀).pool s :=
      SA.pool_mono hr hy (show k' + 1 ≤ k₀ by omega) (fun r h₁ h₂ => hnr r h₁ (by omega)) s hpk'
    refine ⟨hpool, ?_⟩
    rcases SA.pool_origin hr hy k₀ e.msg (by rw [hes]; exact hpool) with
      ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
    · rw [hst₁, SA.etime_of_lt_of]
      by_cases hk₁k' : k₁ ≤ k'
      · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
      · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, he₁m⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
        · have h := (cast_head_fcRoot hr hy ⟨hc₁, he₁⟩).2
          rw [he₁m, hes] at h
          linarith
        · exact absurd (SA.pool_mono hr hy (show k' + 1 ≤ k₁ by omega)
            (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hes]; exact hpk')) hn₁
    · rw [hst₁, SA.etime_of_lt_of]
      linarith [hrsy k₁ hk₁.le ⟨ℓ₁, hc₁, hr₁⟩]
  have held : e.msg ∈ (T.state y k₀).pool s ∧
      (T.state y k₀).voteStamp e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
    rcases (SA.messageServedBefore_iff _ _ _ _).mp hservice with hfresh | hretained
    · exact fresh hfresh
    have hevidence := (hretained.evidence hr hy).weaken (hdl k₀ le_rfl _ htj)
    rcases (SA.poolEvidenceBefore_iff _ _ _).mp hevidence with
      hv | ⟨a, b, hab, hav, hbv, has, hbs, ha, hb⟩
    · exact ⟨hes ▸ hv.1, hv.2⟩
    · obtain ⟨ja, -, ea, hea, hea'⟩ :=
        hrun.honest.pool_vote y hy _ a.slot a ha.1 (by rw [hav, hxv]; exact hx)
      obtain ⟨jb, -, eb, heb, heb'⟩ :=
        hrun.honest.pool_vote y hy _ b.slot b hb.1 (by rw [hbv, hxv]; exact hx)
      rw [hav, hxv] at hea
      rw [hbv, hxv] at heb
      obtain ⟨-, rfl⟩ := SA.one_vote_per_slot sp FGP ro H U T hr x hx ja jb ea eb hea heb
        (by rw [hea', heb', has, hbs])
      exact (hab (hea'.symm.trans heb')).elim
  obtain ⟨hpool, hvst⟩ := held
  -- the head: accepted by the voter before its vote, relayed to the updater before `t_s + 2Δ`
  have hHdP : Hd = P := hU.1 ((SA.frameIn_of_callAt hr hx hcv).2 hHd) hPU (hHdr.trans hhead)
  have hacc : SA.AcceptedBefore T y P (sp.ts s + 2 * sp.Δ) ∧ P ∈ ℓ.frame.tree := by
    rcases frame_anc_accepted hr hx j ℓv hcv P (hHdP ▸ hHd) P .refl with hg | ⟨kx, hkx, hax⟩
    · refine ⟨Or.inl hg, ?_⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy k₀ ℓ hcy
      obtain rfl : P = G := hU.1 hPU hGU (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFP with h | ⟨Q, -, hQ⟩
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    · have hkxt : T.time kx ≤ sp.ts s + sp.Δ := (hr.time_mono hkx).trans htj
      have hrelay : ∃ ky ≤ k₀, T.AcceptAt y ky P ∧
          T.time ky < T.deadline y ky (T.time kx) := by
        have hd : T.deadline y k₀ (T.time kx) ≤ T.time k₀ := by
          rw [htk₀]; linarith [hdl k₀ le_rfl _ hkxt]
        rcases hsync with hs | hs
        · exact hs.2 x hx kx P hax (hPa kx hax)
            (by rw [htk₀]; linarith) y hy k₀ ℓ hcy hd hFP
        · exact hs.relay x hx kx P hax (hr.time_nonneg kx) y hy k₀ ℓ hcy
            (hdl k₀ le_rfl _ hkxt) hd hFP
      obtain ⟨ky, hky, hay, hkyt⟩ := hrelay
      exact ⟨Or.inr ⟨ky, hay, hkyt.trans_le (hdl ky hky _ hkxt)⟩,
        SA.mem_tree_of_acceptAt sp hr hy hay hky hcy hFP⟩
  obtain ⟨hacc, hPt⟩ := hacc
  have hbst := SA.blockStamp_lt_of_acceptedBefore sp hr hy hcy hPt hacc
    (fun k hk hrk => by linarith [hrsy k hk hrk]) (Or.inl (by rw [htk₀]; linarith))
  have hPs : P.slot ≤ e.msg.slot := by
    rw [hU.1 hHd₂ hPU (hHd₂r.trans hhead)] at hHd₂s
    exact hHd₂s
  refine ⟨hPt, hpool, ?_⟩
  unfold SA.resolutionTime
  rw [hhead, SA.lookup_of_mem hΦ hPt]
  dsimp only
  simp only [not_lt.2 hPs, ↓reduceIte]
  exact max_lt hvst hbst

/-- Honest votes reach a joined updater using service through `t_s + 2Δ` only: every delivery
the update counts has its deadline by then, so the update itself may be after `b`. -/
theorem honest_vote_at_update_early (hrun : SA.ACRun proposer T H U) {b : Time} {k₀ : Nat}
    {s : Nat} (hsync : SA.ServiceBefore H U b T) (hsb : sp.ts s + 2 * sp.Δ ≤ b) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt T y k₀ s ℓ)
    {P : SA.Blk sp.n FGP} (hPU : P ∈ U) (hFP : Anc U ℓ.frame.F P)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = s) (hhead : e.msg.head = P.root) :
    P ∈ ℓ.frame.tree ∧ e.msg ∈ (T.state y k₀).pool s ∧
      SA.resolutionTime (T.state y k₀) ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  apply honest_vote_at_update_of_sync (a₀ := 0) hrun (Or.inr {
    message := fun x hx k m hm h0 z hz i ℓ hc hd ht =>
      hsync.message x hx k m hm h0 z hz i ℓ hc (hd.trans hsb) ht
    relay := fun x hx k B hB h0 z hz i ℓ hc hd ht ha =>
      hsync.relay x hx k B hB h0 z hz i ℓ hc (hd.trans hsb) ht ha }) hy hu
    (by simp only [SAParams.ts]; positivity) hPU hFP hx hv hes hhead
  intro kx _
  exact hrun.localRun.time_nonneg kx

/-- Honest votes reach a joined updater using service through the update's time. -/
theorem honest_vote_at_update_before (hrun : SA.ACRun proposer T H U) {b : Time} {k₀ : Nat}
    (hsync : SA.ServiceBefore H U b T) (hb : T.time k₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    {s : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt T y k₀ s ℓ)
    {P : SA.Blk sp.n FGP} (hPU : P ∈ U) (hFP : Anc U ℓ.frame.F P)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = s) (hhead : e.msg.head = P.root) :
    P ∈ ℓ.frame.tree ∧ e.msg ∈ (T.state y k₀).pool s ∧
      SA.resolutionTime (T.state y k₀) ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  have ht : T.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  exact honest_vote_at_update_early hrun hsync (by linarith) hy hu hPU hFP hx hv hes hhead

/-- Whole-run service specializes the same updater argument. -/
theorem honest_vote_at_update (hrun : SA.ACRun proposer T H U) {a₀ : Time} {k₀ : Nat}
    (hsync : SyncAC (SA.goldilocksSA sp FGP ro) H U a₀ (T.time k₀) T) {y : Fin sp.n} (hy : y ∈ H)
    {s : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} (hu : SA.UpdateAt T y k₀ s ℓ)
    (ha₀ : a₀ ≤ sp.ts s) {P : SA.Blk sp.n FGP} (hPU : P ∈ U) (hFP : Anc U ℓ.frame.F P)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : SA.Em sp FGP} (hv : SA.VoteAt T x j e)
    (hes : e.msg.slot = s) (hhead : e.msg.head = P.root)
    (hPa : ∀ kx, T.AcceptAt x kx P → a₀ ≤ T.time kx) :
    P ∈ ℓ.frame.tree ∧ e.msg ∈ (T.state y k₀).pool s ∧
      SA.resolutionTime (T.state y k₀) ℓ.frame e.msg < SA.ETime.of (sp.ts s + 2 * sp.Δ) :=
  honest_vote_at_update_of_sync hrun (Or.inl hsync) hy hu ha₀ hPU hFP hx hv hes hhead hPa

end Node

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}

/-- The honest batch reaches the updater using only service through the bounded horizon. -/
theorem honest_batch_at_update_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {b : Time}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {y : Fin sp.n} (hy : y ∈ H) {k₀ s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k₀ s ℓ)
    (hb : tr.time k₀ ≤ b) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ℓ.frame.tree)
    (hall : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      e.msg ∈ (tr.projAC.state y k₀).pool s ∧
        SA.resolutionTime (tr.projAC.state y k₀) ℓ.frame e.msg <
          SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  intro x hx j e hv hes
  have hr := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr.localRun hy hu.1
  exact (honest_vote_at_update_before hr hsync hb hy hu (hΦU hPt)
    (Anc.mono hΦU (hΦ.rooted.2 P hPt)) hx hv hes (hall x hx j e hv hes)).2

end Consensus.Goldilocks.Compose

end
