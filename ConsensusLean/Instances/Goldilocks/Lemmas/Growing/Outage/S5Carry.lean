module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the restored carry

At an honest slot-`(q+1)` vote of `y` at cut `i`, under receiver service from `g ≤ t_q + Δ`
(`ReceiverServiceAfterAt`: senders honest at the send, the receiver honest at its call):

* `honest_vote_restarts_at`: `y` has no restart after `t_q` up to `i`, and `t_q + 4Δ ≤ t_i`
  (the static `honest_vote_restarts` on the prefix through `t_i`);
* `honest_head_accepted_after_at`: the head of a vote of a slot at most `q`, by a node honest at
  its cast, above `y`'s `Σ.F`, is accepted by `y` before the freeze `t_q + 3Δ`: its voter accepted
  it at a cut at which it was honest, by `t_q + Δ`, and the relay serves `y`;
* `carryAt_after_at`: `Carry_y` for slot-`q` votes of nodes honest at their cast whose heads extend
  `y`'s `Σ.F`. The sends are served by the message service; what `y` holds is read on the prefix
  through `t_i`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A slot-`(s+1)` voter honest at its cut has no restart after `t_s`**, and votes from
`t_s + 4Δ`. -/
theorem honest_vote_restarts_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s : Nat} {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    (∀ c ≤ i, tr.projAC.RestartAt y c → tr.time c ≤ sp.ts s) ∧
      sp.ts s + 4 * sp.Δ ≤ tr.time i := by
  have hd := hrun.time_nonneg i
  have hc' : SA.CastAt (tr.upTo (tr.time i)).projAC y i ℓ e := by
    rw [RunTrace.upTo_projAC]; exact sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  obtain ⟨h1, h2⟩ := honest_vote_restarts (hrun.upTo hd) (hnc.upTo _) hy hc' hs
  refine ⟨fun c hci hrc => h1 c hci ?_, h2⟩
  rw [RunTrace.upTo_projAC]
  exact (ac_restartAt_upTo _).mpr ⟨hrun.time_mono hci, hrc⟩

/-- **An honest head of a slot at most `q` is accepted by `y` before the freeze `t_q + 3Δ`**,
under receiver service from `g ≤ t_q + Δ`, at a slot-`(q+1)` vote of `y` honest at its cut whose
`Σ.F` the head extends: its voter, honest at its cast, accepted it at a cut no later than the
cast (or it is genesis), by `t_q + Δ`, and `y`, joined (so with no restart after `t_q`), receives
it by `max(τ, g) + Δ ≤ t_q + 2Δ`. -/
theorem honest_head_accepted_after_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {q : Nat} (hg : g ≤ sp.ts q + sp.Δ) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = q + 1) {x : Fin sp.n} {k : Nat}
    {e' : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x k e') (hs' : e'.msg.slot ≤ q)
    {Hd : SA.Blk sp.n (List (FG.Att sp.n))} (hHd : Hd ∈ tr.HonestBlocksAt H)
    (hHdr : Hd.root = e'.msg.head) (hFHd : Anc (tr.HonestBlocksAt H) ℓ.frame.F Hd) :
    SA.AcceptedBefore tr.projAC y Hd (sp.ts q + 3 * sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hxk, ℓ', hcx, hex⟩ := hVoteAt_iff.1 hv
  -- the head is in its voter's frame, and the vote is cast by `t_{slot} + Δ ≤ t_q + Δ`
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hkt⟩ := cast_head_fcRoot_at hrun hnc hxk ⟨hcx, hex⟩
  obtain rfl : Hd = Hd' :=
    (hU.1 ((frameIn_at hrun hnc hxk hcx).2 hHd't) hHd (hHd'r.trans hHdr.symm)).symm
  have hkt' : tr.time k ≤ sp.ts q + sp.Δ := by
    have h1 : tr.time k ≤ sp.ts (e'.msg.slot : Int) + sp.Δ := hkt
    have h2 := ts_le_ts (sp := sp) hs'
    linarith only [h1, h2]
  obtain ⟨hrs, hti⟩ := honest_vote_restarts_at hrun hnc hy hc hs
  -- its voter accepted it (or it is genesis), while honest
  rcases frame_anc_accepted_at hrun hnc hxk hcx hHd't .refl with hgen | ⟨m, hmk, hacc⟩
  · exact Or.inl hgen
  have hxm : x ∈ H (tr.time m) := hrun.antitone (hrun.time_mono hmk) hxk
  have hmt : tr.time m ≤ sp.ts q + sp.Δ := (hrun.time_mono hmk).trans hkt'
  have hdl : ∀ c ≤ i, tr.projAC.deadline y c (max (tr.projAC.time m) g) ≤
      sp.ts q + 2 * sp.Δ := fun c hc' => by
    have := Compose.ac_deadline_le_of_restarts (T := tr.projAC)
      (fun k hk hr' => hrs k (hk.trans hc') hr') (max (tr.projAC.time m) g)
    have h₁ : max (max (tr.projAC.time m) g) (sp.ts q) ≤ sp.ts q + sp.Δ :=
      max_le (max_le hmt hg) (le_add_of_nonneg_right hΔ.le)
    change tr.projAC.deadline y c _ ≤ max _ (sp.ts q) + sp.Δ at this
    linarith only [this, h₁]
  obtain ⟨k', hk'i, hAy, hk't⟩ := hS.relay x m Hd hxm hacc i ℓ hy hc.1
    (by have := hdl i le_rfl; change _ ≤ tr.time i; linarith only [this, hti, hΔ]) hFHd
  exact Or.inr ⟨k', hAy, by have := hdl k' hk'i; linarith only [this, hk't, hΔ]⟩

/-- **`Carry_y` after the outage's GST**: at a slot-`(s+1)` vote of `y` honest at its cut, under
receiver service from `g ≤ t_s + Δ`, `Carry_y(s, ·, ·)` holds for slot-`s` votes of nodes honest
at their cast whose heads extend `y`'s `Σ.F`: each is sent by its voter by `t_s + Δ` and its head
accepted by then, so `y` (joined, no restart after `t_s`) holds the vote and accepts the head and
its ancestors before `t_s + 3Δ`. -/
theorem carryAt_after_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} (hS : ReceiverServiceAfterAt H (tr.HonestBlocksAt H) g y tr.projAC)
    {s : Nat} (hg : g ≤ sp.ts s + sp.Δ) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hCV : ∀ v ∈ CV, ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg = v ∧ v.slot = s ∧
      ∃ Hv ∈ tr.HonestBlocksAt H, Hv.root = v.head ∧
        Anc (tr.HonestBlocksAt H) ℓ.frame.F Hv) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  have hd := hrun.time_nonneg i
  have hsub := upTo_subset hrun hd
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hm := hrun.time_mono
  -- the receiver's side is read on the prefix through `t_i`
  set T : ACTrace (SA.goldilocksSA sp (List (FG.Att sp.n)) ro) := tr.projAC.upTo (tr.time i)
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hcT : SA.CastAt T y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨-, -, hyj, -⟩ := castAt_spec_at hrun hnc hy hc
  obtain ⟨hrsy, hti⟩ := honest_vote_restarts_at hrun hnc hy hc hs
  have hrsyT : ∀ c ≤ i, T.RestartAt y c → T.time c ≤ sp.ts s := fun c hc' hrc =>
    hrsy c hc' ((ac_restartAt_upTo _).mp hrc).2
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k τ < sp.ts s + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := Compose.ac_deadline_le_of_restarts (T := tr.projAC)
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') τ
    have h₂ := max_lt hτ (show sp.ts s < sp.ts s + 2 * sp.Δ by linarith only [hΔ])
    change tr.projAC.deadline y k τ ≤ max τ (sp.ts s) + sp.Δ at h₁
    linarith only [h₁, h₂]
  obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy i ℓ hcT.1
  refine ⟨(hr.awake_of_call y hy i ℓ hcT.1).1, hyj, fun v hv => ?_, fun v hv => ?_⟩
  · -- the head and its ancestors are accepted before the freeze
    obtain ⟨x, k, e', hv', rfl, hvs, Hv, hHv, hHvr, hFHv⟩ := hCV _ hv
    refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
    rcases honest_head_accepted_after_at hrun hnc hS hg hy hc hs hv' hvs.le hHv hHvr hFHv with
      hgen | ⟨ky, ⟨ℓk, hck, hcall⟩, hkyt⟩
    · left
      obtain rfl : Hv = G := hU.1 hHv (hsub hGU) (hgen.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
      · exact hGr
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    -- `y` accepted `Hv` at a cut `ky ≤ i`, at which it was honest
    have hkyi : ky ≤ i := by
      by_contra h
      have := hm (le_of_not_ge h)
      change tr.time ky < _ at hkyt
      linarith only [this, hkyt, hti, hΔ]
    have hyk : y ∈ H (tr.time ky) := hrun.antitone (hm hkyi) hy
    have hdk := hrun.time_nonneg ky
    have hHvk : Hv ∈ ℓk.frame.tree :=
      (SA.accept_new sp (acRun_upTo hrun hnc hdk).localRun hyk
        ((ac_acceptAt_upTo _).mpr ⟨le_rfl, ℓk, hck, hcall⟩)).1 ℓk
        ((Trace.upTo_callAt_of_le _ le_rfl).mpr hck)
    rcases frame_anc_accepted_at hrun hnc hyk hck hHvk hX with hgen | ⟨k, hk, hkX⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨k, hkX, lt_of_le_of_lt (hm hk) hkyt⟩
  · -- the vote is held before the freeze
    obtain ⟨x, k, ev, hvk, hev, hvs, -⟩ := hCV v hv
    obtain ⟨hxk, ℓv, hcv, hevv⟩ := hVoteAt_iff.1 hvk
    have hsend : tr.projAC.SendOrAdmit x k v := ⟨ℓv, hcv, Or.inl ⟨ev, hevv, hev⟩⟩
    obtain ⟨hk1, hk2⟩ := hvk.ts_le_cast hrun hnc
    rw [hev, hvs] at hk1 hk2
    have hk1 : sp.ts s ≤ tr.projAC.time k := hk1
    have hk2 : tr.projAC.time k ≤ sp.ts s + sp.Δ := hk2
    have hmx : max (tr.projAC.time k) g < sp.ts s + 2 * sp.Δ :=
      max_lt (by linarith only [hk2, hΔ]) (by linarith only [hg, hΔ])
    obtain ⟨k', hk'i, hkk', hp, hk'dl⟩ := hS.message x k v hxk hsend i ℓ hy hc.1
      (by have := hdl i le_rfl _ hmx; change _ ≤ tr.time i; linarith only [this, hti, hΔ])
    have hk'lt : T.time k' < sp.ts s + 3 * sp.Δ := hk'dl.trans (hdl k' hk'i _ hmx)
    have hpT : T.ProcessAt y k' v := (ac_processAt_upTo _).mpr ⟨hm hk'i, hp⟩
    obtain ⟨ℓ', hc', -⟩ := id hpT
    have hnr : ∀ r, k' + 1 ≤ r → r < i + 1 → ¬ T.RestartAt y r := by
      rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
      obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
      have h₁ := hprev k' (by omega) ℓ' hc'
      have h₂ : T.time r ≤ sp.ts s := hrsyT r (by omega) ⟨ℓr, hcr, hrr⟩
      have hkk'' : sp.ts s ≤ T.time k' := hk1.trans hkk'
      linarith only [h₁, h₂, hu, hkk'']
    have hsk' : sp.slot (T.time k') = s :=
      SA.slot_of_mem sp s (hk1.trans hkk') (by rw [hts]; linarith only [hk'lt, hΔ])
    have hheld : ∀ u ∈ (T.state y (k' + 1)).pool s,
        SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) := by
      intro u hu
      have hus : u.slot = s := SA.state_pool_slot sp hr hy (k' + 1) s u hu
      obtain ⟨hpool, hstamp⟩ := Healing.readPoint_pool_of_ne hr hy hcT (σ := s) (by omega)
      have hu' := SA.pool_mono hr hy (show k' + 1 ≤ i + 1 by omega) hnr s hu
      refine ⟨by rw [hus, ← hpool]; exact hu', ?_⟩
      rw [← hstamp u hus]
      rcases SA.pool_origin hr hy (i + 1) u (by rw [hus]; exact hu') with
        ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
      · rw [hst₁, SA.etime_of_lt_of]
        by_cases hk₁k' : k₁ ≤ k'
        · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
        · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
          · have h := (cast_head_fcRoot hr hy ⟨hc₁, he₁⟩).2
            rw [hus] at h
            linarith only [h, hΔ]
          · exact absurd (SA.pool_mono hr hy (show k' + 1 ≤ k₁ by omega)
              (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hus]; exact hu)) hn₁
      · rw [hst₁, SA.etime_of_lt_of]
        have : T.time k₁ ≤ sp.ts s := hrsyT k₁ (by omega) ⟨ℓ₁, hc₁, hr₁⟩
        linarith only [this, hΔ]
    by_cases hv' : v ∈ (T.state y (k' + 1)).pool s
    · exact Or.inl (hheld v hv')
    · rcases SA.held_of_processAt hr hy hpT (by rw [hvs, hsk']; omega) (by rw [hvs, hsk']) with
        h | ⟨a, ha, c, hc'', hac, hav, hcv⟩
      · rw [hvs] at h
        exact absurd h hv'
      · have ha' : a ∈ (T.state y (k' + 1)).pool s := by rw [← hvs]; exact ha
        have hc' : c ∈ (T.state y (k' + 1)).pool s := by rw [← hvs]; exact hc''
        refine Or.inr ⟨a, c, hac, ?_, ?_, hav, hcv, SA.state_pool_slot sp hr hy _ s a ha',
          SA.state_pool_slot sp hr hy _ s c hc', hheld a ha', hheld c hc'⟩
        · rintro rfl; exact hv' ha'
        · rintro rfl; exact hv' hc'

end Consensus.Goldilocks.Compose.Growing

end
