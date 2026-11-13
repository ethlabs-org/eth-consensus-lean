module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ConfirmedBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: slot 0 on a run synchronous from the start

On a run healthy from the start (`g ≤ 0`, so `ḡ = 0`):

* no honest node restarts (`no_restart_of_sync_startU`): a restart follows a time `≥ 0` at which
  its node was asleep, and every honest node is awake from `0` on;
* every honest validator votes in every slot (`honest_votes_in_slot_of_sync_startU`), slot 0
  included (`honest_votes_slot_zeroU`);
* an honest vote of a slot `s` is retained at every honest call from `t_s + 2Δ` on, with a stamp
  before `t_s + 2Δ` (`vote_pool_of_sync_startU`), so at slot 0 from `2Δ` on
  (`slot_zero_vote_poolU`);
* with trivial frames, an honest slot-0 vote heads genesis (`slot_zero_vote_headU`), and a result
  of an honest update of slot 0 is genesis (`slot_zero_result_genesisU`), as is a saved slot-0
  result (`slot_zero_saved_genesisU`).

These are the forms of `honest_votes_in_slotU`, `late_vote_poolU` and `result_extendedU` without
their premise `t_s ≥ ḡ + 4Δ`, which those use only for `ḡ ≤ t_s` and for the restart bound. -/

namespace Consensus.Goldilocks.SA

variable {m : WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- A majority over a superset of `H` meets `H` when at most `|H|` validators are outside it
(`ConfirmedBase`'s private count). -/
private theorem exists_mem_of_majority {n : Nat} {H T W : Set (Fin n)} (hHW : H ⊆ W)
    (hTW : T ⊆ W) (hmaj : W.ncard < 2 * T.ncard) (hf : Hᶜ.ncard ≤ H.ncard) : ∃ u ∈ H, u ∈ T := by
  by_contra hno
  have hdisj : Disjoint H T := Set.disjoint_left.2 fun u hu huT => hno ⟨u, hu, huT⟩
  have h1 := Set.ncard_le_ncard (Set.union_subset hHW hTW)
  rw [Set.ncard_union_eq hdisj] at h1
  have h2 : T.ncard ≤ Hᶜ.ncard := Set.ncard_le_ncard fun u hu huH => hno ⟨u, huH, hu⟩
  omega

private theorem gbar_eq_zero (hg : g ≤ 0) : gbar g = 0 := max_eq_right hg

/-- **No honest restart** on a run healthy from the start. -/
theorem no_restart_of_sync_startU {u : Nat → Set Lock} (hS : HealthyBaseU m u tr H U proposer g)
    (hg : g ≤ 0) {y : Fin sp.n} (hy : y ∈ H) (k : Nat) : ¬ tr.RestartAt y k := by
  rintro ⟨ℓ, hc, hcall⟩
  obtain ⟨v, hv0, -, hna, -⟩ := hS.run.localRun.sleep_of_restart y hy k ℓ hc hcall
  exact hna (hS.awake hy (by rw [gbar_eq_zero hg]; exact hv0))

/-- The state of an honest node is joined at every time, on a run healthy from the start. -/
private theorem joined_of_sync_start {u : Nat → Set Lock} (hS : HealthyBaseU m u tr H U proposer g)
    (hg : g ≤ 0) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) (t : Time) :
    joined sp (tr.state y i) t := by
  unfold joined
  rcases restartTime_stateU hS.run.localRun hy i with h | ⟨k, -, hk, -⟩
  · rw [h]; exact bot_le
  · exact absurd hk (no_restart_of_sync_startU hS hg hy k)

/-- **Every honest validator votes in every slot**, on a run healthy from the start. -/
theorem honest_votes_in_slot_of_sync_startU {u : Nat → Set Lock}
    (hS : HealthyBaseU m u tr H U proposer g) (hg : g ≤ 0) (s : Nat) :
    ∀ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hm0 : (0 : Time) ≤ sp.ts s := by simp only [SAParams.ts]; positivity
  intro x hx
  have hslot : sp.slot (sp.ts s + sp.Δ) = s := by
    refine slot_of_mem sp s (by linarith) ?_
    rw [show sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ by simp only [SAParams.ts]; push_cast; ring]
    linarith
  obtain ⟨c, ℓ, hc, hcall, htc⟩ := hS.driven.tick x hx (sp.ts s + sp.Δ) (by linarith)
    ⟨4 * s + 1, by simp only [SAParams.ts]; ring⟩
    (hS.awake hx (by rw [gbar_eq_zero hg]; linarith))
  have hj := joined_of_sync_start hS hg hx c (tr.time c)
  by_cases hv : (tr.state x c).votedSlot = (sp.slot (tr.time c) : Int)
  · obtain ⟨j, -, e, he, hes⟩ := (cast_of_votedSlotU hr hx c _ hv).resolve_right
      (by rw [traceWithM_mayVote hr hx c]; decide)
    exact ⟨j, e, he, by rw [hes, htc, hslot]⟩
  · have hT : tr.time c = sp.ts (sp.slot (tr.time c)) + sp.Δ := by rw [htc, hslot]
    obtain ⟨e, hem, hes⟩ := tryVote_votesWith x ℓ.frame hj hv hT (traceWithM_mayVote hr hx c _)
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hx)
    rw [hc.1, hcall] at he
    have h2 : (acOnTickWithM sp m x (u c) (tr.state x c) ℓ.frame (tr.time c)).2 = ℓ.emits :=
      congrArg Prod.snd he
    have h3 : (acOnTickWithM sp m x (u c) (tr.state x c) ℓ.frame (tr.time c)).2 =
        (tryVoteWithM sp m x (u c) (tr.state x c) ℓ.frame (tr.time c)).2 := by
      unfold acOnTickWithM
      dsimp only
      split_ifs
      all_goals first | rfl | exact absurd hj ‹_›
    exact ⟨c, e, ⟨ℓ, hc, h2 ▸ h3 ▸ hem⟩, by rw [hes, htc, hslot]⟩

/-- **Every honest validator votes in slot 0**, on a run healthy from the start. -/
theorem honest_votes_slot_zeroU {u : Nat → Set Lock} (hS : HealthyBaseU m u tr H U proposer g)
    (hg : g ≤ 0) : ∀ x ∈ H, ∃ j e, VoteAt tr x j e ∧ e.msg.slot = 0 :=
  honest_votes_in_slot_of_sync_startU hS hg 0

/-- **An honest vote is retained**, on a run healthy from the start: at every honest call from
`t_s + 2Δ` on, before and after it, every honest slot-`s` vote is held with a stamp before
`t_s + 2Δ`. -/
theorem vote_pool_of_sync_startU {u : Nat → Set Lock} (hS : HealthyBaseU m u tr H U proposer g)
    (hg : g ≤ 0) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) {s : Nat} (ht : sp.ts s + 2 * sp.Δ ≤ tr.time j) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {e : Em sp FGP} (hv : VoteAt tr x i e) (hes : e.msg.slot = s) :
    ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool s ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hs : gbar g ≤ sp.ts s := by
    rw [gbar_eq_zero hg]; simp only [SAParams.ts]; positivity
  obtain ⟨ℓx, hcx, hex⟩ := hv
  obtain ⟨hval, hslx, -, -⟩ := castAt_specU hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts s + sp.Δ := by
    have := vote_time_leU hr hx ⟨ℓx, hcx, hex⟩
    rwa [← hslx, hes] at this
  have hti' : sp.ts s ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hslx, hes])
  have hgi : g ≤ tr.time i := (le_gbar g).trans (by linarith only [hs, hti'])
  have hmax : max (tr.time i) g = tr.time i := max_eq_left hgi
  have hdl : ∀ c, tr.deadline y c (tr.time i) ≤ tr.time i + sp.Δ := fun c =>
    (hS.deadline_le hy c _).trans (by rw [max_eq_left (by
        linarith only [hs, hti'] : gbar g ≤ tr.time i)])
  obtain ⟨k', hk'j, hik', hproc, hk'dl⟩ := hS.healthy.message x hx i e.msg
    ⟨ℓx, hcx, Or.inl ⟨e, hex, rfl⟩⟩ y hy j ℓ hc (by rw [hmax]; linarith only [hdl j, ht, hti])
  rw [hmax] at hk'dl
  have hk'T : tr.time k' < sp.ts s + 2 * sp.Δ := by linarith only [hdl k', hti, hk'dl]
  have hk'j' : k' < j := lt_of_le_of_ne hk'j (by rintro rfl; linarith only [hk'T, ht])
  have hsl' : sp.slot (tr.time k') = s :=
    slot_of_mem sp s (by linarith only [hti', hik']) (by
        rw [SA.ts_succ]; linarith only [hti, hti', hk'T])
  have hxH : e.msg.val ∈ H := hval ▸ hx
  have hheld : e.msg ∈ (tr.state y (k' + 1)).pool s := by
    rcases held_of_processAtU hr hy hproc (by rw [hsl', hes]; omega) (by rw [hsl', hes]) with
      h | ⟨a, ha, b, hb, hab, hav, hbv⟩
    · rwa [hes] at h
    · exfalso
      rw [hes] at ha hb
      obtain ⟨ja, -, ea, hva, rfl⟩ := hS.run.honest.pool_vote y hy (k' + 1) s _ ha (hav ▸ hxH)
      obtain ⟨jb, -, eb, hvb, rfl⟩ := hS.run.honest.pool_vote y hy (k' + 1) s _ hb (hbv ▸ hxH)
      have hsa := state_pool_slotU sp hr hy (k' + 1) s _ ha
      have hsb := state_pool_slotU sp hr hy (k' + 1) s _ hb
      rw [hav] at hva
      rw [hbv] at hvb
      obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hr _ hxH ja jb ea eb hva hvb
        (hsa.trans hsb.symm)
      exact hab rfl
  intro c hcj
  have hst := stamp_lt_of_heldU hS hy (a := k' + 1) (b := c) (by omega) (w := e.msg)
    (by rw [hes]; exact hheld) (T := sp.ts s + 2 * sp.Δ)
    (fun k hk => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk)) hk'T)
    (by rw [hes]; linarith only [hti', hk'T, hik', hΔ]) (by
        linarith only [hs, hΔ]) fun k _ _ hrk => no_restart_of_sync_startU hS hg hy k hrk
  rwa [hes] at hst

/-- **An honest slot-0 vote is retained** at every honest call from `2Δ` on, before and after
the call, with a stamp before `2Δ`, on a run healthy from the start. -/
theorem slot_zero_vote_poolU {u : Nat → Set Lock} (hS : HealthyBaseU m u tr H U proposer g)
    (hg : g ≤ 0) {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (ht : 2 * sp.Δ ≤ tr.time j) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {e : Em sp FGP} (hv : VoteAt tr x i e) (hes : e.msg.slot = 0) :
    ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool 0 ∧
      (tr.state y c).voteStamp e.msg < ETime.of (2 * sp.Δ) := by
  have h0 : sp.ts ((0 : Nat) : Int) = 0 := by simp [SAParams.ts]
  intro c hcj
  have := vote_pool_of_sync_startU hS hg hy hc (s := 0) (by rw [h0]; linarith) hx hv hes c hcj
  rwa [h0, zero_add] at this

/-- **An honest slot-0 vote heads genesis**: its head is a block of its voter's frame of slot
`0`, and the frame is rooted at genesis with slots increasing along it. -/
theorem slot_zero_vote_headU {u : Nat → Set Lock} (hS : StandaloneRunU m u tr H U proposer g)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP} (hv : VoteAt tr x i e)
    (hes : e.msg.slot = 0) : e.msg.head = sp.genesisRoot := by
  have hr := hS.run.localRun
  obtain ⟨ℓ, hc, he⟩ := hv
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hx hc
  obtain ⟨Hd, hHd, hHdr, hHds⟩ := honest_head_frameU hr hx ⟨hc, he⟩
  have hF := (hS.trivial x hx i ℓ hc).1
  have hFHd := (hΦ.rooted.2 Hd hHd).slot_le hΦ.coherent
  by_cases hne : ℓ.frame.F = Hd
  · rw [← hHdr, ← hne, hF]
  · have := hFHd.2 hne
    omega

/-- A block below a parentless block is that block. -/
private theorem eq_of_anc_parent_none {S : Set (Blk sp.n FGP)} {B G : Blk sp.n FGP}
    (h : Anc S B G) (hG : G.parent = none) : B = G := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨C, -, hCG⟩
  · exact h.symm
  · have := hCG.2.2
    rw [hG] at this
    cases this

/-- Below a block of `U` with root `genesisRoot` (through the honest node's genesis block, which
has no parent) is only that block. -/
theorem eq_of_anc_genesisU {u : Nat → Set Lock} (hr : ACLocalRunU m u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    {B X : Blk sp.n FGP} (hX : X ∈ U) (hXr : X.root = sp.genesisRoot) (h : Anc U B X) :
    B = X := by
  obtain ⟨G, hG, hGr, hGp⟩ := genesis_mem_of_callU sp hr hy i ℓ hc
  obtain rfl : X = G := hr.coherent.1 hX hG (hXr.trans hGr.symm)
  exact eq_of_anc_parent_none h hGp

/-- **A slot-0 result is genesis**, on a run synchronous from the start: at an honest call from
`2Δ` on, a block with a strict majority of the slot-0 voters has an honest supporter, whose vote
heads genesis. -/
theorem slot_zero_result_genesisU {u : Nat → Set Lock} (hS : StandaloneRunU m u tr H U proposer g)
    (hg : g ≤ 0) {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt x c ℓ) (ht : 2 * sp.Δ ≤ tr.time c) {C : Blk sp.n FGP}
    (hC : getConfirmation sp (tr.state x c) ℓ.frame 0 = some C) : C.root = sp.genesisRoot := by
  have hr := hS.run.localRun
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hc
  have hmaj := (deepest_mem hC).1.2.2
  unfold confirmationScore at hmaj
  dsimp only at hmaj
  have hHv : H ⊆ voters {v | v ∈ (tr.state x c).pool 0} := by
    intro w hw
    obtain ⟨j, e, hv, hes⟩ := honest_votes_slot_zeroU hS.toHealthyBaseU hg w hw
    obtain ⟨hval, -⟩ := castAt_specU hr hw ⟨hv.choose_spec.1, hv.choose_spec.2⟩
    exact ⟨e.msg, (slot_zero_vote_poolU hS.toHealthyBaseU hg hx hc ht hw hv hes c
      (Or.inl rfl)).1, hval⟩
  have hf : Hᶜ.ncard ≤ H.ncard := by
    have := hS.two_faulty_lt
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  obtain ⟨w, hwH, ⟨-, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hCR⟩⟩ := exists_mem_of_majority hHv
    (T := supporters ℓ.frame ⟨{v | v ∈ (tr.state x c).pool 0}, {v | v ∈ (tr.state x c).pool 0 ∧
      resolutionTime (tr.state x c) ℓ.frame v < ETime.of (sp.ts 0 + 2 * sp.Δ)}⟩ 0 C)
    (fun u ⟨_, x, hx, hxu, _⟩ => ⟨x, hx.1, hxu⟩) hmaj hf
  obtain ⟨j', -, e', hve, rfl⟩ := hS.run.honest.pool_vote x hx c 0 _ hvp hwH
  have hhead := slot_zero_vote_headU hS hwH hve (state_pool_slotU sp hr hx c 0 _ hvp)
  rw [hhead] at hRr
  rw [eq_of_anc_genesisU hr hx hc (hΦU hR) hRr (Anc.mono hΦU hCR)]
  exact hRr

/-- **A saved slot-0 result is genesis**, on a run synchronous from the start (none is
allowed): it is the result of the node's own update of slot 0, at `t_1 + 2Δ = 6Δ`. -/
theorem slot_zero_saved_genesisU {u : Nat → Set Lock} (hS : StandaloneRunU m u tr H U proposer g)
    (hg : g ≤ 0) {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {r : Nat}
    (hr : (tr.state y i).saved 0 = some r) : r = sp.genesisRoot := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨k, -, C, CV, ⟨ℓ, ⟨hc, -, ht, -⟩, hC, -⟩, rfl⟩ :=
    saved_resultU hS.run.localRun hy i 0 (by exact_mod_cast hr)
  exact slot_zero_result_genesisU hS hg hy hc
    (by rw [ht]; simp only [SAParams.ts]; push_cast; linarith) hC

end Consensus.Goldilocks.SA

end
