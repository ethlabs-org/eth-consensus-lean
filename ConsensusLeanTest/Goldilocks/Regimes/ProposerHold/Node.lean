module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHold.Static
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import all ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
import all ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import all ConsensusLean.Lemmas.Model.Retain
@[expose] public section

/-! # The proposer-hold counterexample: honest trees and pools of the retained run

The engine provenance of the full run (`Engine`), read through the node trace of the retained run:

* `tree_twin`: up to time `13`, every non-genesis block of an honest tree is the
  forged twin's block;
* `pool_vote_slot`: every vote of key `0` or `1` in an honest pool is of slot `0` or
  `1`.

A block in an honest tree was accepted from a delivered object or proposed by the node (and then
released by it); a vote in an honest pool was admitted from a delivered vote object or block, or
is the node's own. Each source is an object of the full run, about which `Engine` speaks. -/

namespace Consensus.Goldilocks.Test.ProposerHold
open AsChainShape Shape Blocks Simulation Node
open Consensus.Model (pubOf)

variable {S : Setup}

/-! ### From the retained run to the full run -/

/-- A delivery of the retained run is one of the full run. -/
theorem rhoc_deliver {i : Nat} {w : Fin 5} {o : Obj S} {t : Time}
    (hi : (rhoc S).events[i]? = some (Model.Event.deliver w o t)) :
    ∃ i' : Nat, (rho S).events[i']? = some (Model.Event.deliver w o t) := by
  obtain ⟨i', hi', -, -⟩ := Model.Run.retain_getElem?_preimage hi
  exact ⟨i', hi'⟩

/-- A release of the retained run is one of the full run, by a node other than `0` and `1`. -/
theorem rhoc_release {i : Nat} {v : Fin 5} {o : Obj S} {t : Time} (hs : (rhoc S).SendsAt v i t)
    (ho : o ∈ (rhoc S).releasesAt i) :
    ∃ (i' : Nat) (e : Ev S), (rho S).events[i']? = some e ∧ e.node = v ∧ e.time = t ∧
      v ∉ ({0, 1} : Finset (Fin 5)) ∧
      o ∈ (rho S).releasesAt i' := by
  obtain ⟨e, he, hn, ht⟩ := hs.exists_event
  obtain ⟨i', hi', rfl, hk⟩ := Model.Run.retain_getElem?_preimage he
  rw [Model.Run.retain_releasesAt hi' hk] at ho
  rw [rho_faultyAt, faulty_of_ge (by norm_num)] at hk
  exact ⟨i', e, hi', hn, ht, hn ▸ hk, ho⟩

/-! ### From node calls to engine objects -/

/-- An AC message call of the retained trace processes a delivered vote object. -/
theorem msg_delivered {y : Fin (Fintype.card (Fin 5))} {k : Nat}
    {m : SA.Vote (Fintype.card (Fin 5))}
    (hc : (tr S).MsgCallAt y k m) :
    ∃ (i : Nat) (w : Fin 5) (o : Obj S) (t : Time),
      (rhoc S).events[i]? = some (Model.Event.deliver w o t) ∧
        Model.Obj.Contains o (voteObj m) := by
  obtain ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ := hc
  have hl : (tr S).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, _, _, _, hlab'⟩ :=
    simTrace_cut S (rhoc S) one_le_card hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  obtain ⟨v, o, t, rfl⟩ :=
    eq_deliver_of_cut S (rhoc S) one_le_card he hmem (Or.inr ⟨ℓ, m, hrl, hcall⟩)
  rw [eventCuts_deliver S (rhoc S) one_le_card i v o t he] at hmem
  obtain ⟨o', e, st', ho, hce, q, hq, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
  have hcut := List.getElem_mem hq
  rw [← hc, hrl] at hcut
  have heq : e = .message m := by
    cases e with
    | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
    | message m' =>
      simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq]
        at hcut
      subst ℓ
      cases hcall
      rfl
    | block B =>
      simp only [exec, onBlock] at hcut
      split_ifs at hcut
      · simp at hcut
      · split at hcut <;> simp [acCall] at hcut
        subst ℓ
        cases hcall
    | attestation => simp [exec, onAttestation] at hcut
    | restart =>
      simp only [exec, Node.restart, acCall, List.mem_singleton, Cut.ac.injEq] at hcut
      subst ℓ
      cases hcall
  subst e
  have ho' : o' = voteObj m := by
    rcases canonEvent_eq_some hce with ⟨_, h, _⟩ | ⟨m', h, ho⟩ | ⟨_, h, _⟩
    · cases h
    · cases h; exact ho
    · cases h
  subst o'
  exact ⟨i, v, o, t, he, contains_of_mem_delivered ho⟩

/-- A block event of the retained trace processes a delivered block object. -/
theorem wire_block {y : Fin (Fintype.card (Fin 5))} {j : Nat} {t : Time}
    {B : Blk (S.params (pubOf env) one_le_card)}
    (hg : (tr S).GroupAt (runProposer S (rhoc S) one_le_card) (digestOf S (rhoc S)) y j t
      (.block B)) :
    ∃ (i : Nat) (w : Fin 5) (o : Obj S), (rhoc S).events[i]? = some (Model.Event.deliver w o t) ∧
      Model.Obj.Contains o (blockObj (S.params (pubOf env) one_le_card) B) := by
  obtain ⟨r, i, ev, he, hstart, _, hidx, hpos, _, het, hphase⟩ :=
    groupAt_start S (rhoc S) one_le_card hg
  obtain ⟨hne, hcuts, _⟩ := hg
  obtain ⟨_, _, _, _, hl⟩ := hcuts 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hl
  have hr : (allCuts S (rhoc S) one_le_card)[j]? = some r := by
    have h := allCuts_getElem?_add S (rhoc S) one_le_card i (j - cutMap S (rhoc S) one_le_card i)
      (List.getElem?_eq_some_iff.mp he).1 (List.getElem?_eq_some_iff.mp hidx).1
    rw [Nat.add_sub_cancel' hstart, hidx] at h
    exact h
  cases ev with
  | tick v t' => simp [Event.phase, Model.Event.phase] at hphase
  | restart v t' => simp [Event.phase, Model.Event.phase] at hphase
  | deliver v o t' =>
    have hrmem := List.mem_of_getElem? hidx
    rw [eventCuts_deliver S (rhoc S) one_le_card i v o t' he] at hrmem
    have hrlabel : (tr S).label j = some r.label := by
      rw [simTrace_label, hr]
      rfl
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    rw [hrlabel, Option.some.injEq, List.getElem_of_eq hcs] at hl
    obtain ⟨acc, hc⟩ : ∃ acc, c = .fg (.block B acc) := by
      simp only [exec, onBlock] at hcs
      split_ifs at hcs
      cases hfg : ((tr S).state y j).fg.onBlock B <;> simp only [hfg, List.cons.injEq] at hcs
      · exact ⟨false, hcs.1.symm⟩
      · exact ⟨true, hcs.1.symm⟩
    have hB := delivery_block_authorized _ _ _ _ _ _
      (fun B => blockObj (S.params (pubOf env) one_le_card) B ∈
        delivered (S.params (pubOf env) one_le_card) o) _ _ _
      (fun x hx B' hxB => hxB ▸ hx) r hrmem hpos B acc (hl.trans hc)
    change t' = t at het
    subst het
    exact ⟨i, v, o, he, contains_of_mem_delivered hB⟩

/-- **Where a processed block comes from**: a delivered object carrying it, or the node's own
release of it at the call's time. -/
theorem block_source {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) {k : Nat}
    {B : Blk (S.params (pubOf env) one_le_card)} (hc : (tr S).BlockCallAt y k B) :
    (∃ (i : Nat) (w : Fin 5) (o : Obj S),
      (rhoc S).events[i]? = some (Model.Event.deliver w o ((tr S).time k)) ∧
      Model.Obj.Contains o (blockObj (S.params (pubOf env) one_le_card) B)) ∨
    (∃ i : Nat, (rhoc S).SendsAt ((rhoc S).key y) i ((tr S).time k) ∧
      blockObj (S.params (pubOf env) one_le_card) B ∈ (rhoc S).releasesAt i) := by
  obtain ⟨acc, hcall⟩ := hc
  obtain ⟨j, e, k', hg, rfl, hk⟩ := Compose.call_in_group rhoc_run.toLocalRun hy hcall
  rcases Compose.exec_block _ _ _ _ _ _ hk with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl, -⟩
  · exact Or.inl (wire_block hg)
  have hpos : (tr S).pos (j + 2) ≠ 0 := by
    rw [(hg.2.1 2 (List.getElem?_eq_some_iff.mp hk).1).2.2.2.1]; omega
  have hown : (tr S).OwnBlockAt y (j + 2) B := ⟨⟨acc, hcall⟩, hpos⟩
  obtain ⟨i, hs, ho⟩ :=
    (simTrace_simulates S (rhoc S) one_le_card rhoc_const rhoc_valid).block_released y hy _ B hown
  exact Or.inr ⟨i, hs, ho⟩

/-! ### Honest trees up to `13` -/

/-- **Up to `13`, a non-genesis block of an honest tree is the twin's block.** -/
theorem tree_twin {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) {c : Nat}
    (hc : ∀ k < c, (tr S).time k ≤ 13) {B : Blk (S.params (pubOf env) one_le_card)}
    (hB : B ∈ ((tr S).state y c).fg.tree)
    (hg : B.root ≠ (S.params (pubOf env) one_le_card).genesisRoot) :
    blockObj (S.params (pubOf env) one_le_card) B = twin S := by
  rcases Compose.tree_cases rhoc_run.toLocalRun hy hB with rfl | ⟨k, hk, hacc⟩
  · exact absurd rfl hg
  have htk := hc k hk
  rcases block_source hy ⟨true, hacc⟩ with ⟨i, w, o, hi, hcont⟩ | ⟨i, hs, ho⟩
  · obtain ⟨i', hi'⟩ := rhoc_deliver hi
    exact delivered_proposal hi' htk _ hcont _ _ rfl
  · obtain ⟨i', e, hi', hn, ht, hv, ho'⟩ := rhoc_release hs ho
    refine early_closed i' ⟨e, hi', ht ▸ htk, delay_eq_zero ?_⟩ _ ho' _
      (Model.Obj.Contains.refl _) _ _ rfl
    rintro ⟨h1, -⟩
    exact hv (by rw [← hn, h1]; simp)

/-- The twin's block has the forged header. -/
theorem headerOf_of_twin {B : Blk (S.params (pubOf env) one_le_card)}
    (h : blockObj (S.params (pubOf env) one_le_card) B = twin S) :
    headerOf (S.params (pubOf env) one_le_card) B = hdr := by
  have := congrArg Model.Obj.msg h
  simp only [blockObj, twin, Model.Obj.msg] at this
  exact Model.Msg.item.inj this

/-! ### Votes of the faulty keys in honest pools -/

section ACStep
variable {sp : SA.SAParams} {FGP : Type} {ro : SA.ReplayOrder sp FGP}

theorem admitVote_pool_sub {A : SA.SAState sp.n} {t : Time} {v x : SA.Vote sp.n} {σ : Nat}
    (h : x ∈ (SA.admitVote sp A t v).pool σ) : x ∈ A.pool σ ∨ x = v := by
  unfold SA.admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hσ
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (hσ ▸ h)
      · exact Or.inr (List.mem_singleton.mp h)
    · exact Or.inl h

theorem foldl_admitVote_pool_sub {t : Time} {x : SA.Vote sp.n} {σ : Nat} :
    ∀ (l : List (SA.Vote sp.n)) (A' : SA.SAState sp.n),
      x ∈ (l.foldl (fun A v => SA.admitVote sp A t v) A').pool σ → x ∈ A'.pool σ ∨ x ∈ l
  | [], _, h => Or.inl h
  | v :: l, A', h => by
    rcases foldl_admitVote_pool_sub l _ h with h | h
    · rcases admitVote_pool_sub h with h | rfl
      · exact Or.inl h
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem blockReceipt_pool_sub {A : SA.SAState sp.n} {t : Time} {B : SA.Blk sp.n FGP}
    {x : SA.Vote sp.n} {σ : Nat} (h : x ∈ (SA.blockReceipt sp A t B).pool σ) :
    x ∈ A.pool σ ∨ x ∈ SA.blockVotes B := by
  unfold SA.blockReceipt at h
  exact foldl_admitVote_pool_sub (SA.blockVotes B)
    { A with blockStamp := Function.update A.blockStamp B.root (SA.ETime.of t) } h

theorem tryVote_pool_sub (self : Fin sp.n) {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP} {t : Time}
    {x : SA.Vote sp.n} {σ : Nat} (h : x ∈ (SA.tryVote sp self A Φ t).1.pool σ) :
    x ∈ A.pool σ ∨ x.val = self := by
  unfold SA.tryVote at h
  dsimp only at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  all_goals
    rw [SA.optimistic_pool_eq] at h
    rcases admitVote_pool_sub h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h])

/-- **A vote new in a pool after a call** is the received vote, a vote of the received block, or
the node's own. -/
theorem step_pool_new (self : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time)
    (c : (SA.goldilocksSA sp FGP ro).Call) (hc : c ≠ .restart) {x : SA.Vote sp.n} {σ : Nat}
    (h : x ∈ ((SA.goldilocksSA sp FGP ro).step self A Φ t c).1.pool σ) (hn : x ∉ A.pool σ) :
    c = .message x ∨ (∃ B, c = .block B ∧ x ∈ SA.blockVotes B) ∨ x.val = self := by
  cases c with
  | tick =>
    change x ∈ (SA.acOnTick sp self A Φ t).1.pool σ at h
    unfold SA.acOnTick at h
    dsimp only at h
    split_ifs at h
    all_goals first
      | exact absurd h hn
      | (rw [SA.updateConfirmation_pool_eq] at h
         rcases tryVote_pool_sub self h with h | h
         · exact absurd h hn
         · exact Or.inr (Or.inr h))
      | (rcases tryVote_pool_sub self h with h | h
         · exact absurd h hn
         · exact Or.inr (Or.inr h))
      | (rw [SA.updateConfirmation_pool_eq] at h; exact absurd h hn)
  | proposal =>
    change x ∈ (SA.acProposal sp A Φ t).1.pool σ at h
    unfold SA.acProposal at h
    split_ifs at h <;> exact absurd h hn
  | toFG =>
    change x ∈ (SA.acToFG sp A Φ t).1.pool σ at h
    unfold SA.acToFG at h
    split_ifs at h
    · split at h
      · exact absurd h hn
      · split_ifs at h <;> exact absurd h hn
    · exact absurd h hn
  | message m =>
    change x ∈ (SA.tryVote sp self (SA.optimisticConfirmation sp (SA.admitVote sp A t m) Φ t) Φ
      t).1.pool σ at h
    rcases tryVote_pool_sub self h with h | h
    · rw [SA.optimistic_pool_eq] at h
      rcases admitVote_pool_sub h with h | rfl
      · exact absurd h hn
      · exact Or.inl rfl
    · exact Or.inr (Or.inr h)
  | block B =>
    change x ∈ (SA.tryVote sp self (SA.optimisticConfirmation sp (SA.blockReceipt sp A t B) Φ t) Φ
      t).1.pool σ at h
    rcases tryVote_pool_sub self h with h | h
    · rw [SA.optimistic_pool_eq] at h
      rcases blockReceipt_pool_sub h with h | h
      · exact absurd h hn
      · exact Or.inr (Or.inl ⟨B, rfl, h⟩)
    · exact Or.inr (Or.inr h)
  | restart => exact absurd rfl hc

end ACStep

/-- No restart in the retained trace: everyone is awake throughout. -/
theorem no_restart {y : Fin (Fintype.card (Fin 5))} {k : Nat} : ¬ (tr S).RestartAt y k := by
  intro h
  obtain ⟨i, -, -, he⟩ := simTrace_restart_event S (rhoc S) one_le_card h
  have := (rhoc_valid.restart_at_wake _ _ (List.mem_of_getElem? he)).2
  simp [Wakes, env] at this

theorem val_faulty {x : SA.Vote (Fintype.card (Fin 5))} (h : x.val ∉ H S) :
    x.val = key 0 ∨ x.val = key 1 := by
  rw [mem_H] at h
  by_cases h0 : x.val.val = 0
  · exact Or.inl (Fin.ext h0)
  · exact Or.inr (Fin.ext (by by_contra h1; exact h ⟨h0, h1⟩))

theorem voteObj_mem_blockObj {B : Blk (S.params (pubOf env) one_le_card)}
    {x : SA.Vote (Fintype.card (Fin 5))} (hx : x ∈ SA.blockVotes B) :
    Model.Obj.Contains (blockObj (S.params (pubOf env) one_le_card) B) (voteObj x) :=
  Model.Obj.Contains.step
    (List.mem_append_right _ (List.mem_map.mpr ⟨x, List.mem_append_left _ hx, rfl⟩))
    (Model.Obj.Contains.refl _)

/-- **The faulty keys' votes in honest pools**: a vote of key `0` or `1` in an honest pool is of
a slot up to `1`. -/
theorem pool_vote_slot {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) (c : Nat)
    {x : SA.Vote (Fintype.card (Fin 5))} (hx : x ∈ ((tr S).state y c).ac.pool x.slot)
    (hxH : x.val ∉ H S) : x.slot ≤ 1 := by
  have hac :=
    (Compose.goldilocks_ac_projection _ _ _ _ _ _ (rhoc_run (S := S)) rhoc_noColl).localRun
  rw [← Compose.projAC_state rhoc_run.toLocalRun hy] at hx
  rcases SA.pool_origin hac hy c x hx with ⟨k, -, ⟨ℓ, hc, hsa⟩, -, -⟩ | ⟨k, -, ℓ, hc, hrs, -⟩
  · rcases hsa with ⟨e, he, rfl⟩ | ⟨hnr, hpre, hpost⟩
    · exact absurd ((SA.castAt_spec hac hy ⟨hc, he⟩).1 ▸ hy) hxH
    · have hex := hac.exec k ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at hex
      change x ∈ ((tr S).projAC.post k).pool x.slot at hpost
      change x ∉ ((tr S).projAC.state y k).pool x.slot at hpre
      have hp := congrArg Prod.fst hex
      dsimp only at hp
      rw [← hp] at hpost
      rcases step_pool_new (ro := S.ro _) y ((tr S).projAC.state y k) ℓ.frame ((tr S).projAC.time k)
        ℓ.call hnr hpost hpre with hm | ⟨B, hB, hxB⟩ | hval
      · obtain ⟨i, w, o, t, hi, hcont⟩ := msg_delivered ⟨ℓ, Compose.projAC_callAt.mp hc, hm⟩
        obtain ⟨i', hi'⟩ := rhoc_deliver hi
        exact delivered_vote hi' _ hcont x rfl (val_faulty hxH)
      · obtain ⟨i', rfl, hacc, -⟩ :=
          Compose.acBlock_prev rhoc_run.toLocalRun hy (Compose.projAC_callAt.mp hc) hB
        have hvB := voteObj_mem_blockObj hxB
        rcases block_source hy ⟨true, hacc⟩ with ⟨i, w, o, hi, hcont⟩ | ⟨i, hs, ho⟩
        · obtain ⟨i'', hi''⟩ := rhoc_deliver hi
          exact delivered_vote hi'' _ (hcont.trans hvB) x rfl (val_faulty hxH)
        · obtain ⟨i'', e, hi'', -, -, -, ho'⟩ := rhoc_release hs ho
          exact released_vote i'' _ ho' _ hvB x rfl (val_faulty hxH)
      · exact absurd (hval ▸ hy) hxH
  · exact absurd ⟨ℓ, Compose.projAC_callAt.mp hc, hrs⟩ no_restart

end Consensus.Goldilocks.Test.ProposerHold

end
