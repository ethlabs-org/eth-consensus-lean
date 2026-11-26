module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Static
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeRunSchedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
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
    {m : AC.Vote (Fintype.card (Fin 5))}
    (hc : (tr S).MsgCallAt y k m) :
    ∃ (i : Nat) (w : Fin 5) (o : Obj S) (t : Time),
      (rhoc S).events[i]? = some (Model.Event.deliver w o t) ∧
        ∃ z, Model.Obj.Contains o (voteObj m z) := by
  obtain ⟨ℓ, ⟨_, hlab⟩, hcall⟩ := hc
  have hl : (tr S).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, _, _, he, _, _, hidx, _, _, _, hlab'⟩ :=
    simTrace_cut_origin { S with vote := stock } (rhoc S) one_le_card hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  rcases eq_deliver_of_cut { S with vote := stock } (rhoc S) one_le_card he hmem
      (Or.inr ⟨ℓ, m, hrl, hcall⟩) with ⟨v, o, t, rfl⟩ | ⟨v, t, -, htail⟩
  swap
  · obtain ⟨-, a, ha⟩ := tickTail_label { S with vote := stock } (rhoc S) one_le_card htail
    rw [hrl] at ha
    cases ha
  rw [eventCuts_deliver { S with vote := stock } (rhoc S) one_le_card i v o t he] at hmem
  obtain ⟨o', e, _, ho, hce, q, hq, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ _ hmem
  have hcut := List.getElem_mem hq
  rw [← hc, hrl] at hcut
  have heq : e = .message m := by
    cases e with
    | tick x fgDue => exact False.elim (canonEvent_ne_tick hce x fgDue rfl)
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
  have ho' : ∃ z, o' = voteObj m z := by
    rcases canonEvent_eq_some hce with ⟨_, h, _⟩ | ⟨m', z, h, hobj, _⟩ | ⟨_, h, _⟩
    · cases h
    · cases h; exact ⟨z, hobj⟩
    · cases h
  obtain ⟨z, rfl⟩ := ho'
  exact ⟨i, v, o, t, he, z, contains_of_mem_delivered ho⟩

/-- A block event of the retained trace processes a delivered block object. -/
theorem wire_block {y : Fin (Fintype.card (Fin 5))} {j : Nat} {t : Time}
    {B : Blk (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card)}
    (hg : (tr S).GroupAt (runProposer { S with vote := stock } (rhoc S) one_le_card)
        (digestOf { S with vote := stock } (rhoc S)) y j t
      (.block B)) :
    ∃ (i : Nat) (w : Fin 5) (o : Obj S), (rhoc S).events[i]? = some (Model.Event.deliver w o t) ∧
      Model.Obj.Contains o (blockObj (({ S with vote := AsChainShape.stock } : Setup).params
        (pubOf env) one_le_card) B) := by
  let S' := { S with vote := stock }
  let e := traceEncoding (E := env) S' one_le_card
  have htrace := (simTrace_encoding S' (rhoc S) one_le_card).1
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S' (rhoc S) one_le_card
  change (simTrace S' (rhoc S) one_le_card).GroupAt
    (runProposer S' (rhoc S) one_le_card) (digestOf S' (rhoc S)) y j t (.block B) at hg
  rw [htrace, hpr, hdg] at hg
  obtain ⟨i, ev, he, hlo, _, ht, r, hr, -, hnormal | hown⟩ :=
    NodeAsChainShape.CanonicalTrace.group_origin e (rhoc S) hg
  swap
  · obtain ⟨_, _, _, _, a, ha, -⟩ := hown.1
    cases ha
  have hphase := hnormal.2.1
  obtain ⟨hne, hcuts, _⟩ := hg
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨acc, hc⟩ := exec_block_head _ _ _ _ _ _ hcs
  have hl := (hcuts 0 (List.length_pos_of_ne_nil hne)).2.2.2.2
  have hlookup := NodeAsChainShape.CanonicalTrace.allCuts_getElem?_add e (rhoc S) i _
    (List.getElem?_eq_some_iff.mp he).1 (List.getElem?_eq_some_iff.mp hr).1
  rw [Nat.add_sub_cancel' hlo, hr] at hlookup
  rw [Nat.add_zero, NodeAsChainShape.CanonicalTrace.simTrace_label, hlookup, Option.map_some,
    Option.some.injEq, List.getElem_of_eq hcs] at hl
  cases ev with
  | tick v u => simp [Event.phase, Model.Event.phase] at hphase
  | restart v u => simp [Event.phase, Model.Event.phase] at hphase
  | deliver v o u =>
    obtain ⟨hobj, hcodec⟩ := blockView_encoding (E := env) S' one_le_card
    have hB := NodeAsChainShape.CanonicalTrace.blockObj_delivered e (rhoc S) he
      (List.mem_of_getElem? hr) (hl.trans hc) hcodec
    rw [hobj] at hB
    exact ⟨i, v, o, ht ▸ he, hB⟩

/-- **Where a processed block comes from**: a delivered object carrying it, or the node's own
release of it at the call's time. -/
theorem block_source {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) {k : Nat}
    {B : Blk (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card)}
    (hc : (tr S).BlockCallAt y k B) :
    (∃ (i : Nat) (w : Fin 5) (o : Obj S),
      (rhoc S).events[i]? = some (Model.Event.deliver w o ((tr S).time k)) ∧
      Model.Obj.Contains o (blockObj (({ S with vote := AsChainShape.stock } : Setup).params
        (pubOf env) one_le_card) B)) ∨
    (∃ i : Nat, (rhoc S).SendsAt ((rhoc S).key y) i ((tr S).time k) ∧
      blockObj (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card)
        B ∈ (rhoc S).releasesAt i) := by
  obtain ⟨acc, hcall⟩ := hc
  obtain ⟨j, e, k', hg, rfl, hk⟩ := Compose.call_in_group rhoc_run.toLocalRun hy hcall
  rcases Compose.exec_block _ _ _ _ _ _ hk with ⟨rfl, rfl⟩ | ⟨x, fgDue, rfl, rfl, -⟩
  · exact Or.inl (wire_block hg)
  have hpos : (tr S).pos (j + 2) ≠ 0 := by
    rw [(hg.2.1 2 (List.getElem?_eq_some_iff.mp hk).1).2.2.2.1]; omega
  have hown : (tr S).OwnBlockAt y (j + 2) B := ⟨⟨acc, hcall⟩, hpos⟩
  have hrel := (simTraceAt_simulates { S with vote := stock } (rhoc S) one_le_card
    rhoc_valid).block_released
  rw [simTraceAt_eq] at hrel
  obtain ⟨i, hs, ho⟩ := hrel y _ B (mem_Hg.mpr hy) hown
  exact Or.inr ⟨i, hs, ho⟩

/-! ### Honest trees up to `13` -/

/-- **Up to `13`, a non-genesis block of an honest tree is the twin's block.** -/
theorem tree_twin {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) {c : Nat}
    (hc : ∀ k < c, (tr S).time k ≤ 13)
    {B : Blk (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card)}
    (hB : B ∈ ((tr S).state y c).fg.tree)
    (hg : B.root ≠ (({ S with vote := AsChainShape.stock } : Setup).params
      (pubOf env) one_le_card).genesisRoot) :
    blockObj (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card)
      B = twin S := by
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
theorem headerOf_of_twin
    {B : Blk (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card)}
    (h : blockObj (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card)
      B = twin S) :
    headerOf (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card)
      B = hdr := by
  have := congrArg Model.Obj.msg h
  simp only [blockObj, twin, Model.Obj.msg] at this
  exact Model.Msg.item.inj this

/-! ### Votes of the faulty keys in honest pools -/

section ACStep
variable {sp : AC.ACParams} {FGP : Type} {ro : AC.ReplayOrder sp FGP}

theorem admitVote_pool_sub {A : AC.ACState sp.n} {t : Time} {v x : AC.Vote sp.n} {σ : Nat}
    (h : x ∈ (AC.admitVote sp A t v).pool σ) : x ∈ A.pool σ ∨ x = v := by
  unfold AC.admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hσ
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl (hσ ▸ h)
      · exact Or.inr (List.mem_singleton.mp h)
    · exact Or.inl h

theorem tryVote_pool_sub (self : Fin sp.n) {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP} {t : Time}
    {x : AC.Vote sp.n} {σ : Nat} (h : x ∈ (AC.tryVote sp self A Φ t).1.pool σ) :
    x ∈ A.pool σ ∨ x.val = self := by
  unfold AC.tryVote at h
  dsimp only at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  all_goals
    first
    | exact Or.inl h
    | rw [AC.optimistic_pool_eq] at h
      rcases admitVote_pool_sub h with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h])

/-- **A vote new in a pool after a call** is the received vote or the node's own (a block call
only stamps the block). -/
theorem step_pool_new (self : Fin sp.n) (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time)
    (c : (AC.goldilocksAC sp FGP ro).Call) (hc : c ≠ .restart) {x : AC.Vote sp.n} {σ : Nat}
    (h : x ∈ ((AC.goldilocksAC sp FGP ro).step self A Φ t c).1.pool σ) (hn : x ∉ A.pool σ) :
    c = .message x ∨ x.val = self := by
  cases c with
  | tick =>
    change x ∈ (AC.acOnTick sp self A Φ t).1.pool σ at h
    unfold AC.acOnTick at h
    dsimp only at h
    split_ifs at h
    all_goals first
      | exact absurd h hn
      | (rw [AC.updateConfirmation_pool_eq] at h
         rcases tryVote_pool_sub self h with h | h
         · exact absurd h hn
         · exact Or.inr h)
      | (rcases tryVote_pool_sub self h with h | h
         · exact absurd h hn
         · exact Or.inr h)
      | (rw [AC.updateConfirmation_pool_eq] at h; exact absurd h hn)
  | proposal =>
    change x ∈ (AC.acProposal sp A Φ t).1.pool σ at h
    unfold AC.acProposal at h
    split_ifs at h <;> exact absurd h hn
  | toFG =>
    change x ∈ (AC.acToFG sp A Φ t).1.pool σ at h
    unfold AC.acToFG at h
    split_ifs at h
    · split at h
      · exact absurd h hn
      · split_ifs at h <;> exact absurd h hn
    · exact absurd h hn
  | message m =>
    change x ∈ (AC.tryVote sp self (AC.optimisticConfirmation sp (AC.admitVote sp A t m) Φ t) Φ
      t).1.pool σ at h
    rcases tryVote_pool_sub self h with h | h
    · rw [AC.optimistic_pool_eq] at h
      rcases admitVote_pool_sub h with h | rfl
      · exact absurd h hn
      · exact Or.inl rfl
    · exact Or.inr h
  | block B =>
    change x ∈ (AC.tryVote sp self (AC.optimisticConfirmation sp (AC.blockReceipt sp A t B) Φ t) Φ
      t).1.pool σ at h
    rcases tryVote_pool_sub self h with h | h
    · rw [AC.optimistic_pool_eq] at h
      exact absurd h hn
    · exact Or.inr h
  | restart => exact absurd rfl hc

end ACStep

/-- No restart in the retained trace: everyone is awake throughout. -/
theorem no_restart {y : Fin (Fintype.card (Fin 5))} {k : Nat} : ¬ (tr S).RestartAt y k := by
  intro h
  obtain ⟨i, -, -, he⟩ := simTrace_restart_event { S with vote := stock } (rhoc S) one_le_card h
  have := (rhoc_valid.restart_at_wake _ _ (List.mem_of_getElem? he)).2
  simp [Wakes, env] at this

theorem val_faulty {x : AC.Vote (Fintype.card (Fin 5))} (h : x.val ∉ H S) :
    x.val = key 0 ∨ x.val = key 1 := by
  rw [mem_H] at h
  by_cases h0 : x.val.val = 0
  · exact Or.inl (Fin.ext h0)
  · exact Or.inr (Fin.ext (by by_contra h1; exact h ⟨h0, h1⟩))

/-- **The faulty keys' votes in honest pools**: a vote of key `0` or `1` in an honest pool is of
a slot up to `1`. -/
theorem pool_vote_slot {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) (c : Nat)
    {x : AC.Vote (Fintype.card (Fin 5))} (hx : x ∈ ((tr S).state y c).ac.pool x.slot)
    (hxH : x.val ∉ H S) : x.slot ≤ 1 := by
  have hac :=
    (Compose.goldilocks_ac_projection _ _ _ _ _ _ (rhoc_run (S := S)) rhoc_noColl).localRun
  rw [← Compose.projAC_state rhoc_run.toLocalRun hy] at hx
  rcases AC.pool_origin hac (fun _ => AC.voteStart_initial _) hy c x hx with
    ⟨k, -, ⟨ℓ, hc, hsa⟩, -, -⟩ | ⟨k, -, ℓ, hc, hrs, -⟩
  · rcases hsa with ⟨e, he, rfl⟩ | ⟨hnr, hpre, hpost⟩
    · exact absurd ((AC.castAt_spec hac hy ⟨hc, he⟩).1 ▸ hy) hxH
    · have hex := hac.exec k ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at hex
      change x ∈ ((tr S).projAC.post k).pool x.slot at hpost
      change x ∉ ((tr S).projAC.state y k).pool x.slot at hpre
      have hp := congrArg Prod.fst hex
      dsimp only at hp
      rw [← hp] at hpost
      rcases step_pool_new (ro := S.ro _) y ((tr S).projAC.state y k) ℓ.frame ((tr S).projAC.time k)
        ℓ.call hnr hpost hpre with hm | hval
      · obtain ⟨i, w, o, t, hi, z, hcont⟩ := msg_delivered ⟨ℓ, Compose.projAC_callAt.mp hc, hm⟩
        obtain ⟨i', hi'⟩ := rhoc_deliver hi
        exact delivered_vote hi' _ hcont x z rfl (val_faulty hxH)
      · exact absurd (hval ▸ hy) hxH
  · exact absurd ⟨ℓ, Compose.projAC_callAt.mp hc, hrs⟩ no_restart

end Consensus.Goldilocks.Test.ProposerHold

end
