module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import all ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import all ConsensusLean.Lemmas.Model.Retain
import all ConsensusLean.Lemmas.Model.Canonical.Inject
import all ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
@[expose] public section

/-! # The proposer-hold counterexample: the honest slot-`1` votes

Each of the honest nodes `2, 3, 4` of the retained run receives the forged twin at `13`, before
key `1`'s batch (held back until `14`). Its tree holds nothing else of a slot `≥ 1`
(`tree_twin`), so it accepts the twin's block (or holds it already) and votes on it at once: the
twin is a ready proposal of slot `1` and `13 < t_1 + Δ = 15` (`twin_vote`). One vote per slot
then puts every honest slot-`1` vote at a time `≤ 13` (`vote_time`), where the voter's tree is
genesis and the twin's block: every honest vote of a slot `≤ 1` has the head genesis or the
twin's block (`vote_head`). -/

namespace Consensus.Goldilocks.Test.ProposerHold
open AsChainShape Shape Blocks Simulation Node
open Consensus.Model (pubOf)

variable {S : Setup}

/-! ### The twin's block -/

variable (S) in
/-- The block the twin decodes to: digest `0`, parent genesis, slot `1`, proposer `1`, empty
payloads. -/
def twinBlk : Blk (S.params (pubOf env) one_le_card) :=
  blockOf (S.params (pubOf env) one_le_card) 0 hdr (key 1) [] ([], [])

theorem twin_parts : (twin S).parts = [twin S] := by
  rw [Model.Obj.parts_eq]; rfl

theorem twin_digests : Model.digests (rhoc S).hash (twin S) = [(hdr, 0)] := by
  unfold Model.digests
  rw [twin_parts]
  simp only [List.filterMap_cons, List.filterMap_nil, twin, Model.Obj.item?]
  simp only [Model.Run.retain_hash, rho_hash]
  change [(hdr, (if hdr = hdr then 0 else enc hdr + 1 : Nat))] = _
  simp only [↓reduceIte]

theorem twinBlk_header : headerOf (S.params (pubOf env) one_le_card) (twinBlk S) = hdr := by
  simp [twinBlk, blockOf, headerOf, hdr, parentRef, parentRoot, encodeInfo]

theorem twinBlk_obj : blockObj (S.params (pubOf env) one_le_card) (twinBlk S) = twin S := by
  rw [blockObj, twinBlk_header]; rfl

theorem canon_twin :
    canonEvent (S.params (pubOf env) one_le_card) (S.ro _)
      (Model.digests (rhoc S).hash (twin S)) (twin S) = some (.block (twinBlk S)) := by
  have h := decodeBlock_blockObj (binding := stock) [(hdr, 0)] (twinBlk S)
    (by simp [twinBlk, blockOf, hdr, parentRoot])
    (taggedRoot_ne _ _)
    (by rw [twinBlk_header]; simp [rootOf, twinBlk, blockOf, rawRoot_taggedRoot])
    (by simp [twinBlk, blockOf])
    ⟨by simp [twinBlk, blockOf, SA.blockVotes], by simp [twinBlk, blockOf, SA.blockSupport]⟩
  rw [twinBlk_obj] at h
  simp only [canonEvent, twin_digests, h]

theorem twinBlk_parent :
    (twinBlk S).parent = some (S.params (pubOf env) one_le_card).genesisRoot := rfl

theorem twinBlk_slot : (twinBlk S).slot = 1 := rfl

theorem twinBlk_root_ne :
    (twinBlk S).root ≠ (S.params (pubOf env) one_le_card).genesisRoot :=
  taggedRoot_ne _ _

/-- The block of the twin's object has slot `1`, proposer `1` and an empty payload. -/
theorem of_twin {X : Blk (S.params (pubOf env) one_le_card)}
    (h : blockObj (S.params (pubOf env) one_le_card) X = twin S) :
    X.slot = 1 ∧ SA.blockSupport X = [] ∧ X.proposer = key 1 := by
  have ha := congrArg Model.Obj.auth h
  have hc := congrArg Model.Obj.carried h
  simp only [blockObj, twin, Model.Obj.auth, Model.Obj.carried, payloadObjs] at ha hc
  have hc' := List.append_eq_nil_iff.mp hc
  injection ha with h1 h2
  injection h2 with h3
  exact ⟨h3, (List.append_eq_nil_iff.mp (List.map_eq_nil_iff.mp hc'.2)).2, h1⟩

/-! ### The twin's delivery -/

/-- Every honest node of the retained run receives the twin at `13`. -/
theorem twin_event {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) :
    ∃ i : Nat, (rhoc S).events[i]? = some (Model.Event.deliver ((rhoc S).key y) (twin S) 13) := by
  have hv : (rhoc S).key y ∉ ({0, 1} : Finset (Fin 5)) := by
    have := hy
    erw [mem_honestKeys_iff, rhoc_faultyAt] at this
    exact this
  have hρ : Model.Event.deliver ((rhoc S).key y) (twin S) 13 ∈ (rho S).events := by
    rw [rho_events]
    apply (base S).injectEvents_layer (delay S) (inj S) 13 (by norm_num) (by simp [base])
    rw [Model.Run.mem_injectLayer]
    refine Or.inr (Or.inr ⟨(rhoc S).key y, ?_, rfl, twin S, Or.inl ((mem_inj S).mpr ⟨rfl, rfl⟩),
      rfl⟩)
    change _ ∉ faulty 13
    rw [faulty_of_ge le_rfl]
    exact hv
  have hc : Model.Event.deliver ((rhoc S).key y) (twin S) 13 ∈ (rhoc S).events :=
    Model.Run.mem_retain_events.mpr ⟨hρ, by
      rw [rho_faultyAt, faulty_of_ge (by norm_num)]
      exact hv⟩
  exact List.mem_iff_getElem?.mp hc

/-! ### Acceptance of the twin's block -/

/-- `fg_on_block` accepts a new block with a held parent that extends `Σ.F` and passes the state
transition. -/
theorem onBlock_some {P : Params} {ACP : Type} {st : Store P ACP} {B : NodeBlock P ACP} {pr : Nat}
    (hp : B.parent = some pr) (hnew : st.blocks B.root = none) (hpar : (st.blocks pr).isSome)
    (hanc : Goldilocks.Anc (insert B st.tree) st.F B) {σ' : FG.ChainState P.n}
    (hσ : P.fg.stateTransition (st.σ pr) B.fgView = some σ') : ∃ st', st.onBlock B = some st' := by
  unfold Store.onBlock
  rw [hp]
  dsimp only
  split
  · rename_i h; simp [hnew, Option.isSome_iff_ne_none.mp hpar, hanc] at h
  · rw [hσ]
    exact ⟨_, rfl⟩

/-- The cuts of a run before a cut of a group at `13` are at times `≤ 13`. -/
theorem before_13 {j : Nat} (hj : (tr S).time j ≤ 13) : ∀ k < j, (tr S).time k ≤ 13 :=
  fun _k hk => (rhoc_run.time_mono hk.le).trans hj

/-- **The node accepts a twin's block by `13`**: when it receives the twin, it holds a non-genesis
block (one it accepted before, of the twin), or it accepts the twin's block now. -/
theorem group_accept {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) {j : Nat}
    (hg : (tr S).GroupAt (runProposer ⟨S, stock⟩ (rhoc S) one_le_card)
        (digestOf ⟨S, stock⟩ (rhoc S)) y j 13
      (.block (twinBlk S))) :
    ∃ k X, (tr S).AcceptAt y k X ∧
      blockObj (S.params (pubOf env) one_le_card) X = twin S ∧ (tr S).time k ≤ 13 := by
  obtain ⟨hne, hcuts, -⟩ := hg
  have hj13 : (tr S).time j = 13 := by simpa using (hcuts 0 (List.length_pos_of_ne_nil hne)).2.1
  have hc := before_13 hj13.le
  by_cases hX : ∃ X ∈ ((tr S).state y j).fg.tree,
      X.root ≠ (S.params (pubOf env) one_le_card).genesisRoot
  · obtain ⟨X, hX, hXg⟩ := hX
    rcases Compose.tree_cases rhoc_run.toLocalRun hy hX with rfl | ⟨k, hk, hacc⟩
    · exact absurd rfl hXg
    · exact ⟨k, X, hacc, tree_twin hy hc hX hXg, hc k hk⟩
  push Not at hX
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨acc, rfl⟩ : ∃ acc, c = .fg (.block (twinBlk S) acc) := by
    simp only [exec, onBlock] at hcs
    split_ifs at hcs
    cases hfg : ((tr S).state y j).fg.onBlock (twinBlk S) <;>
      simp only [hfg, List.cons.injEq] at hcs
    · exact ⟨false, hcs.1.symm⟩
    · exact ⟨true, hcs.1.symm⟩
  have hlab := (hcuts 0 (List.length_pos_of_ne_nil hne)).2.2.2.2
  rw [Nat.add_zero, List.getElem_of_eq hcs] at hlab
  have hcall : (tr S).CallAt y j (.fg (.block (twinBlk S) acc)) :=
    ⟨by simpa using (hcuts 0 (List.length_pos_of_ne_nil hne)).1, hlab⟩
  cases acc with
  | true => exact ⟨j, twinBlk S, hcall, twinBlk_obj, hj13.le⟩
  | false =>
    exfalso
    have hlaw := (rhoc_run.cutLaw y hy j _ hcall).1
    have hreach := Compose.fg_reachable rhoc_run.toLocalRun hy j
    obtain ⟨-, htc, hgm, -⟩ := Store.accepted_tree _ _ _ _ hreach
    have hF := (Store.cache_invariants _ _ _ _ hreach).1
    let st := ((tr S).state y j).fg
    have hFg : st.F = (S.params (pubOf env) one_le_card).toParams.genesisBlock
        (goldilocksNode (S.params (pubOf env) one_le_card) (S.ro _)).genesisPayload :=
      htc.1 hF hgm ((hX _ hF).trans rfl)
    obtain ⟨st', hst'⟩ := onBlock_some (st := st) twinBlk_parent
      (by
        by_contra hb
        obtain ⟨X, hXb⟩ := Option.ne_none_iff_exists'.mp hb
        have hXr := hreach.blocks_root hXb
        have hXt : X ∈ st.tree := by change st.blocks X.root = some X; rwa [hXr]
        exact twinBlk_root_ne (hXr ▸ hX X hXt))
      (Option.isSome_iff_exists.mpr ⟨_, hgm⟩)
      (by
        rw [hFg]
        exact Relation.ReflTransGen.single ⟨Set.mem_insert_of_mem _ hgm, Set.mem_insert _ _, rfl⟩)
      (σ' := (S.params (pubOf env) one_le_card).toParams.fg.heightEvents
        { (FG.ChainState.init (S.params (pubOf env) one_le_card).toParams.fg) with
            s := 1, L := (twinBlk S).root })
      (by
        rw [(Store.good hreach).σ_genesis]
        unfold FG.FGParams.stateTransition
        split
        · rfl
        · rename_i h
          exact absurd ⟨Nat.zero_lt_one, fun a ha => (List.not_mem_nil (a := a) ha).elim⟩ h)
    rw [hlaw] at hst'
    cases hst'

/-! ### The vote on a ready receipt -/

section Receipt
open SA
variable {sp : SAParams} {FGP : Type}

theorem rt_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote; split_ifs <;> rfl

theorem rt_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

theorem rt_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').restartTime = A'.restartTime from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => intro A'; simp only [List.foldl_cons]; rw [ih, rt_admitVote]

/-- `try_vote` on a receipt by `t_s + Δ` of a joined node that has not voted in slot `s > 0` and
holds a ready proposal of slot `s` casts a vote of slot `s`. -/
theorem tryVote_ready (x : Fin sp.n) {A : SAState sp.n} (Φ : Frm sp.n FGP) {t : Time}
    (hp : A.mayVote (sp.slot t) = true)
    (hj : joined sp A t) (hv : A.votedSlot ≠ sp.slot t) (ht : t ≤ sp.ts (sp.slot t) + sp.Δ)
    (hs : 0 < sp.slot t) (hr : voteReady sp Φ (sp.slot t)) :
    ∃ e ∈ (tryVote sp x A Φ t).2, e.msg.slot = sp.slot t := by
  rcases vs_tryVote x A Φ t hp with h | h
  · exfalso
    unfold tryVote at h; dsimp only at h
    simp only [hp, ite_true] at h
    split_ifs at h with h1 h2
    · rcases h1 with h1 | h1 | h1
      · exact h1 hj
      · exact hv h1
      · linarith
    · rcases h2.2 with h2 | h2
      · omega
      · exact h2 hr
    all_goals simp at h
  · exact h.2

end Receipt

theorem slot_int {t : Time} (ht : 0 ≤ t) :
    ((S.params (pubOf env) one_le_card).slot t : Int) = t / 12 := by
  rw [SA.slot_eq _ ht]; rfl

theorem slot_one {t : Time} (h12 : 12 ≤ t) (h13 : t ≤ 13) :
    (S.params (pubOf env) one_le_card).slot t = 1 := by
  have h : ((S.params (pubOf env) one_le_card).slot t : Int) = 1 := by
    rw [slot_int (le_trans (by norm_num) h12)]
    dsimp only [Time] at *
    omega
  exact_mod_cast h

/-- **An honest node votes in slot `1` by `13` once it accepts the twin's block by `13`**: at the
AC block call after the acceptance, it has voted in slot `1` already, or it votes now (the twin's
block, or its `Σ.F`, is a ready proposal of slot `1`). -/
theorem accept_vote {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) {k : Nat}
    {X : Blk (S.params (pubOf env) one_le_card)} (hacc : (tr S).AcceptAt y k X)
    (hX : blockObj (S.params (pubOf env) one_le_card) X = twin S) (hk : (tr S).time k ≤ 13) :
    ∃ j e, SA.VoteAt (tr S).projAC y j e ∧ e.msg.slot = 1 ∧ (tr S).time j ≤ 13 := by
  have hac :=
    (Compose.goldilocks_ac_projection _ _ _ _ _ _ (rhoc_run (S := S)) rhoc_noColl).localRun
  obtain ⟨hXs, hX1, hXp⟩ := of_twin hX
  obtain ⟨hsl, hon, -, -⟩ := rhoc_run.cutLaw y hy k _ hacc
  obtain ⟨ℓ, hcℓ, hcall, ht⟩ := Compose.accept_next rhoc_run.toLocalRun hy hacc
  have hpost : (tr S).state y (k + 1) = (tr S).post k := by
    simp only [Trace.state]; exact ite_eq_left ⟨hacc.1, by rw [hacc.2]; simp⟩
  have hreach := Compose.fg_reachable rhoc_run.toLocalRun hy k
  have hXt : X ∈ ((tr S).state y (k + 1)).fg.tree := by
    rw [hpost, (Store.tree_grows _ _ _ _ hreach).1 X _ hon]
    exact Set.mem_insert _ _
  have h12 : 12 ≤ (tr S).time k := by
    have h0 := (rhoc_run (S := S)).time_nonneg k
    have := slot_int (S := S) h0
    change X.slot ≤ (S.params (pubOf env) one_le_card).slot _ at hsl
    rw [hXs] at hsl
    have h1 : (1 : Int) ≤ (tr S).time k / 12 := by rw [← this]; exact_mod_cast hsl
    dsimp only [Time] at *
    omega
  have hs1 : (S.params (pubOf env) one_le_card).slot ((tr S).time (k + 1)) = 1 :=
    slot_one (by rw [ht]; exact h12) (by rw [ht]; exact hk)
  have hcAC : (tr S).projAC.CallAt y (k + 1) ℓ := Compose.projAC_callAt.mpr hcℓ
  obtain ⟨hfr, hstep, -, -⟩ := rhoc_run.cutLaw y hy (k + 1) _ hcℓ
  have hreach1 := Compose.fg_reachable rhoc_run.toLocalRun hy (k + 1)
  have hc13 : ∀ c < k + 1, (tr S).time c ≤ 13 := fun c hc =>
    ((rhoc_run (S := S)).time_mono (Nat.lt_succ_iff.mp hc)).trans hk
  have hAC := Compose.projAC_state rhoc_run.toLocalRun hy (k + 1)
  by_cases hv : ((tr S).state y (k + 1)).ac.votedSlot = 1
  · obtain ⟨j, hj, e, he, hes⟩ :=
      (SA.cast_of_votedSlot hac (fun _ => SA.voteStart_initial _) hy (k + 1) 1
        (by rw [hAC]; exact hv)).resolve_right
        (by rw [SA.trace_mayVote_stock hac hy (k + 1)]; decide)
    exact ⟨j, e, he, hes, ((rhoc_run (S := S)).time_mono hj.le).trans (ht ▸ hk)⟩
  -- the frame holds a ready proposal of slot `1`: the twin's block, or `Σ.F`
  have hready : SA.voteReady (S.params (pubOf env) one_le_card)
      (Node.frame ((tr S).state y (k + 1))) 1 := by
    obtain ⟨-, htc, hgm, hanc⟩ := Store.accepted_tree _ _ _ _ hreach1
    have hF := (Store.cache_invariants _ _ _ _ hreach1).1
    by_cases hFg :
        ((tr S).state y (k + 1)).fg.F.root = (S.params (pubOf env) one_le_card).genesisRoot
    · refine ⟨X, ⟨hXt, ?_⟩, hXs, fun x hx => (List.not_mem_nil (hX1 ▸ hx)).elim⟩
      rw [htc.1 hF hgm (hFg.trans rfl)]
      exact hanc X hXt
    · obtain ⟨hFs, hF1, -⟩ := of_twin (tree_twin hy hc13 hF hFg)
      exact ⟨_, ⟨hF, .refl⟩, hFs, fun x hx => (List.not_mem_nil (hF1 ▸ hx)).elim⟩
  have hrt : ((tr S).state y (k + 1)).ac.restartTime = ⊥ := by
    rw [← hAC]
    rcases SA.restartTime_state hac hy (k + 1) with h | ⟨c, -, hrc, -⟩
    · exact h
    · exact absurd (Compose.projAC_restartAt.mp hrc) no_restart
  rw [hcall] at hstep
  have hem := congrArg Prod.snd hstep
  dsimp only at hem
  obtain ⟨e, he, hes⟩ := tryVote_ready y ℓ.frame (t := (tr S).time (k + 1))
    (A := SA.optimisticConfirmation _ (SA.blockReceipt _ ((tr S).state y (k + 1)).ac
      ((tr S).time (k + 1)) X) ℓ.frame ((tr S).time (k + 1)))
    (by rw [SA.optimisticConfirmation_mayVote, SA.blockReceipt_mayVote, ← hAC]
        exact SA.trace_mayVote_stock hac hy _ _)
    (by unfold SA.joined; rw [rt_optimistic, rt_blockReceipt, hrt]; exact bot_le)
    (by rw [SA.vs_optimistic, SA.vs_blockReceipt, hs1]; exact_mod_cast hv)
    (by rw [hs1, ht]; change _ ≤ (4 * 3 * 1 + 3 : Int); dsimp only [Time] at hk ⊢; omega)
    (by rw [hs1]; exact Nat.one_pos) (by rw [hs1, hfr]; exact hready)
  refine ⟨k + 1, e, ⟨ℓ, hcAC, ?_⟩, hes.trans hs1, ht ▸ hk⟩
  rw [← hem]
  exact he

/-- A delivery of one object is its event's group, or nothing (no event, or no cut). -/
theorem deliverSeq_single {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {tr : GoldilocksTrace sp ro}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {hs : List (Header Info × Nat)}
    {y : Fin sp.n} {t : Time} {o : Wire sp.n} {j j' : Nat}
    (h : DeliverSeq proposer tr dg hs y t [o] j j') :
    (∃ e, canonEvent sp ro hs o = some e ∧ tr.GroupAt proposer dg y j t e) ∨
      canonEvent sp ro hs o = none ∨
      ∃ e, canonEvent sp ro hs o = some e ∧
        (Node.exec proposer dg y (tr.state y j) t e).2 = [] := by
  cases h with
  | event e hce hg _ => exact Or.inl ⟨e, hce, hg⟩
  | drop hce _ => exact Or.inr (Or.inl hce)
  | noCut e hce hz _ => exact Or.inr (Or.inr ⟨e, hce, hz⟩)

/-- **Every honest node votes in slot `1` by `13`**, on receiving the twin. -/
theorem twin_vote {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) :
    ∃ j e, SA.VoteAt (tr S).projAC y j e ∧ e.msg.slot = 1 ∧ (tr S).time j ≤ 13 := by
  obtain ⟨i, hi⟩ := twin_event hy
  have hd := (simTrace_simulates S (rhoc S) one_le_card rhoc_const rhoc_valid).deliver _
    ((mem_honestKeys_iff ⟨S, stock⟩ (rhoc S) y).mp hy) i _ _ hi
  rw [ownKey_key ⟨S, stock⟩ (rhoc S), show delivered (S.params (pubOf env) one_le_card) (twin S) =
      [twin S] from
    twin_parts] at hd
  rcases deliverSeq_single hd with ⟨e, hce, hg⟩ | hce | ⟨e, hce, hz⟩
  · erw [canon_twin] at hce
    cases hce
    obtain ⟨k, X, hacc, hX, hk⟩ := group_accept hy hg
    exact accept_vote hy hacc hX hk
  · erw [canon_twin] at hce
    cases hce
  · erw [canon_twin] at hce
    cases hce
    simp only [exec, onBlock] at hz
    split_ifs at hz with hfut
    · rw [twinBlk_slot] at hfut
      change (S.params (pubOf env) one_le_card).slot 13 < 1 at hfut
      rw [slot_one (by norm_num) (by norm_num)] at hfut
      omega
    · split at hz <;> exact absurd hz (List.cons_ne_nil _ _)

/-- **Every honest vote of a slot `≤ 1` is cast by `13`**: one of slot `0` before `12`, the one of
slot `1` is the vote on the twin (one vote per slot). -/
theorem vote_time {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) {j : Nat}
    {e : SA.Em (S.params (pubOf env) one_le_card)
      (List (FG.Att (S.params (pubOf env) one_le_card).n))}
    (hv : SA.VoteAt (tr S).projAC y j e) (hs : e.msg.slot ≤ 1) : (tr S).time j ≤ 13 := by
  have hac :=
    (Compose.goldilocks_ac_projection _ _ _ _ _ _ (rhoc_run (S := S)) rhoc_noColl).localRun
  obtain ⟨ℓ, hc, he⟩ := hv
  have hsl : e.msg.slot = (S.params (pubOf env) one_le_card).slot ((tr S).time j) :=
    (SA.castAt_spec hac hy ⟨hc, he⟩).2.1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h0 | h1
  · have h0' := slot_int (S := S) ((rhoc_run (S := S)).time_nonneg j)
    rw [← hsl, h0] at h0'
    have := (rhoc_run (S := S)).time_nonneg j
    dsimp only [Time] at *
    omega
  · obtain ⟨j', e', hv', hs', hj'⟩ := twin_vote hy
    obtain ⟨rfl, -⟩ := SA.one_vote_per_slot _ _ _ _ _ _ hac y hy j j' e e' ⟨ℓ, hc, he⟩ hv'
      (h1.trans hs'.symm)
    exact hj'

/-- **Every honest vote of a slot `≤ 1` has the head genesis or the twin's block**, a block of the
voter's tree. -/
theorem vote_head {y : Fin (Fintype.card (Fin 5))} (hy : y ∈ H S) {j : Nat}
    {e : SA.Em (S.params (pubOf env) one_le_card)
      (List (FG.Att (S.params (pubOf env) one_le_card).n))}
    (hv : SA.VoteAt (tr S).projAC y j e) (hs : e.msg.slot ≤ 1) :
    ∃ Hd ∈ ((tr S).state y j).fg.tree, Hd.root = e.msg.head ∧
      (Hd.root = (S.params (pubOf env) one_le_card).genesisRoot ∨
        blockObj (S.params (pubOf env) one_le_card) Hd = twin S) := by
  have hac :=
    (Compose.goldilocks_ac_projection _ _ _ _ _ _ (rhoc_run (S := S)) rhoc_noColl).localRun
  have hj := vote_time hy hv hs
  obtain ⟨ℓ, hc, he⟩ := hv
  obtain ⟨⟨Hd, hHd, hr, -⟩, -⟩ := Compose.cast_head_fcRoot hac hy ⟨hc, he⟩
  rw [Compose.frame_of_projAC rhoc_run hy hc] at hHd
  refine ⟨Hd, hHd.1, hr, ?_⟩
  by_cases hg : Hd.root = (S.params (pubOf env) one_le_card).genesisRoot
  · exact Or.inl hg
  · exact Or.inr (tree_twin hy (fun c hcj => ((rhoc_run (S := S)).time_mono hcj.le).trans hj)
      hHd.1 hg)

end Consensus.Goldilocks.Test.ProposerHold

end
