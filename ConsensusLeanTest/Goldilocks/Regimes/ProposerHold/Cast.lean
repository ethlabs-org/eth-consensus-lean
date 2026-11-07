module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHold.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import all ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import all ConsensusLean.Lemmas.Model.Retain
import all ConsensusLean.Lemmas.Model.Canonical.Inject
@[expose] public section

/-! # The proposer-hold counterexample: the honest slot-`1` votes (R-cast)

Each of the honest nodes `2, 3, 4` of the retained run receives the forged twin at `13`, before
key `1`'s batch (held back until `14`). Its tree holds nothing else of a slot `≥ 1` (R-tree), so it
accepts the twin's block (or holds it already) and votes on it at once: the twin is a ready
proposal of slot `1` and `13 < t_1 + Δ = 15` (`twin_vote`). One vote per slot then puts every
honest slot-`1` vote at a time `≤ 13` (`vote_time`), where the voter's tree is genesis and the
twin's block: every honest vote of a slot `≤ 1` has the head genesis or the twin's block
(`vote_head`). -/

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
  show [(hdr, (if hdr = hdr then 0 else enc hdr + 1 : Nat))] = _
  simp only [↓reduceIte]

theorem twinBlk_header : headerOf (S.params (pubOf env) one_le_card) (twinBlk S) = hdr := by
  simp [twinBlk, blockOf, headerOf, hdr, parentRef, parentRoot, encodeInfo]

theorem twinBlk_obj : blockObj (S.params (pubOf env) one_le_card) (twinBlk S) = twin S := by
  rw [blockObj, twinBlk_header]; rfl

theorem canon_twin :
    canonEvent (S.params (pubOf env) one_le_card) (S.ro _)
      (Model.digests (rhoc S).hash (twin S)) (twin S) = some (.block (twinBlk S)) := by
  have h := decodeBlock_blockObj [(hdr, 0)] (twinBlk S) (by simp [twinBlk, blockOf, hdr, parentRoot])
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
    rw [mem_honestKeys_iff, rhoc_faultyAt] at this
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
    (hg : (tr S).GroupAt (runProposer S (rhoc S) one_le_card) (digestOf S (rhoc S)) y j 13
      (.block (twinBlk S))) :
    ∃ k X, (tr S).AcceptAt y k X ∧
      blockObj (S.params (pubOf env) one_le_card) X = twin S ∧ (tr S).time k ≤ 13 := by
  obtain ⟨hne, hcuts, -⟩ := hg
  have hj13 : (tr S).time j = 13 := by simpa using (hcuts 0 (List.length_pos_of_ne_nil hne)).2.1
  have hc := before_13 hj13.le
  by_cases hX : ∃ X ∈ ((tr S).state y j).fg.tree, X.root ≠ (S.params (pubOf env) one_le_card).genesisRoot
  · obtain ⟨X, hX, hXg⟩ := hX
    rcases Compose.tree_cases rhoc_run.toLocalRun hy hX with rfl | ⟨k, hk, hacc⟩
    · exact absurd rfl hXg
    · exact ⟨k, X, hacc, tree_twin hy hc hX hXg, hc k hk⟩
  push Not at hX
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨acc, rfl⟩ : ∃ acc, c = .fg (.block (twinBlk S) acc) := by
    simp only [exec, onBlock] at hcs
    split_ifs at hcs
    cases hfg : ((tr S).state y j).fg.onBlock (twinBlk S) <;> simp only [hfg, List.cons.injEq] at hcs
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

end Consensus.Goldilocks.Test.ProposerHold

end
