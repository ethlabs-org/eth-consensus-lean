module
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSARun.Proofs.Acceptance -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainFGSARun.Statements.Receipts

-- ROOT-DIGEST-2: private matcher copy; equality is checked by the kernel (BUILD B3).
namespace AvailableChain.FGSA
open AvailableChain.Generic AvailableChain.SimplexFG

private def stamp_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

private theorem stamp_admitBlock_hygiene_eq : @admitBlock = @stamp_admitBlock := rfl

end AvailableChain.FGSA

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem t78_grid_stamp_origin (st : GridCO.State p.n .root)
    (parent v : GridCO.Wire p.n .root) (stamp : Time)
    (hm : (v, stamp) ∈ (GridCO.admitVote p.toParams.engine st parent).voteStamp) :
    (v, stamp) ∈ st.voteStamp ∨ stamp = st.now ∧ v ∉ st.votes ∧ v = parent := by
  obtain ⟨auth, payload⟩ := parent
  cases auth <;> cases payload <;> try exact Or.inl hm
  rename_i r i B
  dsimp only [GridCO.admitVote] at hm
  split at hm
  · exact Or.inl hm
  · rename_i hg
    rcases List.mem_append.mp hm with hm | hm
    · exact Or.inl hm
    · have he : v = (⟨.seat r i, .head B⟩ : GridCO.Wire p.n .root) ∧ stamp = st.now := by
        simpa using hm
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨rfl, by intro h; simp [h] at hg, rfl⟩

private theorem t78_fold_stamp_origin (raw : List (HeadWire p.n))
    (st : GridCO.State p.n .root) (v : GridCO.Wire p.n .root) (stamp : Time)
    (hm : (v, stamp) ∈ ((raw.map baseHead).foldl
      (fun st h => GridCO.admitVote p.toParams.engine st (GridCO.fromHead h)) st).voteStamp) :
    (v, stamp) ∈ st.voteStamp ∨
      stamp = st.now ∧ v ∉ st.votes ∧ v ∈ raw.map baseVote := by
  induction raw generalizing st with
  | nil => exact Or.inl hm
  | cons h raw ih =>
    rcases ih _ hm with hm | ⟨ht, hn, hh⟩
    · rcases t78_grid_stamp_origin st (baseVote h) v stamp hm with hm | ⟨ht, hn, he⟩
      · exact Or.inl hm
      · exact Or.inr ⟨ht, hn, List.mem_cons.mpr (Or.inl he)⟩
    · exact Or.inr ⟨by simpa only [Internal.grid_admitVote_now] using ht,
        fun h => hn (Internal.grid_admitVote_votes_subset st _ h),
        List.mem_cons_of_mem _ hh⟩

private theorem t78_baseVote_eq (a : HeadWire p.n) (s : Slot) (i : Fin p.n) (b : BlockId)
    (h : baseVote a = ⟨.seat s i, .head b⟩) : a = ⟨.seat (.head s) i, b⟩ := by
  obtain ⟨auth, payload⟩ := a
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
    dsimp only [baseVote, baseHead, HeadWire.decode?, GridCO.fromHead] at h
  all_goals (cases h <;> rfl)

private theorem t78_vote_process_origin (st : State p.n) (parent : Obj p)
    (s : Slot) (i : Fin p.n) (b : BlockId) (stamp : Time)
    (hm : ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root), stamp) ∈
      (FGSA.process p st (toWire p parent)).base.voteStamp) :
    ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root), stamp) ∈ st.base.voteStamp ∨
      stamp = st.base.now ∧ (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.base.votes ∧
        handlesS p st parent (ofHead p ⟨.seat (.head s) i, b⟩) := by
  dsimp only [FGSA.process] at hm
  cases hd : (toWire p parent).decode with
  | none => rw [hd] at hm; exact Or.inl hm
  | some m =>
    rw [hd] at hm
    cases m with
    | vote r j B =>
      rcases t78_grid_stamp_origin st.base ⟨.seat r j, .head B⟩ _ stamp hm with
        hm | ⟨ht, hn, he⟩
      · exact Or.inl hm
      · right
        have hs : s = r := by cases he; rfl
        have hi : i = j := by cases he; rfl
        have hb : b = B := by cases he; rfl
        subst r j B
        refine ⟨ht, hn, Or.inl ?_⟩
        apply toWire_injective
        rw [toWire_ofHead, decode_eq_vote.mp hd]
    | row j body =>
      dsimp only at hm
      rw [Internal.admitRow_base] at hm
      exact Or.inl hm
    | block r N =>
      dsimp only at hm
      cases hNamed : namedParentHeld st N with
      | false =>
        rw [admitBlock_refused p st r N (Or.inl hNamed)] at hm
        exact Or.inl hm
      | true =>
        cases hp : parentFG st N.erase with
        | none =>
          rw [admitBlock_refused p st r N (Or.inr (Or.inl hp))] at hm
          exact Or.inl hm
        | some P =>
          cases ha : blockAccepted p st r N P with
          | false =>
            rw [admitBlock_refused p st r N (Or.inr (Or.inr ⟨P, hp, ha⟩))] at hm
            exact Or.inl hm
          | true =>
            obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st r N P hNamed hp ha
            rw [he] at hm
            dsimp only at hm
            have hbase : ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root), stamp) ∈
                (GridCO.admitProposal p.toParams.engine st.base (baseProposal r N.erase N.raw
                    N.support)
                  N.erase (N.raw.map baseHead)).voteStamp := by
              split at hm
              · exact hm
              · rwa [(reconcile_frame _).2.2.2.2.2.2.1] at hm
            unfold GridCO.admitProposal at hbase
            dsimp only [baseProposal] at hbase
            split at hbase
            · exact Or.inl hbase
            · rcases t78_fold_stamp_origin N.raw _ _ stamp hbase with hm | ⟨ht, hn, hv⟩
              · exact Or.inl hm
              · refine Or.inr ⟨ht, hn, Or.inr ?_⟩
                rw [hd]
                obtain ⟨a, ham, hae⟩ := List.mem_map.mp hv
                have hae' := t78_baseVote_eq a s i b hae
                subst a
                exact ⟨⟨hNamed, P, hp, ha⟩, Or.inl (List.mem_map.mpr ⟨_, ham, rfl⟩)⟩
private theorem t78_block_process_origin (st : State p.n) (hInv : CStoreInv p st)
    (o : Obj p) (b : Block) (stamp : Time)
    (hm : (b, stamp) ∈ (FGSA.process p st (toWire p o)).base.blockStamp) :
    (b, stamp) ∈ st.base.blockStamp ∨ stamp = st.base.now ∧
      ∃ s N P, N.erase = b ∧ (toWire p o).decode = some (.block s N) ∧
        blockAccepted p st s N P = true := by
  dsimp only [FGSA.process] at hm
  cases hd : (toWire p o).decode with
  | none => rw [hd] at hm; exact Or.inl hm
  | some m =>
    rw [hd] at hm
    cases m with
    | vote s i B =>
      change (b, stamp) ∈ (GridCO.admitVote p.toParams.engine st.base
        ⟨.seat s i, .head B⟩).blockStamp at hm
      rw [(admitVote_stamps p.toParams.engine st.base _).2.1] at hm
      exact Or.inl hm
    | row i body =>
      dsimp only at hm
      rw [Internal.admitRow_base] at hm
      exact Or.inl hm
    | block s N =>
      dsimp only at hm
      cases hNamed : namedParentHeld st N with
      | false =>
        rw [admitBlock_refused p st s N (Or.inl hNamed)] at hm
        exact Or.inl hm
      | true =>
        cases hp : parentFG st N.erase with
        | none =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))] at hm
          exact Or.inl hm
        | some P =>
          cases ha : blockAccepted p st s N P with
          | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))] at hm
            exact Or.inl hm
          | true =>
            obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hNamed hp ha
            rw [he] at hm
            dsimp only at hm
            rw [(accepted_st2 p st hInv s N P hp ha).2.2.2.1] at hm
            rcases List.mem_append.mp hm with hm | hm
            · exact Or.inl hm
            · have he : b = N.erase ∧ stamp = st.base.now := by simpa using hm
              obtain ⟨rfl, rfl⟩ := he
              exact Or.inr ⟨rfl, s, N, P, rfl, rfl, ha⟩
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2. Body membership gives processed-by-root without injectivity. -/
private theorem t78_block_processed_of_mem (st : State p.n) (hInv : Inv0 p st)
    (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N))
    (hb : N.erase ∈ st.base.blocks) : processedS p st o = true := by
  dsimp only [processedS]
  rw [hd]
  apply decide_eq_true
  obtain ⟨Y, hY, he⟩ := (hInv.2.2 N.erase).mp hb
  exact ⟨Y, hY, by simpa using (eraseFG_root Y).symm.trans (congrArg Block.root he)⟩

/-- Every stored replay vote has the exact wake stamp. -/
theorem fgsa_replay_vote_stamp_time (st : State p.n) (w : Time)
    (v : GridCO.Wire p.n .root) (stamp : Time)
    (hm : (v, stamp) ∈ (acRestart p st w).base.voteStamp) : stamp = w := by
  have hv : v ∈ (acRestart p st w).base.votes := by
    rw [← acRestart_voteStamp_keys]
    exact List.mem_map_of_mem hm
  have hs := acRestart_replay_stamp p st w v hv
  unfold GridCO.stampVote at hs
  cases hf : (acRestart p st w).base.voteStamp.find? (fun row => row.1 == v) with
  | none =>
    have hn := List.find?_eq_none.mp hf (v, stamp) hm
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row =>
    have hr := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    have he : row.1 = v := beq_iff_eq.mp hpred
    have heq : row = (v, stamp) :=
      List.inj_on_of_nodup_map (acRestart_voteStamp_nodup p st w) hr hm he
    rw [hf, heq] at hs
    exact hs

/-- A vote stamp comes from a network acceptance or a local replay. -/
theorem fgsa_vote_stamp_source_or_restart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (x : V) (s : Slot) (i : Fin p.n) (b : BlockId) (stamp : Time)
    (hm : ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root), stamp) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.voteStamp) :
    (∃ j < k, ∃ t, V2.D.Run.acceptsAt E rho j x (ofHead p ⟨.seat (.head s) i, b⟩) t ∧
      stamp = (V2.D.Run.stateBefore E rho j x).st.base.now) ∨
    (∃ j < k, ∃ w, rho.events[j]? = some (.restart x w) ∧ stamp = w ∧
      (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
        (acRestart p (V2.D.Run.stateBefore E rho j x).st w).base.votes) := by
  induction k with
  | zero => exact (List.not_mem_nil hm).elim
  | succ k ih =>
    have carry (hmem : ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root), stamp) ∈
        (V2.D.Run.stateBefore E rho k x).st.base.voteStamp) :
        (∃ j < k + 1, ∃ t,
          V2.D.Run.acceptsAt E rho j x (ofHead p ⟨.seat (.head s) i, b⟩) t ∧
          stamp = (V2.D.Run.stateBefore E rho j x).st.base.now) ∨
        (∃ j < k + 1, ∃ w, rho.events[j]? = some (.restart x w) ∧ stamp = w ∧
          (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
            (acRestart p (V2.D.Run.stateBefore E rho j x).st w).base.votes) := by
      rcases ih hmem with ⟨j, hj, h⟩ | ⟨j, hj, h⟩
      · exact Or.inl ⟨j, by omega, h⟩
      · exact Or.inr ⟨j, by omega, h⟩
    cases he : rho.events[k]? with
    | none => apply carry; simpa [V2.D.Run.stateBefore, List.take_add_one, he] using hm
    | some e =>
      have hpost := V2.D.Run.stateBefore_succ E rho he
      rw [hpost] at hm
      by_cases hx : e.node = x
      · cases e with
        | restart v t =>
          change v = x at hx; subst v
          simp only [V2.D.World.step, Function.update_self] at hm
          change ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root), stamp) ∈
            (acRestart p (V2.D.Run.stateBefore E rho k x).st t).base.voteStamp at hm
          refine Or.inr ⟨k, Nat.lt_succ_self k, t, he,
            fgsa_replay_vote_stamp_time _ t _ stamp hm, ?_⟩
          rw [← acRestart_voteStamp_keys]
          exact List.mem_map_of_mem hm
        | tick v t =>
          change v = x at hx; subst v
          apply carry
          simp only [V2.D.World.step, Function.update_self] at hm
          rwa [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t,
            (clock_cumulative p _ t).2.2.2.1] at hm
        | deliver v parent t =>
          change v = x at hx; subst v
          simp only [V2.D.World.step, Function.update_self] at hm
          rcases t78_vote_process_origin _ parent s i b stamp hm with hm | ⟨ht, hn, hh⟩
          · exact carry hm
          · refine Or.inl ⟨k, Nat.lt_succ_self k, t, ⟨⟨parent, he, hh⟩, ?_, ?_⟩, ht⟩
            · change decide ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
                (V2.D.Run.stateBefore E rho k x).st.base.votes) = false
              exact decide_eq_false_iff_not.mpr hn
            · have hstored : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
                  (V2.D.Run.stateBefore E rho (k + 1) x).st.base.votes := by
                rw [← fgsa_vote_stamp_keys E rho (k + 1) x]
                exact List.mem_map.mpr ⟨(_, stamp),
                  by simpa only [hpost, V2.D.World.step, Function.update_self] using hm, rfl⟩
              change decide ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
                (V2.D.Run.stateBefore E rho (k + 1) x).st.base.votes) = true
              exact decide_eq_true hstored
      · apply carry
        rwa [V2.D.World.step_apply_of_node_ne E rho _ hx] at hm

/-- A block stamp is genesis, a network acceptance, or a restamped held block. -/
theorem fgsa_block_stamp_source_or_restart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (x : V) (b : Block) (stamp : Time)
    (hm : (b, stamp) ∈ (V2.D.Run.stateBefore E rho k x).st.base.blockStamp) :
    (b = .genesis ∧ stamp = 0) ∨
    (∃ j < k, ∃ t o, blockOf? p o = some b ∧ V2.D.Run.acceptsAt E rho j x o t ∧
      stamp = (V2.D.Run.stateBefore E rho j x).st.base.now) ∨
    (∃ j < k, ∃ w, rho.events[j]? = some (.restart x w) ∧ b ≠ .genesis ∧
      b ∈ (V2.D.Run.stateBefore E rho j x).st.base.blocks ∧ stamp = w) := by
  induction k with
  | zero =>
    left
    change (b, stamp) ∈ [(Block.genesis, (0 : Time))] at hm
    simpa only [List.mem_singleton, Prod.mk.injEq] using hm
  | succ k ih =>
    have carry (hmem : (b, stamp) ∈ (V2.D.Run.stateBefore E rho k x).st.base.blockStamp) :
        (b = .genesis ∧ stamp = 0) ∨
        (∃ j < k + 1, ∃ t o, blockOf? p o = some b ∧ V2.D.Run.acceptsAt E rho j x o t ∧
          stamp = (V2.D.Run.stateBefore E rho j x).st.base.now) ∨
        (∃ j < k + 1, ∃ w, rho.events[j]? = some (.restart x w) ∧ b ≠ .genesis ∧
          b ∈ (V2.D.Run.stateBefore E rho j x).st.base.blocks ∧ stamp = w) := by
      rcases ih hmem with hg | ⟨j, hj, h⟩ | ⟨j, hj, h⟩
      · exact Or.inl hg
      · exact Or.inr (Or.inl ⟨j, by omega, h⟩)
      · exact Or.inr (Or.inr ⟨j, by omega, h⟩)
    cases he : rho.events[k]? with
    | none => apply carry; simpa [V2.D.Run.stateBefore, List.take_add_one, he] using hm
    | some e =>
      have hpost := V2.D.Run.stateBefore_succ E rho he
      rw [hpost] at hm
      by_cases hx : e.node = x
      · cases e with
        | restart v t =>
          change v = x at hx; subst v
          simp only [V2.D.World.step, Function.update_self] at hm
          change (b, stamp) ∈ (acRestart p (V2.D.Run.stateBefore E rho k x).st t).base.blockStamp
            at hm
          rw [acRestart_blockStamp] at hm
          obtain ⟨b', hb, hpair⟩ := List.mem_map.mp hm
          have heq : b' = b := congrArg Prod.fst hpair
          subst b'
          have hstamp := congrArg Prod.snd hpair
          dsimp only at hstamp
          by_cases hg : b = .genesis
          · exact Or.inl ⟨hg, by simpa only [hg, ite_true] using hstamp.symm⟩
          · exact Or.inr (Or.inr ⟨k, Nat.lt_succ_self k, t, he, hg, hb,
              by simpa only [hg, ite_false] using hstamp.symm⟩)
        | tick v t =>
          change v = x at hx; subst v
          apply carry
          simp only [V2.D.World.step, Function.update_self] at hm
          rwa [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t,
            (clock_cumulative p _ t).2.2.1] at hm
        | deliver v o t =>
          change v = x at hx; subst v
          simp only [V2.D.World.step, Function.update_self] at hm
          rcases t78_block_process_origin _ (cstoreInv_stateBefore E rho k x) o b stamp hm with
            hm | ⟨ht, s, N, P, heN, hd, ha⟩
          · exact carry hm
          · refine Or.inr (Or.inl
              ⟨k, Nat.lt_succ_self k, t, o, ?_, ⟨⟨o, he, Or.inl rfl⟩, ?_, ?_⟩, ht⟩)
            · dsimp only [blockOf?]
              rw [hd]
              exact congrArg some heN
            · change processedS p (V2.D.Run.stateBefore E rho k x).st o = false
              dsimp only [processedS]
              rw [hd]
              simp only [decide_eq_false_iff_not]
              simpa only [named_erase_root] using (blockAccepted_facts ha).2.2.1
            · have hb : b ∈ (V2.D.Run.stateBefore E rho (k + 1) x).st.base.blocks := by
                rw [← (metaInv_stateBefore E rho (k + 1) x).stampKeys]
                exact List.mem_map.mpr ⟨(b, stamp),
                  by simpa only [hpost, V2.D.World.step, Function.update_self] using hm, rfl⟩
              exact (t78_block_processed_of_mem _ (inv0_stateBefore E rho (k + 1) x)
                o s N hd) (heN ▸ hb)
      · apply carry
        rwa [V2.D.World.step_apply_of_node_ne E rho _ hx] at hm

/-- A stored non-genesis block has a network acceptance in an earlier local epoch. -/
theorem fgsa_block_accepted_origin (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (x : V) (b : Block) (hg : b ≠ .genesis)
    (hm : b ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    ∃ j < k, ∃ t o, blockOf? p o = some b ∧ V2.D.Run.acceptsAt E rho j x o t := by
  induction k with
  | zero => exact (hg (List.mem_singleton.mp hm)).elim
  | succ k ih =>
    have hnext := hm
    have carry (hb : b ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
        ∃ j < k + 1, ∃ t o, blockOf? p o = some b ∧ V2.D.Run.acceptsAt E rho j x o t := by
      obtain ⟨j, hj, h⟩ := ih hb
      exact ⟨j, by omega, h⟩
    cases he : rho.events[k]? with
    | none => apply carry; simpa [V2.D.Run.stateBefore, List.take_add_one, he] using hm
    | some e =>
      have hpost := V2.D.Run.stateBefore_succ E rho he
      rw [hpost] at hm
      by_cases hx : e.node = x
      · cases e with
        | restart v t =>
          change v = x at hx; subst v
          simp only [V2.D.World.step, Function.update_self] at hm
          change b ∈ (acRestart p (V2.D.Run.stateBefore E rho k x).st t).base.blocks at hm
          rw [acRestart_blocks] at hm
          exact carry hm
        | tick v t =>
          change v = x at hx; subst v
          apply carry
          simp only [V2.D.World.step, Function.update_self] at hm
          rwa [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t,
            (clock_cumulative p _ t).2.1] at hm
        | deliver v o t =>
          change v = x at hx; subst v
          by_cases hold : b ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks
          · exact carry hold
          · have hmap : b ∈ (V2.D.Run.stateBefore E rho (k + 1) x).st.base.blockStamp.map
                Prod.fst := by
              rw [(metaInv_stateBefore E rho (k + 1) x).stampKeys]
              exact hnext
            obtain ⟨⟨b', stamp⟩, hs, hb⟩ := List.mem_map.mp hmap
            dsimp only at hb
            subst b'
            have hraw : (b, stamp) ∈
                (FGSA.process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).base.blockStamp :=
              by
                rw [hpost] at hs
                simp only [V2.D.World.step, Function.update_self] at hs
                exact hs
            rcases t78_block_process_origin _ (cstoreInv_stateBefore E rho k x) o b stamp hraw with
              hs | ⟨_, slot, N, P, heN, hd, ha⟩
            · apply False.elim
              apply hold
              rw [← (metaInv_stateBefore E rho k x).stampKeys]
              exact List.mem_map_of_mem hs
            · refine ⟨k, Nat.lt_succ_self k, t, o, ?_, ⟨⟨o, he, Or.inl rfl⟩, ?_, ?_⟩⟩
              · dsimp only [blockOf?]
                rw [hd]
                exact congrArg some heN
              · change processedS p (V2.D.Run.stateBefore E rho k x).st o = false
                dsimp only [processedS]
                rw [hd]
                simp only [decide_eq_false_iff_not]
                simpa only [named_erase_root] using (blockAccepted_facts ha).2.2.1
              · exact (t78_block_processed_of_mem _ (inv0_stateBefore E rho (k + 1) x)
                  o slot N hd) (heN ▸ hnext)
      · apply carry
        rwa [V2.D.World.step_apply_of_node_ne E rho _ hx] at hm

/-- Without a restart, the vote stamp has a network acceptance origin. -/
theorem fgsa_vote_stamp_source (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hNR : V2.D.NoRestart rho) (k : Nat) (x : V) (s : Slot) (i : Fin p.n)
    (b : BlockId) (stamp : Time)
    (hm : ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root), stamp) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.voteStamp) :
    ∃ j < k, ∃ t, V2.D.Run.acceptsAt E rho j x (ofHead p ⟨.seat (.head s) i, b⟩) t ∧
      stamp = (V2.D.Run.stateBefore E rho j x).st.base.now := by
  rcases fgsa_vote_stamp_source_or_restart E rho k x s i b stamp hm with h | ⟨j, _, w, he, _⟩
  · exact h
  · exact (hNR j x w he).elim

/-- Without a restart, a block stamp is genesis or has a network acceptance origin. -/
theorem fgsa_block_stamp_source (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hNR : V2.D.NoRestart rho) (k : Nat) (x : V) (b : Block) (stamp : Time)
    (hm : (b, stamp) ∈ (V2.D.Run.stateBefore E rho k x).st.base.blockStamp) :
    (b = .genesis ∧ stamp = 0) ∨
      ∃ j < k, ∃ t o, blockOf? p o = some b ∧ V2.D.Run.acceptsAt E rho j x o t ∧
        stamp = (V2.D.Run.stateBefore E rho j x).st.base.now := by
  rcases fgsa_block_stamp_source_or_restart E rho k x b stamp hm with hg | hd | ⟨j, _, w, he, _⟩
  · exact Or.inl hg
  · exact Or.inr hd
  · exact (hNR j x w he).elim

end AvailableChain.FGSA.Run
end
