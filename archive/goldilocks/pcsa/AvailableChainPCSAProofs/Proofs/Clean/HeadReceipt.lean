module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadStamps

public section

/-! C6 HEAD stamp keys, receipt origin, and acceptance before a public cutoff. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private def HeadKeys (st : State n) : Prop := st.base.voteStamp.map Prod.fst = st.base.votes
private theorem headKeys_grid_vote (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (h : v.voteStamp.map Prod.fst = v.votes) :
    (GridCO.admitVote q v o).voteStamp.map Prod.fst = (GridCO.admitVote q v o).votes := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first
    | exact h
    | (split
       · exact h
       · rw [List.map_append, h]; rfl)
private theorem headKeys_grid_proposal (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (b : Block) (raw : List (GridCO.HeadWire n .root))
    (h : v.voteStamp.map Prod.fst = v.votes) :
    (GridCO.admitProposal q v o b raw).voteStamp.map Prod.fst =
      (GridCO.admitProposal q v o b raw).votes := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only <;> split
  all_goals first
    | exact h
    | (apply List.foldlRecOn
        (motive := fun v : GridCO.State n .root => v.voteStamp.map Prod.fst = v.votes)
       · exact h
       · intro acc ha row _
         exact headKeys_grid_vote q acc (GridCO.fromHead row) ha)
private theorem headKeys_norm (st : State n) (h : HeadKeys st) : HeadKeys (normalizeS st) := by
  delta normalizeS
  split <;> exact h
private theorem headKeys_reconcile (st : State n) (h : HeadKeys st) : HeadKeys (reconcile st) := by
  apply headKeys_norm
  exact h
private theorem headKeys_collect (st : State n) (h : HeadKeys st) : HeadKeys (collectPCs st) := by
  apply collectPCs_invariant HeadKeys
  · intro st C h _
    rw [installPC_def]
    split <;> exact h
  · exact h
private theorem headKeys_raw (st : State n) (a : AckWire n) (h : HeadKeys st) :
    HeadKeys (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h
private theorem headKeys_row (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : HeadKeys st) : HeadKeys (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h
private theorem headKeys_process (p : Params) (st : State p.n) (o : Wire p.n)
    (h : HeadKeys st) : HeadKeys (process p st o) := by
  change st.base.voteStamp.map Prod.fst = st.base.votes at h
  change (process p st o).base.voteStamp.map Prod.fst = (process p st o).base.votes
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : HeadKeys st) :
      HeadKeys (as.foldl poolAckRaw st) := by
    apply List.foldlRecOn
    · exact h
    · intro acc hh a _
      exact headKeys_raw acc a hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : HeadKeys st) :
      HeadKeys (as.foldl (admitRow p) st) := by
    apply List.foldlRecOn
    · exact h
    · intro acc hh a _
      exact headKeys_row p acc a hh
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact headKeys_grid_vote p.toParams.engine st.base _ h
    | row i body => exact headKeys_row p st _ h
    | ack s i r =>
      apply headKeys_collect
      delta poolAck
      cases AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc C =>
      dsimp only
      delta admitPC
      split
      · exact headKeys_collect _ (ha st C.acks h)
      · exact h
    | block s N =>
      dsimp only
      delta admitBlock
      cases hn : namedParentHeld st N with
      | false => exact h
      | true =>
        dsimp only
        cases parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          cases blockAccepted p st s N P with
          | false => exact h
          | true =>
            apply hr
            apply headKeys_collect
            apply ha
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact headKeys_grid_proposal p.toParams.engine st.base _ _ _ h
              | (apply headKeys_reconcile
                 exact headKeys_grid_proposal p.toParams.engine st.base _ _ _ h)
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every indexed pool has exactly the keys of its HEAD stamp list. -/
theorem pcsa_head_stamp_keys (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (k : Nat) (x : V) :
    (V2.D.Run.stateBefore E rho k x).st.base.voteStamp.map Prod.fst =
      (V2.D.Run.stateBefore E rho k x).st.base.votes := by
  refine Gen.V2.Duty.invariant_triple (P := pcsaWith m p c)
    (fun nd : Node p => HeadKeys nd.st) rfl ?_ ?_ (fun _ _ h => h)
    (fun _ _ => rfl) E rho k x
  · intro nd t h
    change (clock p nd.st t).base.voteStamp.map Prod.fst = (clock p nd.st t).base.votes
    rw [pcsa_clock_headStamps, pcsa_clock_heads]
    exact h
  · intro nd o h
    exact headKeys_process p nd.st (toWire p o) h
/-- A pooled HEAD has an existing first stamp entry. -/
theorem pcsa_head_stamp_lookup (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (k : Nat) (x : V) (o : GridCO.Wire p.n .root)
    (hm : o ∈ (V2.D.Run.stateBefore E rho k x).st.base.votes) :
    ∃ row, (V2.D.Run.stateBefore E rho k x).st.base.voteStamp.find?
      (fun r => r.1 == o) = some row := by
  have hk := pcsa_head_stamp_keys E rho k x
  rw [← hk] at hm
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
  cases hf : (V2.D.Run.stateBefore E rho k x).st.base.voteStamp.find?
      (fun r => r.1 == o) with
  | none =>
    have hn := List.find?_eq_none.mp hf row hr
    rw [he, beq_self_eq_true] at hn
    contradiction
  | some row => exact ⟨row, rfl⟩
/-- A pooled HEAD keeps its first receipt time at every later indexed read. -/
theorem pcsa_head_stamp_stateBefore_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (x : V) {i j : Nat} (hij : i ≤ j) (o : GridCO.Wire p.n .root)
    (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes) :
    GridCO.stampVote (V2.D.Run.stateBefore E rho j x).st.base o =
      GridCO.stampVote (V2.D.Run.stateBefore E rho i x).st.base o := by
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho i x o hm
  exact pcsa_stampVote_eq_of_prefix _ _ o row
    (pcsa_headStamps_stateBefore_prefix E rho hn x hij) hr
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem origin_grid (v : GridCO.State p.n .root)
    (parent o : GridCO.Wire p.n .root) (t : Time)
    (hm : (o, t) ∈ (GridCO.admitVote p.toParams.engine v parent).voteStamp) :
    (o, t) ∈ v.voteStamp ∨ t = v.now ∧ o ∉ v.votes ∧ o = parent := by
  rcases parent with ⟨auth, payload⟩
  cases auth <;> cases payload <;> try exact Or.inl hm
  delta GridCO.admitVote at hm
  dsimp only at hm
  split at hm
  · exact Or.inl hm
  · rename_i hn
    rcases List.mem_append.mp hm with hm | hm
    · exact Or.inl hm
    · have he := List.mem_singleton.mp hm
      have ho := congrArg Prod.fst he
      have ht := congrArg Prod.snd he
      dsimp only at ho ht
      refine Or.inr ⟨ht, ?_, ho⟩
      intro h
      have hn' := hn
      rw [← ho] at hn'
      simp only [h, decide_true, Bool.or_true] at hn'
      contradiction
private theorem origin_fold (raw : List (HeadWire p.n))
    (v : GridCO.State p.n .root) (o : GridCO.Wire p.n .root) (t : Time)
    (hm : (o, t) ∈ ((raw.map baseHead).foldl
      (fun acc row => GridCO.admitVote p.toParams.engine acc (GridCO.fromHead row)) v).voteStamp) :
    (o, t) ∈ v.voteStamp ∨ t = v.now ∧ o ∉ v.votes ∧ o ∈ raw.map baseVote := by
  induction raw generalizing v with
  | nil => exact Or.inl hm
  | cons a raw ih =>
    rcases ih _ hm with hm | ⟨ht, hn, ho⟩
    · rcases origin_grid v (baseVote a) o t hm with hm | ⟨ht, hn, he⟩
      · exact Or.inl hm
      · exact Or.inr ⟨ht, hn, List.mem_cons.mpr (Or.inl he)⟩
    · exact Or.inr ⟨by simpa only [FGSA.Run.Internal.grid_admitVote_now] using ht,
        fun h => hn (FGSA.Run.Internal.grid_admitVote_votes_subset v _ h),
        List.mem_cons_of_mem _ ho⟩
private theorem origin_decoded_head (o : Obj p) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : (toWire p o).decode = some (.vote s i r)) :
    o = (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta toWire toAuth Wire.decode at h <;> cases h
  | seat l j =>
    cases l with
    | prop k => cases payload <;> delta toWire toAuth Wire.decode at h <;> cases h
    | base l =>
      cases l <;> cases payload <;>
        delta toWire toAuth Wire.decode Label.ackSlot? at h <;> cases h
      rfl
private theorem origin_carried_head (a : HeadWire p.n) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : baseVote a = (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root)) :
    ofHead p a = (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta baseVote baseHead HeadWire.decode? GridCO.fromHead at h; cases h
  | proposer k => delta baseVote baseHead HeadWire.decode? GridCO.fromHead at h; cases h
  | seat l j =>
    cases l <;> delta baseVote baseHead HeadWire.decode? GridCO.fromHead at h <;> cases h
    rfl
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem origin_norm (st : State p.n) :
    (normalizeS st).base.voteStamp = st.base.voteStamp := by
  delta normalizeS
  split <;> rfl
private theorem origin_reconcile (st : State p.n) :
    (reconcile st).base.voteStamp = st.base.voteStamp := by
  delta reconcile
  rw [origin_norm]
private theorem origin_row (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.voteStamp = st.base.voteStamp := by
  delta admitRow
  cases a.decode? <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
private theorem origin_collect (st : State p.n) :
    (collectPCs st).base.voteStamp = st.base.voteStamp := by
  apply collectPCs_preserves (fun st => st.base.voteStamp)
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem origin_raw (st : State p.n) (a : AckWire p.n) :
    (poolAckRaw st a).base.voteStamp = st.base.voteStamp := by
  delta poolAckRaw
  cases a.decode? <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
/-- A new HEAD stamp is from the actual direct or carried handler call. -/
theorem pcsa_process_head_stamp_origin (st : State p.n) (parent : Obj p)
    (s : Slot) (i : Fin p.n) (r : BlockId) (stamp : Time)
    (hm : ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root), stamp) ∈
      (process p st (toWire p parent)).base.voteStamp) :
    ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root), stamp) ∈ st.base.voteStamp ∨
      stamp = st.base.now ∧ (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∉ st.base.votes ∧
        handlesS p st parent (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) := by
  have ha (st : State p.n) (as : List (AckWire p.n)) :
      (as.foldl poolAckRaw st).base.voteStamp = st.base.voteStamp := by
    apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.voteStamp = st.base.voteStamp)
    · rfl
    · intro acc hh a _
      rw [origin_raw]
      exact hh
  have hr (st : State p.n) (as : List (RowWire p.n)) :
      (as.foldl (admitRow p) st).base.voteStamp = st.base.voteStamp := by
    apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.voteStamp = st.base.voteStamp)
    · rfl
    · intro acc hh a _
      rw [origin_row]
      exact hh
  delta process at hm
  cases hd : (toWire p parent).decode with
  | none => rw [hd] at hm; exact Or.inl hm
  | some msg =>
    rw [hd] at hm
    cases msg with
    | vote a j b =>
      rcases origin_grid st.base ⟨.seat a j, .head b⟩ _ stamp hm with hm | ⟨ht, hn, he⟩
      · exact Or.inl hm
      · have hh : (s = a ∧ i = j) ∧ r = b := by cases he; exact ⟨⟨rfl, rfl⟩, rfl⟩
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hh
        exact Or.inr ⟨ht, hn, Or.inl (origin_decoded_head parent s i r hd)⟩
    | row j body => rw [origin_row] at hm; exact Or.inl hm
    | ack a j b =>
      change _ ∈
        (collectPCs (poolAck p st (⟨(toWire p parent).auth, b⟩ : AckWire p.n))).base.voteStamp at hm
      rw [origin_collect] at hm
      delta poolAck at hm
      cases hdec : AckWire.decode? (⟨(toWire p parent).auth, b⟩ : AckWire p.n) with
      | none => rw [hdec] at hm; exact Or.inl hm
      | some v =>
        rw [hdec] at hm
        rcases v with ⟨_, _, _⟩
        dsimp only at hm
        split at hm
        · exact Or.inl hm
        · split at hm <;> exact Or.inl hm
    | pc C =>
      dsimp only at hm
      delta admitPC at hm
      split at hm
      · rw [origin_collect, ha] at hm; exact Or.inl hm
      · exact Or.inl hm
    | block a N =>
      dsimp only at hm
      delta admitBlock at hm
      cases hn : namedParentHeld st N with
      | false => rw [hn] at hm; exact Or.inl hm
      | true =>
        rw [hn] at hm
        change _ ∈ (match parentFG st N.erase with
          | none => st
          | some P => if blockAccepted p st a N P then _ else st).base.voteStamp at hm
        generalize hp : parentFG st N.erase = parent at hm
        cases parent with
        | none => exact Or.inl hm
        | some P =>
          dsimp only at hm
          split at hm
          · rename_i hacc
            rw [hr, origin_collect, ha] at hm
            have hbase : ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root), stamp) ∈
                (GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal a N.erase N.raw N.support) N.erase
                  (N.raw.map baseHead)).voteStamp := by
              generalize hc : N.pc = pc at hm
              cases pc <;> dsimp only at hm
              all_goals split_ifs at hm <;> first
                | exact hm
                | (rw [origin_reconcile] at hm; exact hm)
            delta GridCO.admitProposal baseProposal at hbase
            dsimp only at hbase
            split at hbase
            · exact Or.inl hbase
            · rcases origin_fold N.raw _ _ stamp hbase with hm | ⟨ht, hf, ho⟩
              · exact Or.inl hm
              · obtain ⟨wire, hw, he⟩ := List.mem_map.mp ho
                refine Or.inr ⟨ht, hf, Or.inr (Or.inl ?_)⟩
                rw [hd]
                refine ⟨⟨hn, P, hp, hacc⟩, Or.inl ?_⟩
                exact List.mem_map.mpr ⟨wire, hw, origin_carried_head wire s i r he⟩
          · exact Or.inl hm
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every stamped HEAD has an earlier acceptance at that exact store clock. -/
theorem pcsa_head_stamp_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V)
    (s : Slot) (i : Fin p.n) (r : BlockId) (stamp : Time)
    (hm : ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root), stamp) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.voteStamp) :
    ∃ j < k, ∃ t, V2.D.Run.acceptsAt E rho j x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t ∧
      stamp = (V2.D.Run.stateBefore E rho j x).st.base.now := by
  induction k with
  | zero => exact (List.not_mem_nil hm).elim
  | succ k ih =>
    have carry (hm : ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root), stamp) ∈
        (V2.D.Run.stateBefore E rho k x).st.base.voteStamp) :
        ∃ j < k + 1, ∃ t, V2.D.Run.acceptsAt E rho j x
          (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t ∧
          stamp = (V2.D.Run.stateBefore E rho j x).st.base.now := by
      obtain ⟨j, hj, rest⟩ := ih hm
      exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    cases he : rho.events[k]? with
    | none =>
      have hs : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
        delta V2.D.Run.stateBefore
        rw [List.take_add_one, he]
        simp only [Option.toList_none, List.append_nil]
      exact carry (hs ▸ hm)
    | some e =>
      have hp := V2.D.Run.stateBefore_succ E rho he
      rw [hp] at hm
      by_cases hx : e.node = x
      · cases e with
        | restart y t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.voteStamp at hm
          rw [Function.update_self] at hm
          exact (List.not_mem_nil hm).elim
        | tick y t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.voteStamp at hm
          rw [Function.update_self] at hm
          have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
          rw [ht, pcsa_clock_headStamps] at hm
          exact carry hm
        | deliver y parent t =>
          change y = x at hx
          subst y
          change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.voteStamp at hm
          rw [Function.update_self] at hm
          rcases pcsa_process_head_stamp_origin _ parent s i r stamp hm with hm | ⟨ht, hn, hh⟩
          · exact carry hm
          · refine ⟨k, Nat.lt_succ_self k, t, ⟨⟨parent, he, hh⟩, ?_, ?_⟩, ht⟩
            · change decide ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
                (V2.D.Run.stateBefore E rho k x).st.base.votes) = false
              exact decide_eq_false_iff_not.mpr hn
            · have hstored : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
                  (V2.D.Run.stateBefore E rho (k + 1) x).st.base.votes := by
                rw [← pcsa_head_stamp_keys E rho (k + 1) x]
                refine List.mem_map.mpr ⟨(_, stamp), ?_, rfl⟩
                rw [hp]
                change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.voteStamp
                rw [Function.update_self]
                exact hm
              change decide ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
                (V2.D.Run.stateBefore E rho (k + 1) x).st.base.votes) = true
              exact decide_eq_true hstored
      · apply carry
        have heq := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hx
        rwa [heq] at hm
private theorem head_stamp_entry (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V)
    (o : GridCO.Wire p.n .root) (hm : o ∈ (V2.D.Run.stateBefore E rho k x).st.base.votes) :
    (o, GridCO.stampVote (V2.D.Run.stateBefore E rho k x).st.base o) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.voteStamp := by
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho k x o hm
  have he : row.1 = o := beq_iff_eq.mp
    (List.find?_some (p := fun r : GridCO.Wire p.n .root × Time => r.1 == o) hr)
  have hh := List.mem_of_find?_eq_some hr
  rcases row with ⟨a, t⟩
  dsimp only at he
  subst a
  delta GridCO.stampVote
  rw [hr]
  exact hh
/-- A HEAD stamp below a public cutoff gives an acceptance before that cutoff. -/
theorem pcsa_head_accepted_before (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (k : Nat) (x : V) (s : Slot) (i : Fin p.n)
    (r : BlockId) (cut : Time) (hpub : V2.PublicTime E cut) (hzero : 0 ≤ cut)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho k x).st.base.votes)
    (ht : GridCO.stampVote (V2.D.Run.stateBefore E rho k x).st.base
      ⟨.seat s i, .head r⟩ < cut) :
    ∃ j < k, ∃ t, V2.D.Run.acceptsAt E rho j x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t ∧ t < cut := by
  obtain ⟨j, hj, t, ha, he⟩ := pcsa_head_stamp_source E rho k x s i r _
    (head_stamp_entry E rho k x _ hm)
  refine ⟨j, hj, t, ha, ?_⟩
  by_contra hlate
  obtain ⟨parent, hd, _⟩ := ha.1
  have hb := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho hS hn
    hd hpub hzero (le_of_not_gt hlate)
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)] at hb
  rw [he] at ht
  exact (not_lt.mpr hb) ht
end AvailableChain.PCSA.Run
end
