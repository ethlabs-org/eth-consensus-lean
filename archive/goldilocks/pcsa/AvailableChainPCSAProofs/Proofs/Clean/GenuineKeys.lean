module
public import AvailableChainPCSAProofs.Proofs.Clean.AckTargetBody

public section

/-! C6 GenuineKeys: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
/-- Vote admission preserves saved raw results. -/
private theorem genuine_vote (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) : (GridCO.admitVote q v o).genuine = v.genuine := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
/-- Base proposal admission preserves saved raw results. -/
private theorem genuine_proposal (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (B : Block) (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q v o B raw).genuine = v.genuine := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only
  all_goals first
    | rfl
    | (split
       · rfl
       · apply List.foldlRecOn
           (motive := fun acc : GridCO.State n .root => acc.genuine = v.genuine)
         · rfl
         · intro acc hh a _
           exact (genuine_vote q acc (GridCO.fromHead a)).trans hh)
/-- Row admission preserves saved raw results. -/
private theorem genuine_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.genuine = st.base.genuine := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl
/-- Raw ack pooling preserves saved raw results. -/
private theorem genuine_raw (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.genuine = st.base.genuine := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl
/-- Checked ack pooling preserves saved raw results. -/
private theorem genuine_pool (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).base.genuine = st.base.genuine := by
  delta poolAck
  cases a.decode? with
  | none => rfl
  | some v =>
    rcases v with ⟨_, _, _⟩
    dsimp only
    split
    · rfl
    · split <;> rfl
/-- Row admission preserves saved raw results. -/
private theorem genuine_rows (p : Params) (st : State p.n) (rows : List (RowWire p.n)) :
    (rows.foldl (admitRow p) st).base.genuine = st.base.genuine := by
  apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.genuine =
    st.base.genuine)
  · rfl
  · intro acc hh a _
    exact (genuine_row p acc a).trans hh
/-- Raw ack pooling preserves saved raw results. -/
private theorem genuine_raws (st : State n) (acks : List (AckWire n)) :
    (acks.foldl poolAckRaw st).base.genuine = st.base.genuine := by
  apply List.foldlRecOn (motive := fun acc : State n => acc.base.genuine = st.base.genuine)
  · rfl
  · intro acc hh a _
    exact (genuine_raw acc a).trans hh
/-- Record normalization preserves saved raw results. -/
private theorem genuine_norm (st : State n) :
    (normalizeS st).base.genuine = st.base.genuine := by
  delta normalizeS
  split <;> rfl
private theorem genuine_collect (st : State n) :
    (collectPCs st).base.genuine = st.base.genuine := by
  apply collectPCs_preserves (fun st => st.base.genuine)
  intro acc C
  rw [installPC_def]
  split <;> rfl
private theorem genuine_reconcile_keys (st : State n) :
    (reconcile st).base.genuine.map Prod.fst = st.base.genuine.map Prod.fst := by
  delta reconcile
  rw [genuine_norm, List.map_map]
  rfl
/-- Deliveries preserve the labels of saved raw results. -/
theorem pcsa_process_genuine_keys (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.genuine.map Prod.fst = st.base.genuine.map Prod.fst := by
  delta process
  cases o.decode with
  | none => rfl
  | some msg => cases msg with
    | vote s i r =>
      change (GridCO.admitVote p.toParams.engine st.base _).genuine.map Prod.fst = _
      rw [genuine_vote]
    | row i body =>
      change (admitRow p st _).base.genuine.map Prod.fst = _
      rw [genuine_row]
    | ack s i r =>
      change (collectPCs (poolAck p st _)).base.genuine.map Prod.fst = _
      rw [genuine_collect, genuine_pool]
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [genuine_collect, genuine_raws]
      · rfl
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · rfl
      · cases hp : parentFG st N.erase with
        | none => rfl
        | some P =>
          change (if blockAccepted p st s N P then _ else st).base.genuine.map Prod.fst = _
          split
          · let st1 : State p.n := { st with
              base := GridCO.admitProposal p.toParams.engine st.base
                (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
            let st2 := match N.pc with
              | none => st1
              | some C => if pcValid st1 C && !st1.pcs.any
                  (fun old => old.slot == C.slot && old.target == C.target)
                then deleteConflictingLeases st1 C else st1
            let st3 : State p.n := { st2 with
              fg := FGSA.Window.on_block p p.K_W st2.fg (fgBlock P N.erase N.rows)
              proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
            let st4 := if st3.fg.F = st.fg.F then st3 else reconcile st3
            change (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
              st4))).base.genuine.map
              Prod.fst = _
            rw [genuine_rows, genuine_collect, genuine_raws]
            have h1 : st1.base.genuine = st.base.genuine := genuine_proposal _ _ _ _ _
            have h3 : st3.base.genuine = st.base.genuine := by
              change st2.base.genuine = st.base.genuine
              dsimp only [st2]
              cases N.pc with
              | none => exact h1
              | some C => dsimp only; split <;> exact h1
            dsimp only [st4]
            split
            · rw [h3]
            · rw [genuine_reconcile_keys, h3]
          · rfl
/-- Pre-gate clock stages preserve all saved raw results. -/
theorem pcsa_clockPre_genuine (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.genuine = st.base.genuine := by
  delta clockPre
  dsimp only
  split <;> split <;> split <;> rfl
/-- A gate records exactly the result of its raw confirmation read. -/
theorem pcsa_gate_genuine (p : Params) (st : State n) (anchor : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p anchor cs rank st s).base.genuine =
      @GridCO.recordGenuine GridCO.slowLeasePolicy n .root (actView st) s
        (SA.Root.confirmationFrom p.toParams anchor (actView st) s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams anchor (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn
        (motive := fun acc : State n => acc.base.genuine =
          @GridCO.recordGenuine GridCO.slowLeasePolicy n .root (actView st) s (some X))
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn
          (motive := fun acc : State n => acc.base.genuine =
            @GridCO.recordGenuine GridCO.slowLeasePolicy n .root (actView st) s (some X))
        · exact ha
        · intro acc' ha' g _
          exact ha'
private theorem genuine_record_key (v : GridCO.State n .root) (s r : Slot) (result : Option Block)
    (hm : r ∈ (@GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s result).map Prod.fst) :
    r ∈ v.genuine.map Prod.fst ∨ r = s := by
  delta GridCO.recordGenuine at hm
  split at hm
  · rw [List.map_append] at hm
    rcases List.mem_append.mp hm with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (List.mem_singleton.mp hnew)
  · exact Or.inl hm
/-- A clock adds a saved label only at that label's gate time. -/
theorem pcsa_clock_genuine_key_origin (p : Params) (st : State p.n) (t : Time) (r : Slot)
    (hm : r ∈ (clock p st t).base.genuine.map Prod.fst) :
    r ∈ st.base.genuine.map Prod.fst ∨ t = SA.gateTime p.toParams r := by
  delta clock at hm
  dsimp only at hm
  split at hm
  · rename_i hg
    have ht := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hg).2
    rw [gateStep_def, genuine_norm] at hm
    split at hm
    · rw [pcsa_clockPre_genuine] at hm
      exact Or.inl hm
    · rw [pcsa_gate_genuine] at hm
      rcases genuine_record_key _ _ r _ hm with hold | he
      · change r ∈ (clockPre p st t).base.genuine.map Prod.fst at hold
        rw [pcsa_clockPre_genuine] at hold
        exact Or.inl hold
      · exact Or.inr (he ▸ ht)
  · rw [pcsa_clockPre_genuine] at hm
    exact Or.inl hm
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every saved raw-result label has an exact earlier gate tick at that node. -/
theorem pcsa_genuine_key_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) :
    ∀ s ∈ (V2.D.Run.stateBefore E rho k x).st.base.genuine.map Prod.fst,
      ∃ j < k, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) := by
  let Q := fun s => ∃ j < k, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s))
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => ∀ s ∈ nd.st.base.genuine.map Prod.fst, Q s) (Nat.zero_le k) x ?_ ?_
  · intro j e _ hjk he hn ih
    cases e with
    | restart y t =>
      change y = x at hn
      subst y
      change ∀ s ∈ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.genuine.map
        Prod.fst, Q s
      rw [Function.update_self]
      intro s hs
      exact (List.not_mem_nil hs).elim
    | tick y t =>
      change y = x at hn
      subst y
      change ∀ s ∈ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.genuine.map
        Prod.fst, Q s
      rw [Function.update_self]
      have hs := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x t
      rw [hs]
      intro s hm
      rcases pcsa_clock_genuine_key_origin p _ t s hm with hold | ht
      · exact ih s hold
      · exact ⟨j, hjk, ht ▸ he⟩
    | deliver y o t =>
      change y = x at hn
      subst y
      change ∀ s ∈ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.genuine.map
        Prod.fst, Q s
      rw [Function.update_self]
      intro s hm
      change s ∈ (process p (V2.D.Run.stateBefore E rho j x).st (toWire p o)).base.genuine.map
        Prod.fst at hm
      rw [pcsa_process_genuine_keys] at hm
      exact ih s hm
  · intro s hs
    exact (List.not_mem_nil hs).elim
/-- An actual unique gate tick reads an unsaved label. -/
theorem pcsa_gate_input_unsaved (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : rho.events.Nodup)
    (k : Nat) (x : V) (s : Slot) (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams s))) :
    (GridCO.savedGenuine (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)).base s).isSome = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨result, hr⟩ := Option.isSome_iff_exists.mp hh
  delta GridCO.savedGenuine at hr
  obtain ⟨row, hrow, _⟩ := Option.map_eq_some_iff.mp hr
  have hkey : row.1 = s := beq_iff_eq.mp (List.find?_some
    (p := fun row : Slot × Option Block => row.1 == s) hrow)
  have hm := List.mem_of_find?_eq_some hrow
  have hlabel : s ∈ (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams s)).base.genuine.map Prod.fst := List.mem_map.mpr ⟨row, hm, hkey⟩
  rw [pcsa_clockPre_genuine] at hlabel
  obtain ⟨j, hj, he⟩ := pcsa_genuine_key_origin E rho k x s hlabel
  have hjk : j = k := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp he).1 hn).mp
    (he.trans hk.symm)
  exact (Nat.ne_of_lt hj) hjk
end AvailableChain.PCSA.Run

end
