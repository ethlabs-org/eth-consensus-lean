module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadRelay

public section

/-! C6 exact body lists, receipt-stamp keys, and first-stamp preservation. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private def BodyKeys (st : State n) : Prop := st.base.blockStamp.map Prod.fst = st.base.blocks
private theorem bodyKeys_grid_vote (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (h : v.blockStamp.map Prod.fst = v.blocks) :
    (GridCO.admitVote q v o).blockStamp.map Prod.fst = (GridCO.admitVote q v o).blocks := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first | exact h | (split <;> exact h)
private theorem bodyKeys_grid_proposal (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (b : Block) (raw : List (GridCO.HeadWire n .root))
    (h : v.blockStamp.map Prod.fst = v.blocks) :
    (GridCO.admitProposal q v o b raw).blockStamp.map Prod.fst =
      (GridCO.admitProposal q v o b raw).blocks := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only <;> split
  all_goals first
    | exact h
    | (apply List.foldlRecOn
        (motive := fun v : GridCO.State n .root => v.blockStamp.map Prod.fst = v.blocks)
       · change (v.blockStamp ++ [(b, v.now)]).map Prod.fst = v.blocks ++ [b]
         rw [List.map_append, h]
         rfl
       · intro acc ha row _
         exact bodyKeys_grid_vote q acc (GridCO.fromHead row) ha)
private theorem bodyKeys_norm (st : State n) (h : BodyKeys st) : BodyKeys (normalizeS st) := by
  delta normalizeS
  split <;> exact h
private theorem bodyKeys_reconcile (st : State n) (h : BodyKeys st) : BodyKeys (reconcile st) := by
  apply bodyKeys_norm
  exact h
private theorem bodyKeys_collect (st : State n) (h : BodyKeys st) : BodyKeys (collectPCs st) := by
  apply collectPCs_invariant BodyKeys
  · intro st C h _
    rw [installPC_def]
    split <;> exact h
  · exact h
private theorem bodyKeys_raw (st : State n) (a : AckWire n) (h : BodyKeys st) :
    BodyKeys (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h
private theorem bodyKeys_row (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : BodyKeys st) : BodyKeys (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h
private theorem bodyKeys_process (p : Params) (st : State p.n) (o : Wire p.n)
    (h : BodyKeys st) : BodyKeys (process p st o) := by
  change st.base.blockStamp.map Prod.fst = st.base.blocks at h
  change (process p st o).base.blockStamp.map Prod.fst = (process p st o).base.blocks
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : BodyKeys st) :
      BodyKeys (as.foldl poolAckRaw st) := by
    apply List.foldlRecOn
    · exact h
    · intro acc hh a _
      exact bodyKeys_raw acc a hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : BodyKeys st) :
      BodyKeys (as.foldl (admitRow p) st) := by
    apply List.foldlRecOn
    · exact h
    · intro acc hh a _
      exact bodyKeys_row p acc a hh
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact bodyKeys_grid_vote p.toParams.engine st.base _ h
    | row i body => exact bodyKeys_row p st _ h
    | ack s i r =>
      apply bodyKeys_collect
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
      · exact bodyKeys_collect _ (ha st C.acks h)
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
            apply bodyKeys_collect
            apply ha
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact bodyKeys_grid_proposal p.toParams.engine st.base _ _ _ h
              | (apply bodyKeys_reconcile
                 exact bodyKeys_grid_proposal p.toParams.engine st.base _ _ _ h)
end AvailableChain.PCSA
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem body_keys_norm_blocks (st : State n) :
    (normalizeS st).base.blocks = st.base.blocks := by
  delta normalizeS
  split <;> rfl
private theorem body_keys_gate_blocks (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.blocks = st.base.blocks := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => acc.base.blocks = st.base.blocks)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc : State n => acc.base.blocks = st.base.blocks)
        · exact ha
        · intro acc' ha' g _
          exact ha'
/-- Every clock keeps the exact cumulative base body list. -/
theorem pcsa_clock_blocks (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.blocks = st.base.blocks := by
  have hp : (clockPre p st t).base.blocks = st.base.blocks := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, body_keys_norm_blocks]
    split
    · exact hp
    · rw [body_keys_gate_blocks]
      exact hp
  · exact hp
end AvailableChain.PCSA
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem pcsa_bodyStamps_grid_vote (q : GridCO.Params)
    (v : GridCO.State n .root) (o : GridCO.Wire n .root) :
    v.blockStamp <+: (GridCO.admitVote q v o).blockStamp := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first
    | exact List.prefix_refl _
    | (split <;> exact List.prefix_refl _)
private theorem pcsa_bodyStamps_grid_proposal (q : GridCO.Params)
    (v : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    v.blockStamp <+: (GridCO.admitProposal q v o b raw).blockStamp := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only <;> split
  all_goals first
    | exact List.prefix_refl _
    | (apply List.foldlRecOn
        (motive := fun acc : GridCO.State n .root => v.blockStamp <+: acc.blockStamp)
       · exact List.prefix_append _ _
       · intro acc h row _
         exact h.trans (pcsa_bodyStamps_grid_vote q acc (GridCO.fromHead row)))
private theorem pcsa_bodyStamps_norm (st : State n) :
    (normalizeS st).base.blockStamp = st.base.blockStamp := by
  delta normalizeS
  split <;> rfl
private theorem pcsa_bodyStamps_reconcile (st : State n) :
    (reconcile st).base.blockStamp = st.base.blockStamp := by
  delta reconcile
  rw [pcsa_bodyStamps_norm]
private theorem pcsa_bodyStamps_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.blockStamp = st.base.blockStamp := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_bodyStamps_collect (st : State n) :
    (collectPCs st).base.blockStamp = st.base.blockStamp := by
  apply collectPCs_preserves (fun st => st.base.blockStamp)
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem pcsa_bodyStamps_raw_ack (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.blockStamp = st.base.blockStamp := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_bodyStamps_gate (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.blockStamp = st.base.blockStamp := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn
        (motive := fun acc : State n => acc.base.blockStamp = st.base.blockStamp)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn
          (motive := fun acc : State n => acc.base.blockStamp = st.base.blockStamp)
        · exact ha
        · intro acc' ha' g _
          exact ha'
/-- A clock keeps the exact body receipt-stamp list. -/
theorem pcsa_clock_bodyStamps (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.blockStamp = st.base.blockStamp := by
  have hp : (clockPre p st t).base.blockStamp = st.base.blockStamp := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, pcsa_bodyStamps_norm]
    split
    · exact hp
    · rw [pcsa_bodyStamps_gate]
      exact hp
  · exact hp
/-- Delivery appends to the body stamp list. It keeps its full previous prefix. -/
theorem pcsa_process_bodyStamps_prefix (p : Params) (st : State p.n) (o : Wire p.n) :
    st.base.blockStamp <+: (process p st o).base.blockStamp := by
  let H := st.base.blockStamp
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : H <+: st.base.blockStamp) :
      H <+: (as.foldl poolAckRaw st).base.blockStamp := by
    apply List.foldlRecOn (motive := fun acc : State p.n => H <+: acc.base.blockStamp)
    · exact h
    · intro acc hh a _
      rw [pcsa_bodyStamps_raw_ack]
      exact hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : H <+: st.base.blockStamp) :
      H <+: (as.foldl (admitRow p) st).base.blockStamp := by
    apply List.foldlRecOn (motive := fun acc : State p.n => H <+: acc.base.blockStamp)
    · exact h
    · intro acc hh a _
      rw [pcsa_bodyStamps_row]
      exact hh
  delta process
  cases hd : o.decode with
  | none => exact List.prefix_refl _
  | some msg => cases msg with
    | vote s i r => exact pcsa_bodyStamps_grid_vote _ _ _
    | row i body => simpa only [pcsa_bodyStamps_row] using (List.prefix_refl st.base.blockStamp)
    | ack s i r =>
      change st.base.blockStamp <+:
        (collectPCs (poolAck p st (⟨o.auth, r⟩ : AckWire p.n))).base.blockStamp
      rw [pcsa_bodyStamps_collect]
      delta poolAck
      cases AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact List.prefix_refl _
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact List.prefix_refl _
        · split <;> exact List.prefix_refl _
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [pcsa_bodyStamps_collect]
        exact ha st C.acks (List.prefix_refl _)
      · exact List.prefix_refl _
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact List.prefix_refl _
      · cases parentFG st N.erase with
        | none => exact List.prefix_refl _
        | some P =>
          dsimp only
          split
          · apply hr
            rw [pcsa_bodyStamps_collect]
            apply ha
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact pcsa_bodyStamps_grid_proposal _ _ _ _ _
              | (rw [pcsa_bodyStamps_reconcile]
                 exact pcsa_bodyStamps_grid_proposal _ _ _ _ _)
          · exact List.prefix_refl _
/-- Appending receipt stamps leaves an existing first body lookup unchanged. -/
theorem pcsa_stampBlock_eq_of_prefix (src dst : GridCO.State n .root)
    (o : Block) (row : Block × Time)
    (hp : src.blockStamp <+: dst.blockStamp)
    (hr : src.blockStamp.find? (fun r => r.1 == o) = some row) :
    GridCO.stampBlock dst o = GridCO.stampBlock src o := by
  have hd := hp.find?_eq_some hr
  delta GridCO.stampBlock
  rw [hr, hd]
  rfl

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Without restarts, later indexed states keep the full body stamp prefix. -/
theorem pcsa_bodyStamps_stateBefore_prefix (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (y : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i y).st.base.blockStamp <+:
      (V2.D.Run.stateBefore E rho j y).st.base.blockStamp := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p =>
      (V2.D.Run.stateBefore E rho i y).st.base.blockStamp <+: nd.st.base.blockStamp)
    hij y ?_ (List.prefix_refl _)
  intro k e _ _ he hy h
  cases e with
  | restart x t => exact (hn k x t he).elim
  | tick x t =>
    change x = y at hy
    subst x
    change _ <+: (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blockStamp
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht, pcsa_clock_bodyStamps]
    exact h
  | deliver x o t =>
    change x = y at hy
    subst x
    change _ <+: (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blockStamp
    rw [Function.update_self]
    exact List.IsPrefix.trans h (pcsa_process_bodyStamps_prefix p _ (toWire p o))
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every stored body has a receipt-stamp key, including genesis. -/
theorem pcsa_body_stamp_keys (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (k : Nat) (x : V) :
    (V2.D.Run.stateBefore E rho k x).st.base.blockStamp.map Prod.fst =
      (V2.D.Run.stateBefore E rho k x).st.base.blocks := by
  refine Gen.V2.Duty.invariant_triple (P := pcsaWith m p c)
    (fun nd : Node p => BodyKeys nd.st) rfl ?_ ?_ (fun _ _ h => h)
    (fun _ _ => rfl) E rho k x
  · intro nd t h
    change (clock p nd.st t).base.blockStamp.map Prod.fst = (clock p nd.st t).base.blocks
    rw [pcsa_clock_bodyStamps, pcsa_clock_blocks]
    exact h
  · intro nd o h
    exact bodyKeys_process p nd.st (toWire p o) h
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every stored exact body has an existing first receipt-stamp lookup. -/
theorem pcsa_body_stamp_lookup (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (k : Nat) (x : V) (B : Block) (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    ∃ row, (V2.D.Run.stateBefore E rho k x).st.base.blockStamp.find?
      (fun r => r.1 == B) = some row := by
  have hk := pcsa_body_stamp_keys E rho k x
  rw [← hk] at hm
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
  cases hf : (V2.D.Run.stateBefore E rho k x).st.base.blockStamp.find?
      (fun r => r.1 == B) with
  | none =>
    have hn := List.find?_eq_none.mp hf row hr
    rw [he, beq_self_eq_true] at hn
    contradiction
  | some row => exact ⟨row, rfl⟩
/-- Without restarts, a held body's first receipt time stays unchanged. -/
theorem pcsa_body_stamp_stateBefore_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (x : V) {i j : Nat} (hij : i ≤ j) (B : Block)
    (hm : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) :
    GridCO.stampBlock (V2.D.Run.stateBefore E rho j x).st.base B =
      GridCO.stampBlock (V2.D.Run.stateBefore E rho i x).st.base B := by
  obtain ⟨row, hr⟩ := pcsa_body_stamp_lookup E rho i x B hm
  exact pcsa_stampBlock_eq_of_prefix _ _ B row
    (pcsa_bodyStamps_stateBefore_prefix E rho hn x hij) hr
end AvailableChain.PCSA.Run

end
