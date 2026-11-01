module
public import AvailableChainPCSAProofs.Proofs.Clean.AckTargetBody
public import AvailableChainPCSAProofs.Proofs.Clean.HeadPersistence

public section

/-! C6 exact HEAD receipt-stamp preservation. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem pcsa_headStamps_grid_vote (q : GridCO.Params)
    (v : GridCO.State n .root) (o : GridCO.Wire n .root) :
    v.voteStamp <+: (GridCO.admitVote q v o).voteStamp := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first
    | exact List.prefix_refl _
    | (split <;> first
        | exact List.prefix_refl _
        | exact List.prefix_append _ _)
private theorem pcsa_headStamps_grid_proposal (q : GridCO.Params)
    (v : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    v.voteStamp <+: (GridCO.admitProposal q v o b raw).voteStamp := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only <;> split
  all_goals first
    | exact List.prefix_refl _
    | (apply List.foldlRecOn
        (motive := fun acc : GridCO.State n .root => v.voteStamp <+: acc.voteStamp)
       · exact List.prefix_refl _
       · intro acc h row _
         exact h.trans (pcsa_headStamps_grid_vote q acc (GridCO.fromHead row)))
private theorem pcsa_headStamps_norm (st : State n) :
    (normalizeS st).base.voteStamp = st.base.voteStamp := by
  delta normalizeS
  split <;> rfl
private theorem pcsa_headStamps_reconcile (st : State n) :
    (reconcile st).base.voteStamp = st.base.voteStamp := by
  delta reconcile
  rw [pcsa_headStamps_norm]
private theorem pcsa_headStamps_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.voteStamp = st.base.voteStamp := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_headStamps_collect (st : State n) :
    (collectPCs st).base.voteStamp = st.base.voteStamp := by
  apply collectPCs_preserves (fun st => st.base.voteStamp)
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem pcsa_headStamps_raw_ack (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.voteStamp = st.base.voteStamp := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_headStamps_gate (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.voteStamp = st.base.voteStamp := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => acc.base.voteStamp = st.base.voteStamp)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn
          (motive := fun acc : State n => acc.base.voteStamp = st.base.voteStamp)
        · exact ha
        · intro acc' ha' g _
          exact ha'
/-- A clock keeps the exact HEAD receipt-stamp list. -/
theorem pcsa_clock_headStamps (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.voteStamp = st.base.voteStamp := by
  have hp : (clockPre p st t).base.voteStamp = st.base.voteStamp := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, pcsa_headStamps_norm]
    split
    · exact hp
    · rw [pcsa_headStamps_gate]
      exact hp
  · exact hp
/-- Delivery appends to the HEAD stamp list. It keeps its full previous prefix. -/
theorem pcsa_process_headStamps_prefix (p : Params) (st : State p.n) (o : Wire p.n) :
    st.base.voteStamp <+: (process p st o).base.voteStamp := by
  let H := st.base.voteStamp
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : H <+: st.base.voteStamp) :
      H <+: (as.foldl poolAckRaw st).base.voteStamp := by
    apply List.foldlRecOn (motive := fun acc : State p.n => H <+: acc.base.voteStamp)
    · exact h
    · intro acc hh a _
      rw [pcsa_headStamps_raw_ack]
      exact hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : H <+: st.base.voteStamp) :
      H <+: (as.foldl (admitRow p) st).base.voteStamp := by
    apply List.foldlRecOn (motive := fun acc : State p.n => H <+: acc.base.voteStamp)
    · exact h
    · intro acc hh a _
      rw [pcsa_headStamps_row]
      exact hh
  delta process
  cases hd : o.decode with
  | none => exact List.prefix_refl _
  | some msg => cases msg with
    | vote s i r => exact pcsa_headStamps_grid_vote _ _ _
    | row i body => simpa only [pcsa_headStamps_row] using (List.prefix_refl st.base.voteStamp)
    | ack s i r =>
      change st.base.voteStamp <+:
        (collectPCs (poolAck p st (⟨o.auth, r⟩ : AckWire p.n))).base.voteStamp
      rw [pcsa_headStamps_collect]
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
      · rw [pcsa_headStamps_collect]
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
            rw [pcsa_headStamps_collect]
            apply ha
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact pcsa_headStamps_grid_proposal _ _ _ _ _
              | (rw [pcsa_headStamps_reconcile]
                 exact pcsa_headStamps_grid_proposal _ _ _ _ _)
          · exact List.prefix_refl _
/-- Appending receipt stamps leaves an existing first HEAD lookup unchanged. -/
theorem pcsa_stampVote_eq_of_prefix (src dst : GridCO.State n .root)
    (o : GridCO.Wire n .root) (row : GridCO.Wire n .root × Time)
    (hp : src.voteStamp <+: dst.voteStamp)
    (hr : src.voteStamp.find? (fun r => r.1 == o) = some row) :
    GridCO.stampVote dst o = GridCO.stampVote src o := by
  have hd := hp.find?_eq_some hr
  delta GridCO.stampVote
  rw [hr, hd]
  rfl

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Without restarts, later indexed states keep the full HEAD stamp prefix. -/
theorem pcsa_headStamps_stateBefore_prefix (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (y : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i y).st.base.voteStamp <+:
      (V2.D.Run.stateBefore E rho j y).st.base.voteStamp := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i y).st.base.voteStamp <+: nd.st.base.voteStamp)
    hij y ?_ (List.prefix_refl _)
  intro k e _ _ he hy h
  cases e with
  | restart x t => exact (hn k x t he).elim
  | tick x t =>
    change x = y at hy
    subst x
    change _ <+: (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.voteStamp
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht, pcsa_clock_headStamps]
    exact h
  | deliver x o t =>
    change x = y at hy
    subst x
    change _ <+: (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.voteStamp
    rw [Function.update_self]
    exact List.IsPrefix.trans h (pcsa_process_headStamps_prefix p _ (toWire p o))
end AvailableChain.PCSA.Run
end
