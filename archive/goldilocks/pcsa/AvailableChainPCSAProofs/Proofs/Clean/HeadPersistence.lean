module
public import AvailableChainPCSAProofs.Proofs.Clean.AckTargetBody
public import AvailableChainFGSARun.Proofs.Excludes

public section

/-! C6 cumulative HEAD pools and count transport. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem pcsa_heads_norm (st : State n) : (normalizeS st).base.votes = st.base.votes := by
  delta normalizeS
  split <;> rfl
private theorem pcsa_heads_reconcile (st : State n) :
    (reconcile st).base.votes = st.base.votes := by
  delta reconcile
  rw [pcsa_heads_norm]
private theorem pcsa_heads_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.votes = st.base.votes := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_heads_collect (st : State n) : (collectPCs st).base.votes = st.base.votes := by
  apply collectPCs_preserves (fun st => st.base.votes)
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem pcsa_heads_raw_ack (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.votes = st.base.votes := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_heads_gate (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.votes = st.base.votes := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => acc.base.votes = st.base.votes)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc : State n => acc.base.votes = st.base.votes)
        · exact ha
        · intro acc' ha' g _
          exact ha'
/-- A clock keeps every pooled signed HEAD. -/
theorem pcsa_clock_heads (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.votes = st.base.votes := by
  have hp : (clockPre p st t).base.votes = st.base.votes := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, pcsa_heads_norm]
    split
    · exact hp
    · rw [pcsa_heads_gate]
      exact hp
  · exact hp
/-- Delivery keeps every pooled signed HEAD, including through PC and body admission. -/
theorem pcsa_process_heads_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.base.votes ⊆ (process p st o).base.votes := by
  let H := st.base.votes
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : H ⊆ st.base.votes) :
      H ⊆ (as.foldl poolAckRaw st).base.votes := by
    apply List.foldlRecOn (motive := fun acc : State p.n => H ⊆ acc.base.votes)
    · exact h
    · intro acc hh a _
      rw [pcsa_heads_raw_ack]
      exact hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : H ⊆ st.base.votes) :
      H ⊆ (as.foldl (admitRow p) st).base.votes := by
    apply List.foldlRecOn (motive := fun acc : State p.n => H ⊆ acc.base.votes)
    · exact h
    · intro acc hh a _
      rw [pcsa_heads_row]
      exact hh
  delta process
  cases hd : o.decode with
  | none => exact List.Subset.refl _
  | some msg => cases msg with
    | vote s i r => exact FGSA.Run.Internal.grid_admitVote_votes_subset _ _
    | row i body => simpa only [pcsa_heads_row] using (List.Subset.refl st.base.votes)
    | ack s i r =>
      change st.base.votes ⊆ (collectPCs (poolAck p st (⟨o.auth, r⟩ : AckWire p.n))).base.votes
      rw [pcsa_heads_collect]
      delta poolAck
      cases AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact List.Subset.refl _
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact List.Subset.refl _
        · split <;> exact List.Subset.refl _
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [pcsa_heads_collect]
        exact ha st C.acks (List.Subset.refl _)
      · exact List.Subset.refl _
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact List.Subset.refl _
      · cases parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          dsimp only
          split
          · apply hr
            rw [pcsa_heads_collect]
            apply ha
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact FGSA.Run.Internal.grid_admitProposal_votes_subset _ _ _ _
              | (rw [pcsa_heads_reconcile]
                 exact FGSA.Run.Internal.grid_admitProposal_votes_subset _ _ _ _)
          · exact List.Subset.refl _
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Without restarts, later indexed states keep every exact pooled HEAD. -/
theorem pcsa_heads_stateBefore_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (y : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i y).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho j y).st.base.votes := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i y).st.base.votes ⊆ nd.st.base.votes)
    hij y ?_ (List.Subset.refl _)
  intro k e _ _ he hy h
  cases e with
  | restart x t => exact (hn k x t he).elim
  | tick x t =>
    change x = y at hy
    subst x
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.votes
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht, pcsa_clock_heads]
    exact h
  | deliver x o t =>
    change x = y at hy
    subst x
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.votes
    rw [Function.update_self]
    exact List.Subset.trans h (pcsa_process_heads_mono p _ (toWire p o))
end AvailableChain.PCSA.Run
end
