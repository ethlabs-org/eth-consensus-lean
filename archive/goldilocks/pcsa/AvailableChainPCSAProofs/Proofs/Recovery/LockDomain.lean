module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockView

public section

/-! The cumulative resolution domain at recovery reads. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private def LockDomainClear (st : State n) : Prop := st.base.headDomain = none
private theorem lock_domainClear_grid_vote (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (h : v.headDomain = none) :
    (GridCO.admitVote q v o).headDomain = none := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first | exact h | (split <;> exact h)
private theorem lock_domainClear_grid_proposal (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (b : Block) (raw : List (GridCO.HeadWire n .root))
    (h : v.headDomain = none) :
    (GridCO.admitProposal q v o b raw).headDomain = none := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only <;> split
  all_goals first
    | exact h
    | (apply List.foldlRecOn
        (motive := fun v : GridCO.State n .root => v.headDomain = none)
       · exact h
       · intro acc ha row _
         exact lock_domainClear_grid_vote q acc (GridCO.fromHead row) ha)
private theorem lock_domainClear_norm (st : State n) (h : LockDomainClear st) :
    LockDomainClear (normalizeS st) := by
  delta normalizeS
  split <;> exact h
private theorem lock_domainClear_reconcile (st : State n) (h : LockDomainClear st) :
    LockDomainClear (reconcile st) := by
  apply lock_domainClear_norm
  exact h
private theorem lock_domainClear_collect (st : State n) (h : LockDomainClear st) :
    LockDomainClear (collectPCs st) := by
  apply collectPCs_invariant LockDomainClear
  · intro st C h _
    rw [installPC_def]
    split <;> exact h
  · exact h
private theorem lock_domainClear_raw (st : State n) (a : AckWire n) (h : LockDomainClear st) :
    LockDomainClear (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h
private theorem lock_domainClear_row (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : LockDomainClear st) : LockDomainClear (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h
private theorem lock_domainClear_process (p : Params) (st : State p.n) (o : Wire p.n)
    (h : LockDomainClear st) : LockDomainClear (process p st o) := by
  change st.base.headDomain = none at h
  change (process p st o).base.headDomain = none
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : LockDomainClear st) :
      LockDomainClear (as.foldl poolAckRaw st) := by
    apply List.foldlRecOn
    · exact h
    · intro acc hh a _
      exact lock_domainClear_raw acc a hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : LockDomainClear st) :
      LockDomainClear (as.foldl (admitRow p) st) := by
    apply List.foldlRecOn
    · exact h
    · intro acc hh a _
      exact lock_domainClear_row p acc a hh
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact lock_domainClear_grid_vote p.toParams.engine st.base _ h
    | row i body => exact lock_domainClear_row p st _ h
    | ack s i r =>
      apply lock_domainClear_collect
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
      · exact lock_domainClear_collect _ (ha st C.acks h)
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
            apply lock_domainClear_collect
            apply ha
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact lock_domainClear_grid_proposal p.toParams.engine st.base _ _ _ h
              | (apply lock_domainClear_reconcile
                 exact lock_domainClear_grid_proposal p.toParams.engine st.base _ _ _ h)
end AvailableChain.PCSA
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem lock_domain_clock_norm (st : State n) :
    (normalizeS st).base.headDomain = st.base.headDomain := by
  delta normalizeS
  split <;> rfl
private theorem lock_domain_clock_gate (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.headDomain = st.base.headDomain := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn
        (motive := fun acc : State n => acc.base.headDomain = st.base.headDomain)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn
          (motive := fun acc : State n => acc.base.headDomain = st.base.headDomain)
        · exact ha
        · intro acc' ha' g _
          exact ha'
/-- A clock keeps the cumulative head-domain field. -/
theorem recovery_clock_headDomain (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.headDomain = st.base.headDomain := by
  have hp : (clockPre p st t).base.headDomain = st.base.headDomain := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, lock_domain_clock_norm]
    split
    · exact hp
    · rw [lock_domain_clock_gate]
      exact hp
  · exact hp
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every run store resolves root wires in its cumulative body list. -/
theorem recovery_headDomain_stateBefore_none (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) :
    (V2.D.Run.stateBefore E rho k x).st.base.headDomain = none := by
  refine Gen.V2.Duty.invariant_triple (P := pcsaWith m p c)
    (fun nd : Node p => LockDomainClear nd.st) rfl ?_ ?_ (fun _ _ h => h)
    (fun _ _ => rfl) E rho k x
  · intro nd t h
    change (clock p nd.st t).base.headDomain = none
    rw [recovery_clock_headDomain]
    exact h
  · intro nd o h
    exact lock_domainClear_process p nd.st (toWire p o) h
end AvailableChain.PCSA.Run
end
