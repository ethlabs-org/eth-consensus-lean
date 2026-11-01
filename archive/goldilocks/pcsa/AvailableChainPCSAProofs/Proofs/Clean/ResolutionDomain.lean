module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadRelay
public import AvailableChainPCSAProofs.Proofs.Clean.BodyStamps
public import AvailableChainPCSAProofs.Proofs.Shared.CleanGate

public section

/-! C6 cumulative resolution domain and exact held-body HEAD lookup. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private def DomainClear (st : State n) : Prop := st.base.headDomain = none
private theorem domainClear_grid_vote (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (h : v.headDomain = none) :
    (GridCO.admitVote q v o).headDomain = none := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first | exact h | (split <;> exact h)
private theorem domainClear_grid_proposal (q : GridCO.Params) (v : GridCO.State n .root)
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
         exact domainClear_grid_vote q acc (GridCO.fromHead row) ha)
private theorem domainClear_norm (st : State n) (h : DomainClear st) :
    DomainClear (normalizeS st) := by
  delta normalizeS
  split <;> exact h
private theorem domainClear_reconcile (st : State n) (h : DomainClear st) :
    DomainClear (reconcile st) := by
  apply domainClear_norm
  exact h
private theorem domainClear_collect (st : State n) (h : DomainClear st) :
    DomainClear (collectPCs st) := by
  apply collectPCs_invariant DomainClear
  · intro st C h _
    rw [installPC_def]
    split <;> exact h
  · exact h
private theorem domainClear_raw (st : State n) (a : AckWire n) (h : DomainClear st) :
    DomainClear (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h
private theorem domainClear_row (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : DomainClear st) : DomainClear (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h
private theorem domainClear_process (p : Params) (st : State p.n) (o : Wire p.n)
    (h : DomainClear st) : DomainClear (process p st o) := by
  change st.base.headDomain = none at h
  change (process p st o).base.headDomain = none
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : DomainClear st) :
      DomainClear (as.foldl poolAckRaw st) := by
    apply List.foldlRecOn
    · exact h
    · intro acc hh a _
      exact domainClear_raw acc a hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : DomainClear st) :
      DomainClear (as.foldl (admitRow p) st) := by
    apply List.foldlRecOn
    · exact h
    · intro acc hh a _
      exact domainClear_row p acc a hh
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact domainClear_grid_vote p.toParams.engine st.base _ h
    | row i body => exact domainClear_row p st _ h
    | ack s i r =>
      apply domainClear_collect
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
      · exact domainClear_collect _ (ha st C.acks h)
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
            apply domainClear_collect
            apply ha
            cases N.pc <;> dsimp only
            all_goals split_ifs <;> first
              | exact domainClear_grid_proposal p.toParams.engine st.base _ _ _ h
              | (apply domainClear_reconcile
                 exact domainClear_grid_proposal p.toParams.engine st.base _ _ _ h)
end AvailableChain.PCSA
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem domain_clock_norm (st : State n) :
    (normalizeS st).base.headDomain = st.base.headDomain := by
  delta normalizeS
  split <;> rfl
private theorem domain_clock_reconcile (st : State n) :
    (reconcile st).base.headDomain = st.base.headDomain := by
  delta reconcile
  rw [domain_clock_norm]
private theorem domain_clock_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.headDomain = st.base.headDomain := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem domain_clock_collect (st : State n) :
    (collectPCs st).base.headDomain = st.base.headDomain := by
  apply collectPCs_preserves (fun st => st.base.headDomain)
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem domain_clock_raw_ack (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.headDomain = st.base.headDomain := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem domain_clock_gate (p : Params) (st : State n) (a : Block)
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
theorem pcsa_clock_headDomain (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.headDomain = st.base.headDomain := by
  have hp : (clockPre p st t).base.headDomain = st.base.headDomain := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, domain_clock_norm]
    split
    · exact hp
    · rw [domain_clock_gate]
      exact hp
  · exact hp
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every run store resolves root wires in its cumulative body list. -/
theorem pcsa_headDomain_stateBefore_none (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) :
    (V2.D.Run.stateBefore E rho k x).st.base.headDomain = none := by
  refine Gen.V2.Duty.invariant_triple (P := pcsaWith m p c)
    (fun nd : Node p => DomainClear nd.st) rfl ?_ ?_ (fun _ _ h => h)
    (fun _ _ => rfl) E rho k x
  · intro nd t h
    change (clock p nd.st t).base.headDomain = none
    rw [pcsa_clock_headDomain]
    exact h
  · intro nd o h
    exact domainClear_process p nd.st (toWire p o) h
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- An exact relayed body resolves the signed HEAD at any honest stage-1 clocked read. -/
theorem pcsa_resolved_head_of_held_body (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (k : Nat) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (B : Block) (u : Time)
    (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k x).st u))
      ⟨.seat s i, .head B.root⟩ = some B := by
  have hf : (clock p (V2.D.Run.stateBefore E rho k x).st u).fg.F = .genesis := by
    rw [pcsa_body_clock_fg]
    exact (hF x hx k).1
  have hblocks := pcsa_actView_blocks_of_genesis _ hf
  have hclock := pcsa_clock_blocks p (V2.D.Run.stateBefore E rho k x).st u
  have hdomain := pcsa_headDomain_stateBefore_none E rho k x
  have hclockDomain := pcsa_clock_headDomain p (V2.D.Run.stateBefore E rho k x).st u
  have hscope := pcsa_body_scope E rho k x hx
  have hunique : ∀ A ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks,
      ∀ C ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks, A.root = C.root → A = C := by
    intro A ha C hc hr
    exact pcsa_scoped_root_eq E rho h.idealization A C
      (hscope A ha) (hscope C hc) hr
  have hlookup := Block.findByRoot?_of_unique hm hunique
  have hd : GridCO.resolutionTree
      (actView (clock p (V2.D.Run.stateBefore E rho k x).st u)) =
      (V2.D.Run.stateBefore E rho k x).st.base.blocks := by
    change GridCO.resolutionTree
      ((clock p (V2.D.Run.stateBefore E rho k x).st u).base) = _
    change (clock p (V2.D.Run.stateBefore E rho k x).st u).base.headDomain.getD
      (clock p (V2.D.Run.stateBefore E rho k x).st u).base.blocks = _
    rw [hclockDomain, hdomain]
    exact hclock
  have hmem : B ∈ (actView (clock p (V2.D.Run.stateBefore E rho k x).st u)).blocks := by
    rw [hblocks, hclock]
    exact hm
  delta GridCO.resolvedHead?
  change ((Block.findByRoot? _ B.root).bind fun A => if A ∈ _ then some A else none) = some B
  rw [hd]
  have hl : Block.findByRoot?
      (V2.D.Run.stateBefore E rho k x).st.base.blocks B.root = some B := hlookup
  rw [hl]
  exact ite_eq_left hmem
end AvailableChain.PCSA.Run

end
