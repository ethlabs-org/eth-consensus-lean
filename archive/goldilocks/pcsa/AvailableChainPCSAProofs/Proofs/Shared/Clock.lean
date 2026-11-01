module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainKitV2.DutyEngineClock
public import AvailableChainFGSARun.Proofs.Excludes

public section

/-! Run clock facts for slot checks on honest acks. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem pcsa_internal_norm_now (st : State n) : (normalizeS st).base.now = st.base.now := by
  delta normalizeS
  split <;> rfl
private theorem pcsa_internal_row_now (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.now = st.base.now := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_internal_gate_now (p : Params) (a : Block) (cs : List (PC n))
    (rank : Option PCRank) (st : State n) (s : Slot) :
    (gateFrom p a cs rank st s).base.now = st.base.now := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => acc.base.now = st.base.now)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc : State n => acc.base.now = st.base.now)
        · exact ha
        · intro acc' ha' g _
          exact ha'
theorem pcsa_clock_now (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.now = t := by
  have hpre : (clockPre p st t).base.now = t := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, pcsa_internal_norm_now]
    split
    · exact hpre
    · rw [pcsa_internal_gate_now]
      exact hpre
  · exact hpre
theorem pcsa_process_now (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.now = st.base.now := by
  delta process
  cases hd : o.decode with
  | none => rfl
  | some msg => cases msg with
    | vote s i r => exact FGSA.Run.Internal.grid_admitVote_now _ _
    | row i body => exact pcsa_internal_row_now p st _
    | ack s i r =>
      change (collectPCs (poolAck p st (⟨o.auth, r⟩ : AckWire p.n))).base.now = _
      rw [(collectPCs_frame _).1]
      delta poolAck
      cases AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => rfl
      | some v =>
        dsimp only
        rcases v with ⟨_, _, _⟩
        split
        · rfl
        · split <;> rfl
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [(collectPCs_frame _).1]
        apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.now = st.base.now)
        · rfl
        · intro acc ha a _
          rw [(poolAckRaw_frame acc a).2.2.1]
          exact ha
      · rfl
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · rfl
      · cases parentFG st N.erase with
        | none => rfl
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.now = st.base.now)
            · rw [(collectPCs_frame _).1]
              have hm (st' : State p.n) :
                  (N.pcAcks.foldl poolAckRaw st').base.now = st'.base.now := by
                apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.now = st'.base.now)
                · rfl
                · intro acc ha a _
                  rw [(poolAckRaw_frame acc a).2.2.1]
                  exact ha
              rw [hm]
              cases N.pc <;> dsimp only
              all_goals repeat first
                | rfl
                | (delta reconcile; rw [pcsa_internal_norm_now])
                | split
                | exact FGSA.Run.Internal.grid_admitProposal_now _ _ _ _
            · intro acc ha a _
              rw [pcsa_internal_row_now]
              exact ha
          · rfl
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable (p : Params) {In : Type} (c : AppCodec In) {m : FGMode}
def pcsaClock : V2.D.Engine.ClockLaws (pcsaWith m p c) where
  now nd := nd.st.base.now
  init := rfl
  clock nd t := pcsa_clock_now p nd.st t
  process nd o := pcsa_process_now p nd.st (toWire p o)
  recordOwn_now _ _ := rfl
/-- The clock interface reads the base store clock. -/
theorem pcsa_clock_read (nd : Node p) :
    (pcsaClock p c (m := m)).now nd = nd.st.base.now := by
  change nd.st.base.now = nd.st.base.now
  rfl

end AvailableChain.PCSA.Run
end
