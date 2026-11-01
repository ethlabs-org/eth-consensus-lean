module
public import AvailableChainPCSAProofs.Proofs.Shared.BodyScope
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainFGSA.Proofs.HeadDomain

public section

/-! Store roots, shared by the lanes. Reachable stores keep the cumulative
resolution domain unset, so active and base HEAD resolution are root lookups.
An honest duty read is root-unique under run collision freedom, so a root
resolved in a sub-store resolves to the same body. Moved from the Formation
lane (Clean/FormationStore.lean, Clean/FormationInputs.lean, c45746d1). -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA
variable {n : Nat}

private theorem headDomain_installPC (st : State n) (c : PC n) :
    (installPC st c).base.headDomain = st.base.headDomain := by
  rw [installPC_def]
  split
  · rfl
  · rfl

private theorem headDomain_collect (st : State n) :
    (collectPCs st).base.headDomain = st.base.headDomain :=
  collectPCs_preserves (fun s => s.base.headDomain) headDomain_installPC st

private theorem headDomain_raws (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).base.headDomain = st.base.headDomain := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.1]

private theorem headDomain_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.headDomain = st.base.headDomain := by
  delta admitRow
  cases a.decode? <;> dsimp only
  split <;> rfl

private theorem headDomain_rows (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).base.headDomain = st.base.headDomain := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, headDomain_row]

private theorem headDomain_pool (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).base.headDomain = st.base.headDomain := by
  delta poolAck
  cases a.decode? with
  | none => rfl
  | some val =>
    rcases val with ⟨s, i, r⟩
    dsimp only
    split_ifs <;> rfl

private theorem headDomain_process (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.headDomain = st.base.headDomain := by
  cases hd : o.decode with
  | none => delta process; rw [hd]
  | some d =>
    cases d with
    | vote s i r =>
      delta process
      rw [hd]
      exact FGSA.admitVote_headDomain _ _ _
    | row i body => delta process; rw [hd, headDomain_row]
    | ack s i r =>
      delta process
      rw [hd]
      change (collectPCs (poolAck p st ⟨o.auth, r⟩)).base.headDomain = _
      rw [headDomain_collect, headDomain_pool]
    | pc C =>
      delta process
      rw [hd]
      change (admitPC st C).base.headDomain = _
      delta admitPC
      split
      · rw [headDomain_collect, headDomain_raws]
      · rfl
    | block s N =>
      delta process
      rw [hd]
      change (admitBlock p st s N).base.headDomain = _
      delta admitBlock
      split
      · rfl
      · cases parentFG st N.erase with
        | none => rfl
        | some B =>
          dsimp only
          split
          · rw [headDomain_rows, headDomain_collect, headDomain_raws]
            cases N.pc <;> dsimp only <;> split_ifs <;>
              first
              | exact FGSA.admitProposal_headDomain _ _ _ _ _
              | (delta reconcile normalizeS; dsimp only; split_ifs <;>
                  exact FGSA.admitProposal_headDomain _ _ _ _ _)
          · rfl

private theorem headDomain_gate (p : Params) (st : State p.n) (a : Block)
    (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.headDomain = st.base.headDomain := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some result =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn
        (motive := fun acc : State p.n => acc.base.headDomain = st.base.headDomain)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn
          (motive := fun acc' : State p.n => acc'.base.headDomain = st.base.headDomain)
        · exact ha
        · intro acc' ha' g _
          exact ha'

private theorem headDomain_clock (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.headDomain = st.base.headDomain := by
  have hp : (clockPre p st t).base.headDomain = st.base.headDomain := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    delta normalizeS
    split <;> split <;>
      first
      | exact hp
      | (rw [headDomain_gate]; exact hp)
  · exact hp

/-- Every reachable PC-SA store keeps the cumulative resolution domain unset. -/
theorem pcsa_reachable_headDomain_none (p : Params) (st : State p.n)
    (h : Reachable p st) : st.base.headDomain = none := by
  induction h with
  | init => rfl
  | tick t _ ih => rw [headDomain_clock, ih]
  | deliver o _ ih => rw [headDomain_process, ih]

/-- A root resolved in a sub-store resolves to the same body in a root-unique store. -/
theorem pcsa_findByRoot_mono {src dst : List Block} {r : BlockId} {B : Block}
    (hsub : src ⊆ dst) (hu : ∀ C ∈ dst, ∀ D ∈ dst, C.root = D.root → C = D)
    (h : Block.findByRoot? src r = some B) : Block.findByRoot? dst r = some B := by
  have hm := Block.findByRoot?_mem h
  have hr := Block.findByRoot?_root h
  exact (Block.findByRoot?_spec dst r B).mpr
    ⟨hsub hm, hr, fun C hC hCr => hu C hC B (hsub hm) (hCr.trans hr.symm)⟩

/-- With the cumulative domain unset, active resolution is a root lookup. -/
theorem pcsa_actView_resolved {n : Nat} (st : State n)
    (hd : st.base.headDomain = none) (o : GridCO.Wire n .root) (B : Block)
    (h : GridCO.resolvedHead? (actView st) o = some B) :
    ∃ r, GridCO.headTarget? o = some r ∧ Block.findByRoot? st.base.blocks r = some B := by
  have htree : GridCO.resolutionTree (actView st) = st.base.blocks := by
    change (some (GridCO.resolutionTree st.base)).getD (actView st).blocks = _
    rw [Option.getD_some, GridCO.resolutionTree, hd, Option.getD_none]
  rw [GridCO.resolvedHead?] at h
  cases ht : GridCO.headTarget? o with
  | none => rw [ht] at h; cases h
  | some r =>
    rw [ht] at h
    change Option.bind (GridCO.resolveTarget .root (GridCO.resolutionTree (actView st)) r)
      (fun B => if B ∈ (actView st).blocks then some B else none) = some B at h
    rw [htree, GridCO.resolveTarget] at h
    dsimp only at h
    cases hf : Block.findByRoot? st.base.blocks r with
    | none => rw [hf] at h; cases h
    | some C =>
      rw [hf] at h
      change (if C ∈ (actView st).blocks then some C else none) = some B at h
      split at h
      · cases h
        exact ⟨r, rfl, hf⟩
      · cases h

/-- With the cumulative domain unset, base resolution is a root lookup. -/
theorem pcsa_base_resolved {n : Nat} (st : State n)
    (hd : st.base.headDomain = none) (o : GridCO.Wire n .root) (r : BlockId) (B : Block)
    (ht : GridCO.headTarget? o = some r) (hf : Block.findByRoot? st.base.blocks r = some B) :
    GridCO.resolvedHead? st.base o = some B := by
  rw [GridCO.resolvedHead?, ht]
  change Option.bind (GridCO.resolveTarget .root (GridCO.resolutionTree st.base) r)
    (fun B => if B ∈ st.base.blocks then some B else none) = some B
  rw [GridCO.resolutionTree, hd, Option.getD_none, GridCO.resolveTarget]
  dsimp only
  rw [hf]
  change (if B ∈ st.base.blocks then some B else none) = some B
  split
  · rfl
  · exact absurd (Block.findByRoot?_mem hf) ‹_›

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every body of an honest duty read is in the run's named root scope. -/
theorem pcsa_read_root_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho) (y : V)
    (hy : y ∈ rho.honest) (t : Time) (nd : Node p) (hr : pcsa_postClock E rho y t = some nd) :
    ∀ C ∈ nd.st.base.blocks, ∀ D ∈ nd.st.base.blocks, C.root = D.root → C = D := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  have hscope := pcsa_clock_body_scope p (RootBlockInRun p c E rho)
    (V2.D.Run.stateBefore E rho k y).st t (pcsa_body_scope E rho k y hy)
  intro C hC D hD he
  exact pcsa_scoped_root_eq E rho hBase.idealization C D (hscope C hC) (hscope D hD) he

/-- A post-clock duty read is a reachable store. -/
theorem pcsa_read_reachable (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (y : V) (t : Time) (nd : Node p)
    (hr : pcsa_postClock E rho y t = some nd) : Reachable p nd.st := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  exact Reachable.tick _ (pcsa_reachable_stateBefore E rho k y)

end AvailableChain.PCSA.Run
end
