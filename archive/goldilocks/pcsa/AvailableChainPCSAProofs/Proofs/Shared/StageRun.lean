module
public import AvailableChainPCSAProofs.Proofs.Shared.StageStore
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSARun.Statements.Roots
public import AvailableChainKitV2.DutyStable

public section

/-! Run forms of the Outage store facts (pcsa34-r4.3 §5.4.1, stage 1): the
store invariant at every indexed state of an honest node, and the stage-1
monotonicity of held PCs and stored frozen rows between two indices. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A decoded proposal wire carries that proposal as its payload. -/
theorem pcsa_outage_decoded_proposal (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) : o.payload = .proposal N := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> simp [toWire, toAuth, Wire.decode] at h
  | seat l j =>
    cases l with
    | prop k =>
      cases payload <;> simp [toWire, toAuth, Wire.decode] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | base l => cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h

/-- Every indexed store of an honest node satisfies the Outage store invariant
for the run's named blocks. -/
theorem pcsa_outageStore_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (i : Nat) (v : V) (hv : v ∈ rho.honest) :
    OutageStore (RootBlockInRun p c E rho) (V2.D.Run.stateBefore E rho i v).st := by
  have hg : RootBlockInRun p c E rho .genesis := by
    refine ⟨.genesis, ⟨.genesis, Or.inr ⟨v, hv, 0, ?_⟩, ?_⟩, rfl⟩
    · dsimp only [V2.D.Run.stateBefore, pcsaWith]
      dsimp only [initial]
      simp [State.namedBodies]
    · simp [NamedProposal.Preceq, NamedProposal.preceq]
  have hz : OutageStore (RootBlockInRun p c E rho) (initial p.n) :=
    pcsa_initial_outageStore _ hg
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => OutageStore (RootBlockInRun p c E rho) nd.st) (Nat.zero_le i) v ?_ hz
  intro k e _ _ he hn h
  cases e with
  | restart u t =>
    change u = v at hn
    subst u
    change OutageStore _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact hz
  | tick u t =>
    change u = v at hn
    subst u
    change OutageStore _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self, pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k v) v t]
    exact pcsa_clock_outageStore p _ _ t h
  | deliver u o t =>
    change u = v at hn
    subst u
    change OutageStore _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    apply pcsa_process_outageStore p _ _ (toWire p o) h
    intro s N hd
    refine ⟨N, ⟨N, Or.inl ⟨v, o, t, List.mem_of_getElem? he,
      pcsa_outage_decoded_proposal o s N hd⟩, ?_⟩, rfl⟩
    cases N <;> simp [NamedProposal.Preceq, NamedProposal.preceq]

/-- The stage-1 monotonicity of one honest node between two indices: held PCs
stay held, and a stored frozen row keeps its PCs. -/
theorem pcsa_stageOne_mono (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hnr : V2.D.NoRestart rho) (hfr : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i x).st.pcs ⊆ (V2.D.Run.stateBefore E rho j x).st.pcs ∧
    ∀ k, ((V2.D.Run.stateBefore E rho i x).st.pcSnapshot.find? (fun row => row.1 == k)).isSome →
      pcSnapshotAt (V2.D.Run.stateBefore E rho j x).st k =
        pcSnapshotAt (V2.D.Run.stateBefore E rho i x).st k ∧
      ((V2.D.Run.stateBefore E rho j x).st.pcSnapshot.find? (fun row => row.1 == k)).isSome := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i x).st.pcs ⊆ nd.st.pcs ∧
      ∀ k, ((V2.D.Run.stateBefore E rho i x).st.pcSnapshot.find?
          (fun row => row.1 == k)).isSome →
        pcSnapshotAt nd.st k = pcSnapshotAt (V2.D.Run.stateBefore E rho i x).st k ∧
        (nd.st.pcSnapshot.find? (fun row => row.1 == k)).isSome) hij x ?_
    ⟨List.Subset.refl _, fun k hk => ⟨rfl, hk⟩⟩
  intro k e _ _ he hn h
  cases e with
  | restart u t =>
    exact absurd he (hnr k u t)
  | tick u t =>
    change u = x at hn
    subst u
    have hs : (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.tick x t) x).st =
        clock p (V2.D.Run.stateBefore E rho k x).st t := by
      change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
      rw [Function.update_self]
      exact pcsa_tick_st E rho _ x t
    rw [hs, (pcsa_clock_frame p _ t).1]
    refine ⟨h.1, fun k' hk => ?_⟩
    obtain ⟨h1, h2⟩ := h.2 k' hk
    obtain ⟨g1, g2⟩ := pcsa_clock_pcSnapshotAt p _ t k' h2
    exact ⟨g1.trans h1, g2⟩
  | deliver u o t =>
    change u = x at hn
    subst u
    have hF : (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).fg.F = .genesis := by
      have hv := hfr x hx (k + 1)
      rw [V2.D.Run.stateBefore_succ E rho he] at hv
      change FrameVacuous p (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st at hv
      rw [Function.update_self] at hv
      exact ((FrameVacuous_def p _).mp hv).1
    obtain ⟨g1, g2⟩ := pcsa_process_stageOne p _ (toWire p o) hF
    have hs : (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.deliver x o t) x).st =
        process p (V2.D.Run.stateBefore E rho k x).st (toWire p o) := by
      change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
      rw [Function.update_self]
      rfl
    rw [hs]
    refine ⟨List.Subset.trans h.1 g1, fun k' hk => ?_⟩
    rw [pcSnapshotAt_eq_of_list_eq _ _ k' g2, g2]
    exact h.2 k' hk

end AvailableChain.PCSA.Run
end
