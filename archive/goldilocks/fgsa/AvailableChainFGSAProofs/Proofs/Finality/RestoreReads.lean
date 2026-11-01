module
public import AvailableChainFGSAProofs.Proofs.Shared.RowReads -- shake: keep (source declarations)
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGCompose.Proofs.Finality.RestoreReads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def d7a5rr_proposalFG := (fgsaCoreReads p c).proposalFG

private theorem d7a5rr_reads_eq :
    fgsaCoreReads p c =
      { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
        erase := eraseFG
        source := fun nd => FGSA.fgSource p nd.st
        headVote := fun nd s => FGSA.headVote p nd.st s
        finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
        proposalFG := d7a5rr_proposalFG p c } :=
  congrArg (fun reads => { reads with proposalFG := d7a5rr_proposalFG p c })
    (fgsaCoreReads_def p c)

/-- The FG-SA durable-finality leaves: the step laws and the restart store equation. -/
private theorem d7a5rr_durable : FGCompose.FGFinalityDurableLaws (fgsaCoreReads p c) := by
  rw [d7a5rr_reads_eq]
  refine ⟨fun X => fgsa_monoAlong_preceq_F p c X, fun nd t => ?_⟩
  change (acRestart p nd.st t).fg.F = nd.st.fg.F
  rw [acRestart_fg]

private theorem d7a5rr_accepts_eq (x : V) (X : FGBlock (Fin p.n)) (d : Time) :
    FGCompose.AcceptsFinalBefore (fgsaCoreReads p c) E rho x X d =
      AcceptsFinalBefore p c E rho x X d := by
  rw [d7a5rr_reads_eq]
  rfl

/-- Finalized ancestry survives restore because F is durable. -/
theorem finality_restore_preceq_F (X : FGBlock (Fin p.n)) :
    ∀ nd t, FGBlock.Preceq X nd.st.fg.F →
      FGBlock.Preceq X ((fgsa p c).restore ((fgsa p c).durable nd) t).st.fg.F := by
  intro nd t h
  have r := FGCompose.finality_restore_preceq_F (fgsaCoreReads p c) (d7a5rr_durable p c) X nd t
  rw [d7a5rr_reads_eq] at r
  exact r h

/-- A strict-before index witness gives acceptance across sleep and restore. -/
theorem finality_acceptsFinalBefore_of_idx
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X : FGBlock (Fin p.n)} {d : Time}
    (h : ∃ i ≤ rho.events.length,
      (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
      FGBlock.Preceq X (storeAt p c E rho i x).fg.F) :
    AcceptsFinalBefore p c E rho x X d := by
  rw [← d7a5rr_accepts_eq]
  apply FGCompose.finality_acceptsFinalBefore_of_idx _ E rho (d7a5rr_durable p c) hs
  rw [d7a5rr_reads_eq]
  exact h

/-- A later deadline preserves acceptance of durable finality. -/
theorem finality_acceptsFinalBefore_mono_deadline
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X : FGBlock (Fin p.n)}
    {d d' : Time} (hdd : d ≤ d') (h : AcceptsFinalBefore p c E rho x X d) :
    AcceptsFinalBefore p c E rho x X d' := by
  rw [← d7a5rr_accepts_eq] at h ⊢
  exact FGCompose.finality_acceptsFinalBefore_mono_deadline _ E rho (d7a5rr_durable p c) hs
    hdd h

/-- Acceptance of a descendant also accepts its ancestor at a later deadline. -/
theorem finality_acceptsFinalBefore_mono_ancestor
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X U : FGBlock (Fin p.n)}
    {d d' : Time} (hXU : FGBlock.Preceq X U) (hdd : d ≤ d')
    (h : AcceptsFinalBefore p c E rho x U d) : AcceptsFinalBefore p c E rho x X d' := by
  rw [← d7a5rr_accepts_eq] at h ⊢
  exact FGCompose.finality_acceptsFinalBefore_mono_ancestor _ E rho (d7a5rr_durable p c) hs
    hXU hdd h

private theorem d7a5rr_rowHeld_eq (nd : (fgsa p c).State) (a : RowWire p.n) :
    FGCompose.rowHeld (fgsaCoreReads p c) (fun nd => FGSA.blockWireRows nd.st) nd a =
      rowHeld p nd.st a := by
  rw [d7a5rr_reads_eq]
  rfl

/-- Held rows are cumulative along the run, including restore. -/
private theorem d7a5rr_held_durable (i j : Nat) (x : V) (a : RowWire p.n) (hij : i ≤ j)
    (h : rowHeld p (storeAt p c E rho i x) a) : rowHeld p (storeAt p c E rho j x) a := by
  have hcumul := fgsa_store_durable p c E rho hij x
  rcases h with hp | hb
  · exact Or.inl (hcumul.2.2.2.subset hp)
  · right
    change a ∈ allBlockRows _ at hb
    change a ∈ allBlockRows _
    unfold allBlockRows at hb ⊢
    obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp hb
    obtain ⟨w, hw, hdec⟩ := List.mem_filterMap.mp hxs
    exact List.mem_flatten.mpr ⟨xs,
      List.mem_filterMap.mpr ⟨w, hcumul.2.2.1.subset hw, hdec⟩, ha⟩

/-- The clock keeps the row pool and the proposals. -/
private theorem d7a5rr_held_clock (st : State p.n) (t : Time) (a : RowWire p.n)
    (h : rowHeld p st a) : rowHeld p (FGSA.clock p st t) a := by
  rcases h with hp | hb
  · left
    rw [clock_rowPool]
    exact hp
  · right
    change a ∈ allBlockRows _ at hb
    change a ∈ allBlockRows (FGSA.clock p st _)
    unfold allBlockRows at hb ⊢
    rw [clock_proposals]
    exact hb

/-- Durable rows remain held at a later proposal read across restore. -/
theorem finality_heldBefore_at_proposal (hs : V2.D.ScheduleWellFormed E rho)
    {s : Slot} {a : RowWire p.n} {d : Time} {st : State p.n}
    (hst : proposalStateAt p c E rho s = some st)
    (hheld : HeldBefore p c E rho (V2.D.proposerOf rho (fgsaInterface p c) s) a d)
    (hd : d ≤ SA.proposalTime p.toParams s) : heldAtProposal p c E rho s a := by
  obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
  have r := FGCompose.finality_heldBefore_at_proposal (fgsaCoreReads p c) E rho
    (fgsaInterface p c) (fun nd => FGSA.blockWireRows nd.st) hs
    (fun i j x a hij h => by
      rw [d7a5rr_rowHeld_eq] at h ⊢
      exact d7a5rr_held_durable p c E rho i j x a hij h)
    (fun nd t a h => by
      rw [d7a5rr_rowHeld_eq] at h ⊢
      exact d7a5rr_held_clock p nd.st t a h)
    hnd (by
      revert hheld
      delta HeldBefore FGCompose.HeldBefore
      simp only [d7a5rr_rowHeld_eq]
      exact id) hd
  obtain ⟨nd', hnd', hheld'⟩ := r
  rw [d7a5rr_rowHeld_eq] at hheld'
  exact ⟨nd'.st, Option.map_eq_some_iff.mpr ⟨nd', hnd', rfl⟩, hheld'⟩

end AvailableChain.FGSA.Run
end
