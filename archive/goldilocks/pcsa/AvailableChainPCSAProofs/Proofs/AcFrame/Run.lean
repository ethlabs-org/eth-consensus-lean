module
public import AvailableChainPCSAProofs.Proofs.AcFrame.Rows
public import AvailableChainPCSAProofs.Proofs.AcFrame.Store

public section

/-! AC-only frame invariant over the authenticated event run (pcsa34-r4.3 §5.0). -/

namespace AvailableChain.PCSA.Run
open SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem decoded_block_payload (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) : o.payload = .proposal N := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> simp [toWire, toAuth, Wire.decode] at h
  | seat l i =>
    cases l with
    | base l => cases l <;> cases payload <;> simp [toWire, toAuth, Wire.decode] at h
    | prop j =>
      cases payload <;> simp only [toWire, toAuth, Wire.decode] at h
      all_goals first | contradiction | (cases h; rfl)

private theorem row_wire_shape (a : RowWire p.n) (r : Row (Fin p.n))
    (h : a.toRow? = some r) : ∃ body, a = ⟨.seat .fg r.signer, body⟩ := by
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => dsimp only [RowWire.toRow?, RowWire.decode?] at h; contradiction
  | proposer s => dsimp only [RowWire.toRow?, RowWire.decode?] at h; contradiction
  | seat l i =>
    cases l with
    | head s => dsimp only [RowWire.toRow?, RowWire.decode?] at h; contradiction
    | ack s => dsimp only [RowWire.toRow?, RowWire.decode?] at h; contradiction
    | fg =>
      have hr : body.toRow i = r := Option.some.inj h
      subst r
      exact ⟨body, rfl⟩

/-- Every decoded row in a delivered block has a faulty FG holder. -/
theorem pcsa_ac_block_rows_faulty (E : Generic.Env V) (rho : V2.D.Run V (pcsaAC p c))
    (hv : V2.D.UnforgeableSignatures E rho) (x : V) (o : Obj p) (t : Time)
    (hp : V2.D.Run.processes rho x o t) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    ∀ r ∈ N.rows.filterMap RowWire.toRow?, rho.seatOf (.base .fg) r.signer ∉ rho.honest := by
  intro r hr
  obtain ⟨a, ha, har⟩ := List.mem_filterMap.mp hr
  obtain ⟨body, he⟩ := row_wire_shape a r har
  subst a
  apply pcsa_ac_carried_row_faulty E rho hv x o t hp r.signer body
  change carriesS p o _
  delta carriesS
  rw [decoded_block_payload o s N hd]
  exact Or.inl (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨_, ha, rfl⟩))))

/-- The initial store satisfies the AC frame invariant for any faulty seat set. -/
theorem pcsa_initial_acSafe (F : Finset (Fin p.n)) : AcStoreSafe F (initial p.n) := by
  rw [AcStoreSafe_def]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro B hB W hW a ha
  have hB' : B = .genesis := Finset.mem_singleton.mp hB
  subst B
  have hW' := KitFG.preceq_genesis.mp hW
  subst W
  exact (List.not_mem_nil ha).elim

/-- Authenticated AC-only executions keep the store frame initial. -/
theorem pcsa_ac_storeSafe (E : Generic.Env V) (rho : V2.D.Run V (pcsaAC p c))
    (hv : V2.D.ExecutionValid E rho) (F : Finset (Fin p.n))
    (hF : p.E.weightOf F < p.E.q)
    (hmem : ∀ i, i ∈ F ↔ rho.seatOf (.base .fg) i ∉ rho.honest)
    (j : Nat) (v : V) : AcStoreSafe F (V2.D.Run.stateBefore E rho j v).st := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => AcStoreSafe F nd.st) (Nat.zero_le j) v ?_ (pcsa_initial_acSafe F)
  intro k e _ _ he hn h
  cases e with
  | restart u t =>
    change u = v at hn
    subst u
    change AcStoreSafe F (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact pcsa_initial_acSafe F
  | tick u t =>
    change u = v at hn
    subst u
    change AcStoreSafe F (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    have ht : (V2.D.tick E rho (V2.D.Run.stateBefore E rho k v) v t).1.st =
        clock p (V2.D.Run.stateBefore E rho k v).st t :=
      pcsa_tick_st (p := p) (c := c) (m := .idle) E rho (V2.D.Run.stateBefore E rho k v) v t
    rw [ht]
    simpa only [AcStoreSafe_def, pcsa_clock_fg] using h
  | deliver u o t =>
    change u = v at hn
    subst u
    change AcStoreSafe F (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    apply pcsa_process_acSafe p F hF _ (toWire p o) h
    intro s N hd a ha
    exact (hmem a.signer).mpr
      (pcsa_ac_block_rows_faulty E rho hv.toUnforgeableSignatures v o t ⟨k, he⟩ s N hd a ha)

/-- The PC fault bound and linked FG seats give the AC-only frame at every event state. -/
theorem pcsa_ac_frame [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (pcsaAC p c))
    (h : Base₂ p c E rho) (hf : FaultsBelowQA p c rho) : StageOneFrame p c E rho := by
  classical
  let F : Finset (Fin p.n) := Finset.univ.filter (fun i => rho.seatOf (.base .fg) i ∉ rho.honest)
  have hmem (i : Fin p.n) : i ∈ F ↔ rho.seatOf (.base .fg) i ∉ rho.honest := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  have hi : Function.Injective (rho.seatOf (.base .fg)) :=
    (h.linked.toCStar (.base .fg) trivial).1
  have hcard : F.card ≤ (Gen.V2.Duty.faulty rho).card := by
    rw [← Finset.card_image_of_injective F hi]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hmem i).mp hi⟩
  have hcap : p.E.weightOf F < p.E.q :=
    pcsa_faults_lt_fg_quorum p F (hcard.trans_lt hf)
  intro v _ j
  exact pcsa_acSafe_frame p F _ (pcsa_ac_storeSafe E rho h.valid F hcap hmem j v)

end AvailableChain.PCSA.Run
end
