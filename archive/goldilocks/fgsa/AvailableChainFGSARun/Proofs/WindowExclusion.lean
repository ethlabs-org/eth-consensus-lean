module
public import AvailableChainFGSARun.Proofs.EmissionWellFormed
public import AvailableChainFGSA.Proofs.WindowAdmissionInvariant
public import AvailableChainFGSA.Proofs.WindowOccurrences -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem decoded_r3W (wire : RowWire p.n) (a : Row (Fin p.n))
    (decode : wire.toRow? = some a) (valid : wire.valid = true) :
    (RowBody.ofRow a).valid = true := by
  change wire.decode?.map (fun x => x.2.toRow x.1) = some a at decode
  obtain ⟨⟨i, payload⟩, hd, eq⟩ := Option.map_eq_some_iff.mp decode
  cases payload with
  | vote body =>
      subst a
      change body.valid = true
      change (wire.decode?.map (fun x => x.2.valid)).getD false = true at valid
      rw [hd] at valid
      exact valid

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Checked deliveries supply R3 for each decoded row of a stored block.
The existing execution validity includes this delivery check. -/
theorem stored_rows_r3W (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (checked : V2.D.DeliveryWellFormed E rho) (i : Nat) (v : V)
    (P : FGBlock (Fin p.n)) (s : Slot) (root : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (stored : FGBlock.node P s root x rs ∈ (V2.D.Run.stateBefore E rho i v).st.fg.TF)
    (a : Row (Fin p.n)) (ha : a ∈ rs) : (RowBody.ofRow a).valid = true := by
  have bundle := storeBundle_stateBefore E rho i v
  obtain ⟨t, N, wire, _, sameRows⟩ := stored_wire_of_block p _ bundle.cstore
    bundle.«meta» stored (by intro eq; cases eq)
  change rs = N.rows.filterMap RowWire.toRow? at sameRows
  rw [sameRows] at ha
  obtain ⟨w, hw, hd⟩ := List.mem_filterMap.mp ha
  have hr := (fgsa_emissionRowsValid E rho checked i v).2
    _ wire t N rfl w hw
  exact decoded_r3W w a hd hr

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. The combined R3/R6W ancestor premise follows from the run's existing
validity and local admission history. It is not a new caller obligation. -/
theorem stored_chain_rowsValidW (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (checked : V2.D.DeliveryWellFormed E rho) (i : Nat) (v : V)
    (B : FGBlock (Fin p.n)) (stored : B ∈ (V2.D.Run.stateBefore E rho i v).st.fg.TF) :
    ∀ P s root x rs, FGBlock.Preceq (.node P s root x rs) B → ∀ a ∈ rs,
      (RowBody.ofRow a).valid = true ∧ Window.r6w (Window.derive p p.K_W P) a = true := by
  intro P s root x rs ancestor a ha
  have reachable := reachable_stateBefore E rho i v
  have closed := ancestor_closed_of_parent_closed _
    (storeBundle_stateBefore E rho i v).cstore.fg.closed
  exact ⟨stored_rows_r3W E rho checked i v P s root x rs (closed B stored _ ancestor) a ha,
    stored_chain_r6wW p reachable B stored P s root x rs ancestor a ha⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Exact-row exclusion at a stored block in a valid run. The signer is
already in the retained entry's Q; the pure R3/R6W input is discharged here. -/
theorem exact_row_exclusion_checkedW (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (checked : V2.D.DeliveryWellFormed E rho) (i : Nat) (v : V)
    (B : FGBlock (Fin p.n)) (stored : B ∈ (V2.D.Run.stateBefore E rho i v).st.fg.TF)
    (y : Height) (U : FGBlock (Fin p.n)) (d : Window.Entry (Fin p.n))
    (hd : d ∈ (Window.derive p p.K_W B).W) (hj : d.j = y) (hX : d.X = U)
    (P : FGBlock (Fin p.n)) (s : Slot) (root : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (ancestor : FGBlock.Preceq (.node P s root x rs) B) (a : Row (Fin p.n)) (ha : a ∈ rs)
    (matchRow : a.finality_pair = some ⟨y, U.root⟩) : a.signer ∈ d.Q :=
  Window.window_exact_row_no_missing_effect p p.K_W p.kWLarge B y U d hd hj hX
    (stored_chain_rowsValidW E rho checked i v B stored) P s root x rs ancestor a ha matchRow

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. The public execution-validity form consumes its existing delivery field. -/
theorem exact_row_exclusionW (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (valid : V2.D.ExecutionValid E rho) (i : Nat) (v : V)
    (B : FGBlock (Fin p.n)) (stored : B ∈ (V2.D.Run.stateBefore E rho i v).st.fg.TF)
    (y : Height) (U : FGBlock (Fin p.n)) (d : Window.Entry (Fin p.n))
    (hd : d ∈ (Window.derive p p.K_W B).W) (hj : d.j = y) (hX : d.X = U)
    (P : FGBlock (Fin p.n)) (s : Slot) (root : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (ancestor : FGBlock.Preceq (.node P s root x rs) B) (a : Row (Fin p.n)) (ha : a ∈ rs)
    (matchRow : a.finality_pair = some ⟨y, U.root⟩) : a.signer ∈ d.Q :=
  exact_row_exclusion_checkedW E rho valid.toDeliveryWellFormed i v B stored y U d hd hj hX
    P s root x rs ancestor a ha matchRow

end AvailableChain.FGSA.Run
end
