module
public import AvailableChainFGSARun.Proofs.Hooks
public import AvailableChainGeneric.Proofs.V2.Duty.Receipt
public import AvailableChainGeneric.Statements.V2.Duty.Receipt

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In : Type} {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An object that does not decode as a block has no dependencies. -/
theorem depsS_of_not_block (st : State p.n) (o : Obj p)
    (hNotBlock : ∀ s N,
      (toWire p o).decode ≠ some (.block s N)) :
    depsS p st o = true := by
  change (match (toWire p o).decode with
    | some (.block _ N) => namedParentHeld st N && (parentFG st N.erase).isSome
    | _ => true) = true
  cases hd : (toWire p o).decode with
  | none => rfl
  | some m =>
    cases m with
    | vote s i b => rfl
    | row i body => rfl
    | block s N => exact False.elim (hNotBlock s N hd)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A non-proposal payload has no dependencies, for any authentication. -/
theorem depsS_of_not_proposal (st : State p.n) (o : Obj p)
    (hNotProposal : ∀ N, o.payload ≠ .proposal N) :
    depsS p st o = true := by
  apply depsS_of_not_block st o
  intro s N hd
  have hp := congrArg Signed.payload (decode_eq_block.mp hd)
  exact hNotProposal N hp

variable {V : Type} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {dl : Time → Time} {t : Time} {w : V} {o : Obj p}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The delivery wire check supplies well-formedness of each handled child. -/
theorem fgsa_hWF_of_delivery
    (hWire : ∀ (i : Nat) (v : V) (o' : Obj p) (t' : Time),
      rho.events[i]? = some (.deliver v o' t') →
      (fgsa p c).wellFormed o' = true) :
    ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true := by
  intro i t' _ hh
  obtain ⟨o', he, hh⟩ := hh
  exact handles_wellFormed p c _ o' o hh (hWire i w o' t' he)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Readiness before the deadline for an object that does not decode as a block. -/
theorem fgsa_hReady_of_not_block
    (hNotBlock : ∀ s N,
      (toWire p o).decode ≠ some (.block s N))
    (hWF : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true) :
    ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho i w) o = true := by
  intro i t' hi hh
  exact ⟨hWF i t' hi hh, depsS_of_not_block _ o hNotBlock⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Proposal readiness reduces to its FG parent being stored at each handled event. -/
theorem fgsa_hReady_of_parentStored
    {s : Slot} {N : NamedProposal p.n}
    (hBlock : (toWire p o).decode = some (.block s N))
    (hWF : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true)
    (hParent : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) →
      V2.D.Run.handlesAt E rho i w o t' →
      namedParentHeld (V2.D.Run.stateBefore E rho i w).st N = true ∧
        (parentFG (V2.D.Run.stateBefore E rho i w).st N.erase).isSome = true) :
    ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho i w) o = true := by
  intro i t' hi hh
  refine ⟨hWF i t' hi hh, ?_⟩
  change (match (toWire p o).decode with
    | some (.block _ M) => namedParentHeld (V2.D.Run.stateBefore E rho i w).st M &&
        (parentFG (V2.D.Run.stateBefore E rho i w).st M.erase).isSome
    | _ => true) = true
  rw [hBlock]
  exact Bool.and_eq_true_iff.mpr (hParent i t' hi hh)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[T7.12 input; lead decision (c)+(iii)] `accepted_by_deadline` for an FG-SA proposal,
with `hReady` discharged from `hWF` and the named parent hypothesis `hParent`
(the K8 dependency-ordering fact). The frozen Gen boundary is used unchanged. -/
theorem fgsa_accepted_by_deadline_of_parentStored
    {p : Params} {In : Type} {c : AppCodec In} {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {Timely : (fgsa p c).State → (fgsa p c).Object → Prop}
    {Inv : (fgsa p c).State → Prop}
    (dl : Time → Time) (cut : Time) (o : Obj p) (t : Time) (w : V)
    {s : Slot} {N : NamedProposal p.n}
    (hBlock : (toWire p o).decode = some (.block s N))
    (hWF : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true)
    (hParent : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) →
      V2.D.Run.handlesAt E rho i w o t' →
      namedParentHeld (V2.D.Run.stateBefore E rho i w).st N = true ∧
        (parentFG (V2.D.Run.stateBefore E rho i w).st N.erase).isSome = true)
    (hD : Gen.V2.Duty.DeliveryWithin E rho dl cut)
    (hT : Gen.V2.Duty.ReadyTrigger E rho o t w t (dl t))
    (hw : w ∈ rho.honest) (ht0 : 0 ≤ t) (hcut : dl t ≤ cut) (hlt : t < dl t)
    (hhor : dl t ≤ rho.horizon)
    (hHistory : Gen.V2.Duty.HistorySafeAt E rho w o t)
    (hS : V2.D.ScheduleWellFormed E rho)
    (hrf : V2.D.restartFree rho w (V2.D.Run.actionCut rho t)
      (V2.D.Run.idxBefore rho (dl t)))
    (hHooks : V2.D.HooksSound (fgsa p c))
    (hA : Gen.V2.Duty.AcceptanceLaw (fgsa p c) Timely Inv)
    (hInv : ∀ i, Inv (V2.D.Run.stateBefore E rho i w))
    (hTimely : ∀ i t', t ≤ t' → t' < dl t → V2.D.Run.handlesAt E rho i w o t' →
      Timely (V2.D.Run.stateBefore E rho i w) o)
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho (dl t) w) o = true := by
  apply Gen.V2.Duty.accepted_by_deadline E rho Timely Inv dl cut o t t w hD hT hw
    (le_refl t) ht0 hlt hcut hhor hHistory hS hrf hHooks hA ?_ hNX
  intro i t' htt htd hh
  have hcall := hh
  obtain ⟨parent, he, -⟩ := hh
  have hi := (Gen.V2.Duty.index_lt_idxBefore_iff hS he (dl t)).2 htd
  obtain ⟨hWF', hDeps⟩ := fgsa_hReady_of_parentStored hBlock hWF hParent i t' hi hcall
  exact ⟨hInv i, hWF', hDeps, hTimely i t' htt htd hcall⟩

end AvailableChain.FGSA.Run
end
