module
public import AvailableChainFGCompose.Proofs.ExecutionObs
public import AvailableChainGeneric.Proofs.V2.Duty.Reads

public section

/-! X1b: accepted-body origin of the driver observation, the strict-cut causal history at a
real held cut (generic), at the driver's drained duty HEAD read, and the one-way ordinary
bridge from the nested strict-time history `ChainRowsBefore`. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body Row Latest LeafIn : Type}
variable {Leaf : V2.ProtocolSpecD LeafIn}

/-- Receiver-local driver origin: every body that a trace step adds to accepted storage is
accepted by that step's leaf operation with its original token, whose full receipt origin
(receiver, delivery index, wire, receipt time, epoch, decode, geometry and rows) holds. -/
theorem accepted_body_origin_driver_at (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) (x : V)
    (TL : FGDependencyTraceLaws E rho x H W D L Step (T x) F (Op x) Arrival Notify
      leafState leafWire ActualRead)
    (hacc : ∀ k b, k ≤ (T x).length →
      (b ∈ H.acceptedBodies ((T x).state k) ↔ D.accepted ((T x).state k) b)) :
    FGAcceptedBodyOrigin E rho H W (driverFGExecutionObs E rho F T Op) x := by
  refine ⟨fun k b hk hb hnb => Or.inl ?_⟩
  change k < (T x).length at hk
  change b ∈ H.acceptedBodies ((T x).state (k + 1)) at hb
  change b ∉ H.acceptedBodies ((T x).state k) at hnb
  have h1 := (hacc (k + 1) b hk).1 hb
  have h2 : ¬ D.accepted ((T x).state k) b := fun h => hnb ((hacc k b hk.le).2 h)
  obtain ⟨o, _, havail, hop, _, _⟩ := TL.origin_attribution k b hk h1 h2
  exact ⟨o, ⟨hk, b, hop⟩, (TL.origin_valid (k + 1) b o hk havail).1⟩

/-- The E1F accepted-body origin obligation of X1a, proved from the trace laws. -/
theorem accepted_body_origin_driver (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) :
    AcceptedBodyOriginDriverStatement (Leaf := Leaf) E rho H W D L Step F T Op Arrival Notify
      leafState leafWire ActualRead := by
  rw [AcceptedBodyOriginDriverStatement_def]
  intro TL hacc x
  rw [DriverTraceLaws_def] at TL
  exact accepted_body_origin_driver_at E rho H W D L Step F T Op Arrival Notify leafState
    leafWire ActualRead x (TL x) (hacc x)

omit [DecidableEq V] in
/-- Generic strict-cut history: a block held at a parent-closed local cut inside the
segment of an actual event whose whole prefix is before the deadline has its causal history
held at that real cut. -/
theorem chainRows_of_held_obs (R : FGCoreReads P n Base Proposal Wire) (rho : V2.D.Run V P)
    (O : FGExecutionObs V P) {x : V} {j k : Nat} {e : V2.Event V P.Object}
    {X : FGBlock (Fin n)} {deadline : Time} (hx : x ∈ rho.honest)
    (hj : rho.events[j]? = some e) (h1 : O.start x j ≤ k) (h2 : k ≤ O.done x j)
    (hpre : ∀ i ei, rho.events[i]? = some ei → i ≤ j → ei.time < deadline)
    (hcl : ∀ B ∈ (R.core (O.cutState x k)).fg.TF, B.parent ∈ (R.core (O.cutState x k)).fg.TF)
    (hX : X ∈ (R.core (O.cutState x k)).fg.TF) :
    FGChainRowsAtCut R rho O X deadline := by
  rw [FGChainRowsAtCut_def]
  intro W hW _ _
  exact ⟨x, hx, Or.inr ⟨j, e, k, hj, h1, h2, hpre,
    ancestor_closed_of_parent_closed _ hcl X hX W hW⟩⟩

omit [DecidableEq V] in
private theorem driver_good {H : FGHistoricalReads P.State Body}
    {D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest}
    {Step : FGDependencyStepKind → V → P.State → P.State → Prop}
    {R : FGCoreReads P n Base Proposal Wire} {Good : P.State → Prop}
    (SL : DriverCoreStepLaws R H D Step Good) {x : V} {T : FGDependencyTrace P.State}
    (h0 : T.state 0 = P.init)
    (hstep : ∀ k, k < T.length → ∃ kind, Step kind x (T.state k) (T.state (k + 1))) :
    ∀ k, k ≤ T.length → Good (T.state k) := by
  intro k
  induction k with
  | zero => intro _; rw [h0]; exact SL.good_init
  | succ k ih =>
    intro hk
    obtain ⟨kind, hs⟩ := hstep k hk
    exact SL.good_step kind x _ _ hs (ih (Nat.le_of_succ_le hk))

/-- HEAD to strict causal history on the driver run, from the drained duty cut of an honest
tick: the HEAD block and its ancestors are held at that real cut, inside the tick's segment.
No strict-time TF equality is used, so a completed restart that adds bodies is harmless. -/
theorem chainRows_of_head_driver (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) {Good : P.State → Prop} {x : V}
    (TL : FGDependencyTraceLaws E rho x H W D L Step (T x) F (Op x) Arrival Notify
      leafState leafWire ActualRead)
    (SL : DriverCoreStepLaws R H D Step Good) (CL : FGCoreLaws R)
    {j : Nat} {t : Time} {s : Slot} {X : FGBlock (Fin n)} {deadline : Time}
    (hx : x ∈ rho.honest) (hj : rho.events[j]? = some (.tick x t))
    (hh : R.headVote ((T x).state ((T x).dutyCut j)) s = R.erase X)
    (hpre : ∀ i ei, rho.events[i]? = some ei → i ≤ j → ei.time < deadline) :
    FGChainRowsAtCut R rho (driverFGExecutionObs E rho F T Op) X deadline := by
  obtain ⟨hentry, h12, h23, _, _⟩ := TL.entry_boundary j _ hj
  obtain ⟨_, hfin⟩ := TL.finite_segment j _ hj
  obtain ⟨_, _, _, hclosed, _⟩ := TL.atomic_tick j t hj
  have hgood := driver_good SL TL.initial TL.micro_step ((T x).dutyCut j) (h23.trans hfin)
  obtain ⟨B, hB, hBe⟩ := SL.head_mem _ s hgood hclosed
  have hBX : B = X := CL.erase_inj (hBe.trans hh)
  subst hBX
  exact chainRows_of_held_obs R rho (driverFGExecutionObs E rho F T Op) hx hj
    (k := (T x).dutyCut j) (by change (T x).start j ≤ (T x).dutyCut j; omega) h23 hpre
    (SL.parent_closed _ hgood) hB

/-- Ordinary bridge, ONE-WAY: the nested strict-time history `ChainRowsBefore` gives the
strict-cut history on the ordinary observation (sorted schedule). The converse fails on
integer time (Tests/X1b `ordinary_converse_fails`). -/
theorem ordinary_chainRows_atCut_of_before (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P) (hS : V2.D.ScheduleWellFormed E rho)
    {X : FGBlock (Fin n)} {cut : Time} (h : ChainRowsBefore R E rho X cut) :
    FGChainRowsAtCut R rho (ordinaryFGExecutionObs E rho) X cut := by
  rw [FGChainRowsAtCut_def]
  intro W hW row hrow
  obtain ⟨x, t, hx, htc, hheld⟩ := (ChainRowsBefore_def R E rho X cut ▸ h) W hW row hrow
  rw [Gen.V2.Duty.HoldsBefore_def, ← Gen.V2.Duty.stateBefore_idxBefore E rho t hS] at hheld
  refine ⟨x, hx, ?_⟩
  rcases hm : V2.D.Run.idxBefore rho t with _ | j
  · rw [hm] at hheld
    exact Or.inl hheld
  · rw [hm] at hheld
    have hlen : j + 1 ≤ rho.events.length := by
      rw [← hm, V2.D.Run.idxBefore_def]; exact List.length_filter_le ..
    obtain ⟨e, he⟩ : ∃ e, rho.events[j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have EL := ordinaryFGExecutionObs_laws E rho
    obtain ⟨h1, h2, h3, _⟩ := EL.cut_order j e x he
    refine Or.inr ⟨j, e, (ordinaryFGExecutionObs E rho).done x j, he, by omega, le_rfl,
      ?_, ?_⟩
    · intro i ei hi hij
      have hlt : i < V2.D.Run.idxBefore rho t := by rw [hm]; omega
      exact lt_trans ((Gen.V2.Duty.index_lt_idxBefore_iff hS hi t).1 hlt) htc
    · rw [EL.done_state j e x he]
      exact hheld

end AvailableChain.FGCompose
end
