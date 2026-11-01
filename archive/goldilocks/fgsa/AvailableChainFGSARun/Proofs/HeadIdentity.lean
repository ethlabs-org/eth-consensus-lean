module
public import AvailableChainFGSARun.Proofs.Content -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainFGSA.Proofs.HeadResolution

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]

/-- [ROOT-DIGEST-2 W2; DC NamedRootCollisionFree; S2] Stored blocks have actual named witnesses. -/
theorem stored_block_eq_of_root_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (i j : Nat) (x y : V) {A B : Block}
    (hA : A ∈ (rho.stateBefore E i x).st.base.blocks)
    (hB : B ∈ (rho.stateBefore E j y).st.base.blocks) (he : A.root = B.root) : A = B := by
  obtain ⟨N, hN, rfl⟩ := (namedBodies_erase_domain p _ (cstoreInv_stateBefore E rho i x)
    (metaInv_stateBefore E rho i x) A).mp hA
  obtain ⟨M, hM, rfl⟩ := (namedBodies_erase_domain p _ (cstoreInv_stateBefore E rho j y)
    (metaInv_stateBefore E rho j y) B).mp hB
  exact congrArg NamedProposal.erase (namedStored_eq E rho hr i j x y hN hM (by simpa using he))

/-- [ROOT-DIGEST-2 W2; DC goldfish_vote] The selected sender body was held before its tick. -/
theorem headTargetAtEmission_stored (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} {o : Obj p} {t : Time} {H : Block}
    (hH : HeadTargetAtEmission p c E rho x o t H) :
    ∃ i, H ∈ (rho.stateBefore E i x).st.base.blocks := by
  obtain ⟨i, s, _, _, _, _, rfl⟩ := hH
  refine ⟨i, ?_⟩
  have hm := headVote_stored p _ (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) t) s
  rwa [clock_base_blocks] at hm

/-- [ROOT-DIGEST-2 W2; DC goldfish_vote] Honest emission has named held-body scope. -/
theorem headTargetAtEmission_scope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} (hx : x ∈ rho.honest) {o : Obj p} {t : Time} {H : Block}
    (hH : HeadTargetAtEmission p c E rho x o t H) : RootBlockInRun p c E rho H := by
  obtain ⟨i, hi⟩ := headTargetAtEmission_stored E rho hH
  exact rootBlockInRun_held E rho hx i hi

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] A resolved HEAD retains its exact signed root. -/
theorem resolvedHead_root {n : Nat} (st : GridCO.State n .root) (o : GridCO.Wire n .root)
    {B : Block} (h : GridCO.resolvedHead? st o = some B) :
    GridCO.headTarget? o = some B.root := by
  change ((GridCO.headTarget? o).bind fun r =>
    (Block.findByRoot? (GridCO.resolutionTree st) r).bind fun C =>
      if C ∈ st.blocks then some C else none) = some B at h
  obtain ⟨r, ht, hh⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨C, hc, he⟩ := Option.bind_eq_some_iff.mp hh
  split at he
  · cases he
    simpa only [Block.findByRoot?_root hc] using ht
  · contradiction

/-- [ROOT-DIGEST-2 W2; DC Blocks.find?] Receiver resolution agrees with the actual sender
body. Both operands come from named stores; the HEAD identifier is not a scope seed. -/
theorem headTargetAtEmission_receiver_eq (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hr : NamedRootCollisionFree p c E rho)
    {x : V} {o : Obj p} {t : Time} {H B : Block}
    (hH : HeadTargetAtEmission p c E rho x o t H)
    (j : Nat) (y : V) (st : GridCO.State p.n .root) (w : GridCO.Wire p.n .root)
    (hsub : st.blocks ⊆ (rho.stateBefore E j y).st.base.blocks)
    (hw : GridCO.headTarget? w = some H.root)
    (hresolve : GridCO.resolvedHead? st w = some B) : B = H := by
  obtain ⟨i, hi⟩ := headTargetAtEmission_stored E rho hH
  apply stored_block_eq_of_root_eq E rho hr j i y x
    (hsub (resolvedHead_mem st w hresolve)) hi
  exact Option.some.inj ((resolvedHead_root st w hresolve).symm.trans hw)

/-- [ROOT-DIGEST-2 W2; DC duty provenance] The named occurrence fixes its selected body
at any equal scheduled tick, without a root-equality premise. -/
theorem headTargetAtEmission_at_tick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {o : Obj p} {t : Time} {H : Block}
    (hH : HeadTargetAtEmission p c E rho x o t H) {i : Nat}
    (hi : rho.events[i]? = some (.tick x t)) {s : Slot} {k : Fin p.n}
    (ha : o.auth = .seat (.base (.head s)) k) :
    H = headVote p (clock p (rho.stateBefore E i x).st t) s := by
  obtain ⟨j, r, q, hj, _, ho, hH⟩ := hH
  have hij := fgsa_tick_unique E rho hs hi hj
  subst j
  have hr : r = s := by
    have he := (congrArg (fun o : Obj p => o.auth) ho).symm.trans ha
    have h := congrArg (fun a => match a with
      | .seat (.base (.head u)) _ => some u
      | _ => none) he
    exact Option.some.inj h
  simpa only [hr] using hH

/-- [ROOT-DIGEST-2 W2; DC NamedRootCollisionFree] A receiver's stored body can identify
an emitted root only through the two actual named store origins. -/
theorem headTargetAtEmission_of_stored (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {x : V} {o : Obj p} {t : Time} {B : Block}
    (hem : V2.D.Run.emits E rho x o t) (ho : o.payload = .head B.root)
    (j : Nat) (y : V) (hB : B ∈ (rho.stateBefore E j y).st.base.blocks) :
    HeadTargetAtEmission p c E rho x o t B := by
  obtain ⟨H, hH⟩ := headTargetAtEmission_exists E rho hem ho
  obtain ⟨i, hi⟩ := headTargetAtEmission_stored E rho hH
  have hroot : H.root = B.root := by
    obtain ⟨_, _, _, _, _, he, _⟩ := hH
    exact Msg.head.inj ((congrArg (fun o : Obj p => o.payload) he).symm.trans ho)
  have he := stored_block_eq_of_root_eq E rho hr i j x y hi hB hroot
  exact he ▸ hH

/-- [ROOT-DIGEST-2 W2; DC NamedRootCollisionFree] A stored receiver body and a selected
sender HEAD are equal only after both have actual named origins. -/
theorem stored_eq_headVote (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (i : Nat) (x : V) {B : Block}
    (hB : B ∈ (rho.stateBefore E i x).st.base.blocks)
    (j : Nat) (y : V) (t : Time) (s : Slot)
    (he : B.root = (headVote p (clock p (rho.stateBefore E j y).st t) s).root) :
    B = headVote p (clock p (rho.stateBefore E j y).st t) s := by
  have hm := headVote_stored p _ (cstoreInv_clock p _ (cstoreInv_stateBefore E rho j y) t) s
  rw [clock_base_blocks] at hm
  exact stored_block_eq_of_root_eq E rho hr i j x y hB hm he

end AvailableChain.FGSA.Run
end
