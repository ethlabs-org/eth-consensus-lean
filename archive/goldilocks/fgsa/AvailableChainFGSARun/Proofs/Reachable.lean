module
public import AvailableChainFGSARun.Proofs.ClockLaws -- shake: keep (re-export)
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainFGSA.Proofs.StoreBundle -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Restore -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In : Type} {c : AppCodec In}
variable {V : Type} [DecidableEq V]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every indexed run state has a reachable store, including after restarts. -/
theorem reachable_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) : Reachable p (V2.D.Run.stateBefore E rho i v).st :=
  fgsa_reachable_stateBefore p c E rho i v

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The strict time reader needs no event order premise. -/
theorem reachable_stateBeforeTime (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (t : Time) (v : V) : Reachable p (V2.D.Run.stateBeforeTime E rho t v).st := by
  let rho' := { rho with events := rho.events.filter (fun e => decide (e.time < t)) }
  have hs : V2.D.World.step E rho' = V2.D.World.step E rho := by
    funext w e
    cases e <;> rfl
  have h := reachable_stateBefore E rho' rho'.events.length v
  change Reachable p ((rho'.events.take rho'.events.length).foldl
    (V2.D.World.step E rho') V2.D.World.init v).st at h
  rw [List.take_length, hs] at h
  exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The inclusive time reader needs no event order premise. -/
theorem reachable_readAt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (t : Time) (v : V) : Reachable p (V2.D.Run.readAt E rho t v).st := by
  let rho' := { rho with events := rho.events.filter (fun e => decide (e.time ≤ t)) }
  have hs : V2.D.World.step E rho' = V2.D.World.step E rho := by
    funext w e
    cases e <;> rfl
  have h := reachable_stateBefore E rho' rho'.events.length v
  change Reachable p ((rho'.events.take rho'.events.length).foldl
    (V2.D.World.step E rho') V2.D.World.init v).st at h
  rw [List.take_length, hs] at h
  exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The complete event list leaves a reachable store. -/
theorem reachable_final (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (v : V) : Reachable p (V2.D.Run.final E rho v).st := by
  have h := reachable_stateBefore E rho rho.events.length v
  change Reachable p ((rho.events.take rho.events.length).foldl
    (V2.D.World.step E rho) V2.D.World.init v).st at h
  rw [List.take_length] at h
  exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The clock of any indexed state leaves a reachable store. -/
theorem reachable_postClock (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (t : Time) :
    Reachable p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i v) t).st :=
  Reachable.tick t (reachable_stateBefore E rho i v)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The own-record fold after the clock keeps the reachable store. -/
theorem reachable_postTick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (t : Time) :
    Reachable p (V2.D.tick E rho (V2.D.Run.stateBefore E rho i v) v t).1.st := by
  rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho i v) v t]
  exact Reachable.tick t (reachable_stateBefore E rho i v)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The one store bundle supplies the run invariants. -/
theorem storeBundle_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) : StoreBundle p (V2.D.Run.stateBefore E rho i v).st :=
  storeBundle_of_reachable p _ (reachable_stateBefore E rho i v)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The bundle at the strict time reader. -/
theorem storeBundle_stateBeforeTime (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (t : Time) (v : V) : StoreBundle p (V2.D.Run.stateBeforeTime E rho t v).st :=
  storeBundle_of_reachable p _ (reachable_stateBeforeTime E rho t v)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The bundle at the inclusive time reader. -/
theorem storeBundle_readAt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (t : Time) (v : V) : StoreBundle p (V2.D.Run.readAt E rho t v).st :=
  storeBundle_of_reachable p _ (reachable_readAt E rho t v)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The bundle after the complete event list. -/
theorem storeBundle_final (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (v : V) : StoreBundle p (V2.D.Run.final E rho v).st :=
  storeBundle_of_reachable p _ (reachable_final E rho v)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The bundle after the clock of an indexed state. -/
theorem storeBundle_postClock (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (t : Time) :
    StoreBundle p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i v) t).st :=
  storeBundle_of_reachable p _ (reachable_postClock E rho i v t)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The bundle after the whole tick of an indexed state. -/
theorem storeBundle_postTick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (t : Time) :
    StoreBundle p (V2.D.tick E rho (V2.D.Run.stateBefore E rho i v) v t).1.st :=
  storeBundle_of_reachable p _ (reachable_postTick E rho i v t)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The admission invariant follows from the same store bundle. -/
theorem inv0_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) : Inv0 p (V2.D.Run.stateBefore E rho i v).st :=
  (storeBundle_stateBefore E rho i v).cstore.toInv0

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The composite store invariant at every indexed state. -/
theorem cstoreInv_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) : CStoreInv p (V2.D.Run.stateBefore E rho i v).st :=
  (storeBundle_stateBefore E rho i v).cstore

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The metadata invariant includes the ordered signed rows and rowsOk. -/
theorem metaInv_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) : MetaInv p (V2.D.Run.stateBefore E rho i v).st :=
  (storeBundle_stateBefore E rho i v).«meta»

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The erased finalized block is below the stored output. -/
theorem nestOK_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) : NestOK (V2.D.Run.stateBefore E rho i v).st :=
  (storeBundle_stateBefore E rho i v).nest

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Run form of comp.outputNesting.v2; both interface outputs read S. -/
theorem outputNesting_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) :
    Block.Preceq (finalizedOut (V2.D.Run.stateBefore E rho i v))
      ((fgsaInterface p c).confirmed (V2.D.Run.stateBefore E rho i v)) ∧
    (fgsaInterface p c).confirmed (V2.D.Run.stateBefore E rho i v) =
      (V2.D.Run.stateBefore E rho i v).st.base.stableRecord ∧
    (fgsaInterface p c).stable (V2.D.Run.stateBefore E rho i v) =
      (fgsaInterface p c).confirmed (V2.D.Run.stateBefore E rho i v) :=
  ⟨nestOK_stateBefore E rho i v, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every node's live lease targets are below its output. -/
theorem leaseBelowOutput_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) : LeaseBelowOutputStore p (V2.D.Run.stateBefore E rho i v).st :=
  (storeBundle_stateBefore E rho i v).lease

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The honest restriction needed by the AC lease statement. -/
theorem leaseBelowOutput_honest (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (_hv : v ∈ rho.honest)
    (ℓ : Block × Nat × Time) (hℓ : ℓ ∈ (V2.D.Run.stateBefore E rho i v).st.base.obligations)
    (hlive : (V2.D.Run.stateBefore E rho i v).st.base.now < ℓ.2.2) :
    Block.Preceq ℓ.1 ((fgsaInterface p c).confirmed (V2.D.Run.stateBefore E rho i v)) :=
  leaseBelowOutput_stateBefore E rho i v ℓ hℓ hlive


/-- [ROOT-DIGEST-2 W2; DC NamedStore] Admission identifies the only new named wire. -/
private theorem fgsa_process_stored_wire_origin (st : State p.n) (h : CStoreInv p st)
    (o w : Wire p.n) (hw : w ∈ (FGSA.process p st o).proposals) :
    w ∈ st.proposals ∨ w = o := by
  obtain ⟨auth, msg⟩ := o
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> cases msg <;> try exact Or.inl hw
  · change w ∈ (admitRow p st _).proposals at hw
    rcases admitRow_eq p st _ with he | he <;> rw [he] at hw
    · exact Or.inl hw
    · exact Or.inl hw
  · rename_i s N
    change w ∈ (admitBlock p st s N).proposals at hw
    cases hn : namedParentHeld st N with
    | false =>
      rw [admitBlock_refused p st s N (Or.inl hn)] at hw
      exact Or.inl hw
    | true =>
      cases hP : parentFG st N.erase with
      | none =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))] at hw
          exact Or.inl hw
      | some P =>
          cases ha : blockAccepted p st s N P with
          | false =>
              rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, ha⟩))] at hw
              exact Or.inl hw
          | true =>
              obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hn hP ha
              rw [he] at hw
              have hp := (accepted_st2 p st h s N P hP ha).1
              dsimp only at hw
              rw [hp, List.mem_append, List.mem_singleton] at hw
              rcases hw with hw | hw
              · exact Or.inl hw
              · exact Or.inr hw

/-- A stored proposal was delivered in an earlier epoch or the current epoch.
The exact wire stays in durable storage at every index since that delivery. -/
theorem stored_proposal_delivered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (w : Wire p.n)
    (hw : w ∈ (V2.D.Run.stateBefore E rho i v).st.proposals) :
    ∃ j o t, j < i ∧ rho.events[j]? = some (.deliver v o t) ∧
      toWire p o = w ∧ (∃ s N, o.payload = .proposal N ∧
        o.auth = .seat (.prop s) ⟨0, Nat.one_pos⟩) ∧
      ∀ k, j + 1 ≤ k → k ≤ i → w ∈ (V2.D.Run.stateBefore E rho k v).st.proposals := by
  have origin : ∀ i v w, w ∈ (V2.D.Run.stateBefore E rho i v).st.proposals →
      ∃ j o t, j < i ∧ rho.events[j]? = some (.deliver v o t) ∧ toWire p o = w ∧
        ∀ k, j + 1 ≤ k → k ≤ i → w ∈ (V2.D.Run.stateBefore E rho k v).st.proposals := by
    intro i
    induction i with
    | zero =>
        intro v w hw
        exact (List.not_mem_nil hw).elim
    | succ i ih =>
        intro v w hw
        have carry (hm : w ∈ (V2.D.Run.stateBefore E rho i v).st.proposals) :
            ∃ j o t, j < i + 1 ∧ rho.events[j]? = some (.deliver v o t) ∧ toWire p o = w ∧
              ∀ k, j + 1 ≤ k → k ≤ i + 1 →
                w ∈ (V2.D.Run.stateBefore E rho k v).st.proposals := by
          obtain ⟨j, o, t, hj, hd, ho, hr⟩ := ih v w hm
          refine ⟨j, o, t, by omega, hd, ho, ?_⟩
          intro k hjk hki
          by_cases hk : k ≤ i
          · exact hr k hjk hk
          · have : k = i + 1 := by omega
            subst k; exact hw
        cases he : rho.events[i]? with
        | none =>
            apply carry
            simpa only [V2.D.Run.stateBefore, List.take_add_one, he,
              Option.toList_none, List.append_nil] using hw
        | some e =>
            have hw' := hw
            rw [V2.D.Run.stateBefore_succ E rho he] at hw'
            by_cases hv : e.node = v
            · cases e with
              | restart u t =>
                  change u = v at hv; subst u
                  simp only [V2.D.World.step, Function.update_self] at hw'
                  apply carry
                  change w ∈ (acRestart p (V2.D.Run.stateBefore E rho i v).st t).proposals at hw'
                  rwa [acRestart_proposals] at hw'
              | tick u t =>
                  change u = v at hv; subst u
                  simp only [V2.D.World.step, Function.update_self] at hw'
                  rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho i v) v t,
                    clock_proposals] at hw'
                  exact carry hw'
              | deliver u o t =>
                  change u = v at hv; subst u
                  simp only [V2.D.World.step, Function.update_self] at hw'
                  rcases fgsa_process_stored_wire_origin _ (cstoreInv_stateBefore E rho i v)
                      (toWire p o) w hw' with hm | ho
                  · exact carry hm
                  · refine ⟨i, o, t, Nat.lt_succ_self i, he, ho.symm, ?_⟩
                    intro k hik hki
                    have : k = i + 1 := by omega
                    subst k; exact hw
            · rw [V2.D.World.step_apply_of_node_ne E rho _ hv] at hw'
              exact carry hw'
  obtain ⟨j, o, t, hj, hd, ho, hr⟩ := origin i v w hw
  obtain ⟨s, N, he, -, -, -⟩ := (metaInv_stateBefore E rho i v).wireTree w hw
  have eo : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
    apply toWire_injective
    rw [toWire_ofWire, ho, he]
  refine ⟨j, o, t, hj, hd, ho, ⟨s, N, ?_, ?_⟩, hr⟩ <;> rw [eo] <;> rfl

end AvailableChain.FGSA.Run
end
