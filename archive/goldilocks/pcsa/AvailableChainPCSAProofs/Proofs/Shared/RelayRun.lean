module
public import AvailableChainPCSAProofs.Proofs.Shared.RelayStore
public import AvailableChainPCSAProofs.Proofs.Shared.StageRun
public import AvailableChainPCSAProofs.Proofs.Shared.RunEvidence
public import AvailableChainPCSAProofs.Proofs.Shared.Relay

public section

/-! The stage-1 PC relay origin (pcsa34-r4.3 §3.6, §5.2.3). A held key was
first installed by a delivery that accepts the installed PC object: in stage 1
the installing call carries the PC (an ack in it, a PC or proposal on its slot
and root). A handled PC object pools its acks, and once the target is stored,
collection closure installs the key (`CollectClosed`). Each lane keeps its own
delivery-premise wrapper. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

/-- A decoded ack wire is the ack object of its auth and root. -/
theorem pcsa_outage_decoded_ack (o : Obj p) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : (toWire p o).decode = some (.ack s i r)) : ofAck p ⟨(toWire p o).auth, r⟩ = o := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> simp [toWire, toAuth, Wire.decode] at h
  | seat l j =>
    cases l with
    | prop k => cases payload <;> simp [toWire, toAuth, Wire.decode] at h
    | base l =>
      cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl

/-- A decoded PC wire carries that PC as its payload. -/
theorem pcsa_outage_decoded_pc (o : Obj p) (d : PC p.n)
    (h : (toWire p o).decode = some (.pc d)) : o.payload = .pc d := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none =>
    cases payload <;> simp [toWire, toAuth, Wire.decode] at h
    subst h
    rfl
  | seat l j =>
    cases l with
    | prop k => cases payload <;> simp [toWire, toAuth, Wire.decode] at h
    | base l => cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h

omit [DecidableEq V] [Fintype V] in
/-- A stored block of an outage store is a run block. -/
theorem pcsa_outage_block_prop {R : Block → Prop} {st : State p.n} (hO : OutageStore R st)
    (b : Block) (hb : b ∈ st.base.blocks) : R b := by
  obtain ⟨B, hB, he⟩ := hO.lift b hb
  rw [← he]
  exact hO.tf B hB

omit [Fintype V] in
/-- Two scoped blocks with one root are equal. -/
theorem pcsa_outage_rootBlock_eq (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) {X Y : Block} (hX : RootBlockInRun p c E rho X)
    (hY : RootBlockInRun p c E rho Y) (he : X.root = Y.root) : X = Y :=
  pcsa_rootBlock_eq E rho h.idealization X Y hX hY he


omit [DecidableEq V] [Fintype V] in
/-- A PC object is processed exactly when its key is held. -/
theorem pcsa_processed_pc (nd : Node p) (C : PC p.n) :
    (pcsaWith m p c).processed nd (⟨.none, .pc C⟩ : Obj p) = true ↔
      KeyHeld nd.st C.slot C.target := by
  rw [pcsa_keyHeld_iff_any]
  exact Iff.rfl

omit [DecidableEq V] [Fintype V] in
/-- A handled PC object either installs its key or pools its acks. -/
theorem pcsa_handles_pc_store (st : State p.n) (o : Obj p) (C : PC p.n)
    (hwf : C.wellFormed = true) (h : handlesS p st o (⟨.none, .pc C⟩ : Obj p)) :
    KeyHeld (process p st (toWire p o)) C.slot C.target ∨
      ∀ a ∈ C.acks, a ∈ (process p st (toWire p o)).ackPool := by
  rcases h with rfl | h | ⟨-, C', hC', hm, -⟩
  · right
    exact pcsa_admitPC_pool st C hwf
  · exfalso
    revert h
    cases (toWire p o).decode with
    | none => exact id
    | some msg =>
      cases msg with
      | block s N =>
        intro h
        obtain ⟨-, hm | hm | hm⟩ := (h : _ ∧ _)
        all_goals
          obtain ⟨x, -, hx⟩ := List.mem_map.mp hm
          cases congrArg (fun x : Obj p => x.payload) hx
      | pc d =>
        intro h
        obtain ⟨x, -, hx⟩ := List.mem_map.mp (h : (⟨.none, .pc C⟩ : Obj p) ∈ d.acks.map (ofAck p))
        cases congrArg (fun x : Obj p => x.payload) hx
      | vote => exact id
      | row => exact id
      | ack => exact id
  · have he := congrArg (fun x : Obj p => x.payload) hC'
    cases he
    left
    rw [KeyHeld_def]
    exact ⟨C, hm, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- [pcsa34-r4.3 §5.2.3] Stage 1: the call that installs a key that a closed
store does not hold carries the installed PC: an ack call (the completing ack
is in the PC), a PC call (its slot and root) or a proposal call (the slot and
root of its block or of its PC). -/
theorem pcsa_install_carries (st : State p.n) (o : Obj p)
    (hwfo : PCSA.wellFormed p (toWire p o) = true) (hcl : CollectClosed st)
    (hF : st.fg.F = .genesis) (C : PC p.n) (hC : C ∈ (process p st (toWire p o)).pcs)
    (hk : ¬ KeyHeld st C.slot C.target) :
    carriesS p o (⟨.none, .pc C⟩ : Obj p) := by
  have hheld : C ∉ st.pcs := fun hm => hk ((KeyHeld_def _ _ _).mpr ⟨C, hm, rfl, rfl⟩)
  delta carriesS
  right
  refine ⟨C, rfl, ?_⟩
  revert hwfo hC
  delta process PCSA.wellFormed
  cases hd : (toWire p o).decode with
  | none => intro _ hC; exact absurd hC hheld
  | some msg => cases msg with
    | vote s i r => intro _ hC; exact absurd hC hheld
    | row i body =>
      dsimp only
      intro _ hC
      rw [(pcsa_admitRow_frame p st _).1] at hC
      exact absurd hC hheld
    | ack s i r =>
      dsimp only
      intro _ hC
      have ha := pcsa_ack_new_key p st _ hcl hF C hC hk
      rw [← pcsa_outage_decoded_ack o s i r hd]
      exact List.mem_map.mpr ⟨_, ha, rfl⟩
    | pc d =>
      dsimp only
      intro hw hC
      rw [show (admitPC st d) = collectPCs (d.acks.foldl poolAckRaw st) by
        delta admitPC
        simp only [hw, ↓reduceIte]] at hC
      · rcases pcsa_collect_new_key st st d.acks .genesis (List.Subset.refl _) rfl
            (fun x hx => Or.inl hx) hcl hF C hC hk with ⟨hb, hn, -⟩ | ⟨a, ha, i, hi⟩
        · exact absurd hb hn
        · rw [pcsa_outage_decoded_pc o d hd]
          obtain ⟨j, hj⟩ := (pcsa_pc_wellFormed_parts d hw).2.2.2.2.2 a ha
          rw [hi] at hj
          have he := Option.some.inj hj
          simp only [Prod.mk.injEq] at he
          exact ⟨he.1.symm, he.2.2.symm⟩
    | block s N =>
      dsimp only
      intro hw hC
      have hG := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
      revert hC
      delta admitBlock
      split
      · intro hC; exact absurd hC hheld
      · cases hP : parentFG st N.erase with
        | none => intro hC; exact absurd hC hheld
        | some P =>
          dsimp only
          split
          · intro hC
            refine (fun hres => ?_) (pcsa_admitBlock_new_key p st _ _ N.rows N.pcAcks N.erase
              ?_ ?_ ?_ hcl hF C hC hk)
            · rw [pcsa_outage_decoded_proposal o s N hd]
              rcases hres with ⟨-, hB, hs⟩ | ⟨a, ha, i, hi⟩
              · exact Or.inl ⟨hs, by rw [hB]⟩
              · right
                revert ha hG
                change (N.pc.map PC.wellFormed).getD true = true →
                  a ∈ (N.pc.map PC.acks).getD [] → _
                cases N.pc with
                | none => intro _ ha; exact absurd ha List.not_mem_nil
                | some d =>
                  intro hdw ha
                  obtain ⟨j, hj⟩ := (pcsa_pc_wellFormed_parts d hdw).2.2.2.2.2 a ha
                  rw [hi] at hj
                  have he := Option.some.inj hj
                  simp only [Prod.mk.injEq] at he
                  exact ⟨d, rfl, he.1.symm, he.2.2.symm⟩
            · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
                (try simp only [deleteConflictingLeases_def])
              all_goals exact List.Subset.refl _
            · cases N.pc
              · rfl
              · dsimp only
                split_ifs <;> rfl
            · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
                (try simp only [deleteConflictingLeases_def])
              all_goals exact fun x hx => pcsa_admitProposal_blocks _ _ _ _ _ x hx
          · intro hC; exact absurd hC hheld

omit [Fintype V] in
/-- The state after a tick of its node is the clock. -/
theorem pcsa_tick_step (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat)
    (v : V) (t : Time) :
    (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.tick v t) v).st =
      clock p (V2.D.Run.stateBefore E rho k v).st t := by
  change (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st = _
  rw [Function.update_self]
  exact pcsa_tick_st E rho _ v t

omit [Fintype V] in
/-- The state after a delivery to its node is the delivery handler. -/
theorem pcsa_deliver_succ (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) {k : Nat}
    {v : V} {o : Obj p} {t : Time} (he : rho.events[k]? = some (.deliver v o t)) :
    (V2.D.Run.stateBefore E rho (k + 1) v).st =
      process p (V2.D.Run.stateBefore E rho k v).st (toWire p o) := by
  rw [V2.D.Run.stateBefore_succ E rho he]
  change (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st = _
  rw [Function.update_self]
  rfl

omit [Fintype V] in
/-- The ack pool of an honest node only grows. -/
theorem pcsa_ackPool_mono_run (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hnr : V2.D.NoRestart rho) (y : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆ (V2.D.Run.stateBefore E rho j y).st.ackPool := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆ nd.st.ackPool) hij y ?_
    (List.Subset.refl _)
  intro k e _ _ he hn hk
  cases e with
  | restart u t => exact absurd he (hnr k u t)
  | tick u t =>
    change u = y at hn
    subst u
    show _ ⊆ (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.tick y t) y).st.ackPool
    rw [pcsa_tick_step, (pcsa_clock_frame p _ t).2.1]
    exact hk
  | deliver u o t =>
    change u = y at hn
    subst u
    rw [← V2.D.Run.stateBefore_succ E rho he, pcsa_deliver_succ E rho he]
    exact List.Subset.trans hk (pcsa_process_pool_mono p _ (toWire p o))

omit [Fintype V] in
/-- Stored roots of an honest node name one block (root collision freedom). -/
theorem pcsa_rootsUnique_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (j : Nat) (y : V) (hy : y ∈ rho.honest) :
    RootsUnique (V2.D.Run.stateBefore E rho j y).st := by
  have hO := pcsa_outageStore_stateBefore E rho j y hy
  rw [RootsUnique_def]
  intro b hb b' hb' hr
  exact pcsa_outage_rootBlock_eq E rho h (pcsa_outage_block_prop hO b hb)
    (pcsa_outage_block_prop hO b' hb') hr

omit [Fintype V] in
/-- [pcsa34-r4.3 §3.6] Every indexed store of an honest node is closed under
collection. -/
theorem pcsa_collectClosed_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (y : V) (hy : y ∈ rho.honest) (j : Nat) :
    CollectClosed (V2.D.Run.stateBefore E rho j y).st := by
  refine V2.D.Engine.stateBefore_step_induction E rho (fun nd : Node p => CollectClosed nd.st)
    (Nat.zero_le j) y ?_ pcsa_initial_collectClosed
  intro k e _ _ he hn hk
  cases e with
  | restart u t => exact absurd he (h.noRestart k u t)
  | tick u t =>
    change u = y at hn
    subst u
    show CollectClosed (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.tick y t) y).st
    rw [pcsa_tick_step]
    exact pcsa_clock_collectClosed p _ t hk
  | deliver u o t =>
    change u = y at hn
    subst u
    have hsucc := pcsa_deliver_succ E rho he
    have hu := pcsa_rootsUnique_stateBefore E rho h (k + 1) y hy
    rw [hsucc] at hu
    rw [← V2.D.Run.stateBefore_succ E rho he, hsucc]
    exact pcsa_process_collectClosed p _ (toWire p o) hk hu

omit [Fintype V] in
/-- [pcsa34-r4.3 §3.6, §5.2.3] Stage 1: a key held at an honest index was
installed by an earlier delivery that accepts the installed PC object (the
installing call carries it). -/
theorem pcsa_keyHeld_accepted (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) (v : V) (hv : v ∈ rho.honest)
    (s : Slot) (B : Block) (K : Nat)
    (hK : KeyHeld (V2.D.Run.stateBefore E rho K v).st s B) :
    ∃ i < K, ∃ (C : PC p.n) (t : Time), C.slot = s ∧ C.target = B ∧
      C ∈ (V2.D.Run.stateBefore E rho (i + 1) v).st.pcs ∧
      V2.D.Run.acceptsAt E rho i v (⟨.none, .pc C⟩ : Obj p) t := by
  by_contra hno
  revert hK
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => ¬ KeyHeld nd.st s B) (Nat.zero_le K) v ?_ ?_
  · intro k e _ hkK he hn hk
    cases e with
    | restart u t => exact absurd he (h.noRestart k u t)
    | tick u t =>
      change u = v at hn
      subst u
      show ¬ KeyHeld (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.tick v t) v).st s B
      rw [pcsa_tick_step, KeyHeld_def, (pcsa_clock_frame p _ t).1, ← KeyHeld_def]
      exact hk
    | deliver u o t =>
      change u = v at hn
      subst u
      have hsucc := pcsa_deliver_succ E rho he
      rw [← V2.D.Run.stateBefore_succ E rho he, hsucc]
      intro hk'
      apply hno
      rw [KeyHeld_def] at hk'
      obtain ⟨C, hC, hCs, hCt⟩ := hk'
      have hCn : C ∉ (V2.D.Run.stateBefore E rho k v).st.pcs := by
        intro hm
        exact hk ((KeyHeld_def _ _ _).mpr ⟨C, hm, hCs, hCt⟩)
      refine ⟨k, hkK, C, t, hCs, hCt, by rw [hsucc]; exact hC, ⟨o, he, ?_⟩, ?_, ?_⟩
      · have hcar := pcsa_install_carries _ o (h.valid.wire k v o t he)
          (pcsa_collectClosed_stateBefore E rho h v hv k)
          ((FrameVacuous_def p _).mp (hfr v hv k)).1 C hC (by rw [hCs, hCt]; exact hk)
        exact Or.inr (Or.inr ⟨hcar, C, rfl, hC, hCn⟩)
      · cases hb : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho k v)
          (⟨.none, .pc C⟩ : Obj p)
        · rfl
        · have hk2 := (pcsa_processed_pc _ C).mp hb
          rw [hCs, hCt] at hk2
          exact absurd hk2 hk
      · refine (pcsa_processed_pc _ C).mpr ?_
        rw [hsucc, KeyHeld_def]
        exact ⟨C, hC, rfl, rfl⟩
  · intro h0
    rw [KeyHeld_def] at h0
    obtain ⟨c', hc, -⟩ := h0
    exact List.not_mem_nil hc

end AvailableChain.PCSA.Run
end
