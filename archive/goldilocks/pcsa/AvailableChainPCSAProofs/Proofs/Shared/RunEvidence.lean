module
public import AvailableChainPCSAProofs.Proofs.Shared.StoreEvidence
public import AvailableChainPCSAClaims.Statements.Regimes

public section

/-! Authentic HEADs and named-body scope across stores (proof plan C1). -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Each honest stored HEAD has an emission with its exact label, seat, and root. -/
def HeadAuthentic (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (o : GridCO.Wire p.n .root) : Prop :=
  ∀ s i r, o = ⟨.seat s i, .head r⟩ → rho.seatOf (.base (.head s)) i ∈ rho.honest →
    ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) i)
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t

theorem HeadAuthentic_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (o : GridCO.Wire p.n .root) : HeadAuthentic E rho o =
      (∀ s i r, o = ⟨.seat s i, .head r⟩ → rho.seatOf (.base (.head s)) i ∈ rho.honest →
        ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) i)
          (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

/-- Named ancestry contains each body itself. -/
theorem pcsa_named_preceq_refl (N : NamedProposal p.n) : NamedProposal.Preceq N N := by
  cases N <;> simp [NamedProposal.Preceq, NamedProposal.preceq]

/-- Named erasure keeps the root identifier. -/
theorem pcsa_named_erase_root (N : NamedProposal p.n) : N.erase.root = N.root := by
  cases N <;> rfl

/-- A directly delivered named body is in the collision-freedom scope. -/
theorem pcsa_rootBlock_delivered (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (x : V) (o : Obj p) (t : Time) (N : NamedProposal p.n)
    (hp : V2.D.Run.processes rho x o t) (ho : o.payload = .proposal N) :
    RootBlockInRun p c E rho N.erase := by
  obtain ⟨k, hk⟩ := hp
  exact ⟨N, ⟨N, Or.inl ⟨x, o, t, List.mem_of_getElem? hk, ho⟩,
    pcsa_named_preceq_refl N⟩, rfl⟩

/-- Collision freedom turns equal scoped roots into equal target blocks. -/
theorem pcsa_rootBlock_eq (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : NamedRootCollisionFree p c E rho) (b d : Block)
    (hb : RootBlockInRun p c E rho b) (hd : RootBlockInRun p c E rho d)
    (he : b.root = d.root) : b = d := by
  obtain ⟨N, hN, rfl⟩ := hb
  obtain ⟨M, hM, rfl⟩ := hd
  have hroot : N.root = M.root := by simpa only [pcsa_named_erase_root] using he
  have hn := h.root_injective N M hN hM N M
    (Or.inl (pcsa_named_preceq_refl N)) (Or.inr (pcsa_named_preceq_refl M)) hroot
  exact congrArg NamedProposal.erase hn

private theorem decoded_head (o : Obj p) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : (toWire p o).decode = some (.vote s i r)) :
    o = ⟨.seat (.base (.head s)) i, .head r⟩ := by
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

private theorem decoded_proposal (o : Obj p) (s : Slot) (N : NamedProposal p.n)
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

private theorem baseHead_shape (a : HeadWire p.n) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : GridCO.fromHead (baseHead a) = (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root)) :
    ofHead p a = ⟨.seat (.base (.head s)) i, .head r⟩ := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => dsimp only [baseHead, HeadWire.decode?, GridCO.fromHead] at h; simp at h
  | proposer k => dsimp only [baseHead, HeadWire.decode?, GridCO.fromHead] at h; simp at h
  | seat l j =>
    cases l <;> dsimp only [baseHead, HeadWire.decode?, GridCO.fromHead] at h <;> simp at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl

/-- Every run store has scoped PC targets and authentic HEAD evidence. -/
theorem evidence_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.UnforgeableSignatures E rho) (j : Nat) (v : V) (hh : v ∈ rho.honest) :
    StoreEvidence (RootBlockInRun p c E rho) (HeadAuthentic E rho)
      (V2.D.Run.stateBefore E rho j v).st := by
  have hg : RootBlockInRun p c E rho .genesis := by
    refine ⟨.genesis, ⟨.genesis, Or.inr ⟨v, hh, 0, ?_⟩, ?_⟩, rfl⟩
    · dsimp only [V2.D.Run.stateBefore, pcsaWith]
      dsimp only [initial]
      simp [State.namedBodies]
    · exact pcsa_named_preceq_refl _
  have hz : StoreEvidence (RootBlockInRun p c E rho) (HeadAuthentic E rho) (initial p.n) := by
    rw [StoreEvidence_def]
    dsimp only [initial]
    exact ⟨by simpa [GridCO.initial] using hg, by simp, by simp [GridCO.initial]⟩
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => StoreEvidence (RootBlockInRun p c E rho) (HeadAuthentic E rho) nd.st)
    (Nat.zero_le j) v ?_ hz
  intro k e _ _ he hn h
  cases e with
  | restart u t =>
    change u = v at hn
    subst u
    change StoreEvidence _ _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact hz
  | tick u t =>
    change u = v at hn
    subst u
    change StoreEvidence _ _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k v) v t
    rw [ht]
    exact clock_evidence p _ _ _ t h
  | deliver u o t =>
    change u = v at hn
    subst u
    change StoreEvidence _ _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    apply process_evidence p _ _ _ (toWire p o) h
    · intro s i r hd s' i' r' hshape hh'
      have hs : (s = s' ∧ i = i') ∧ r = r' := by simpa using hshape
      rcases hs with ⟨⟨rfl, rfl⟩, rfl⟩
      have ho := decoded_head o s i r hd
      subst o
      obtain ⟨t', _, ht⟩ := hv.unforgeable v _ t ⟨k, he⟩ _ hh' rfl
      exact ⟨t', ht⟩
    · intro s N hd
      have ho := decoded_proposal o s N hd
      refine ⟨pcsa_rootBlock_delivered E rho v o t N ⟨k, he⟩ ho, ?_⟩
      intro a ha s' i r hshape hh'
      have hcar : (pcsaWith m p c).carries o (ofHead p a) := by
        change carriesS p o (ofHead p a)
        unfold carriesS
        rw [ho]
        exact Or.inl (Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩))
      rw [baseHead_shape a s' i r hshape] at hcar
      obtain ⟨t', _, ht⟩ := hv.carried v o t ⟨k, he⟩ _ hcar _ hh' rfl
      exact ⟨t', ht⟩

/-- The inclusive store reader preserves body scope and HEAD authenticity. -/
theorem evidence_storeAt (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.ExecutionValid E rho) (v : V) (hh : v ∈ rho.honest) (t : Time) :
    StoreEvidence (RootBlockInRun p c E rho) (HeadAuthentic E rho) (storeAt p c E rho v t) := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore hv.toScheduleWellFormed]
  exact evidence_stateBefore E rho hv.toUnforgeableSignatures _ v hh

end AvailableChain.PCSA.Run
end
