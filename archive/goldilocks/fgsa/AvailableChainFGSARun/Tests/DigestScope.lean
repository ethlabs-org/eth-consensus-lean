module
public import AvailableChainFGSARun.Proofs.NamedScope

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.DigestScope

abbrev pT : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def ba : Block := .node .genesis 4 ⟨5⟩ (packBody 0 ([] : List (RowWire 4)))
def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
def traceRun (p : Params) (es : List (V2.Event (Fin 1) (Obj p))) :
    V2.D.Run (Fin 1) (fgsa p unitCodec) where
  honest := ∅
  horizon := 20
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

abbrev collisionParams : Params := { pT with digest := fun _ => ⟨77⟩ }
def namedA : NamedProposal 4 := namedProposal collisionParams .genesis 1 0 [] [] []
def namedB : NamedProposal 4 := namedProposal collisionParams .genesis 1 1 [] [] []
def collisionA : Block := namedA.erase
def collisionB : Block := namedB.erase
def collisionWireA : Wire 4 := ⟨.proposer 1, .proposal namedA⟩
def collisionWireB : Wire 4 := ⟨.proposer 1, .proposal namedB⟩
def collisionRun := traceRun collisionParams
  [.deliver 0 (ofWire collisionParams collisionWireA) 4,
    .deliver 0 (ofWire collisionParams collisionWireB) 4]

/-- Separate stores admit both bodies. Local reachability does not prove the run premise. -/
theorem body_collision_admitted :
    collisionA ∈ (process collisionParams (clock collisionParams (initial 4) 4)
      collisionWireA).base.blocks ∧
    collisionB ∈ (process collisionParams (clock collisionParams (initial 4) 4)
      collisionWireB).base.blocks ∧
    contentOk collisionParams collisionA [] [] [] = true ∧
    contentOk collisionParams collisionB [] [] [] = true := by decide +kernel

theorem body_collision_control :
    Reachable collisionParams (process collisionParams (clock collisionParams (initial 4) 4)
      collisionWireA) ∧
    Reachable collisionParams (process collisionParams (clock collisionParams (initial 4) 4)
      collisionWireB) ∧
    ¬ NamedRootCollisionFree collisionParams unitCodec env collisionRun := by
  refine ⟨.deliver _ (.tick _ .init), .deliver _ (.tick _ .init), ?_⟩
  exact namedScope_collision env collisionRun
    (namedScope_delivered env collisionRun (N := namedA)
      (o := ofWire collisionParams collisionWireA)
      (x := 0) (t := 4) (by exact List.mem_cons_self) rfl)
    (namedScope_delivered env collisionRun (N := namedB)
      (o := ofWire collisionParams collisionWireB)
      (x := 0) (t := 4) (by exact List.mem_cons_of_mem _ List.mem_cons_self) rfl) rfl
    (by decide +kernel : namedA ≠ namedB)

/-- A root-only HEAD cannot retain the old alias body. -/
def fakeHeadBody : Block := .node .genesis 1 genesisRoot (packBody 0 ([] : List (RowWire 4)))
def fakeHead : HeadWire 4 := ⟨.seat (.head 3) 0, fakeHeadBody.root⟩
def headWire : Wire 4 := ⟨fakeHead.auth, .head fakeHeadBody.root⟩
def headNamed : NamedProposal 4 :=
  .node .genesis 4 ⟨5⟩ (packBody (n := 4) 0 []) [fakeHead] [fakeHead] []
def headProposal : Wire 4 := ⟨.proposer 4, .proposal headNamed⟩
def headRun := traceRun pT
  [.deliver 0 (ofWire pT headWire) 16, .deliver 0 (ofWire pT headProposal) 16]

theorem head_named_direct_scope (N : NamedProposal 4)
    (h : DirectNamedProposalInRun pT unitCodec env headRun N) : N = headNamed := by
  rcases h with ⟨v, o, t, hm, hp⟩ | ⟨v, hv, _⟩
  · change V2.Event.deliver v o t ∈
      [.deliver 0 (ofWire pT headWire) 16, .deliver 0 (ofWire pT headProposal) 16] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · cases hp
    · exact (Msg.proposal.inj hp).symm
  · exact (Finset.notMem_empty v hv).elim

theorem head_direct_scope (B : Block) (h : DirectRootBlockInRun pT unitCodec env headRun B) :
    B = ba := by
  obtain ⟨N, hN, rfl⟩ := h
  rw [head_named_direct_scope N hN]
  rfl

def headTable : List (NamedProposal 4) := [.genesis, headNamed]
theorem head_named_scope (N : NamedProposal 4)
    (h : NamedProposalInRun pT unitCodec env headRun N) : N ∈ headTable := by
  obtain ⟨tip, ht, hb⟩ := h
  rw [head_named_direct_scope tip ht] at hb
  simpa only [headTable, headNamed, NamedProposal.Preceq, NamedProposal.preceq,
    Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, false_or, or_comm] using hb

theorem head_body_scope (B : Block) (h : RootBlockInRun pT unitCodec env headRun B) :
    B ∈ ([.genesis, ba] : List Block) := by
  obtain ⟨N, hN, rfl⟩ := h
  have hm := head_named_scope N hN
  simp only [headTable, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide +kernel

theorem head_scope_control : NamedRootCollisionFree pT unitCodec env headRun ∧
    ¬ RootBlockInRun pT unitCodec env headRun fakeHeadBody := by
  constructor
  · constructor
    intro B C hB hC A D hA hD hr
    have mem (X : NamedProposal 4)
        (hX : NamedProposal.Preceq X B ∨ NamedProposal.Preceq X C) : X ∈ headTable := by
      exact head_named_scope X (hX.elim (namedScope_ancestor env headRun hB)
        (namedScope_ancestor env headRun hC))
    have hinj : ∀ X ∈ headTable, ∀ Y ∈ headTable, X.root = Y.root → X = Y := by
      decide +kernel
    exact hinj A (mem A hA) D (mem D hD) hr
  · intro h
    exact (by decide +kernel : fakeHeadBody ∉ ([.genesis, ba] : List Block))
      (head_body_scope fakeHeadBody h)

/-- Both variant bodies are delivered, including a list change at an ancestor only. -/
def ha : HeadWire 4 := ⟨.seat (.head 0) 0, genesisRoot⟩
def hb : HeadWire 4 := ⟨.seat (.head 0) 1, genesisRoot⟩
def variant (raw support : List (HeadWire 4)) : NamedProposal 4 :=
  .node .genesis 1 ⟨77⟩ (packBody (n := 4) 0 []) raw support []
def variants : List (NamedProposal 4 × NamedProposal 4) :=
  [(variant [] [], variant [ha] []),
    (variant [ha] [], variant [ha] [ha]),
    (variant [ha, hb] [], variant [hb, ha] []),
    (variant [ha, hb] [], variant [ha, hb, ha] []),
    (.node (variant [ha] []) 2 ⟨88⟩ (packBody (n := 4) 0 []) [] [] [],
      .node (variant [hb] []) 2 ⟨88⟩ (packBody (n := 4) 0 []) [] [] [])]
def variantRun (N M : NamedProposal 4) := traceRun collisionParams
  [.deliver 0 (ofWire collisionParams ⟨.proposer N.slot, .proposal N⟩) 8,
    .deliver 0 (ofWire collisionParams ⟨.proposer M.slot, .proposal M⟩) 8]

theorem list_collision_controls : ∀ pair ∈ variants,
    pair.1.erase = pair.2.erase ∧ pair.1.root = pair.2.root ∧ pair.1 ≠ pair.2 ∧
      ¬ NamedRootCollisionFree collisionParams unitCodec env (variantRun pair.1 pair.2) := by
  have facts : ∀ pair ∈ variants,
      pair.1.erase = pair.2.erase ∧ pair.1.root = pair.2.root ∧ pair.1 ≠ pair.2 := by
    decide +kernel
  intro pair hp
  obtain ⟨herase, hroot, hne⟩ := facts pair hp
  refine ⟨herase, hroot, hne, ?_⟩
  apply namedScope_collision (p := collisionParams) env (variantRun pair.1 pair.2) ?_ ?_ hroot hne
  · apply namedScope_delivered env (variantRun pair.1 pair.2) (o :=
      ofWire collisionParams ⟨.proposer pair.1.slot, .proposal pair.1⟩) (t := 8) (x := 0)
    · exact List.mem_cons_self
    · rfl
  · apply namedScope_delivered env (variantRun pair.1 pair.2) (o :=
      ofWire collisionParams ⟨.proposer pair.2.slot, .proposal pair.2⟩) (t := 8) (x := 0)
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rfl

/-- Rejection cannot remove a delivered named value from scope. -/
def rejected : NamedProposal 4 := .node .genesis 1 ⟨99⟩ 0 [] [] []
def rejectedRun := traceRun pT [.deliver 0 (ofWire pT ⟨.proposer 1, .proposal rejected⟩) 4]
theorem rejected_scope : wellFormed pT ⟨.proposer 1, .proposal rejected⟩ = false ∧
    NamedProposalInRun pT unitCodec env rejectedRun rejected := by
  refine ⟨by decide +kernel, ?_⟩
  exact namedScope_delivered env rejectedRun (N := rejected)
    (o := ofWire pT ⟨.proposer 1, .proposal rejected⟩) (x := 0) (t := 4)
    (by exact List.mem_cons_self) rfl

theorem empty_scope : (∀ N, ¬ NamedProposalInRun pT unitCodec env (traceRun pT []) N) ∧
    NamedRootCollisionFree pT unitCodec env (traceRun pT []) := by
  have empty (N) : ¬ NamedProposalInRun pT unitCodec env (traceRun pT []) N := by
    rintro ⟨_, (⟨_, _, _, hm, _⟩ | ⟨v, hv, _⟩), _⟩
    · exact List.not_mem_nil hm
    · exact Finset.notMem_empty v hv
  exact ⟨empty, ⟨fun B _ hB => (empty B hB).elim⟩⟩

#print axioms body_collision_admitted
#print axioms body_collision_control
#print axioms head_direct_scope
#print axioms head_body_scope
#print axioms head_scope_control
#print axioms list_collision_controls
#print axioms rejected_scope
#print axioms empty_scope

end AvailableChain.FGSA.Run.Tests.DigestScope
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.ba
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.collisionA
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.collisionB
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.collisionParams
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.collisionRun
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.collisionWireA
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.collisionWireB
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.env
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.fakeHead
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.fakeHeadBody
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.headProposal
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.headRun
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.headWire
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.pT
#print axioms AvailableChain.FGSA.Run.Tests.DigestScope.traceRun
