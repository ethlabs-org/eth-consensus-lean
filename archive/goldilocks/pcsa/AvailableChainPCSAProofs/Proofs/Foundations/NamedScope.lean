module
public import AvailableChainPCSAProofs.Proofs.Foundations.Proposals
public import AvailableChainPCSAProofs.Proofs.Foundations.TickOutput
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Shared.Roots
public import AvailableChainPCSARun.Statements.Roots
public import AvailableChainKitFG.RootScopeDef

public section

/-! Named ancestry, delivery origin, and scoped roots for PC-SA (FG finality
safety, step P5). These results use PC-SA names only. -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- Named ancestry contains each body itself. -/
theorem pcsa_named_preceq_self (N : NamedProposal n) : NamedProposal.Preceq N N := by
  cases N <;> simp [NamedProposal.Preceq, NamedProposal.preceq]

/-- Erasure keeps the parent geometry. -/
theorem pcsa_named_erase_parent (N : NamedProposal n) : N.erase.parent = N.parent.erase := by
  cases N <;> rfl

/-- Named ancestry composes. -/
theorem pcsa_named_preceq_trans {A B C : NamedProposal n}
    (hAB : NamedProposal.Preceq A B) (hBC : NamedProposal.Preceq B C) :
    NamedProposal.Preceq A C := by
  induction C with
  | genesis =>
      have h : B = .genesis := by simpa [NamedProposal.Preceq, NamedProposal.preceq] using hBC
      simpa [h] using hAB
  | node P s r x raw sup rows pc ih =>
      simp only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hBC ⊢
      rcases hBC with rfl | h
      · simpa only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
          decide_eq_true_eq] using hAB
      · exact Or.inr (ih h)

/-- Named ancestry preserves geometry. -/
theorem pcsa_named_preceq_erase {A B : NamedProposal n} (h : NamedProposal.Preceq A B) :
    Block.Preceq A.erase B.erase := by
  induction B with
  | genesis =>
      have he : A = .genesis := by simpa [NamedProposal.Preceq, NamedProposal.preceq] using h
      subst A
      rfl
  | node P s r x raw sup rows pc ih =>
      simp only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at h
      simp only [NamedProposal.erase, Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq]
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (ih h)

/-- An erased ancestor lifts to a named ancestor, without injectivity. -/
theorem pcsa_named_erase_ancestor {N : NamedProposal n} {b : Block}
    (h : Block.Preceq b N.erase) :
    ∃ A, NamedProposal.Preceq A N ∧ A.erase = b := by
  induction N with
  | genesis =>
      have he : b = .genesis := by
        simpa [NamedProposal.erase, Block.Preceq, Block.preceq] using h
      exact ⟨.genesis, pcsa_named_preceq_self _, he.symm⟩
  | node P s r x raw sup rows pc ih =>
      simp only [NamedProposal.erase, Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at h
      rcases h with he | h
      · exact ⟨.node P s r x raw sup rows pc, pcsa_named_preceq_self _, he.symm⟩
      · obtain ⟨A, hA, he⟩ := ih h
        refine ⟨A, ?_, he⟩
        simp only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
          decide_eq_true_eq]
        exact Or.inr hA

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every stored proposal wire came from an earlier delivery to the same node.
The run can contain restarts. -/
theorem pcsa_stored_proposal_delivered (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (i : Nat) (v : V) (w : Wire p.n)
    (hw : w ∈ (V2.D.Run.stateBefore E rho i v).st.proposals) :
    ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver v o t) ∧ toWire p o = w := by
  let Q : Node p → Prop := fun nd => ∀ w ∈ nd.st.proposals,
    ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver v o t) ∧ toWire p o = w
  have h0 : Q (V2.D.Run.stateBefore E rho 0 v) := by
    intro w hw
    change w ∈ ([] : List (Wire p.n)) at hw
    exact (List.not_mem_nil hw).elim
  refine V2.D.Engine.stateBefore_step_induction E rho Q (Nat.zero_le i) v ?_ h0 w hw
  intro k e _ hki he hn h
  cases e with
  | restart u t =>
      change u = v at hn
      subst u
      change Q (Function.update (V2.D.Run.stateBefore E rho k) v _ v)
      rw [Function.update_self]
      intro w hw
      change w ∈ ([] : List (Wire p.n)) at hw
      exact (List.not_mem_nil hw).elim
  | tick u t =>
      change u = v at hn
      subst u
      change Q (Function.update (V2.D.Run.stateBefore E rho k) v _ v)
      rw [Function.update_self]
      intro w hw
      have hw' := Eq.mp (congrArg (fun st : State p.n => w ∈ st.proposals)
        (pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k v) v t)) hw
      rw [pcsa_clock_proposals] at hw'
      exact h w hw'
  | deliver u o t =>
      change u = v at hn
      subst u
      change Q (Function.update (V2.D.Run.stateBefore E rho k) v _ v)
      rw [Function.update_self]
      intro w hw
      change w ∈ (PCSA.process p (V2.D.Run.stateBefore E rho k v).st (toWire p o)).proposals
        at hw
      rcases pcsa_process_proposals p _ (toWire p o) with hp | ⟨s, N, hd, hp⟩
      · rw [hp] at hw
        exact h w hw
      · rw [hp, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact h w hw
        · exact ⟨k, o, t, hki, he, pcsa_wire_decode_block _ s N hd⟩

/-- Every held named body is genesis or the payload of a delivery to that node. -/
theorem pcsa_namedBody_delivered (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (i : Nat) (v : V) (N : NamedProposal p.n)
    (hN : N ∈ (V2.D.Run.stateBefore E rho i v).st.namedBodies) :
    N = .genesis ∨ ∃ o t, V2.Event.deliver v o t ∈ rho.events ∧ o.payload = .proposal N := by
  rw [State.namedBodies, List.mem_cons, List.mem_filterMap] at hN
  rcases hN with rfl | ⟨w, hw, hN⟩
  · exact Or.inl rfl
  · right
    obtain ⟨k, o, t, -, hk, ho⟩ := pcsa_stored_proposal_delivered E rho i v w hw
    obtain ⟨s, rfl⟩ := pcsa_wire_proposal_some w N hN
    refine ⟨o, t, List.mem_of_getElem? hk, ?_⟩
    exact congrArg (fun w : Wire p.n => w.payload) ho

/-- Genesis is in the named scope when one node is honest. -/
theorem pcsa_namedScope_genesis (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {x : V} (hx : x ∈ rho.honest) : NamedProposalInRun p c E rho .genesis := by
  refine ⟨.genesis, Or.inr ⟨x, hx, 0, ?_⟩, pcsa_named_preceq_self _⟩
  rw [State.namedBodies]
  exact List.mem_cons_self

/-- A delivered proposal is in the named scope, even if it is refused. -/
theorem pcsa_namedScope_delivered (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {x : V} {o : Obj p} {t : Time} {N : NamedProposal p.n}
    (hd : V2.Event.deliver x o t ∈ rho.events) (ho : o.payload = .proposal N) :
    NamedProposalInRun p c E rho N :=
  ⟨N, Or.inl ⟨x, o, t, hd, ho⟩, pcsa_named_preceq_self N⟩

/-- A body held by any node, honest or not, is in the named scope when one node is
honest. -/
theorem pcsa_namedScope_held (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {x : V} (hx : x ∈ rho.honest) (i : Nat) (v : V) {N : NamedProposal p.n}
    (hN : N ∈ (V2.D.Run.stateBefore E rho i v).st.namedBodies) :
    NamedProposalInRun p c E rho N := by
  rcases pcsa_namedBody_delivered E rho i v N hN with rfl | ⟨o, t, hd, ho⟩
  · exact pcsa_namedScope_genesis E rho hx
  · exact pcsa_namedScope_delivered E rho hd ho

/-- The named scope is closed under named ancestry. -/
theorem pcsa_namedScope_ancestor (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {A B : NamedProposal p.n} (hB : NamedProposalInRun p c E rho B)
    (hAB : NamedProposal.Preceq A B) : NamedProposalInRun p c E rho A := by
  obtain ⟨C, hC, hBC⟩ := hB
  exact ⟨C, hC, pcsa_named_preceq_trans hAB hBC⟩

/-- The projected scope is closed under ancestry. -/
theorem pcsa_rootBlockInRun_ancestor (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {A B : Block}
    (hB : RootBlockInRun p c E rho B) (hAB : Block.Preceq A B) :
    RootBlockInRun p c E rho A := by
  obtain ⟨N, hN, rfl⟩ := hB
  obtain ⟨M, hM, he⟩ := pcsa_named_erase_ancestor hAB
  exact ⟨M, pcsa_namedScope_ancestor E rho hN hM, he⟩

/-- Collision freedom makes the projected scope injective on roots. -/
theorem pcsa_rootBlockInRun_root_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hr : NamedRootCollisionFree p c E rho)
    {A B : Block} (hA : RootBlockInRun p c E rho A) (hB : RootBlockInRun p c E rho B)
    (he : A.root = B.root) : A = B := by
  obtain ⟨N, hN, rfl⟩ := hA
  obtain ⟨M, hM, rfl⟩ := hB
  have hN' : N.erase.root = N.root := by cases N <;> rfl
  have hM' : M.erase.root = M.root := by cases M <;> rfl
  have hroot : N.root = M.root := by
    rw [← hN', ← hM']
    exact he
  exact congrArg NamedProposal.erase (hr.root_injective N M hN hM N M
    (Or.inl (pcsa_named_preceq_self N)) (Or.inr (pcsa_named_preceq_self M)) hroot)

/-- Scoped FG chains have injective roots. -/
theorem pcsa_rootInjectiveOn_run (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hr : NamedRootCollisionFree p c E rho) {K W : FGBlock (Fin p.n)}
    (hK : RootBlockInRun p c E rho (eraseFG K))
    (hW : RootBlockInRun p c E rho (eraseFG W)) : KitFG.RootInjectiveOn K W := by
  rw [AvailableChain.PCSA.pcsa_eraseFG_eq] at hK hW
  intro A B hA hB he
  apply FGSA.eraseFG_injective
  apply pcsa_rootBlockInRun_root_eq E rho hr
  · rcases hA with hA | hA
    · exact pcsa_rootBlockInRun_ancestor E rho hK (FGSA.eraseFG_preceq hA)
    · exact pcsa_rootBlockInRun_ancestor E rho hW (FGSA.eraseFG_preceq hA)
  · rcases hB with hB | hB
    · exact pcsa_rootBlockInRun_ancestor E rho hK (FGSA.eraseFG_preceq hB)
    · exact pcsa_rootBlockInRun_ancestor E rho hW (FGSA.eraseFG_preceq hB)
  · simpa only [FGSA.eraseFG_root] using he

/-- An emitted proposal names a parent that its emitter already held. -/
theorem pcsa_emitted_proposal_parent (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) (t : Time) (s : Slot)
    (N : NamedProposal p.n) (hk : rho.events[k]? = some (.tick x t))
    (hem : ofWire p ⟨.proposer s, .proposal N⟩ ∈ V2.D.Run.emitsAt E rho k) :
    N.parent ∈ (V2.D.Run.stateBefore E rho k x).st.namedBodies := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at hem
  have hp := ((pcsa_emits_proposal m E rho _ x t s _).mp hem).2.2.2
  rw [propose] at hp
  split_ifs at hp
  · cases hp
  · simp only [Option.map_map] at hp
    obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp hp
    have hparent : N.parent = P := by
      have h := congrArg (fun msg : Msg p.n =>
        match msg with | .proposal M => M.parent | _ => .genesis) he
      exact h.symm
    have hm := (pcsa_namedByErase_sound _ _ P hP).1
    rw [pcsa_clock_namedBodies] at hm
    rw [hparent]
    exact hm

end AvailableChain.PCSA.Run
end
