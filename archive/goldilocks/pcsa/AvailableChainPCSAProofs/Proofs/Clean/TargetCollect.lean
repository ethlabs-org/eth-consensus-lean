module
public import AvailableChainPCSAProofs.Proofs.Clean.AckAdmit

public section

/-! C3 exact lookup and collection for held run targets. -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Collision freedom makes the lookup of a held target exact. -/
theorem pcsa_lookup_held_target (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (j : Nat) (y : V) (hy : y ∈ rho.honest) (B : Block)
    (hB : B ∈ (V2.D.Run.stateBefore E rho j y).st.base.blocks) :
    (V2.D.Run.stateBefore E rho j y).st.base.blocks.find? (fun b => b.root == B.root) = some B := by
  let st := (V2.D.Run.stateBefore E rho j y).st
  cases hf : st.base.blocks.find? (fun b => b.root == B.root) with
  | none =>
    have hn := List.find?_eq_none.mp hf B hB
    have ht : (B.root == B.root) = true := BEq.rfl
    exact (hn ht).elim
  | some D =>
    have hm := List.mem_of_find?_eq_some hf
    have hr : (D.root == B.root) = true :=
      List.find?_some (p := fun b : Block => b.root == B.root) hf
    have hs := pcsa_body_scope E rho j y hy
    have he := pcsa_scoped_root_eq E rho h.idealization D B (hs D hm) (hs B hB)
      (beq_iff_eq.mp hr)
    exact congrArg some he
/-- Run-level collection for a held slot-correct target in stage 1. -/
theorem pcsa_collect_held_target (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (j : Nat) (y : V) (hy : y ∈ rho.honest)
    (s : Slot) (B : Block) (hs : 0 < s) (hb : B.slot = s)
    (hB : B ∈ (V2.D.Run.stateBefore E rho j y).st.base.blocks)
    (Q : Finset (Fin p.n)) (hQ : pcQuorum p.n ≤ Q.card)
    (hp : ∀ i ∈ Q, (⟨.seat (.ack s) i, B.root⟩ : AckWire p.n) ∈
      (V2.D.Run.stateBefore E rho j y).st.ackPool) :
    ∃ C ∈ (collectPCs (V2.D.Run.stateBefore E rho j y).st).pcs,
      C.slot = s ∧ C.target = B := by
  exact pcsa_collectPCs_quorum p _ s B hs hb
    (pcsa_lookup_held_target E rho h j y hy B hB) (hF y hy j).1 Q hQ hp
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA
private theorem pcsa_proposed_slot (p : Params) (st : State p.n) (s app : Nat)
    (N : NamedProposal p.n)
    (h : (propose p st s).map (Run.withApp p app) = some (.proposal N)) : N.erase.slot = s := by
  obtain ⟨M, hM, hN⟩ := Option.map_eq_some_iff.mp h
  delta propose at hM
  split at hM
  · cases hM
  · obtain ⟨P, _, hMsg⟩ := Option.map_eq_some_iff.mp hM
    subst M
    change Msg.proposal (namedProposal p P s app _ _ _ _) = Msg.proposal N at hN
    obtain rfl := Msg.proposal.inj hN
    rfl
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem pcsa_prop_signLabel (d : RunDuty) (s : Slot) :
    d.signLabel = .prop s ↔ d = .propAction s := by
  cases d <;> dsimp only [RunDuty.signLabel] <;> simp

theorem pcsa_proposal_emitted_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (N : NamedProposal p.n)
    (t : Time) (he : V2.D.Run.emits E rho x
      (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p) t) : N.erase.slot = s := by
  obtain ⟨k, hk, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, _, ha⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.prop s) (0 : Fin 1) (.proposal N)).mp ho
  obtain rfl := (pcsa_prop_signLabel d s).mp hl
  cases m <;>
    change (propose p (clock p (V2.D.Run.stateBefore E rho k x).st t) s).map
      (withApp p (c.app (rho.input x t))) = some (.proposal N) at ha
  all_goals exact pcsa_proposed_slot p _ s _ N ha
/-- Formation's hPCCollect interface once exact body receipt is supplied. -/
theorem pcsa_formation_collect_of_held_body [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF)
    (hBody : ∀ y ∈ rho.honest, N.erase ∈
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.base.blocks) :
    ∀ y ∈ rho.honest, ∀ Q : Finset (Fin p.n),
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card → ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = N.erase := by
  have hs : N.erase.slot = s := pcsa_proposal_emitted_slot E rho _ s N _ h.proposal.2
  intro y hy Q
  dsimp only
  intro hp hQ
  have hj := Gen.V2.Duty.stateBefore_idxBefore E rho (SA.freezeTime p.toParams s)
    h.base.valid.toScheduleWellFormed
  have hb := hBody y hy
  rw [← hj] at hp hb ⊢
  exact pcsa_collect_held_target E rho h.base h.frame _ y hy s N.erase h.slotPos hs hb Q hQ hp

end AvailableChain.PCSA.Run

end
