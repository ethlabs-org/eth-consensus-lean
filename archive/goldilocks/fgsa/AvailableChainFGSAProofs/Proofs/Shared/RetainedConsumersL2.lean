module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 L2-W:2080–2095,2119–2126; L2:2149–2162. Class (iii).
DC: INTENTIONAL; the new J-rooted frame and inherited lease support are separate.
There is no premise that the preceding HEAD batch covers J. -/
structure RetainedL2Input (p : Params) (src dst : State p.n) (s : Slot)
    (J : FGBlock (Fin p.n)) : Prop where
  source_root : (controls p src).Z = J
  target_root : (controls p dst).Z = J
  source_floor : (controls p src).lo ≤ (heightView p J).h
  target_floor : (controls p dst).lo ≤ (heightView p J).h
  proposer_prior : Block.Preceq (ap p src) (z p src) ∨
    RetainedPriorSupport p src s (ap p src)
  reader_prior : Block.Preceq (ay p dst) (z p src) ∨
    RetainedPriorSupport p src s (ay p dst) ∨
    ∀ W ∈ src.fg.TF, (controls p src).lo ≤ (heightView p W).h →
      Block.Preceq (ay p dst) (eraseFG W)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 L2:2159–2162. Class (iii).
DC: INTENTIONAL; both roots equal J, so the prefix to the deeper of J and ay is empty. -/
private theorem consumer_l2_cone (p : Params) (src dst : State p.n) (s : Slot)
    (J : FGBlock (Fin p.n)) (h : RetainedL2Input p src dst s J) :
    RetainedConeInput p src dst s J := by
  have hz : z p src = eraseFG J := congrArg eraseFG h.source_root
  have hjy : Block.Preceq (eraseFG J) (ay p dst) := by
    have hh := fgsa_Z_preceq_liveRoot p dst
    rw [h.target_root] at hh
    exact hh
  refine ⟨h.proposer_prior, h.reader_prior, Or.inl ?_, h.source_floor, h.target_floor, ?_⟩
  · rw [hz]
    exact block_preceq_refl _
  · intro L hL hlt
    have he : L = eraseFG J := hL.elim (fun he => he.trans hz) id
    rw [he] at hlt
    have heq := block_preceq_antisymm hjy (Bool.and_eq_true_iff.mp hlt).2
    have hn := (Bool.and_eq_true_iff.mp hlt).1
    simp only [heq, decide_true, Bool.not_true, Bool.false_eq_true] at hn

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 L2:2128–2167; L2-W:2119–2126. Class (iii).
DC: INTENTIONAL; inherited service and root-evidence time are both retained.
rd is the original inherited deadline; an unresolved repair does not reset it.
stop is the next effective event. The preceding HEAD need not cover J.
The source root is J and Kc is the deeper of J and ay, with an empty prefix. -/
theorem fgsa_retainedReads_L2
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (J : FGBlock (Fin p.n))
    (rd w stop : Time)
    (hinherited : rd ≤ SA.gateTime p.toParams s)
    (hevidence : w + 2 * p.Δ ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (rd ≤ SA.gateTime p.toParams s ∧
        w + 2 * p.Δ ≤ SA.proposalTime p.toParams s ∧ SA.gateTime p.toParams s < stop) →
      RetainedL2Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s J)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s J N.erase Kc := by
  apply fgsa_retainedReads_H17 (hroots := hroots)
    E rho hE hN hDelta s hSync hx hip hseat N hem J
  intro y hy ih hih
  exact consumer_l2_cone p _ _ s J
    (hinput y hy ih hih ⟨hinherited, hevidence, hstop⟩)

theorem fgsa_retainedReads_L2_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (J : FGBlock (Fin p.n))
    (rd w stop : Time)
    (hinherited : rd ≤ SA.gateTime p.toParams s)
    (hevidence : w + 2 * p.Δ ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      (rd ≤ SA.gateTime p.toParams s ∧
        w + 2 * p.Δ ≤ SA.proposalTime p.toParams s ∧ SA.gateTime p.toParams s < stop) →
      RetainedL2Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s J)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s J N.erase Kc := by
  apply fgsa_retainedReads_H17_on (hroots := hroots) (hServices := hServices)
    E rho hE s hx hip hseat N hem J
  intro y hy ih hih
  exact consumer_l2_cone p _ _ s J
    (hinput y hy ih hih ⟨hinherited, hevidence, hstop⟩)

/-- Joined reader form; service is required only for that reader. -/
theorem fgsa_retainedReads_L2_joined
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (J : FGBlock (Fin p.n))
    (rd w stop : Time)
    (hinherited : rd ≤ SA.gateTime p.toParams s)
    (hevidence : w + 2 * p.Δ ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      (rd ≤ SA.gateTime p.toParams s ∧
        w + 2 * p.Δ ≤ SA.proposalTime p.toParams s ∧ SA.gateTime p.toParams s < stop) →
      RetainedL2Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s J)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s J N.erase Kc := by
  apply fgsa_retainedReads_H17_joined (hroots := hroots) (hServices := hServices)
    E rho hE s hx hip hseat N hem J
  intro y hy ih hih hjoined
  exact consumer_l2_cone p _ _ s J
    (hinput y hy ih hih hjoined ⟨hinherited, hevidence, hstop⟩)

end AvailableChain.FGSA.Run
end
