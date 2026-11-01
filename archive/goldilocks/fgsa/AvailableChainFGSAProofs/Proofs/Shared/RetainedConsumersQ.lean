module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem retained_vote_before_stop (p : Params) (s : Slot) (stop : Time)
    (hstop : SA.gateTime p.toParams s < stop) : SA.voteTime p.toParams s < stop :=
  (fgsa_vote_lt_gate p s).trans hstop

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 L4-R:2200–2222,2280–2292. Class (iii).
DC: INTENTIONAL; use the Q cone only in d_q ≤ e < min(w_a,w_b).
The later proposal's gate is strictly before both stops. The lane input is
scoped to both actual reads in that interval. No property of Q at w_a is assumed. -/
theorem fgsa_retainedReads_L4R
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
    (Q : FGBlock (Fin p.n))
    (q : Slot) (w_a w_b : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < min w_a w_b)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < min w_a w_b) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q N.erase Kc := by
  have hhead := retained_vote_before_stop p s _ hstop
  exact fgsa_retainedReads_H17 (hroots := hroots)
    E rho hE hN hDelta s hSync hx hip hseat N hem Q
    (fun y hy ih hih => hinput y hy ih hih ⟨hafter, hhead⟩)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 HG.1:1500–1574. Class (iii).
DC: INTENTIONAL; stop is the first honest frontier rise above m.
The lane input describes reads after d_q and before that stop. Slot q+1's
proposal and HEAD precede d_q (1570–1574), so they use H.6/H.6-S instead. -/
theorem fgsa_retainedReads_HG1
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
    (Q : FGBlock (Fin p.n))
    (q : Slot) (stop : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < stop) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q N.erase Kc := by
  have hhead := retained_vote_before_stop p s _ hstop
  exact fgsa_retainedReads_H17 (hroots := hroots)
    E rho hE hN hDelta s hSync hx hip hseat N hem Q
    (fun y hy ih hih => hinput y hy ih hih ⟨hafter, hhead⟩)

theorem fgsa_retainedReads_L4R_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Q : FGBlock (Fin p.n))
    (q : Slot) (w_a w_b : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < min w_a w_b)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < min w_a w_b) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q N.erase Kc := by
  have hhead := retained_vote_before_stop p s _ hstop
  exact fgsa_retainedReads_H17_on (hroots := hroots)
    E rho hE s hx hip hseat N hem Q
    (hServices := hServices)
    (fun y hy ih hih => hinput y hy ih hih ⟨hafter, hhead⟩)

theorem fgsa_retainedReads_HG1_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Q : FGBlock (Fin p.n))
    (q : Slot) (stop : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < stop) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q N.erase Kc := by
  have hhead := retained_vote_before_stop p s _ hstop
  exact fgsa_retainedReads_H17_on (hroots := hroots)
    E rho hE s hx hip hseat N hem Q
    (hServices := hServices)
    (fun y hy ih hih => hinput y hy ih hih ⟨hafter, hhead⟩)

/-- Joined reader form; service is required only for that reader. -/
theorem fgsa_retainedReads_L4R_joined
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Q : FGBlock (Fin p.n))
    (q : Slot) (w_a w_b : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < min w_a w_b)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < min w_a w_b) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q)
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
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q N.erase Kc := by
  have hhead := retained_vote_before_stop p s _ hstop
  exact fgsa_retainedReads_H17_joined (hroots := hroots)
    E rho hE s hx hip hseat N hem Q
    (hServices := hServices)
    (fun y hy ih hih hjoined => hinput y hy ih hih hjoined ⟨hafter, hhead⟩)

/-- Joined reader form; service is required only for that reader. -/
theorem fgsa_retainedReads_HG1_joined
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Q : FGBlock (Fin p.n))
    (q : Slot) (stop : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < stop) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q)
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
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q N.erase Kc := by
  have hhead := retained_vote_before_stop p s _ hstop
  exact fgsa_retainedReads_H17_joined (hroots := hroots)
    E rho hE s hx hip hseat N hem Q
    (hServices := hServices)
    (fun y hy ih hih hjoined => hinput y hy ih hih hjoined ⟨hafter, hhead⟩)

end AvailableChain.FGSA.Run
end
