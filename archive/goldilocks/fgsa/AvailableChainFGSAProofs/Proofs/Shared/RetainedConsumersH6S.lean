module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6-S:988–1033; H.4-S:817–854. Class (iii).
DC: INTENTIONAL; reuse the H.6 field producers with H.4-S prior support.
Here the prior-support part of hinput is the upstream consequence of (S),
the last actual write split, and expiry before the preceding HEAD duty.
Equality at expiry is permitted; a renewal uses its last write. The theorem
assembles those lane facts and does not assert that the lane induction is closed. -/
theorem fgsa_retainedReads_H6S
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
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s
        (controls p (clock p (rho.stateBefore E ip x).st
          (SA.proposalTime p.toParams s))).Z N.erase Kc := by
  exact fgsa_retainedReads_H6 (hroots := hroots)
    E rho hE hN hDelta s hSync hx hip hseat N hem hinput

theorem fgsa_retainedReads_H6S_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s
        (controls p (clock p (rho.stateBefore E ip x).st
          (SA.proposalTime p.toParams s))).Z N.erase Kc := by
  exact fgsa_retainedReads_H6_on (hroots := hroots)
    E rho hE s hx hip hseat N hem hinput hServices

/-- Joined reader form; service is required only for that reader. -/
theorem fgsa_retainedReads_H6S_joined
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (V2.Event.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s)
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
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s
        (controls p (clock p (rho.stateBefore E ip x).st
          (SA.proposalTime p.toParams s))).Z N.erase Kc := by
  exact fgsa_retainedReads_H6_joined (hroots := hroots)
    E rho hE s hx hip hseat N hem hinput hServices

end AvailableChain.FGSA.Run
end
