module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

/-! S5 J6, H.17; blueprint 21:2958–3012. The retained cone is an abstract
input. Its later producer is HG.3–HG.5 / G-H17. This file does not construct
that producer or use the full healing witness. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.17 abstract retained cone at labels at least sStar + 2. The later producer
is HG.3–HG.5 / G-H17. For each actual honest proposal with its HEAD deadline
inside the horizon, it supplies exactly the per-reader `RetainedConeInput`
premise of `fgsa_retainedReads_H17`, with one pivot D for that proposal.
It supplies no exact HEAD, gate geometry, service, or source-prefix fact. -/
def PostResetRetainedCone (w : HealingWitness) : Prop :=
  ∀ s, w.sStar + 2 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
  ∀ {ip : Nat} {x : V}, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x →
  ∀ (N : NamedProposal p.n),
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip →
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D1; DC: SAME cone at one label. -/
def PostResetConeAt (w : HealingWitness) (s : Slot) : Prop :=
  w.sStar + 2 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
  ∀ {ip : Nat} {x : V}, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x →
  ∀ (N : NamedProposal p.n),
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip →
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D1; DC: SAME cone at one label. -/
theorem PostResetConeAt_def (w : HealingWitness) (s : Slot) :
    PostResetConeAt p c E rho w s = (
  w.sStar + 2 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
  ∀ {ip : Nat} {x : V}, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x →
  ∀ (N : NamedProposal p.n),
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip →
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D) := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D1; DC: SAME cone at one label. -/
theorem postResetRetainedCone_iff_at (w : HealingWitness) :
    PostResetRetainedCone p c E rho w ↔ ∀ s, PostResetConeAt p c E rho w s := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Application theorem for this module's abstract input; consumers can apply it
without access to private module data. -/
theorem postResetRetainedCone_iff (w : HealingWitness) :
    PostResetRetainedCone p c E rho w ↔
    (∀ s, w.sStar + 2 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    ∀ {ip : Nat} {x : V}, x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x →
    ∀ (N : NamedProposal p.n),
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
        rho.emitsAt E ip →
      ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
        rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
        RetainedConeInput p
          (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
          (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D) := Iff.rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Risk 6: the reset label is at most v - 2 at every H3 proposal. -/
theorem postReset_source_label_le_sub_two (w : HealingWitness) {v : Slot}
    (hv : w.sStar + 2 ≤ v) : w.sStar ≤ v - 2 := Nat.le_sub_of_add_le hv

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Risk 6: q_(sStar) is the release time. It precedes the next H3
proposal's synchronization window, including v = sStar + 2. This is a
clock bound, not a claim that reset transfer has been proved. -/
theorem postReset_release_before_proposal (w : HealingWitness) {v : Slot}
    (hv : w.sStar + 2 ≤ v) :
    SA.releaseTime p.toParams w.sStar ≤ SA.proposalTime p.toParams v - p.Δ := by
  have hvI : (w.sStar : Int) + 2 ≤ (v : Int) := by exact_mod_cast hv
  change 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ ≤ 4 * p.Δ * (v : Int) - p.Δ
  nlinarith [p.deltaPos]

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Risk 4: a HEAD deadline inside the horizon also contains its proposal. -/
theorem postReset_proposal_horizon {v : Slot}
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon) :
    SA.proposalTime p.toParams v ≤ rho.horizon := by
  have hd := p.deltaPos
  change 4 * p.Δ * (v : Int) + p.Δ ≤ rho.horizon at hHeadHorizon
  change 4 * p.Δ * (v : Int) ≤ rho.horizon
  linarith

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Risk 4: the gate horizon implies the distinct HEAD horizon. -/
theorem postReset_head_horizon {v : Slot}
    (hGateHorizon : SA.gateTime p.toParams v ≤ rho.horizon) :
    SA.voteTime p.toParams v ≤ rho.horizon := by
  have hd := p.deltaPos
  change 4 * p.Δ * (v : Int) + 6 * p.Δ ≤ rho.horizon at hGateHorizon
  change 4 * p.Δ * (v : Int) + p.Δ ≤ rho.horizon
  linarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H0Reset.synchronous gives the H.17 window without H.18 proposal data. -/
theorem postReset_synchronous_window (w : HealingWitness)
    (hreset : H0Reset p c E rho w) {v : Slot} (hv : w.sStar + 2 ≤ v) :
    E.t_GST ≤ SA.proposalTime p.toParams v - p.Δ := by
  have hrelease := postReset_release_before_proposal p w hv
  have hvote : SA.voteTime p.toParams w.sStar ≤ SA.releaseTime p.toParams w.sStar := by
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤ 4 * p.Δ * (w.sStar : Int) + 5 * p.Δ
    linarith [p.deltaPos]
  exact hreset.synchronous.trans (hvote.trans hrelease)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A cone is empty only when every relevant HEAD deadline is outside the
horizon. This lemma makes no reset or service claim for such a short run. -/
theorem postResetRetainedCone_of_horizon_lt (w : HealingWitness)
    (hshort : rho.horizon < SA.voteTime p.toParams (w.sStar + 2)) :
    PostResetRetainedCone p c E rho w := by
  intro s hs hHeadHorizon
  have hsI : ((w.sStar + 2 : Nat) : Int) ≤ (s : Int) := by exact_mod_cast hs
  change rho.horizon < 4 * p.Δ * ((w.sStar + 2 : Nat) : Int) + p.Δ at hshort
  change 4 * p.Δ * (s : Int) + p.Δ ≤ rho.horizon at hHeadHorizon
  have hmono : 4 * p.Δ * ((w.sStar + 2 : Nat) : Int) + p.Δ ≤
      4 * p.Δ * (s : Int) + p.Δ := by nlinarith [p.deltaPos]
  exact (not_lt_of_ge (hmono.trans hHeadHorizon) hshort).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Apply the abstract cone to the existing H.17 supplier. The output keeps
each reader's actual state and the common proposal pivot.
Blueprint 21 H.17:2946–3040; plan RE-BIND D2; DC: SAME per-label cone. -/
theorem healing_postReset_retainedReads_at
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (w : HealingWitness) (s : Slot) (hcone : PostResetConeAt p c E rho w s) (hs : w.sStar + 2 ≤ s)
    (hHeadHorizon : SA.voteTime p.toParams s ≤ rho.horizon)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  obtain ⟨D, hinput⟩ := hcone hs hHeadHorizon hx hip hseat N hem
  exact ⟨D, fgsa_retainedReads_H17 (hroots := hroots) E rho hE hN hDelta s hSync hx hip hseat
    N hem D hinput⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.17:2946–3040; plan RE-BIND D2/D3; DC: SAME cone at its label. -/
theorem healing_postReset_retainedReads
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (w : HealingWitness) (hcone : PostResetRetainedCone p c E rho w)
    (s : Slot) (hs : w.sStar + 2 ≤ s)
    (hHeadHorizon : SA.voteTime p.toParams s ≤ rho.horizon)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  exact healing_postReset_retainedReads_at (hroots := hroots) p c E rho hE hN hDelta w s
    ((postResetRetainedCone_iff_at p c E rho w).mp hcone s) hs hHeadHorizon hSync
    hx hip hseat N hem

/-- H.17 retained reads use joined readers and exact per-object receiver services. -/
theorem healing_postReset_retainedReads_at_on
    (hE : V2.D.ExecutionValid E rho) (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip)
    (hcone : ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D)
    (hServices : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  obtain ⟨D, hinput⟩ := hcone
  exact ⟨D, fgsa_retainedReads_H17_joined (hroots := hroots)
    E rho hE s hx hip hseat N hem D hinput hServices⟩

end AvailableChain.FGSA.Run
end
