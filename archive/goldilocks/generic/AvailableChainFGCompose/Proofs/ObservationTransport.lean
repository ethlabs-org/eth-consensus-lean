module
public import AvailableChainFGCompose.Statements.Channels
public import AvailableChainFGCompose.Statements.SafetyClient
public import AvailableChainFGCompose.Proofs.SourceHead

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (Q : FGSelectionReads P n)
variable (Good : P.State → Prop) (fields : FGBlock (Fin n) → HeadFields)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

/-- A nonempty source at the actual read shares its head with the signing client. -/
theorem selection_at_read (laws : FGCompose.FGSelectionLaws R O Q Good fields)
    (client : FGSelectionClientLaws Q S) {x : V} {t : Time} {nd : P.State}
    {C : FGBlock (Fin n)} (hread : postClock E rho x t = some nd)
    (hgood : Good nd) (hsource : R.source nd = some C) :
    ∃ i H, rho.events[i]? = some (.tick x t) ∧
      P.clock (V2.D.Run.stateBefore E rho i x) t = nd ∧
      Q.select nd = (some C, some H) ∧ H ∈ (R.core nd).fg.TF ∧
      FGBlock.Preceq C H ∧ S.inputs nd = (some C, fields H) := by
  obtain ⟨i, hi, hnd⟩ := postClock_tick E rho hread
  obtain ⟨H, hH, hheld⟩ := laws.head_held nd hgood
  have hC := (laws.source_eq nd hgood).trans hsource
  have hpair : Q.select nd = (some C, some H) := Prod.ext hC hH
  refine ⟨i, H, hi, hnd, hpair, hheld, laws.source_head nd C H hgood hpair, ?_⟩
  rw [← client.inputs_eq, laws.client_eq nd H hgood hH, hC]

/-- The actual tick uses the same paired inputs, including its durable record. -/
theorem selection_tick_rows (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (client : FGSelectionClientLaws Q S) (rows : FGSafetyClientLaws S Ef cfg)
    (e : Fin n ≃ V) (hseat : ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i)
    (nd : P.State) (x : V) (t : Time) :
    ((V2.D.tick E rho nd x t).2.filter P.objSelfVisible).filterMap S.decodeObject =
      if E.awake x t = true ∧ S.enabled t = true then
        (createRowOnce Ef cfg (S.record nd) (e.symm x)
          (Q.clientInputs (P.clock nd t)).1 (Q.clientInputs (P.clock nd t)).2).1.toList
      else [] := by
  rw [client.inputs_eq]
  exact rows.tick_rows E rho e hseat nd x t

/-- Both absent ticks and empty sources remain visible in the nested Option read. -/
theorem action_source_at_read (T : FGTiming) {x : V} {r : Nat} {nd : P.State}
    (hread : postClock E rho x (T.action r) = some nd) :
    actionSourceFG R E rho T x r = some (R.source nd) := by
  unfold actionSourceFG
  rw [hread, Option.map_some]

end AvailableChain.FGCompose
end
