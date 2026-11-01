module
public import AvailableChainFGCompose.Proofs.SafetyStore
public import AvailableChainFGCompose.Proofs.SafetyClient
public import AvailableChainFGCompose.Statements.SafetyClaims
public import AvailableChainFGCompose.Proofs.Population.Safety

public section

/-! S3b field 8: honest FG seats are never slashed. Ports
F/ClientOrigin.lean (readAt_chain_row_origin), F/Carrier.lean
(stored_chain_row_origin_delivery) and F/HonestNeverSlashed.lean
(fgsa_honestNeverSlashed). Stored rows come from delivered proposals;
unforgeability gives the honest holder's emission; client safety excludes a
slashable pair. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {Ef : Electorate (Fin n)} {H : FGHeightView (Fin n)} {f : FGFinalityView (Fin n)}
variable {cfg : FGConfig}
variable [DecidableEq V] {E : Generic.Env V} {rho : V2.D.Run V P}
variable {Good : P.State → Prop}

/-- Every row of a time-read chain is decoded from a proposal row that the
node received in the original run. -/
theorem safety_read_row_origin (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (t : Time) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF)
    (u : Row (Fin n)) (hu : u ∈ chainRows B) :
    ∃ a o t', V2.Event.deliver x o t' ∈ rho.events ∧ a ∈ S.proposalRows o ∧
      S.decode a = some u := by
  induction B with
  | genesis => exact (Finset.notMem_empty u hu).elim
  | node Q s root body rows ih =>
    change u ∈ rows.toFinset ∪ chainRows Q at hu
    rcases (Finset.mem_union.mp hu).symm with hu | hu
    · exact ih ((safety_invariant_readAt L E rho t x).closed _ hB) hu
    · obtain ⟨o, t', hd, -, hrows⟩ :=
        safety_read_delivery C L E rho t x _ hB (by intro h; cases h)
      change rows = (S.proposalRows o).filterMap S.decode at hrows
      have hur : u ∈ rows := List.mem_toFinset.mp hu
      rw [hrows] at hur
      obtain ⟨a, ha, hau⟩ := List.mem_filterMap.mp hur
      exact ⟨a, o, t', hd, ha, hau⟩

/-- The rows of a time read are carried: each has a wire, and an honest
holder emitted that wire. -/
theorem safety_read_carriage (C : FGCoreLaws R) (L : FGSafetyStoreLaws R S H f Good)
    (W : FGSafetyWireLaws S) (hu : V2.D.UnforgeableSignatures E rho)
    (t : Time) (x : V) :
    safetyCarriage S E rho (safetyRows R (V2.D.Run.readAt E rho t x)) := by
  rw [safetyCarriage_def]
  intro u hmem
  rw [safetyRows_def] at hmem
  obtain ⟨B, hB, hrow⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨a, o, t', hd, ha, hdec⟩ := safety_read_row_origin C L t x B hB u hrow
  refine ⟨a, hdec, fun hh => ?_⟩
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hd
  have hholder :
      V2.D.Run.holder rho (S.encode a).auth = some (safetyHolder S rho u.signer) := by
    rw [W.decode_auth a u hdec, safetyHolder_def]
    rfl
  obtain ⟨t'', -, i, hi, hem⟩ :=
    hu.carried x o t' ⟨k, hk⟩ (S.encode a) (W.carried o a ha) _ hh hholder
  rw [safetyEmits_def]
  exact ⟨i, t'', hi, hem⟩

variable (R S Ef H f cfg E rho Good)

/-- Field 8. Under Linked and unforgeable signatures, slashing by the read
evidence never names an honest node. -/
theorem safety_honest_never_slashed
    (C : FGCoreLaws R) (W : FGSafetyWireLaws S)
    (L : FGSafetyStoreLaws R S H f Good)
    (J : FGSafetyClientLaws S Ef cfg)
    (linked : P.Label → Prop) (hfg : linked S.fgLabel)
    (I : Gen.V2.Duty.SlashingInterface (V := V) P)
    (hi : safetySlashesRead R S E rho I)
    (hu : V2.D.UnforgeableSignatures E rho) (hl : V2.D.Linked linked rho) :
    Gen.V2.Duty.HonestNeverSlashed I rho := by
  exact safety_honest_never_slashed_holder S E rho R
    (fun t x => safety_read_carriage C L W hu t x)
    (fun i _ => safety_emitted_noSlash S Ef cfg E rho W J linked hfg hl
      (safetyHolder S rho i)) I hi

end AvailableChain.FGCompose
end
