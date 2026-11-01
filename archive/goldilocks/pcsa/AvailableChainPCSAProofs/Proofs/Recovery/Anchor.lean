module
public import AvailableChainPCSAClaims.Statements.Premises

public section

/-! Anchor arming (pcsa34-r4.3b §5.6.1).
The named Formation input is the prefix form: common stamps by z_c.
The full FormationPrem requires delivery through d_c, which CLEAN(z_c)
does not supply. The Clean lane must provide this prefix bridge. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

omit [Fintype V] in
/-- A common PC immediately arms the next label: the intermediate ack interval is empty. -/
theorem arm_next_of_common_stamp (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (P : Block)
    (hstamp : ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s P) :
    Arm p c E rho s P (s + 1) := by
  try delta Slot Time at *
  constructor
  · simpa only [Nat.add_sub_cancel] using hstamp
  · intro _ j _ hlo hhi _
    exact (Nat.not_lt_of_ge hlo hhi).elim

/-- The anchor PC is common and arms the next label under prefix Formation.
This hypothesis includes the corrected proposer-root premise in its producer. -/
theorem recovery_anchor (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (cA : Slot) (ΔF : Time)
    (anchorPos : 0 < cA)
    (hclean : Clean₂ p c E rho (SA.freezeTime p.toParams cA) ΔF)
    (hframe : StageOneFrame p c E rho) (hcap : QuarterCap p c rho)
    (hprop : Gen.V2.Duty.HonestAwakeProposer E
      (pcsaInterface p c (m := m)).toInterface rho cA)
    (hpart : nQuorum p.n ≤ (awakeHonestLabel p c E rho cA).card)
    (formationPrefix : ∀ s : Slot, 0 < s →
      Clean₂ p c E rho (SA.freezeTime p.toParams s) ΔF →
      StageOneFrame p c E rho → QuarterCap p c rho →
      Gen.V2.Duty.HonestAwakeProposer E
        (pcsaInterface p c (m := m)).toInterface rho s →
      nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card →
      ∃ N : NamedProposal p.n, HonestNamedProposal p c E rho s N ∧
        ∀ y ∈ rho.honest,
          PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) :
    ∃ N : NamedProposal p.n, HonestNamedProposal p c E rho cA N ∧
      (∀ y ∈ rho.honest,
        PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA N.erase) ∧
      Arm p c E rho cA N.erase (cA + 1) := by
  try delta Slot Time at *
  obtain ⟨N, hN, hs⟩ := formationPrefix cA anchorPos hclean hframe hcap hprop hpart
  exact ⟨N, hN, hs, arm_next_of_common_stamp E rho cA N.erase hs⟩

omit [Fintype V] in
/-- A named honest proposal is an honest proposal in the output interface. -/
theorem honestProposal_of_named (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n)
    (h : HonestNamedProposal p c E rho s N) :
    Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho s N.erase :=
  ⟨h.1, .proposal N, rfl, h.2⟩

end AvailableChain.PCSA.Run
end
