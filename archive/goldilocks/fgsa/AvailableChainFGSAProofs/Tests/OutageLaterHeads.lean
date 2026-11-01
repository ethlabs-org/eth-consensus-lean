module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedCatchUp -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Foundations.Store

public section

namespace AvailableChain.FGSA.Run.Tests.OutageLaterHeads

open AvailableChain.SimplexFG Gen.Pure

/-- Restart at 9 permits the label-3 gate but suppresses its label-3 HEAD.
An enabled gate therefore does not supply a joined batch at the earlier vote. -/
theorem wake_nine_guard (p : Params) (hd : p.Δ = 1) :
    joinedAtTime p (some 9) (SA.voteTime p.toParams 3) = false ∧
      joinedAtTime p (some 9) (SA.gateTime p.toParams 3) = true := by
  norm_num [joinedAtTime, Params.slotOf, arming_vote_eq, arming_gate_eq, slotStartZ, hd]

/-- The label-3 marker read cannot use a time-12 transport anchor when GST is 20. -/
theorem pre_gst_marker_anchor (p : Params) (hd : p.Δ = 1) :
    ¬ (20 ≤ SA.proposalTime p.toParams 3) := by
  norm_num [arming_proposal_eq, hd]

/-- A later label-6 reader can use the time-24 anchor after the same GST. -/
theorem post_gst_marker_anchor (p : Params) (hd : p.Δ = 1) :
    20 ≤ SA.proposalTime p.toParams 6 := by
  norm_num [arming_proposal_eq, hd]

/-- With r=2 and k=2, label 6 is beyond E's fixed count window. -/
theorem post_e_count_window (p : Params) (hk : p.k = 2) :
    ¬ ((6 : Slot) ≤ 2 + p.k + 1) := by
  norm_num [hk]

/-- A gate after handover can still read a HEAD label inside E.
Its gate time does not supply the healthy joined count at that earlier vote. -/
theorem caught_gate_count_boundary (p : Params) (hd : p.Δ = 1) (hk : p.k = 2) :
    OutageEnd p 2 ≤ SA.gateTime p.toParams 4 ∧
      SA.voteTime p.toParams 4 < OutageEnd p 2 := by
  norm_num [OutageEnd, slotStartZ, arming_gate_eq, arming_vote_eq, hd, hk]

/-- The finite prefix for an early marker ends after a HEAD used by the next gate.
The seed must therefore contain source history before its own cut. -/
theorem early_marker_prefix_order (p : Params) (hd : p.Δ = 1) (hk : p.k = 2) :
    SA.voteTime p.toParams 5 < SA.gateTime p.toParams (max 3 (2 + p.k)) := by
  norm_num [arming_vote_eq, arming_gate_eq, hd, hk]

/-- An asleep deterministic read cannot be selected as an actual regression. -/
theorem asleep_not_scoped_regression {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (fast : Bool) (b₀ b₁ : Time) (B : Block) (k : Nat) (s : Slot)
    (hAsleep : ∀ q, E.awake (rho.seatOf (.base (.head s)) q)
      (SA.voteTime p.toParams s) = false) :
    ¬ OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho) fast b₀ b₁ B k s := by
  rintro ⟨_, q, _, _, hReader, _, _⟩
  have hAwake := hReader.1.2.1
  rw [hAsleep q] at hAwake
  contradiction

/-- The marker service consumes the actual Foundation monotonicity producer.
The remaining facts name this source marker and this joined read only. -/
theorem marker_service_from_foundation {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {k i : Nat} {y x : V} {m s : Slot} {B P : FGBlock (Fin p.n)}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams m)))
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hms : m ≤ s) (hGST : E.t_GST ≤ SA.voteTime p.toParams m)
    (hP : P ∈ (storeAt p c E rho k y).fg.TF) (hBP : FGBlock.Preceq B P)
    (hF : Block.Compatible (F_at p c E rho i x) (eraseFG B)) :
    Block.Preceq (eraseFG B) (F_at p c E rho i x) ∨
      P ∈ (storeAt p c E rho i x).fg.TF :=
  outage_later_marker_receipt hBase hSync (fgsa_rMonoAll p c E rho)
    hk hi hy hx hJ hms hGST hP hBP hF

/-- A restart at GST=20 suppresses the preceding HEAD but permits label 6.
The label-5 batch and freeze are after GST and before that actual joined read. -/
theorem restart_at_gst_guard (p : Params) (hd : p.Δ = 1) :
    joinedAtTime p (some 20) (SA.voteTime p.toParams 5) = false ∧
      joinedAtTime p (some 20) (SA.voteTime p.toParams 6) = true ∧
      20 ≤ SA.voteTime p.toParams 5 ∧
      SA.freezeTime p.toParams 5 < SA.voteTime p.toParams 6 := by
  norm_num [joinedAtTime, Params.slotOf, slotStartZ, arming_vote_eq, arming_freeze_eq, hd]

/-- The restart-at-9/GST=20 read has no transport request at label 3.
The first post-GST prior-batch label is 5, whose next read is joined. -/
theorem wake_nine_gst_twenty_batch (p : Params) (hd : p.Δ = 1) :
    ¬ (20 ≤ SA.voteTime p.toParams 2) ∧
      ¬ (20 ≤ SA.voteTime p.toParams 3) ∧
      20 ≤ SA.voteTime p.toParams 5 ∧
      joinedAtTime p (some 9) (SA.voteTime p.toParams 6) = true := by
  norm_num [joinedAtTime, Params.slotOf, slotStartZ, arming_vote_eq, hd]

end AvailableChain.FGSA.Run.Tests.OutageLaterHeads

#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.wake_nine_guard
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.pre_gst_marker_anchor
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.post_gst_marker_anchor
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.post_e_count_window
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.caught_gate_count_boundary
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.early_marker_prefix_order
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.asleep_not_scoped_regression
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.marker_service_from_foundation

#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.restart_at_gst_guard
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.wake_nine_gst_twenty_batch
