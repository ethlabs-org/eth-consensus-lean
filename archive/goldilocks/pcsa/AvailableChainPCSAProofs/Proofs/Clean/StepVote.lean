module
public import AvailableChainPCSAProofs.Proofs.Shared.Walk
public import AvailableChainPCSAClaims.Statements.LaneReads

public section

/-! CI StepVote: the root branch and the slot-zero HEAD. -/

namespace AvailableChain.PCSA.Run
open Gen.Pure
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- At a positive slot, an honest HEAD extends its actual duty root. -/
theorem pcsa_honestHead_extends_root (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (H R : Block)
    (hs : 0 < s) (hH : HonestHeadAt p c E rho x s H)
    (hR : liveRootAt p c E rho x s = some R) : Block.Preceq R H := by
  have hh := hH.2.2
  rw [pcsa_voteHeadAt_def] at hh
  obtain ⟨nd, hnd, he⟩ := Option.map_eq_some_iff.mp hh
  rw [pcsa_liveRootAt_def, hnd] at hR
  have hr : liveRoot p nd.st (voterPC p nd.st s) = R := Option.some.inj hR
  rw [← hr, ← he]
  delta headVote
  rw [ite_eq_right (Nat.ne_of_gt hs)]
  exact pcsa_headInTree_extends_root p nd.st _ _ _ _
/-- The root-above-result branch of CI step (a). -/
theorem pcsa_clean_head_above_root_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (s : Slot) (H R X : Block)
    (hs : 0 < s) (hH : HonestHeadAt p c E rho x s H)
    (hR : liveRootAt p c E rho x s = some R) (hX : Block.Preceq X R) :
    Block.Preceq X H :=
  block_preceq_trans hX (pcsa_honestHead_extends_root E rho x s H R hs hH hR)
/-- The slot-zero HEAD is genesis, including when the node has other stored bodies. -/
theorem pcsa_honestHead_zero (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (H : Block)
    (hH : HonestHeadAt p c E rho x 0 H) : H = .genesis := by
  have hh := hH.2.2
  rw [pcsa_voteHeadAt_def] at hh
  obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hh
  change Block.genesis = H at he
  exact he.symm
end AvailableChain.PCSA.Run

end
