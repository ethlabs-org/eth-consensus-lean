module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks

public section

/-! # The constant honest set is the static run model

At `H := fun _ => H₀` the growing-fault run model is the static one: `Growing.LocalRun` is
`Node.LocalRun` (`Growing.LocalRun.const_iff`). -/

namespace Consensus.Goldilocks

variable {P : Params}

namespace Growing

variable {A : NodeAC P} {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- The run model with a constant honest set is `Node.LocalRun`. -/
theorem LocalRun.const_iff :
    Growing.LocalRun proposer dg (fun _ => H) sg tr ini ↔
      Node.LocalRun proposer dg H sg tr ini := by
  constructor
  · intro h
    exact
      { init := h.init
        grouped := fun y hy i c hc => h.grouped y i c hc hy
        cutLaw := fun y hy i c hc => h.cutLaw y i c hc hy
        wire := fun y hy j t e he => h.wire y j t e hy he
        proposerCredential := fun y hy j t B hB => h.proposerCredential y j t B hy hB
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        finite := h.finite
        phase_order := fun y hy y' hy' j j' t e e' => h.phase_order y y' j j' t e e' hy hy'
        tick_public := fun y hy j t => h.tick_public y j t hy
        tick_unique := fun y hy j j' t => h.tick_unique y j j' t hy
        tick_of_awake := fun y hy t => h.tick_of_awake y t hy
        awake_in_horizon := fun y hy t => h.awake_in_horizon y t hy
        awake_of_call := fun y hy i => h.awake_of_call y i hy
        restart_of_sleep := fun y hy i u => h.restart_of_sleep y i u hy
        restart_at_wake := fun y hy u v => h.restart_at_wake y u v hy
        sleep_of_restart := fun y hy i => h.sleep_of_restart y i hy
        block_unforgeable := fun y hy i B hB hp => h.block_unforgeable y i B hy hB hp
        att_unforgeable := fun y hy i a ha hv => h.att_unforgeable y i a hy ha hv
        msg_unforgeable := fun y hy i m hm hs => h.msg_unforgeable y i m hy hm hs }
  · intro h
    exact
      { antitone := fun _ _ _ => le_rfl
        init := h.init
        grouped := fun y i c hc hy => h.grouped y hy i c hc
        cutLaw := fun y i c hc hy => h.cutLaw y hy i c hc
        wire := fun y j t e hy he => h.wire y hy j t e he
        proposerCredential := fun y j t B hy hB => h.proposerCredential y hy j t B hB
        time_nonneg := h.time_nonneg
        time_mono := h.time_mono
        finite := h.finite
        phase_order := fun y y' j j' t e e' hy hy' => h.phase_order y hy y' hy' j j' t e e'
        tick_public := fun y j t hy => h.tick_public y hy j t
        tick_unique := fun y j j' t hy => h.tick_unique y hy j j' t
        tick_of_awake := fun y t hy => h.tick_of_awake y hy t
        awake_in_horizon := fun y t hy => h.awake_in_horizon y hy t
        awake_of_call := fun y i hy => h.awake_of_call y hy i
        restart_of_sleep := fun y i u hy => h.restart_of_sleep y hy i u
        restart_at_wake := fun y u v hy => h.restart_at_wake y hy u v
        sleep_of_restart := fun y i hy => h.sleep_of_restart y hy i
        block_unforgeable := fun y i B hy hB hp => h.block_unforgeable y hy i B hB hp
        att_unforgeable := fun y i a hy ha hv => h.att_unforgeable y hy i a ha hv
        msg_unforgeable := fun y i m hy hm hs => h.msg_unforgeable y hy i m hm hs }

end Growing

namespace Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

end Growing

end Consensus.Goldilocks

end
