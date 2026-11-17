module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest

public section

/-! # The growing-fault Compose run and Persist statements imply the static ones

At `H := fun _ => H₀` the run, the component contracts, the blocks held while honest, `Sync`, the
counts and the namers are the static ones (`Lemmas/Growing/Run/Const`), so each statement of
`Statements/Compose/Growing/{Run,Persist}` implies its static counterpart. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

theorem eventOrder_of_growing (h : Compose.Growing.EventOrder) : EventOrder := by
  intro P A dg H sg tr proposer hrun
  have r := h P A dg (fun _ => H) sg tr proposer (Goldilocks.Growing.LocalRun.const_iff.mpr hrun)
  exact
    { time_of_lt := r.time_of_lt
      phase := fun y hy y' hy' j j' t e e' => r.phase y y' j j' t e e' hy hy'
      tick_steps := fun y hy j t x => r.tick_steps y j t x hy
      block_before := fun y hy i B hB hp => r.block_before y i B hy hB hp
      att_before := fun y hy i a ha hv => r.att_before y i a hy ha hv
      msg_before := fun y hy i m hm hs => r.msg_before y i m hy hm hs
      finite := r.finite }

theorem acProjection_of_growing (h : Compose.Growing.ACProjection) : ACProjection := by
  intro P A dg H sg tr proposer ini hreq hpay hrun hnc
  have r := h P A dg (fun _ => H) sg tr proposer hreq hpay
    (Goldilocks.Growing.LocalRun.const_iff.mpr hrun) hnc
  rw [RunTrace.honestBlocksAt_const] at r
  exact Goldilocks.Growing.ACLocalRun.const_iff.mp r

theorem fgProjection_of_growing (h : Compose.Growing.FGProjection) : FGProjection := by
  intro P A dg H sg tr proposer hreq hg hrun hnc
  have r := h P A dg (fun _ => H) sg tr proposer hreq hg
    (Goldilocks.Growing.LocalRun.const_iff.mpr hrun) hnc
  rw [RunTrace.honestBlocksAt_const] at r
  exact Goldilocks.Growing.FGLocalRun.const_iff.mp r

theorem goldilocksACProjection_of_growing (h : Compose.Growing.GoldilocksACProjection) :
    GoldilocksACProjection := by
  intro sp ro dg H tr proposer hrun hnc
  have r := h sp ro dg (fun _ => H) tr proposer
    (Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) hnc
  rw [RunTrace.honestBlocksAt_const] at r
  exact SA.acRun_const.mp r

theorem groupStatesReachable_of_growing (h : Compose.Growing.GroupStatesReachable) :
    GroupStatesReachable :=
  fun P A dg H sg tr proposer hrun y hy j t e hg =>
    h P A dg (fun _ => H) sg tr proposer (Goldilocks.Growing.LocalRun.const_iff.mpr hrun) y j t e
      hy hg

theorem syncProjection_of_growing (h : Compose.Growing.SyncProjection) : SyncProjection := by
  intro P A dg H sg tr proposer ΔF a b hrun hsync
  have r := h P A dg (fun _ => H) sg tr proposer ΔF a b
    (Goldilocks.Growing.LocalRun.const_iff.mpr hrun) ((RunTrace.syncRunAt_const tr).mpr hsync)
  rw [RunTrace.honestBlocksAt_const] at r
  exact syncACAt_const.mp r

theorem joinedProjection_of_growing (h : Compose.Growing.JoinedProjection) :
    JoinedProjection := by
  intro sp ro dg H tr proposer hrun y hy t
  obtain ⟨h1, h2⟩ := h sp ro dg (fun _ => H) tr proposer
    (Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun)
  exact ⟨(h1 y t hy).1, (h1 y t hy).2, h2 t t⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)}

end Consensus.Goldilocks.Compose

end
