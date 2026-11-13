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

private theorem honestVotes_const (σ : Nat) :
    Compose.Growing.honestVotes tr (fun _ => H) σ = honestVotes tr H σ := by
  ext v
  exact ⟨fun ⟨x, j, e', hx, h⟩ => ⟨x, hx, j, e', h⟩, fun ⟨x, hx, j, e', h⟩ => ⟨x, j, e', hx, h⟩⟩

private theorem excludedEntries_const (s : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) :
    Compose.Growing.excludedEntries tr (fun _ => H) s B = excludedEntries tr H s B := by
  ext E'
  simp only [Compose.Growing.excludedEntries, excludedEntries, RunTrace.honestBlocksAt_const]
  exact ⟨fun ⟨hc, y, j, hy, h⟩ => ⟨hc, y, hy, j, h⟩, fun ⟨hc, y, hy, j, h⟩ => ⟨hc, y, j, hy, h⟩⟩

/-- Static premises of C1.1 are growing-fault premises of the constant honest set. -/
private theorem persistPremises_of_static {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} {proposer : Nat → Fin sp.n} (hrun : GoldilocksRun proposer dg H tr)
    (h : PersistPremises tr H dg ΔF x i₀ s m B CV) :
    Compose.Growing.PersistPremises tr (fun _ => H) dg ΔF x i₀ s m B CV where
  writer_honest := h.writer_honest
  fastLock := h.fastLock
  writer_joined := h.writer_joined
  lt := h.lt
  sync := (RunTrace.syncRunAt_const tr).mpr h.sync
  carry := by rw [RunTrace.honestBlocksAt_const]; exact (SA.carry_const _ _).mpr h.carry
  halfCommittee := fun s' h1 h2 => by
    convert h.halfCommittee s' h1 h2 using 4
    ext x'
    exact ⟨fun ⟨hx, j, e', _, h⟩ => ⟨hx, j, e', h⟩, fun ⟨hx, j, e', h⟩ => ⟨hx, j, e', hx, h⟩⟩
  carryLater := fun s' h1 h2 => by
    rw [RunTrace.honestBlocksAt_const, honestVotes_const]
    exact (SA.carry_const _ _).mpr (h.carryLater s' h1 h2)
  faultBound := fun y i e hy hv h1 h2 => h.faultBound y hy i e hv h1 h2
  twoFaults := faulty_lt_half hrun h
  noColl := h.noColl
  clean :=
    { caches := fun y j hy hj => by
        rw [RunTrace.honestBlocksAt_const]; exact h.clean.caches y hy j hj
      fgAttCut := fun E' hE => by
        rw [excludedEntries_const] at hE
        exact h.clean.fgAttCut E' hE
      heightLead := fun y i ℓ e hy hc h1 h2 => by
        rw [RunTrace.honestBlocksAt_const]; exact h.clean.heightLead y hy i ℓ e hc h1 h2 }
  stock := h.stock

/-- A growing-fault conclusion of C1.1 for the constant honest set is the static conclusion. -/
private theorem persistAt_to_static {B : SA.Blk sp.n (List (FG.Att sp.n))} {s s' : Nat}
    (h : Compose.Growing.PersistAt tr (fun _ => H) B s s') : PersistAt tr H B s s' where
  cut := fun y hy =>
    { chains := fun i X hX h1 h2 => by
        have := (h.cut y).chains i X hy hX h1 h2
        simpa only [RunTrace.honestBlocksAt_const] using this
      caches := fun k hk => by
        have := (h.cut y).caches k (hk.elim (fun hk => Or.inl ⟨hy, hk⟩) fun hk => Or.inr ⟨hy, hk⟩)
        simpa only [RunTrace.honestBlocksAt_const] using this
      caches_own := fun k X hP ht hA => by
        have := (h.cut y).caches_own k X hy hP ht hA
        simpa only [RunTrace.honestBlocksAt_const] using this }
  viable := fun y hy i ℓ e hc hs => by
    have := h.viable y i ℓ e hy hc hs
    simpa only [RunTrace.honestBlocksAt_const] using this
  extends_ := fun y hy i e hv hs => by
    have := h.extends_ y i e hy hv hs
    simpa only [RunTrace.honestBlocksAt_const] using this

theorem honestFastConfirmationsPersist_of_growing
    (h : Compose.Growing.HonestFastConfirmationsPersist) : HonestFastConfirmationsPersist :=
  fun sp ro dg H tr ΔF x i₀ s m B CV proposer hrun hp s' h1 h2 =>
    persistAt_to_static (h sp ro dg (fun _ => H) tr ΔF x i₀ s m B CV proposer
      (Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (persistPremises_of_static hrun hp)
      s' h1 h2)

theorem recentSourceNextVote_of_growing (h : Compose.Growing.RecentSourceNextVote) :
    RecentSourceNextVote := by
  intro sp ro dg H tr ΔF x i₀ i j m ℓ B CV proposer hrun hp hto hs hj hm y hy k e hv he
  have := h sp ro dg (fun _ => H) tr ΔF x i₀ i j m ℓ B CV proposer
    (Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) (persistPremises_of_static hrun hp)
    hp.writer_honest hto hs hj hm y k e hy hv he
  simpa only [RunTrace.honestBlocksAt_const] using this

end Consensus.Goldilocks.Compose

end
