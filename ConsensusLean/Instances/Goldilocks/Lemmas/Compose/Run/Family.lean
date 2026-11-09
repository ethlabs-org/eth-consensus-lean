module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Family
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.FamilySafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal

public section

namespace Consensus.Goldilocks

/-- Forget execution, retaining precisely the observational AC obligations. -/
theorem ACLocalRun.observation {P : Params} {FGP : Type} {A : ACInterface P FGP}
    {H : Set (Fin P.n)} {U : Set A.Blk} {tr : ACTrace A} (h : ACLocalRun A H U tr) :
    ACObsRun A H U tr :=
  ⟨h.coherent, h.init, h.frameLaw, h.time_nonneg, h.time_mono, h.awake_of_call,
    h.restart_of_sleep, h.restart_at_wake, h.sleep_of_restart⟩

/-- Goldilocks is a family run without exposing its execution law to consumers. -/
theorem GoldilocksRun.family {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} (h : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) :
    FamilyRun (SA.goldilocksFamily sp (List (FG.Att sp.n)) ro) proposer dg H
      SA.Vote.val tr where
  toLocalRun := h.toLocalRun
  genesis_root_ok := h.genesis_root_ok
  carried_vote_unforgeable := by
    intro y hy i B hB v hv hvH
    obtain ⟨j, hji, ℓ, hc, e, he, hev⟩ := h.carried_vote_unforgeable y hy i B hB v hv hvH
    exact ⟨j, hji, e, ⟨ℓ, Compose.projAC_callAt.mpr hc, he⟩, hev⟩
  observation :=
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer h hnc).localRun.observation

namespace FamilySafety

/-- A retained observation reads the actual caller's FG frame. -/
theorem frame_of_observation {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {S M : Type}
    {A : SA.SAOperations sp (List (FG.Att sp.n)) S M}
    {F : SA.SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {sg : M → Fin sp.n}
    (hr : FamilyRun F proposer dg H sg tr) {x : Fin sp.n} (hx : x ∈ H)
    {i : Nat} {ℓ} (hc : (F.proj tr.projAC).CallAt x i ℓ) :
    ℓ.frame = Node.frame (tr.state x i) := by
  obtain ⟨ℓ', hl', hf⟩ := F.frame tr.projAC i ℓ hc.2
  have hn : tr.projAC.node i = x := by simpa only [F.node] using hc.1
  exact hf.trans (hr.cutLaw x hx i _ (Compose.projAC_callAt.mp ⟨hn, hl'⟩)).1

set_option backward.isDefEq.respectTransparency false

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

/-- The concrete origin vocabulary is exactly the family instance. -/
theorem originWithin_goldilocks {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {b : Time} :
    OriginWithin (SA.goldilocksFamily sp _ ro) tr H C s b ↔ Compose.OriginWithin tr H C s b := by
  simp only [OriginWithin, SA.goldilocksFamily, SA.goldilocksOperations, SA.SAOperations.toAC,
    Compose.originWithin_iff]
  rfl

/-- The concrete chain vocabulary is exactly the family instance. -/
theorem onOriginChainWithin_goldilocks {B : SA.Blk sp.n (List (FG.Att sp.n))} {b : Time} :
    OnOriginChainWithin (SA.goldilocksFamily sp _ ro) tr H B b ↔
      Compose.OnOriginChainWithin tr H B b := by
  simp only [OnOriginChainWithin, Compose.onOriginChainWithin_iff, originWithin_goldilocks]

/-- Bridge the concrete prefix package without changing any original field's statement. -/
theorem sleepyInvariantUpTo_goldilocks {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hr : GoldilocksRun proposer dg H tr) {b : Time} :
    SleepyInvariantUpTo (SA.goldilocksFamily sp _ ro) tr H b ↔
      Compose.SleepyInvariantUpTo tr H b := by
  dsimp only [SA.goldilocksOperations, SA.SAOperations.toAC] at *
  have hp : (SA.goldilocksFamily sp _ ro).proj tr.projAC = tr.projAC := rfl
  have ho (C : SA.Blk sp.n (List (FG.Att sp.n))) (s : Nat) :
      OriginWithin (SA.goldilocksFamily sp _ ro) tr H C s b = Compose.OriginWithin tr H C s b :=
    propext originWithin_goldilocks
  have hc (B : SA.Blk sp.n (List (FG.Att sp.n))) :
      OnOriginChainWithin (SA.goldilocksFamily sp _ ro) tr H B b =
        Compose.OnOriginChainWithin tr H B b := propext onOriginChainWithin_goldilocks
  have hs (y : Fin sp.n) (hy : y ∈ H) (i : Nat) :
      ((SA.goldilocksFamily sp _ ro).proj tr.projAC).state y i = (tr.state y i).ac := by
    dsimp only [SA.goldilocksFamily, SA.goldilocksOperations, SA.SAOperations.toAC]
    exact Compose.projAC_state hr.toLocalRun hy i
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [ho] using h.origins_compatible
    · simpa only [ho, hp] using h.vote_extends
    · intro y hy i hi
      simpa only [hs y hy i, ho] using h.record y hy i hi
    · simpa only [hc] using h.caches
    · intro y hy i hi
      simpa only [hs y hy i, hc] using h.locks y hy i hi
    · intro y hy i hi ℓ C hs
      exact (hc C) ▸ h.sources y hy i hi ℓ C hs
    · simpa only [ho] using h.viable
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [ho] using h.origins_compatible
    · simpa only [ho, hp] using h.vote_extends
    · intro y hy i hi
      simpa only [hs y hy i, ho] using h.record y hy i hi
    · simpa only [hc] using h.caches
    · intro y hy i hi
      simpa only [hs y hy i, hc] using h.locks y hy i hi
    · intro y hy i hi ℓ C hs
      exact (hc C).symm ▸ h.sources y hy i hi ℓ C hs
    · simpa only [ho] using h.viable

/-- The lock-floor instance uses the actual run's AC projection state. -/
theorem floorAt_goldilocks {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    (hr : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {i j m : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} :
    FloorAt (SA.goldilocksFamily sp _ ro) tr y i B j m ↔ Compose.FloorAt tr y i B j m := by
  dsimp only [FloorAt, SA.goldilocksFamily, SA.goldilocksOperations, SA.SAOperations.toAC,
    Compose.FloorAt]
  change (∃ l ∈ (tr.projAC.state y i).locks, l.slot = j ∧ m ≤ l.expiry ∧
    ∃ B' ∈ (tr.state y i).fg.toFrame.tree, B'.root = l.block ∧
      (tr.state y i).fg.toFrame.Anc B B') ↔ _
  rw [Compose.projAC_state hr.toLocalRun hy]

end FamilySafety

end Consensus.Goldilocks

end
