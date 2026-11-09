module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Family
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs

public section

/-! # Outage premises over an arbitrary SA family

One premise package owns the generic run vocabulary. The old package stays unchanged;
its conversion below reads only its existing hypotheses.
-/

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload Vote SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  (F : SAFamily sp (List (FG.Att sp.n)) ro A) (tr : RunTrace A.toAC)
  (H : Set (Fin sp.n))

/-- Actual acceptance relay and projected AC service within a horizon. -/
structure SleepyServiceBefore (ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  ac : SA.ServiceBefore H (tr.HonestBlocks H) b (F.proj tr.projAC)
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
      tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B → tr.BlockAcceptedBy y j (tr.time i) B

/-- The previous-label arming base in projected lock vocabulary. -/
def PrevBase (P : SA.Blk sp.n (List (FG.Att sp.n))) (j : Nat) (x : Fin sp.n) (c : Nat)
    (ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) : Prop :=
  Anc (tr.HonestBlocks H) P (tr.state x c).fg.F ∨
    ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc P L ∧
      (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ ((F.proj tr.projAC).state x (c + 1)).locks

/-- The cover arming base, independent of whether the record write is vetoed. -/
def CoverBase (P : SA.Blk sp.n (List (FG.Att sp.n))) (j : Nat) (x : Fin sp.n) (c : Nat)
    (ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) : Prop :=
  Anc (tr.HonestBlocks H) P (tr.state x c).fg.F ∨
    ∃ L f, ℓ.frame.Anc P L ∧
      (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ ((F.proj tr.projAC).state x (c + 1)).locks

/-- The outage assumptions over the actual run and its SA observations. -/
structure OutageLockPremises (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (sg : M → Fin sp.n) where
  b₀ : Time
  b₁ : Time
  a : Time
  z : Time
  P : SA.Blk sp.n (List (FG.Att sp.n))
  σ : Nat
  j₀ : Nat
  r : Nat
  A₀ : Set (Fin sp.n)
  W : Set (Fin sp.n)
  hrun : FamilyRun F proposer dg H sg tr
  hnc : Compose.NoCollRun dg tr
  hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀ ∧ b₀ < sp.ts (j₀ + 1 : Nat) + 2 * sp.Δ
  hr : b₁ ≤ sp.ts r + sp.Δ ∧ ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → r ≤ s
  hσ : σ + sp.k < j₀
  hrk : j₀ + 1 ≤ r ∧ r ≤ j₀ + sp.k
  hgap : b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ
  hb₀ : b₀ ≤ b₁
  hP : P ∈ tr.HonestBlocks H ∧
    (P.root = sp.genesisRoot ∨ OriginWithin F tr H P σ b₀)
  hpre : SleepyInvariantUpTo F tr H b₀
  hpreSvc : SleepyServiceBefore F tr H sp.Δ b₀
  hFB : ∀ s : Nat, (∃ x ∈ H, ∃ i, tr.IsCall x i ∧ sp.ts s + sp.Δ ≤ tr.time i) →
    tr.FaultBound H (sp.ts s + sp.Δ)
  hA₀ : A₀ ⊆ H
  hW : W ⊆ H ∧ Disjoint A₀ W
  hcohort : (Hᶜ ∪ W).ncard < A₀.ncard
  hawake : ∀ x ∈ H, ∀ t, a ≤ t → t ≤ z → tr.awake x t → x ∈ A₀ ∪ W
  hA₀awake : ∀ x ∈ A₀, ∀ t, a ≤ t → t ≤ z → tr.awake x t
  hA₀join : ∀ x ∈ A₀, ∀ k, tr.RestartAt x k → tr.time k ≤ z → tr.time k ≤ a + sp.Δ
  ha : a + sp.Δ ≤ sp.ts j₀
  hz : ∀ t, t ≤ sp.ts (j₀ + sp.k : Nat) + sp.Δ →
    (∃ x ∈ H, ∃ i, tr.IsCall x i ∧ t ≤ tr.time i) → t ≤ z
  lockPrev : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y ∈ H, ∃ i, tr.IsCall y i ∧ sp.ts j₀ + 2 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, SA.UpdateAt (F.proj tr.projAC) x c (j₀ - 1) ℓ ∧
      PrevBase F tr H P (j₀ - 1) x c ℓ
  lockCover : ∀ x ∈ A₀, P.root ≠ sp.genesisRoot →
    (∃ y ∈ H, ∃ i, tr.IsCall y i ∧ sp.ts j₀ + 6 * sp.Δ ≤ tr.time i) →
    ∃ c ℓ, SA.UpdateAt (F.proj tr.projAC) x c j₀ ℓ ∧
    (∀ k < c, ∀ ℓ', ¬ SA.UpdateAt (F.proj tr.projAC) x k j₀ ℓ') ∧
    (Compatible (tr.HonestBlocks H) (tr.state x c).fg.F P →
     (Anc (tr.HonestBlocks H) (tr.state x c).fg.F P → ℓ.frame.AncestorCandidate P) →
     (∀ y ∈ A₀, ∀ j e, SA.VoteAt (F.proj tr.projAC) y j e → e.msg.slot = j₀ + 1 → j < c →
        SA.VoteExtends (tr.HonestBlocks H) e.msg P) → CoverBase F tr H P j₀ x c ℓ)
  PG : ∀ w ∈ H, ∀ c m ℓ, SA.UpdateAt (F.proj tr.projAC) w c m ℓ → r ≤ m →
    ∀ x ∈ H, ∀ i e, SA.VoteAt (F.proj tr.projAC) x i e → e.msg.slot = m →
      e.msg ∈ ((F.proj tr.projAC).state w c).pool m

variable {F tr H} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

theorem prevBase_iff {P : SA.Blk sp.n (List (FG.Att sp.n))} {j c : Nat} {x : Fin sp.n} {ℓ} :
    PrevBase F tr H P j x c ℓ ↔
    Anc (tr.HonestBlocks H) P (tr.state x c).fg.F ∨
      ∃ L f, L ∈ ℓ.frame.tree ∧ ℓ.frame.Anc P L ∧
        (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ ((F.proj tr.projAC).state x (c + 1)).locks := by rfl

theorem coverBase_iff {P : SA.Blk sp.n (List (FG.Att sp.n))} {j c : Nat} {x : Fin sp.n} {ℓ} :
    CoverBase F tr H P j x c ℓ ↔
    Anc (tr.HonestBlocks H) P (tr.state x c).fg.F ∨
      ∃ L f, ℓ.frame.Anc P L ∧
        (⟨L.root, j, f, j + sp.k⟩ : SA.Lock) ∈ ((F.proj tr.projAC).state x (c + 1)).locks := by rfl

/-- Protection by a projected floor lock or the actual FG finalized cache. -/
def Prot (D : OutageLockPremises F tr H proposer dg sg) (x : Fin sp.n) (i j m : Nat) : Prop :=
  FloorAt F tr x i D.P j m ∨ Anc (tr.HonestBlocks H) D.P (tr.state x i).fg.F

theorem prot_iff {D : OutageLockPremises F tr H proposer dg sg} {x : Fin sp.n}
    {i j m : Nat} : Prot D x i j m ↔
    FloorAt F tr x i D.P j m ∨ Anc (tr.HonestBlocks H) D.P (tr.state x i).fg.F := by rfl

/-- The vote component of the outage invariant. -/
structure OutageVoteInv (D : OutageLockPremises F tr H proposer dg sg) (i : Nat) : Prop where
  votes : ∀ x ∈ H, ∀ k < i, ∀ e, SA.VoteAt (F.proj tr.projAC) x k e → D.σ < e.msg.slot →
    e.msg.slot ≤ D.j₀ + sp.k → (tr.time k ≤ D.b₀ ∨ x ∈ D.A₀) →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D.P
  late : ∀ x ∈ H, ∀ k < i, ∀ e, SA.VoteAt (F.proj tr.projAC) x k e →
    D.j₀ + sp.k < e.msg.slot → Compose.VoteCompat (tr.HonestBlocks H) e.msg D.P

/-- The entire outage cut invariant over the shared run vocabulary. -/
structure OutageLockInv (D : OutageLockPremises F tr H proposer dg sg) (i : Nat) : Prop
    extends OutageVoteInv D i where
  results : ∀ y ∈ H, ∀ k < i, ∀ m C CV, SA.ResultAt (F.proj tr.projAC) y k m C CV →
    (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocks H) C D.P
  locks : ∀ y ∈ H, ∀ k ≤ i, ∀ l ∈ ((F.proj tr.projAC).state y k).locks,
    ∃ L ∈ (tr.state y k).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L D.P
  sources : ∀ y ∈ H, ∀ k < i, ∀ ℓ C, ACToFGAt tr.projAC y k ℓ C →
    Compatible (tr.HonestBlocks H) C D.P
  caches : ∀ y ∈ H, ∀ k ≤ i, Compatible (tr.HonestBlocks H) (tr.state y k).fg.F D.P ∧
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.J D.P
  viable : ∀ y ∈ H, ∀ k ≤ i, D.P ∈ (Node.frame (tr.state y k)).tree →
    (Node.frame (tr.state y k)).AncestorCandidate D.P
  protPrev : ∀ x ∈ D.A₀, ∀ c ℓ, SA.UpdateAt (F.proj tr.projAC) x c (D.j₀ - 1) ℓ →
    PrevBase F tr H D.P (D.j₀ - 1) x c ℓ →
    ∀ k, c < k → k ≤ i → sp.slot (tr.time (k - 1)) ≤ D.j₀ - 1 + sp.k →
      Prot D x k (D.j₀ - 1) (D.j₀ - 1 + sp.k)
  protCover : ∀ x ∈ D.A₀, ∀ c ℓ, SA.UpdateAt (F.proj tr.projAC) x c D.j₀ ℓ →
    CoverBase F tr H D.P D.j₀ x c ℓ →
    ∀ k, c < k → k ≤ i → sp.slot (tr.time (k - 1)) ≤ D.j₀ + sp.k →
      Prot D x k D.j₀ (D.j₀ + sp.k)

/-- The restored-vote step remains an external premise of the lock induction. -/
def OutageS5StepAt (D : OutageLockPremises F tr H proposer dg sg) : Prop :=
  ∀ i, OutageLockInv D i → ∀ y ∈ H, ∀ e, SA.VoteAt (F.proj tr.projAC) y i e →
    D.j₀ + sp.k < e.msg.slot → Compose.VoteCompat (tr.HonestBlocks H) e.msg D.P

theorem outageS5StepAt_iff {D : OutageLockPremises F tr H proposer dg sg} :
    OutageS5StepAt D ↔ ∀ i, OutageLockInv D i → ∀ y ∈ H, ∀ e,
      SA.VoteAt (F.proj tr.projAC) y i e → D.j₀ + sp.k < e.msg.slot →
        Compose.VoteCompat (tr.HonestBlocks H) e.msg D.P := by rfl

end Consensus.Goldilocks.FamilySafety

namespace Consensus.Goldilocks.Compose

set_option backward.isDefEq.respectTransparency false

open SA (SAParams ReplayOrder Payload)

/-- The concrete outage assumptions supply their family instance with no new premise.
In particular `D.hnc`, already in the old package, discharges the collision premise.
-/
noncomputable def OutageLockPremises.family {sp : SAParams}
    {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (D : OutageLockPremises tr H proposer dg) :
    FamilySafety.OutageLockPremises (SA.goldilocksFamily sp _ ro) tr H proposer dg SA.Vote.val where
  b₀ := D.b₀
  b₁ := D.b₁
  a := D.a
  z := D.z
  P := D.P
  σ := D.σ
  j₀ := D.j₀
  r := D.r
  A₀ := D.A₀
  W := D.W
  hrun := D.hrun.family D.hnc
  hnc := D.hnc
  hj₀ := D.hj₀
  hr := D.hr
  hσ := D.hσ
  hrk := D.hrk
  hgap := D.hgap
  hb₀ := D.hb₀
  hP := ⟨D.hP.1, D.hP.2.imp_right FamilySafety.originWithin_goldilocks.mpr⟩
  hpre := (FamilySafety.sleepyInvariantUpTo_goldilocks D.hrun).mpr D.hpre
  hpreSvc := ⟨D.hpreSvc.deltaF, D.hpreSvc.ac, D.hpreSvc.relay⟩
  hFB := D.hFB
  hA₀ := D.hA₀
  hW := D.hW
  hcohort := D.hcohort
  hawake := D.hawake
  hA₀awake := D.hA₀awake
  hA₀join := D.hA₀join
  ha := D.ha
  hz := D.hz
  lockPrev := by
    intro x hx hg hh
    obtain ⟨c, ℓ, hu, hb⟩ := D.lockPrev x hx hg hh
    refine ⟨c, ℓ, hu, ?_⟩
    rw [prevBase_iff] at hb
    simpa only [FamilySafety.PrevBase, SA.goldilocksFamily,
      SA.goldilocksOperations, SA.SAOperations.toAC, id_eq,
      projAC_state D.hrun.toLocalRun (D.hA₀ hx)] using hb
  lockCover := by
    intro x hx hg hh
    obtain ⟨c, ℓ, hu, hfirst, hb⟩ := D.lockCover x hx hg hh
    refine ⟨c, ℓ, hu, hfirst, fun hF hva hv => ?_⟩
    have hb := hb hF hva hv
    rw [coverBase_iff] at hb
    simpa only [FamilySafety.CoverBase, SA.goldilocksFamily,
      SA.goldilocksOperations, SA.SAOperations.toAC, id_eq,
      projAC_state D.hrun.toLocalRun (D.hA₀ hx)] using hb
  PG := by
    intro w hw c m ℓ hu hr x hx i e hv hs
    have hp := D.PG w hw c m ℓ hu hr x hx i e hv hs
    simpa only [SA.goldilocksFamily, SA.goldilocksOperations, SA.SAOperations.toAC, id_eq,
      projAC_state D.hrun.toLocalRun hw] using hp

theorem OutageLockPremises.family_j₀ {sp : SAParams}
    {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (D : OutageLockPremises tr H proposer dg) : D.family.j₀ = D.j₀ := by rfl

theorem OutageLockPremises.family_r {sp : SAParams}
    {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (D : OutageLockPremises tr H proposer dg) : D.family.r = D.r := by rfl

theorem OutageLockPremises.family_P {sp : SAParams}
    {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    (D : OutageLockPremises tr H proposer dg) : D.family.P = D.P := by rfl

/-- The vote invariant has no extra family hypotheses at the concrete instance. -/
theorem OutageVoteInv.family_iff {sp : SAParams}
    {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {D : OutageLockPremises tr H proposer dg} {i : Nat} :
    FamilySafety.OutageVoteInv D.family i ↔ OutageVoteInv D i := by
  constructor
  · intro h
    exact ⟨h.votes, h.late⟩
  · intro h
    exact ⟨h.votes, h.late⟩

/-- Every component of the old cut invariant has the same family instance. -/
theorem OutageLockInv.family_iff {sp : SAParams}
    {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
    {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {D : OutageLockPremises tr H proposer dg} {i : Nat} :
    FamilySafety.OutageLockInv D.family i ↔ OutageLockInv D i := by
  have hs (y : Fin sp.n) (hy : y ∈ H) (k : Nat) :
      ((SA.goldilocksFamily sp _ ro).proj tr.projAC).state y k = (tr.state y k).ac :=
    projAC_state D.hrun.toLocalRun hy k
  have hp (x : Fin sp.n) (hx : x ∈ H) (k j m : Nat) :
      FamilySafety.Prot D.family x k j m ↔ Prot D x k j m := by
    simp only [FamilySafety.Prot, prot_iff, OutageLockPremises.family_P,
      FamilySafety.floorAt_goldilocks D.hrun hx]
  have hb (x : Fin sp.n) (hx : x ∈ D.A₀) (c : Nat) (j : Nat) (ℓ) :
      FamilySafety.PrevBase (SA.goldilocksFamily sp _ ro) tr H D.family.P j x c ℓ ↔
        PrevBase tr H D.P j x c ℓ := by
    simp only [FamilySafety.PrevBase, OutageLockPremises.family_P, prevBase_iff, hs x (D.hA₀ hx)]
  have hc (x : Fin sp.n) (hx : x ∈ D.A₀) (c : Nat) (j : Nat) (ℓ) :
      FamilySafety.CoverBase (SA.goldilocksFamily sp _ ro) tr H D.family.P j x c ℓ ↔
        CoverBase tr H D.P j x c ℓ := by
    simp only [FamilySafety.CoverBase, OutageLockPremises.family_P, coverBase_iff, hs x (D.hA₀ hx)]
  constructor
  · intro h
    refine ⟨OutageVoteInv.family_iff.mp h.toOutageVoteInv, h.results, ?_, h.sources,
      h.caches, h.viable, ?_, ?_⟩
    · intro y hy k hk l hl
      exact h.locks y hy k hk l ((hs y hy k).symm ▸ hl)
    · intro x hx c ℓ hu hbase k hck hk hslot
      exact (hp x (D.hA₀ hx) k _ _).mp
        (h.protPrev x hx c ℓ hu ((hb x hx c _ ℓ).mpr hbase) k hck hk hslot)
    · intro x hx c ℓ hu hbase k hck hk hslot
      exact (hp x (D.hA₀ hx) k _ _).mp
        (h.protCover x hx c ℓ hu ((hc x hx c _ ℓ).mpr hbase) k hck hk hslot)
  · intro h
    refine ⟨OutageVoteInv.family_iff.mpr h.toOutageVoteInv, h.results, ?_, h.sources,
      h.caches, h.viable, ?_, ?_⟩
    · intro y hy k hk l hl
      exact h.locks y hy k hk l (hs y hy k ▸ hl)
    · intro x hx c ℓ hu hbase k hck hk hslot
      exact (hp x (D.hA₀ hx) k _ _).mpr
        (h.protPrev x hx c ℓ hu ((hb x hx c _ ℓ).mp hbase) k hck hk hslot)
    · intro x hx c ℓ hu hbase k hck hk hslot
      exact (hp x (D.hA₀ hx) k _ _).mpr
        (h.protCover x hx c ℓ hu ((hc x hx c _ ℓ).mp hbase) k hck hk hslot)

end Consensus.Goldilocks.Compose

end
