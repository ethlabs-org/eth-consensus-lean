module
public import ConsensusLeanTest.Goldilocks.AC.Base
public import ConsensusLean.Instances.Goldilocks.Proofs.Comparison.Main

@[expose] public section

/-! # The Tier A lock-memory premises at a non-parent write mode are satisfiable

With one validator, `Δ = 1`, `t_s = 4s`, `k = 2` (`Base`), at the write mode `slowOnly 2 false`
(no fast arm, no optimistic write), a trace in which the validator makes one `on_tick` call at
time `0` with the genesis frame meets every premise of each lock-memory claim:

* (a) `parent_lockMemory_witness`: the parent's stage at that mode (`ACLocalRunU` at the parent's
  unlock oracle at the mode, `parentOracleM`), with `TickOnce`;
* (a) `er_lockMemory_witness`: evidence release at that mode (`ACLocalRun` of
  `evidenceReleaseSAM`), with `TickOnce`;
* (a) `cert_lockMemory_witness`: the late-certificate rule at that mode (`ACLocalRun` of
  `certRecoverySAM`), with `TickOnce`;

and so the conclusions of `LockMemoryAC0`, `LockMemoryERAC0` and `LockMemoryCertAC0` hold on it.
The traces have one call, a tick at `0`, which is neither a vote time (`t_0 + Δ`) nor an update
time (`t_0 + 2Δ`): they show the premises satisfiable, not the bound reached. -/

namespace Consensus.Goldilocks.SA.Test.CostWitness

open Consensus.Goldilocks.Comparison EvidenceRelease LateCertificate

/-- The write mode: slow locks of width `2`, no fast arm, no optimistic write. -/
abbrev m1 : WriteMode := WriteMode.slowOnly 2 false

/-- The one-tick trace of an AC with the genesis frame: validator `0` makes one `on_tick` call at
time `0`, then the AC stutters; the validator is always awake. -/
noncomputable def oneTickOf (A : ACInterface sp1.toParams Unit) (Φ : A.Frm) : ACTrace A where
  init := fun _ => A.initial
  node := fun _ => v0
  time := fun _ => 0
  event := fun i => i
  pos := fun _ => 0
  label := fun i => if i = 0 then some ⟨.tick, Φ, (A.step v0 A.initial Φ 0 .tick).2⟩ else none
  post := fun _ => (A.step v0 A.initial Φ 0 .tick).1
  awake := fun _ _ => True

theorem oneTickOf_label {A : ACInterface sp1.toParams Unit} {Φ : A.Frm} {i : Nat} {ℓ}
    (h : (oneTickOf A Φ).label i = some ℓ) :
    i = 0 ∧ ℓ = ⟨.tick, Φ, (A.step v0 A.initial Φ 0 .tick).2⟩ := by
  simp only [oneTickOf] at h
  split_ifs at h with h0
  · exact ⟨h0, (Option.some.inj h).symm⟩

/-- The one-tick trace has one tick per node and time. -/
theorem tickOnce_oneTickOf (A : ACInterface sp1.toParams Unit) (Φ : A.Frm) :
    TickOnce (oneTickOf A Φ) Set.univ := by
  intro y _ i j ℓ ℓ' hc hc' _ _ _
  rw [(oneTickOf_label hc.2).1, (oneTickOf_label hc'.2).1]

/-- The one-tick trace with the genesis frame satisfies the AC trace contract, for every AC
whose genesis payload is the genesis frame's. -/
theorem localRun_oneTickOf (A : ACInterface sp1.toParams Unit) (Φ : A.Frm) {U : Set A.Blk}
    (hcoh : Coherent U) (hU : A.FrameIn U Φ) (hI : A.InitialFrame Φ) :
    ACLocalRun A Set.univ U (oneTickOf A Φ) where
  coherent := hcoh
  init := fun _ _ => rfl
  exec := fun i ℓ h _ => by
    obtain ⟨rfl, rfl⟩ := oneTickOf_label h
    rfl
  frameLaw := fun y _ i ℓ h => by
    obtain ⟨rfl, rfl⟩ := oneTickOf_label h.2
    exact Or.inl ⟨fun k _ hk => absurd hk (Nat.not_lt_zero k), Φ, hI, hU, hU, rfl⟩
  time_nonneg := fun _ => le_rfl
  time_mono := fun _ _ _ => le_rfl
  awake_of_call := fun _ _ _ _ _ => trivial
  restart_of_sleep := fun _ _ _ _ _ _ _ _ hu _ => absurd trivial hu
  restart_at_wake := fun _ _ _ _ _ _ hu _ => absurd trivial hu
  sleep_of_restart := fun y _ i ℓ h hr => by
    obtain ⟨rfl, rfl⟩ := oneTickOf_label h.2
    cases hr

/-- Evidence release at `slowOnly 2 false`. -/
noncomputable abbrev ER1 : ACInterface sp1.toParams Unit := evidenceReleaseSAM sp1 m1 Unit ro1

/-- The late-certificate rule at `slowOnly 2 false`. -/
noncomputable abbrev Cert1 : ACInterface sp1.toParams Unit := certRecoverySAM sp1 m1 Unit ro1

/-- (a) **Evidence release at `slowOnly 2 false`: the premises of `LockMemoryERAC0` hold** on the
one-tick trace, and so its conclusion. -/
theorem er_lockMemory_witness :
    ACLocalRun ER1 Set.univ ({g} : Set (Blk sp1.n Unit)) (oneTickOf ER1 Φ₀) ∧
      TickOnce (oneTickOf ER1 Φ₀) Set.univ ∧
      ∀ i, lockMemoryW sp1 ((oneTickOf ER1 Φ₀).state v0 i) ((oneTickOf ER1 Φ₀).time i) ≤
        (lockBound sp1 m1 : ℕ) := by
  have hl := localRun_oneTickOf ER1 Φ₀ (U := {g}) coherent_g ⟨frameOK_Φ₀, le_rfl⟩
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  have ht := tickOnce_oneTickOf ER1 Φ₀
  exact ⟨hl, ht, fun i => (lockMemoryERAC0 sp1 m1 Unit ro1 _ _ _ rfl hl ht v0 trivial i).1⟩

/-- (a) **The late-certificate rule at `slowOnly 2 false`: the premises of `LockMemoryCertAC0`
hold** on the one-tick trace, and so its conclusion. -/
theorem cert_lockMemory_witness :
    ACLocalRun Cert1 Set.univ ({g} : Set (Blk sp1.n Unit)) (oneTickOf Cert1 Φ₀) ∧
      TickOnce (oneTickOf Cert1 Φ₀) Set.univ ∧
      ∀ i, lockMemoryW sp1 ((oneTickOf Cert1 Φ₀).state v0 i).er ((oneTickOf Cert1 Φ₀).time i) ≤
        (lockBound sp1 m1 : ℕ) := by
  have hl := localRun_oneTickOf Cert1 Φ₀ (U := {g}) coherent_g ⟨frameOK_Φ₀, le_rfl⟩
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  have ht := tickOnce_oneTickOf Cert1 Φ₀
  exact ⟨hl, ht, fun i => (lockMemoryCertAC0 sp1 m1 Unit ro1 _ _ _ rfl hl ht v0 trivial i).1⟩

/-- The parent's tick at time `0` at mode `m1`, at the parent's unlock at the mode. -/
noncomputable abbrev tick1 : SAState sp1.n × List (Em sp1 Unit) :=
  stepWithM sp1 ro1 m1 v0 (parentUnlockM (ro := ro1) sp1 m1 (SAState.initial 0) Φ₀ 0 .tick)
    (SAState.initial 0) Φ₀ 0 .tick

/-- The parent's one-tick trace at mode `m1`: the step at the parent's unlock at the mode. -/
noncomputable def oneTickM : SATrace sp1 Unit ro1 where
  init := fun _ => SAState.initial 0
  node := fun _ => v0
  time := fun _ => 0
  event := fun i => i
  pos := fun _ => 0
  label := fun i => if i = 0 then some ⟨.tick, Φ₀, tick1.2⟩ else none
  post := fun _ => tick1.1
  awake := fun _ _ => True

theorem oneTickM_label {i : Nat} {ℓ} (h : oneTickM.label i = some ℓ) :
    i = 0 ∧ ℓ = ⟨.tick, Φ₀, tick1.2⟩ := by
  simp only [oneTickM] at h
  split_ifs at h with h0
  · exact ⟨h0, (Option.some.inj h).symm⟩

/-- The parent's one-tick trace at mode `m1` is a run of the parent's stage at the mode. -/
theorem localRunU_oneTickM :
    ACLocalRunU m1 (parentOracleM sp1 m1 oneTickM) Set.univ ({g} : Set (Blk sp1.n Unit))
      oneTickM where
  coherent := coherent_g
  init := fun _ _ => rfl
  exec := fun i ℓ h _ => by
    obtain ⟨rfl, rfl⟩ := oneTickM_label h
    rfl
  lawful := fun i ℓ h _ hΦ => by
    obtain ⟨rfl, rfl⟩ := oneTickM_label h
    exact unlockRel_unlock hΦ _ _ _ _
  frameLaw := fun y _ i ℓ h => by
    obtain ⟨rfl, rfl⟩ := oneTickM_label h.2
    exact Or.inl ⟨fun k _ hk => absurd hk (Nat.not_lt_zero k), Φ₀, ⟨rfl, rfl, rfl, rfl, rfl⟩,
      ⟨frameOK_Φ₀, le_rfl⟩, ⟨frameOK_Φ₀, le_rfl⟩, rfl⟩
  time_nonneg := fun _ => le_rfl
  time_mono := fun _ _ _ => le_rfl
  awake_of_call := fun _ _ _ _ _ => trivial
  restart_of_sleep := fun _ _ _ _ _ _ _ _ hu _ => absurd trivial hu
  restart_at_wake := fun _ _ _ _ _ _ hu _ => absurd trivial hu
  sleep_of_restart := fun y _ i ℓ h hr => by
    obtain ⟨rfl, rfl⟩ := oneTickM_label h.2
    cases hr

/-- (a) **The parent's stage at `slowOnly 2 false`: the premises of `LockMemoryAC0` hold** on the
one-tick trace, and so its conclusion. -/
theorem parent_lockMemory_witness :
    ACLocalRunU m1 (parentOracleM sp1 m1 oneTickM) Set.univ ({g} : Set (Blk sp1.n Unit))
        oneTickM ∧ TickOnce oneTickM Set.univ ∧
      ∀ i, lockMemory sp1 (oneTickM.state v0 i) (oneTickM.time i) ≤ (lockBound sp1 m1 : ℕ) := by
  have ht : TickOnce oneTickM Set.univ := by
    intro y _ i j ℓ ℓ' hc hc' _ _ _
    rw [(oneTickM_label hc.2).1, (oneTickM_label hc'.2).1]
  exact ⟨localRunU_oneTickM, ht, fun i =>
    (lockMemoryAC0 sp1 m1 Unit ro1 _ _ _ rfl localRunU_oneTickM ht v0 trivial i).1⟩

end Consensus.Goldilocks.SA.Test.CostWitness

end
