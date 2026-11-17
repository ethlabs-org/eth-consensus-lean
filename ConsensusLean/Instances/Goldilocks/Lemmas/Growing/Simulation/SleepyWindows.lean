module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Layer1Proofs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.GoldilocksBridge
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Sleepy window discharge at the canonical engine map

Local threshold and look-ahead fits are explicit: an arbitrary local-correctness
witness does not fix its data.
The population quorum is a separate consequence of the half-threshold population
regime, not of the committee count. No stored-clock read transport is asserted.
The run's own indexed point (`goldilocksPoint`) also carries the outage participation clauses
(`goldilocks_outageTransport`, with `goldilocksOutagePolicy`). At its data equations the local
supplier matches the endpoint contract's outage policy (`goldilocks_outageRecoveryBinding`).
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Transport both sleepy regime clauses through the canonical validator map.
The same point witnesses both windows; their look-aheads remain independent.
Catch-up domination belongs to `ClaimDeadlineFit`, not to this head. -/
def GoldilocksSleepyWindowSupply : Prop :=
  ∀ (S : Setup) (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (K : Contract ProgressReq)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (goldilocksRunMap S rho hn hv).signer),
    C.θ = K.params.θ → 0 ≤ C.θ → C.θ ≤ 1 →
    C.look = (Sys (goldilocks S) V).aheadDur K ⟨E, rho⟩ →
    C.committeeLook = (Sys (goldilocks S) V).committeeAheadDur K ⟨E, rho⟩ →
    SleepyWindowSupply (goldilocksRunMap S rho hn hv) K C

/-- The population clause at threshold at least one half supplies the shared FG
quorum at each bounded time. Committee participation alone does not suffice. -/
def GoldilocksPopulationQuorumSupply : Prop :=
  ∀ (S : Setup) (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (K : Contract ProgressReq),
    (1 / 2 : ℚ) ≤ K.params.θ →
    PopulationQuorumSupply (goldilocksRunMap S rho hn hv) K

/-- The sleepy window supply, without exposing the definition's body. -/
theorem goldilocksSleepyWindowSupply_iff :
    GoldilocksSleepyWindowSupply (V := V) ↔
      ∀ (S : Setup) (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E)
        (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (K : Contract ProgressReq)
        (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
          (goldilocksRunMap S rho hn hv).signer),
        C.θ = K.params.θ → 0 ≤ C.θ → C.θ ≤ 1 →
        C.look = (Sys (goldilocks S) V).aheadDur K ⟨E, rho⟩ →
        C.committeeLook = (Sys (goldilocks S) V).committeeAheadDur K ⟨E, rho⟩ →
        SleepyWindowSupply (goldilocksRunMap S rho hn hv) K C := by
  exact Iff.rfl

/-- The population quorum supply, without exposing the definition's body. -/
theorem goldilocksPopulationQuorumSupply_iff :
    GoldilocksPopulationQuorumSupply (V := V) ↔
      ∀ (S : Setup) (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E)
        (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (K : Contract ProgressReq),
        (1 / 2 : ℚ) ≤ K.params.θ →
        PopulationQuorumSupply (goldilocksRunMap S rho hn hv) K := by
  exact Iff.rfl

/-- The canonical run committee is constant from a slot start to its vote time.
This is an instance obligation, not a law of arbitrary committee functions. -/
def GoldilocksSlotConstancy : Prop :=
  ∀ (S : Setup) (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (s : Int),
    runCommittee S rho hn ((S.params (pubOf E) hn).ts s + (S.params (pubOf E) hn).Δ) =
      runCommittee S rho hn ((S.params (pubOf E) hn).ts s)

omit [DecidableEq V] in
/-- Slot selection is unchanged at the vote offset, including negative slot indices. -/
theorem goldilocks_slot_constancy : GoldilocksSlotConstancy (V := V) := by
  intro S E rho hn s
  let sp := S.params (pubOf E) hn
  change runCommittee S rho hn (sp.ts s + sp.Δ) = runCommittee S rho hn (sp.ts s)
  have hd : 0 < sp.Δ := sp.toParams.hΔ
  have hs : sp.slot (sp.ts s + sp.Δ) = sp.slot (sp.ts s) := by
    by_cases h : 0 ≤ s
    · lift s to Nat using h
      rw [SA.slot_of_mem sp s (by linarith) (by
        simp only [SA.SAParams.ts]
        push_cast
        linarith), SA.slot_of_mem sp s le_rfl (by
        simp only [SA.SAParams.ts]
        push_cast
        linarith)]
    · have hn : s ≤ -1 := by omega
      have ht : sp.ts s + sp.Δ < 0 := by
        have := mul_le_mul_of_nonneg_left hn (show 0 ≤ 4 * sp.Δ by positivity)
        simp only [SA.SAParams.ts]
        linarith
      rw [SA.slot_of_neg ht, SA.slot_of_neg (by linarith : sp.ts s < 0)]
  exact runCommittee_eq_of_slot_eq S rho hn hs

/-- The population sleepy budget at threshold at least one half gives an FG majority. -/
theorem goldilocks_population_quorum_supply : GoldilocksPopulationQuorumSupply (V := V) := by
  intro S E rho hn hv K hθ _ hs t ht htb
  classical
  have h := hs.2.1 t ht htb
  change (rho.point.retain (rho.point.lookAhead _ t)).ReadyAbove K.params.θ _ t at h
  let q := rho.point.retain (rho.point.lookAhead ((Sys (goldilocks S) V).aheadDur K ⟨E, rho⟩) t)
  let c := (Sys (goldilocks S) V).cDur K ⟨E, rho⟩
  change K.params.θ * ((q.readyAt c t).card + q.faultCount t : ℚ) < (q.readyAt c t).card at h
  have hhalf := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hθ
    (show (0 : ℚ) ≤ (q.readyAt c t).card + q.faultCount t by positivity)) h
  have hlt : (q.faultyAt t).card < (q.readyAt c t).card := by
    unfold EnvPoint.faultCount at hhalf
    exact_mod_cast (show ((q.faultyAt t).card : ℚ) < (q.readyAt c t).card by linarith)
  have hdis : Disjoint (q.readyAt c t) (q.faultyAt t) := by
    apply Finset.disjoint_left.mpr
    intro v hv hf
    exact (Finset.mem_filter.mp hv).2.1 hf
  have hcard := Finset.card_le_univ (s := q.readyAt c t ∪ q.faultyAt t)
  rw [Finset.card_union_of_disjoint hdis] at hcard
  have htime : t ≤ rho.point.lookAhead ((Sys (goldilocks S) V).aheadDur K ⟨E, rho⟩) t := by
    apply le_min _ htb
    have : 0 ≤ (Sys (goldilocks S) V).aheadDur K ⟨E, rho⟩ := by
      change 0 ≤ (K.params.ahead : Time) * E.ΔAC
      exact mul_nonneg (Int.natCast_nonneg _) E.ΔAC_pos.le
    linarith
  have hfc : (rho.faultyAt t).card ≤ (q.faultyAt t).card :=
    Finset.card_le_card (rho.faultyAt_mono htime)
  have hf : (honestKeysAt S rho t)ᶜ.ncard = (rho.faultyAt t).card := by
    have heq : (honestKeysAt S rho t)ᶜ = rho.key ⁻¹' (↑(rho.faultyAt t) : Set V) := by
      ext k
      simp [mem_honestKeysAt_iff, min_eq_left htb]
    rw [heq, Set.ncard_preimage_of_injective_subset_range rho.key.injective
      (by simp [rho.key.surjective.range_eq]), Set.ncard_coe_finset]
  rw [goldilocksRunMap_honest, hf]
  change 2 * (rho.faultyAt t).card < Fintype.card V
  omega

/-- The run's environment point on the validator indices, with the honest sets, awake times
and horizon of the canonical run map. -/
noncomputable def goldilocksPoint {O : OutputSchema} {F₀ : Model.ProtocolFamily O} {E : Env V}
    (rho : Model.Run F₀ E) :
    EnvPoint (Fin (Fintype.card V)) where
  env := {
    ΔAC := E.ΔAC
    ΔAC_pos := E.ΔAC_pos
    ΔFG := E.ΔFG
    ΔFG_pos := E.ΔFG_pos
    awake := fun y t => decide (E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon) }
  faultyAt := fun t => (rho.faultyAt (min t rho.horizon)).preimage rho.key rho.key.injective.injOn
  faultyAt_mono := fun t u htu y hy => by
    simp only [Finset.mem_preimage] at hy ⊢
    exact rho.faultyAt_mono (min_le_min_right _ htu) hy
  horizon := rho.horizon
  submit := fun y t => rho.point.submit (rho.key y) t

section Point

variable {S : Setup} {E : Env V} {rho : Model.Run (compiled (goldilocks S)) E}

omit [DecidableEq V] in
theorem goldilocksPoint_horizon : (goldilocksPoint rho).horizon = rho.horizon := by rfl

/-- The point is bound to the canonical run map. -/
theorem goldilocksPoint_binding (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) :
    RunPointBinding (goldilocksRunMap S rho hn hv).trace (goldilocksRunMap S rho hn hv).honest
      (goldilocksPoint rho) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro y t
    simp only [goldilocksRunMap_honest, mem_honestKeysAt_iff, EnvPoint.HonestAt,
      goldilocksPoint, Finset.mem_preimage]
  · intro y t
    simpa only [goldilocksPoint, decide_eq_true_eq, goldilocksRunMap_validator] using
      (goldilocksRunMap S rho hn hv).awake_eq y t
  · exact (goldilocksRunMap S rho hn hv).horizon_eq

omit [DecidableEq V] in
/-- Ready validators map to the run's ready validators at bounded times. -/
theorem goldilocksPoint_readyAt (c t d : Time) (htb : t ≤ rho.horizon) :
    (((goldilocksPoint rho).retain d).readyAt c t).map rho.key.toEmbedding =
      (rho.point.retain (min d rho.horizon)).readyAt c t := by
  classical
  ext v
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyh, hyw⟩ := (Finset.mem_filter.mp hy).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [EnvPoint.HonestAt, EnvPoint.retain, goldilocksPoint, Model.Run.point,
        Finset.mem_preimage] using hyh
    · intro u hu hut
      have := hyw u hu hut
      exact (of_decide_eq_true this).1
  · intro hv
    refine ⟨rho.key.symm v, ?_, rho.key.apply_symm_apply v⟩
    obtain ⟨hvh, hvw⟩ := (Finset.mem_filter.mp hv).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [EnvPoint.HonestAt, EnvPoint.retain, goldilocksPoint, Model.Run.point,
        Finset.mem_preimage, Equiv.apply_symm_apply] using hvh
    · intro u hu hut
      apply decide_eq_true_eq.mpr
      refine ⟨?_, (le_max_left _ _).trans hu, hut.trans htb⟩
      simpa only [EnvPoint.retain, Model.Run.point, Equiv.apply_symm_apply] using hvw u hu hut

omit [DecidableEq V] in
/-- Faulty validators map to the run's faulty validators at the clamped retention time. -/
theorem goldilocksPoint_faultyAt (d t : Time) :
    (((goldilocksPoint rho).retain d).faultyAt t).map rho.key.toEmbedding =
      rho.faultyAt (min d rho.horizon) := by
  ext v
  simp only [Finset.mem_map, Equiv.toEmbedding_apply, EnvPoint.retain, goldilocksPoint,
    Finset.mem_preimage]
  exact ⟨fun ⟨y, hy, he⟩ => he ▸ hy,
    fun hv => ⟨rho.key.symm v, by simpa using hv, rho.key.apply_symm_apply v⟩⟩

omit [DecidableEq V] in
/-- Validators honest and awake in a window map to the run's, inside `[0, horizon]`. -/
theorem goldilocksPoint_awakeIn (d a b : Time) (ha : 0 ≤ a) (hb : b ≤ rho.horizon) :
    (((goldilocksPoint rho).retain d).awakeIn a b).map rho.key.toEmbedding =
      (rho.point.retain (min d rho.horizon)).awakeIn a b := by
  classical
  ext v
  simp only [Finset.mem_map, EnvPoint.awakeIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨u, hau, hub, hh, hw⟩, rfl⟩
    refine ⟨u, hau, hub, ?_, (of_decide_eq_true hw).1⟩
    simpa only [EnvPoint.HonestAt, EnvPoint.retain, goldilocksPoint, Model.Run.point,
      Finset.mem_preimage, Equiv.toEmbedding_apply] using hh
  · rintro ⟨u, hau, hub, hh, hw⟩
    refine ⟨rho.key.symm v, ⟨u, hau, hub, ?_, decide_eq_true_eq.mpr
      ⟨by rw [Equiv.apply_symm_apply]; exact hw, ha.trans hau, hub.trans hb⟩⟩,
      rho.key.apply_symm_apply v⟩
    simpa only [EnvPoint.HonestAt, EnvPoint.retain, goldilocksPoint, Model.Run.point,
      Finset.mem_preimage, Equiv.apply_symm_apply] using hh

/-- The mapped committee is the run's selected committee at nonnegative times. -/
theorem goldilocksPoint_committee (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (t : Time) (ht : 0 ≤ t) :
    ((goldilocksRunMap S rho hn hv).committee t).map rho.key.toEmbedding =
      (Model.sysExternal _ (compiled (goldilocks S)) V).selected E (rho.key, rho.sel) t := by
  ext v
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  have hc := (goldilocksRunMap S rho hn hv).committee_eq
  simp only [goldilocksRunMap_validator] at hc
  exact ⟨fun ⟨y, hy, he⟩ => he ▸ (hc y t ht).mp hy,
    fun hmem => ⟨rho.key.symm v, (hc _ t ht).mpr (by simpa using hmem),
      rho.key.apply_symm_apply v⟩⟩

end Point

/-- One canonical indexed environment transports both independent sleepy windows. -/
theorem goldilocks_sleepy_window_supply : GoldilocksSleepyWindowSupply (V := V) := by
  intro S E rho hn hv K C hθ h0 h1 hlook hcommitteeLook
  classical
  let p := goldilocksPoint rho
  refine ⟨p, goldilocksPoint_binding hn hv, rfl, hθ, h0, h1, hlook, hcommitteeLook, ?_⟩
  intro _ hs
  constructor
  · intro t ht htb
    have h := hs.2.1 t ht htb
    change (rho.point.retain (rho.point.lookAhead _ t)).ReadyAbove K.params.θ _ t at h
    change C.θ * (((p.retain (p.lookAhead C.look t)).readyAt _ t).card +
      ((p.retain (p.lookAhead C.look t)).faultyAt t).card : ℚ) <
      ((p.retain (p.lookAhead C.look t)).readyAt _ t).card
    rw [← Finset.card_map rho.key.toEmbedding, goldilocksPoint_readyAt _ _ _ htb,
      ← Finset.card_map (s := (p.retain _).faultyAt t) rho.key.toEmbedding,
      goldilocksPoint_faultyAt]
    simpa only [p, goldilocksPoint, EnvPoint.lookAhead, min_assoc, min_self, hθ, hlook,
      EnvPoint.ReadyAbove, EnvPoint.faultCount, EnvPoint.retain, Model.Run.point] using h
  · intro t ht htb hne
    have hne' := hne.map (f := rho.key.toEmbedding)
    rw [goldilocksPoint_committee hn hv t ht] at hne'
    have h := hs.2.2 t ht htb hne'
    change K.params.θ * (((rho.point.retain (rho.point.lookAhead _ t)).readyAt _ t ∩
      (Model.sysExternal _ (compiled (goldilocks S)) V).selected E (rho.key, rho.sel) t).card +
      ((rho.point.retain (rho.point.lookAhead _ t)).faultyAt t ∩
      (Model.sysExternal _ (compiled (goldilocks S)) V).selected
        E (rho.key, rho.sel) t).card : Nat) <
      (((rho.point.retain (rho.point.lookAhead _ t)).readyAt _ t ∩
      (Model.sysExternal _ (compiled (goldilocks S)) V).selected
        E (rho.key, rho.sel) t).card : ℚ) at h
    simp only [show (0 : Time) ≤ 0 from le_refl _, ite_true]
    rw [← Finset.card_map rho.key.toEmbedding, Finset.map_inter,
      goldilocksPoint_readyAt _ _ _ htb, goldilocksPoint_committee hn hv t ht,
      ← Finset.card_map (s := (p.retain _).faultyAt t ∩ _) rho.key.toEmbedding,
      Finset.map_inter, goldilocksPoint_faultyAt, goldilocksPoint_committee hn hv t ht]
    simpa only [p, goldilocksPoint, EnvPoint.lookAhead, min_assoc, min_self, hθ,
      hcommitteeLook, EnvPoint.retain, Model.Run.point] using h

/-- The outage policy of the canonical run map: the run's own indexed point. -/
noncomputable def goldilocksOutagePolicy (S : Setup) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) : OutagePolicy (goldilocksRunMap S rho hn hv) :=
  ⟨goldilocksPoint rho, goldilocksPoint_binding hn hv, goldilocksPoint_horizon⟩

/-- The canonical outage policy retains the run's own indexed point. -/
theorem goldilocksOutagePolicy_point (S : Setup) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) :
    (goldilocksOutagePolicy S rho hn hv).point = goldilocksPoint rho := by rfl

/-- Outage participation transports to the canonical run map's own point and committee. -/
theorem goldilocks_outageTransport (S : Setup) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (K : Contract ProgressReq) :
    OutageTransport (goldilocksRunMap S rho hn hv) (goldilocksOutagePolicy S rho hn hv) K where
  participation _ T b₀ b₁ h := by
    classical
    obtain ⟨-, -, hp, hc⟩ := h
    change rho.point.EtaSleepyOn K.params.θ ((K.params.η : Time) * E.ΔAC)
      (max ((Sys (goldilocks S) V).cDur K ⟨E, rho⟩) ((K.params.η : Time) * E.ΔAC - 1))
      ((Sys (goldilocks S) V).aheadDur K ⟨E, rho⟩) 0 rho.horizon at hp
    change ∀ δ : Time, 0 ≤ δ → δ ≤ (K.params.η : Time) * E.ΔAC →
      rho.point.CommitteeSleepyOn
        (fun t => (Model.sysExternal _ (compiled (goldilocks S)) V).selected E
          (rho.key, rho.sel) (max 0 (t - δ)))
        K.params.θ ((K.params.η : Time) * E.ΔAC)
        (max ((Sys (goldilocks S) V).cDur K ⟨E, rho⟩) ((K.params.η : Time) * E.ΔAC - 1))
        ((Sys (goldilocks S) V).committeeAheadDur K ⟨E, rho⟩) 0 rho.horizon at hc
    let p := goldilocksPoint rho
    change p.EtaSleepyOn _ _ _ _ 0 rho.horizon ∧ ∀ δ, 0 ≤ δ → δ ≤ _ →
      p.CommitteeSleepyOn _ _ _ _ _ 0 rho.horizon
    constructor
    · intro t ht htb
      have h := hp t ht htb
      change (rho.point.retain (rho.point.lookAhead _ t)).EtaReadyAbove _ _ _ t at h
      unfold EnvPoint.EtaReadyAbove at h ⊢
      split_ifs at h ⊢
      · simp only [EnvPoint.ReadyAbove, EnvPoint.faultCount]
        rw [← Finset.card_map rho.key.toEmbedding, goldilocksPoint_readyAt _ _ _ htb,
          ← Finset.card_map (s := (p.retain _).faultyAt t) rho.key.toEmbedding,
          goldilocksPoint_faultyAt]
        simpa only [p, goldilocksPoint, EnvPoint.lookAhead, min_assoc, min_self,
          EnvPoint.ReadyAbove, EnvPoint.faultCount, EnvPoint.retain, Model.Run.point] using h
      · rw [← Finset.card_map rho.key.toEmbedding, Finset.map_union, Finset.map_union,
          goldilocksPoint_readyAt _ _ _ htb,
          goldilocksPoint_awakeIn _ _ _ (le_max_left _ _) htb, goldilocksPoint_faultyAt,
          ← Finset.card_map (s := (p.retain _).readyAt _ t) rho.key.toEmbedding,
          goldilocksPoint_readyAt _ _ _ htb]
        simpa only [p, goldilocksPoint, EnvPoint.lookAhead, min_assoc, min_self,
          EnvPoint.retain, Model.Run.point] using h
    · intro δ hδ hδη t ht htb hne
      have hm : 0 ≤ max 0 (t - δ) := le_max_left _ _
      have hne' := hne.map (f := rho.key.toEmbedding)
      rw [goldilocksPoint_committee hn hv _ hm] at hne'
      have h := hc δ hδ hδη t ht htb hne'
      dsimp only at h ⊢
      split_ifs at h ⊢
      · rw [← Finset.card_map rho.key.toEmbedding, Finset.map_inter,
          goldilocksPoint_readyAt _ _ _ htb, goldilocksPoint_committee hn hv _ hm,
          ← Finset.card_map (s := (p.retain _).faultyAt t ∩ _) rho.key.toEmbedding,
          Finset.map_inter, goldilocksPoint_faultyAt, goldilocksPoint_committee hn hv _ hm]
        simpa only [p, goldilocksPoint, EnvPoint.lookAhead, min_assoc, min_self,
          EnvPoint.retain, Model.Run.point] using h
      · rw [← Finset.card_map rho.key.toEmbedding, Finset.map_inter, Finset.map_union,
          Finset.map_union, goldilocksPoint_readyAt _ _ _ htb,
          goldilocksPoint_awakeIn _ _ _ (le_max_left _ _) htb, goldilocksPoint_faultyAt,
          goldilocksPoint_committee hn hv _ hm,
          ← Finset.card_map (s := (p.retain _).readyAt _ t ∩ _) rho.key.toEmbedding,
          Finset.map_inter, goldilocksPoint_readyAt _ _ _ htb,
          goldilocksPoint_committee hn hv _ hm]
        simpa only [p, goldilocksPoint, EnvPoint.lookAhead, min_assoc, min_self,
          EnvPoint.retain, Model.Run.point] using h

/-- Signer transport preserves the local service, durations, outage policy and healing drain. -/
theorem local_data_cast {P : Params} {A : NodeAC P} {sg sg' : A.Msg → Fin P.n}
    (h : sg = sg') (C : ACCorrectLocal A sg) :
    (h ▸ C).served = C.served ∧ (h ▸ C).look = C.look ∧
      (h ▸ C).catchUp = C.catchUp ∧ (h ▸ C).latency = C.latency ∧
      (h ▸ C).margin = C.margin ∧ (h ▸ C).hold = C.hold ∧
      (h ▸ C).run.Run = C.run.Run ∧ (h ▸ C).committeeLook = C.committeeLook ∧
      (h ▸ C).θ = C.θ ∧ (h ▸ C).recovery = C.recovery ∧
      (h ▸ C).outageEta = C.outageEta ∧ (h ▸ C).outageLag = C.outageLag ∧
      (h ▸ C).outageBudget = C.outageBudget ∧ (h ▸ C).healing.drain = C.healing.drain := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At the local data equations, the fixed local outage policy matches the endpoint contract:
catch-up `18Δ + 1 ≤ 19Δ`, and equal recovery, threshold, look-aheads, look-back, arming lag and
budget, for every run map of the binding's parameters. -/
theorem goldilocks_outageRecoveryBinding (S : Setup) (A : ContractAssumptions S) {E : Env V}
    {rho : Model.Run (compiled (goldilocks S)) E} (hn : 1 ≤ Fintype.card V)
    {payload : Blk (S.params (pubOf E) hn) → Set Nat}
    (M : RunMap (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) rho payload)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (fun v => v.val))
    (hC : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C)
    (hsg : (fun v => v.val) = M.signer) :
    OutageRecoveryBinding M (goldilocksContract A (contract_coefficients S A)) (hsg ▸ C) := by
  obtain ⟨-, hθ, hc, hl, hcl, -, -, -, hr, hη, hlag, hb, -, -⟩ := hC
  obtain ⟨-, el, ec, -, -, -, -, ecl, eθ, er, eη, elag, eb, -⟩ := local_data_cast hsg C
  have hΔ : (S.params (pubOf E) hn).Δ = E.ΔAC := rfl
  have h1 : (1 : Time) ≤ E.ΔAC := E.ΔAC_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change _ = (9 : Time) * E.ΔAC
    rw [er, hr, hΔ]
  · rw [eθ, hθ]
    rfl
  · change _ + 1 ≤ ((19 : Nat) : Time) * E.ΔAC
    rw [ec, hc, hΔ]
    push_cast
    linarith
  · change _ = ((5 : Nat) : Time) * E.ΔAC
    rw [el, hl, hΔ]
    norm_num
  · change _ = ((5 : Nat) : Time) * E.ΔAC
    rw [ecl, hcl, hΔ]
    norm_num
  · rw [eη, hη]
  · rw [elag, hlag]
    rfl
  · rw [eb, hb]
    rfl

end Consensus.Goldilocks.Simulation

namespace Consensus.Goldilocks.Generic.SleepyLayer1

open AsChainShape Simulation Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : Setup) {E : Env V}
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
  (hv : rho.ExecutionValid)

/-- The canonical map supplies the slot-constant committee and the horizon binding;
the local data equations supply the numerical fits, not an existential supplier. -/
private theorem canonical_window_premises
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (fun v => v.val))
    (hdata : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C)
    {p : EnvPoint (Fin (Fintype.card V))} {ΔF b : Time}
    (hb : b ≤ rho.horizon)
    (hbind : RunPointBinding (goldilocksRunMap S rho hn hv).trace
      (goldilocksRunMap S rho hn hv).honest p)
    {C' : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (goldilocksRunMap S rho hn hv).signer}
    (hserved : C'.served = fun tr y j τ m => SA.FamilyFacts.MessageServedBefore tr.projAC y j τ m)
    (hpre : SleepyServicePrefix C' (goldilocksRunMap S rho hn hv).trace
      (goldilocksRunMap S rho hn hv).honest ΔF C.look b)
    (hK : CommitteeWindow C p (goldilocksRunMap S rho hn hv).committee b)
    (hpop : PopulationWindow C p b) :
    GoldilocksWindowPremises (goldilocksRunMap S rho hn hv).trace
      (goldilocksRunMap S rho hn hv).honest p
      (goldilocksRunMap S rho hn hv).committee
      C.catchUp C.look C.committeeLook ΔF b := by
  obtain ⟨_, hθ, hc, hl, hcl, _⟩ := hdata
  rw [goldilocksWindowPremises_iff]
  rw [goldilocksRunMap_trace, goldilocksRunMap_honest] at hpre
  obtain ⟨hb0, hsvc⟩ := sleepyServiceBefore_of_prefix
    (Simulation.simTraceAt_goldilocksRun S rho hn hv) hserved hpre
  refine ⟨hbind, ?_, ?_, hl.ge, hcl.ge, ?_, hb0, ?_, ?_, ?_⟩
  · exact (hbind.2.2.2 b).mp ((goldilocksRunMap S rho hn hv).horizon_eq b |>.mpr hb)
  · rw [hc]
    rfl
  · intro s
    rw [goldilocksRunMap_committee]
    exact goldilocks_slot_constancy S E rho hn s
  · rw [goldilocksRunMap_trace, goldilocksRunMap_honest]
    exact hsvc
  · simpa only [CommitteeWindow, hθ] using hK
  · simpa only [PopulationWindow, hθ] using hpop

/-- The fixed concrete event proof supplies the generic map-bound event-safety row. -/
theorem goldilocksRunMap_event_safety
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (fun v => v.val))
    (hdata : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C) :
    EventSafety (goldilocksRunMap S rho hn hv)
      ((goldilocksRunMap_signer S rho hn hv).symm ▸ C)
      (goldilocksEvents (S.params (pubOf E) hn) (S.ro _)) := by
  intro ΔF b p hb hrun hnc hbind hpre hK hpop hframes B B' hB hB'
  obtain ⟨hsv, hl, hc, -, -, -, hr, hcl, hθ, -⟩ :=
    Simulation.local_data_cast (goldilocksRunMap_signer S rho hn hv).symm C
  rw [hr] at hrun
  rw [hl] at hpre
  simp only [CommitteeWindow, PopulationWindow, hl, hc, hcl, hθ] at hK hpop
  have hrun' : (goldilocksRunInterface (S.params (pubOf E) hn) (S.ro _)).Run
      (goldilocksRunMap S rho hn hv).committee (goldilocksRunMap S rho hn hv).proposer
      (goldilocksRunMap S rho hn hv).digest (goldilocksRunMap S rho hn hv).honest
      (goldilocksRunMap S rho hn hv).trace := by
    rw [hdata.healing.1.1] at hrun
    exact (goldilocksRunInterface_run_iff _).mpr hrun
  exact (goldilocksEventSafety_iff.mp goldilocks_event_safety)
    _ _ _ _ _ p C.catchUp C.look C.committeeLook ΔF b hrun' hnc
    (((goldilocksRunInterface_run_iff _).mp hrun').2.2.2 hnc)
    (canonical_window_premises S rho hn hv C hdata hb hbind
      (hsv.trans hdata.served) hpre hK hpop)
    hframes B B' hB hB'

/-- The concrete extension proof keeps the canonical map's two read boundaries. -/
theorem goldilocksRunMap_extension
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (fun v => v.val))
    (hdata : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C) :
    Extension (goldilocksRunMap S rho hn hv)
      ((goldilocksRunMap_signer S rho hn hv).symm ▸ C)
      (goldilocksEvents (S.params (pubOf E) hn) (S.ro _)) := by
  intro ΔF b p hb hrun hnc hbind hpre hK hpop hframes y i j t u hi hj hbi hbj hij htu
  obtain ⟨hsv, hl, hc, -, -, -, hr, hcl, hθ, -⟩ :=
    Simulation.local_data_cast (goldilocksRunMap_signer S rho hn hv).symm C
  rw [hr, hdata.healing.1.1] at hrun
  rw [hl] at hpre
  rw [hc] at hi hj
  simp only [CommitteeWindow, PopulationWindow, hl, hc, hcl, hθ] at hK hpop
  have hr' := (goldilocksRunInterface_run_iff _).mpr hrun
  exact (goldilocksExtension_iff.mp goldilocks_extension)
    _ _ _ _ _ p C.catchUp C.look C.committeeLook ΔF b hr' hnc
    (hrun.2.2.2 hnc)
    (canonical_window_premises S rho hn hv C hdata hb hbind
      (hsv.trans hdata.served) hpre hK hpop)
    hframes y i j t u hi hj hbi hbj hij htu

/-- The proposal adapter retains the local hold and margin equations. -/
theorem goldilocksRunMap_proposal_coverage
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (fun v => v.val))
    (hdata : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C) :
    ProposalCoverage (goldilocksRunMap S rho hn hv)
      ((goldilocksRunMap_signer S rho hn hv).symm ▸ C)
      (goldilocksEvents (S.params (pubOf E) hn) (S.ro _)) := by
  intro ΔF b p hb hrun hnc hbind hpre hK hpop hframes B k y j t hP hk hhold hkb hkt hy hread hjt
  obtain ⟨hsv, hl, hc, -, hm, hh, hr, hcl, hθ, -⟩ :=
    Simulation.local_data_cast (goldilocksRunMap_signer S rho hn hv).symm C
  rw [hr, hdata.healing.1.1] at hrun
  rw [hl] at hpre
  rw [hc, hh] at hP
  rw [hc] at hy
  rw [hh] at hhold
  rw [hm] at hkt
  simp only [CommitteeWindow, PopulationWindow, hl, hc, hcl, hθ] at hK hpop
  have hr' := (goldilocksRunInterface_run_iff _).mpr hrun
  exact (goldilocksProposalCoverage_iff.mp goldilocks_proposal_coverage)
    _ _ _ _ _ p C.catchUp C.look C.committeeLook ΔF b C.hold C.margin hr' hnc
    (hrun.2.2.2 hnc)
    (canonical_window_premises S rho hn hv C hdata hb hbind
      (hsv.trans hdata.served) hpre hK hpop)
    (by rw [hdata.hold])
    (by rw [hdata.margin])
    hframes B k y j t hP hk hhold hkb hkt hy hread hjt

end Consensus.Goldilocks.Generic.SleepyLayer1

end
