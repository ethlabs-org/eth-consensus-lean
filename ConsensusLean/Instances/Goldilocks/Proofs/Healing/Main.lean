module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Bridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Assembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Service

public section

/-! # Goldilocks milestone Healing

`HealingACStatements` (H.1, its corollary, H.2) from `Lemmas/Healing/`.

`HealingRunStatements` (HR.1–HR.4, H.2 (run), H.3, H.4) and `PhaseServiceStatements` (HS.1–HS.4)
are open only through H.3's `Inv` half and HS.3 (a). Everything else is assembled here, without
`sorry`:

* `healing_run_proved`: the run bundle without H.3 (HR.1–HR.4, H.2 (run), H.4);
  `non_interference_of_reset_inv` gives H.3 from its `Inv` half alone (H.3 (a) is HR.3, (b) is HR.4,
  the `Geo` half of (c) is `settled_geo`, combined at `max(T_b, 8Δ)` by `Inv.mono`); and
  `healing_run_statements_of_reset_inv` is the bundle from that half.
* `phase_service_proved`: the phase-service bundle without HS.3 (HS.1, HS.2, HS.4);
  `frozen_tree_agreement_of_unlocked` gives HS.3 from its part (a) alone ((b) is
  `frozen_tree_agreement_clean`, from HS.2); and `phase_service_statements_of_unlocked` is the
  bundle from that part.

So a proof of H.3's `Inv` half or of HS.3 (a) closes its bundle in one step. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **Healing, the AC statements**: H.1, its corollary and H.2. -/
theorem healing_ac_statements : SA.HealingACStatements where
  standalone := SA.ac_healing_standalone
  corollary := SA.ac_healing_standalone_corollary
  inclusion := SA.ac_inclusion

/-! ## The run bundle -/

/-- **The proved run statements**: HR.1–HR.4, H.2 (run) and H.4 (conditional on the bridge, as
stated), i.e. `HealingRunStatements` without H.3 (`nonInterference`). -/
theorem healing_run_proved :
    CutAndReset ∧ (∀ (P : Params) (ACP : Type), PhaseCount P ACP) ∧ ResetExistence ∧
      HeightScopedRetention ∧ RunInclusion ∧ AvailableHealing :=
  ⟨cut_and_reset, phase_count, reset_existence, height_scoped_retention, run_inclusion,
    available_healing⟩

/-- **H.3 from its `Inv` half.** If the AC projection satisfies `Inv(a_z + T_b)` after the reset,
for a `T_b ≥ 0` that is a function of the parameters only, then H.3 holds: (a) is HR.3, (b) is
HR.4, and the bridge (c) takes `max(T_b, 8Δ)`, with `Inv` by monotonicity (`Inv.mono`) and `Geo`
from the settled phase (`settled_geo`). The premise is the open part of H.3. -/
theorem non_interference_of_reset_inv
    (hinv : ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
      ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
        (proposer : Nat → Fin sp.n)
        (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
        (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
        GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
        PropPlus tr H proposer g Gp → ∀ a, IsReset tr H g a →
          SA.Inv proposer tr.projAC H (tr.HonestBlocks H)
            (a + Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt)) :
    NonInterference := by
  obtain ⟨Tb, hTb, hinv⟩ := hinv
  refine ⟨fun n Δ ΔF k δt => max (Tb n Δ ΔF k δt) (8 * Δ), fun n Δ ΔF k δt =>
    (hTb n Δ ΔF k δt).trans (le_max_left _ _),
    fun sp ro proposer dg H tr g ΔF Gp hrun hs hc hp => ?_⟩
  have hr := reset_existence sp ro proposer dg H tr g ΔF Gp hrun hs hc hp
  obtain ⟨a, ha⟩ := hr.2.2.1
  exact ⟨a, ha, (hr.2.2.2.1 a ha).trans hr.2.2.2.2.1,
    height_scoped_retention sp ro proposer dg H tr g ΔF hrun hs.healthy hs.noColl a ha,
    (hinv sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a ha).mono
      (add_le_add_right (le_max_left _ _) a),
    fun p P hP htp hph => settled_geo hrun hs hc hp ha (le_max_right _ _) p P hP htp hph⟩

/-- **The run bundle from H.3's `Inv` half** (`non_interference_of_reset_inv` and
`healing_run_proved`). -/
theorem healing_run_statements_of_reset_inv
    (hinv : ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
      ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
        (proposer : Nat → Fin sp.n)
        (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
        (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
        GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
        PropPlus tr H proposer g Gp → ∀ a, IsReset tr H g a →
          SA.Inv proposer tr.projAC H (tr.HonestBlocks H)
            (a + Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt)) :
    HealingRunStatements where
  cutAndReset := cut_and_reset
  phaseCount := phase_count
  resetExistence := reset_existence
  heightScopedRetention := height_scoped_retention
  runInclusion := run_inclusion
  nonInterference := non_interference_of_reset_inv hinv
  availableHealing := available_healing

/-! ## The phase-service bundle -/

/-- **The proved phase-service statements**: HS.1, HS.2 and HS.4, i.e. `PhaseServiceStatements`
without HS.3 (`frozenTreeAgreement`), whose part (b) is `frozen_tree_agreement_clean`. -/
theorem phase_service_proved :
    ViableWitnessRetention ∧ CleanLockDrain ∧ CommonPathAcquisition :=
  ⟨viable_witness_retention, clean_lock_drain, common_path_acquisition⟩

/-- **HS.3 from its part (a).** The premise is `FrozenTreeAgreement`'s first conjunct (the
unlocked case, under its own lock and proposer-start premises), with the same quantifiers; the
second conjunct, (b), is `frozen_tree_agreement_clean` from HS.2. The premise is the open part of
HS.3. -/
theorem frozen_tree_agreement_of_unlocked
    (ha : ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (proposer : Nat → Fin sp.n)
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF w : Time) (i₀ i m : Nat)
      (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
      GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
      SettledIn tr H g w i₀ m c → i₀ ≤ i →
      ∀ (p : Fin sp.n) (kP s : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
        ReadyProposal tr H proposer p kP s P → i ≤ kP →
        tr.time i ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ →
        gbar g ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ →
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          PhaseOn tr.projFG H i k m c) →
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
            ∀ L ∈ ℓ.frame.tree, L.root = l.block →
              Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot) →
        (∀ kq ℓP, tr.projAC.CallAt p kq ℓP → ℓP.call = .proposal → tr.time kq = sp.ts s →
          ∀ l ∈ SA.liveLocks sp (tr.post kq).ac.locks ℓP.frame (tr.time kq), l.slot < s →
            ∀ L ∈ ℓP.frame.tree, L.root = l.block →
              ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
                (∃ l' ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k),
                  ∃ L' ∈ ℓ.frame.tree, L'.root = l'.block ∧ Anc (tr.HonestBlocks H) L L') ∨
                Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot) →
          ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
            e.msg.head = P.root ∧
            ((P ∈ ℓ.frame.viableHeads ∧
                P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
              Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot) ∧
            ∀ X, Anc (tr.HonestBlocks H) X P →
              X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
              Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot) :
    FrozenTreeAgreement :=
  fun sp ro proposer dg H tr g ΔF w i₀ i m c hrun hs hc hw hi₀ p kP s P hP hikP hti hg hph =>
    ⟨ha sp ro proposer dg H tr g ΔF w i₀ i m c hrun hs hc hw hi₀ p kP s P hP hikP hti hg hph,
      frozen_tree_agreement_clean clean_lock_drain sp ro proposer dg H tr g ΔF w i₀ i m c hrun hs
        hc hw hi₀ p kP s P hP hikP hti hg hph⟩

/-- **The phase-service bundle from HS.3 (a)** (`frozen_tree_agreement_of_unlocked` and
`phase_service_proved`). -/
theorem phase_service_statements_of_unlocked
    (ha : ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (proposer : Nat → Fin sp.n)
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF w : Time) (i₀ i m : Nat)
      (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))),
      GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
      SettledIn tr H g w i₀ m c → i₀ ≤ i →
      ∀ (p : Fin sp.n) (kP s : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
        ReadyProposal tr H proposer p kP s P → i ≤ kP →
        tr.time i ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ →
        gbar g ≤ sp.ts ((s : Int) - 1) + 3 * sp.Δ →
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          PhaseOn tr.projFG H i k m c) →
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          ∀ l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k), l.slot < s →
            ∀ L ∈ ℓ.frame.tree, L.root = l.block →
              Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot) →
        (∀ kq ℓP, tr.projAC.CallAt p kq ℓP → ℓP.call = .proposal → tr.time kq = sp.ts s →
          ∀ l ∈ SA.liveLocks sp (tr.post kq).ac.locks ℓP.frame (tr.time kq), l.slot < s →
            ∀ L ∈ ℓP.frame.tree, L.root = l.block →
              ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
                (∃ l' ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k),
                  ∃ L' ∈ ℓ.frame.tree, L'.root = l'.block ∧ Anc (tr.HonestBlocks H) L L') ∨
                Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot) →
          ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
            e.msg.head = P.root ∧
            ((P ∈ ℓ.frame.viableHeads ∧
                P ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s)) ∨
              Anc (tr.HonestBlocks H) P ℓ.frame.fcRoot) ∧
            ∀ X, Anc (tr.HonestBlocks H) X P →
              X ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
              Anc (tr.HonestBlocks H) X ℓ.frame.fcRoot) :
    PhaseServiceStatements where
  viableWitnessRetention := viable_witness_retention
  cleanLockDrain := clean_lock_drain
  frozenTreeAgreement := frozen_tree_agreement_of_unlocked ha
  commonPathAcquisition := common_path_acquisition

end Consensus.Goldilocks.Healing

end
