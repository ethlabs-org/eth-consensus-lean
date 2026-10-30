module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Service

public section

/-! # Goldilocks Healing: the phase service HS.1–HS.4 and HS.5's consumption step

The phase-service statements HS.1–HS.4 (`Statements/Healing/Service`; claims §"Healing: phase
service"; `phase-service.md` §§2–5 and §7), and the interface through which HS.5
(`Producer(A)`, `producer` in `Reset`) consumes them:

* `AcquiredPath` is HS.4 (a)'s second branch (the acquired common path: an honest unanimous
  proposal `W` of slot `s` with an entry `E` at `h ∈ {ℓ, m}` whose reports or rows every honest
  validator has by `t_s + 6Δ`, still in the phase), `ClientProgress` is HS.4 (b) (the client
  subclaim), and `common_path_acquisition'` restates HS.4 with them;
* `consume_continue` is HS.5's consumption and continuation (`phase-service.md` §6, §8.1;
  workbench#6 P3): from the acquired path, the phase changes by `w + A_HS`; one level down, its
  three steps that HS.1–HS.4 do not export are `historical_source_rows`,
  `fixed_upper_proposal_rows` and `mature_progress_consumption` (over `ProtectedBranch`,
  `ReportsBy`, `RowsBy` and `PathAt`, the pieces of `AcquiredPath`).

This is the paper orb's proposed contract, not yet certified. Interfaces: HS.1–HS.4,
`consume_continue` and its three helpers are open. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **HS.1, effective-phase viable-witness retention** (`phase-service.md` §2 "Why lower finality
is benign", §7 HS.1). -/
theorem viable_witness_retention : ViableWitnessRetention := by
  sorry

/-- **HS.2, clean-lock transfer and two-window drain** (`phase-service.md` §4 "Clean evidence and
the two-window drain", §7 HS.2). -/
theorem clean_lock_drain : CleanLockDrain := by
  sorry

/-- **HS.3, honest-proposal frozen-tree agreement** (`phase-service.md` §3 "Relay and the
honest-proposal sandwich", §7 HS.3). -/
theorem frozen_tree_agreement : FrozenTreeAgreement := by
  sorry

/-- **HS.4, bounded common path and actual-report acquisition** (`phase-service.md` §5 "First
proposal, actual reports, and the one extra wait", §7 HS.4). -/
theorem common_path_acquisition : CommonPathAcquisition := by
  sorry

section Contract

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The acquired common path** (HS.4 (a)'s second branch): a slot `s` with `t_s ≥ r`, a height
`h ∈ {ℓ, m}` with `h ≥ 1`, an entry `E` at `h` and an honest proposal `W` of slot `s` extending
`E` with state height `h`, with `w ≤ t_s` and `v = t_s + 6Δ ≤ w + D`; the phase is still `(m, c)`
after all events at `v`; every honest slot-`s` vote is exactly `W` (viable or at or below
`fc_root`); by `v` every honest validator has received a source with entry `E` at `h` or signed a
matching row; and until the phase end every later honest vote and honest proposal parent extends
`W`. -/
def AcquiredPath (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (Gp w : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) : Prop :=
  ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
    (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
    tr.ProposesAt (sp.toParams.proposer s) kW W ∧ W.slot = s ∧ sp.toParams.proposer s ∈ H ∧
    EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
    w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
    (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) ∧
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = W.root ∧
      (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot)) ∧
    (∀ y ∈ H, (∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
        tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ (tr.state y k).fg.Anc W C ∧
        EntryOf (tr.state y k).fg C E h ∧ ((tr.state y k).fg.σ C.root).h = h ∧
        EffAllowed (tr.state y k).fg m c C) ∨
      ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = h ∧
        att.T = E.root) ∧
    (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W) ∧
    ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
      tr.ProposesAt (sp.toParams.proposer s') k' P' → sp.toParams.proposer s' ∈ H →
      PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr

theorem acquiredPath_iff (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (Gp w : Time)
    (i₀ m : Nat) (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) :
    AcquiredPath tr H Gp w i₀ m c ↔
      ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
        (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
        tr.ProposesAt (sp.toParams.proposer s) kW W ∧ W.slot = s ∧ sp.toParams.proposer s ∈ H ∧
        EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
        w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
        (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) ∧
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
          e.msg.head = W.root ∧
          (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
            Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot)) ∧
        (∀ y ∈ H, (∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ sp.ts s ≤ tr.time k ∧
            tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ (tr.state y k).fg.Anc W C ∧
            EntryOf (tr.state y k).fg C E h ∧ ((tr.state y k).fg.σ C.root).h = h ∧
            EffAllowed (tr.state y k).fg m c C) ∨
          ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = h ∧
            att.T = E.root) ∧
        (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
          PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W) ∧
        ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
          P'.slot = s' → tr.ProposesAt (sp.toParams.proposer s') k' P' →
          sp.toParams.proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
          ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr :=
  Iff.rfl

/-- **The client subclaim** (HS.4 (b), P1/P2 of workbench#6): in the settled phase, at an honest
`fg_attest` whose source `C` has state height `h ≥ ℓ` and entry `E` and is allowed in the phase
geometry, the client signs a matching row for `E`, or has signed one at an earlier cut. -/
def ClientProgress (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) : Prop :=
  ∀ y ∈ H, ∀ k (C : SA.Blk sp.n (List (FG.Att sp.n))) (signed : Option (FG.Att sp.n)),
    tr.CallAt y k (.fg (.attest C signed)) → i₀ ≤ k → PhaseOn tr.projFG H i₀ k m c →
    ∀ E h, EntryOf (tr.state y k).fg C E h → ((tr.state y k).fg.σ C.root).h = h →
      phaseFloor m c ≤ h →
      EffAllowed (tr.state y k).fg m c C →
      (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
      ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root

theorem clientProgress_iff (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) :
    ClientProgress tr H i₀ m c ↔
      ∀ y ∈ H, ∀ k (C : SA.Blk sp.n (List (FG.Att sp.n))) (signed : Option (FG.Att sp.n)),
        tr.CallAt y k (.fg (.attest C signed)) → i₀ ≤ k → PhaseOn tr.projFG H i₀ k m c →
        ∀ E h, EntryOf (tr.state y k).fg C E h → ((tr.state y k).fg.σ C.root).h = h →
          phaseFloor m c ≤ h →
          EffAllowed (tr.state y k).fg m c C →
          (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
          ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root :=
  Iff.rfl

/-! ### The pieces of the acquired path that HS.5's consumption reads -/

/-- **The protected branch** of an honest proposal `W` of slot `s` (HS.4 (a), HS.3 (b)): every
honest slot-`s` vote is exactly `W` (viable or at or below `fc_root`), and until the phase end
every later honest vote and every honest proposal parent of a later slot extends `W`. -/
def ProtectedBranch (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (s : Nat)
    (W : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
    e.msg.head = W.root ∧
    (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
      Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot)) ∧
  (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
    PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W) ∧
  ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
    tr.ProposesAt (sp.toParams.proposer s') k' P' → sp.toParams.proposer s' ∈ H →
    PhaseOn tr.projFG H i₀ k' m c →
    ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr

theorem protectedBranch_iff (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (s : Nat)
    (W : SA.Blk sp.n (List (FG.Att sp.n))) :
    ProtectedBranch tr H i₀ m c s W ↔
      (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
        e.msg.head = W.root ∧
        (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
          Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot)) ∧
      (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
        PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W) ∧
      ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
        P'.slot = s' → tr.ProposesAt (sp.toParams.proposer s') k' P' →
        sp.toParams.proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
        ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr :=
  Iff.rfl

/-- **Reports or rows by `v`** (HS.4 (a)'s acquisition clause): every honest validator has, by
`v`, received a source (an `ac_to_fg` return) of state height `h` with entry `E`, or signed a
matching row for `E` at `h`. -/
def ReportsBy (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (u v : Time) (h m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (E W : SA.Blk sp.n (List (FG.Att sp.n))) :
    Prop :=
  ∀ y ∈ H, (∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ u ≤ tr.time k ∧ tr.time k ≤ v ∧
      (tr.state y k).fg.Anc W C ∧ EntryOf (tr.state y k).fg C E h ∧
      ((tr.state y k).fg.σ C.root).h = h ∧ EffAllowed (tr.state y k).fg m c C) ∨
    ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = E.root

theorem reportsBy_iff (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (u v : Time) (h m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (E W : SA.Blk sp.n (List (FG.Att sp.n))) :
    ReportsBy tr H u v h m c E W ↔
      ∀ y ∈ H, (∃ k ℓ C, SA.ToFGAt tr.projAC y k ℓ C ∧ u ≤ tr.time k ∧ tr.time k ≤ v ∧
          (tr.state y k).fg.Anc W C ∧ EntryOf (tr.state y k).fg C E h ∧
          ((tr.state y k).fg.σ C.root).h = h ∧ EffAllowed (tr.state y k).fg m c C) ∨
        ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = E.root :=
  Iff.rfl

/-- **Rows by `v`**: every honest validator has signed a matching row for `E` at `h` by `v` (so
the matching rows have weight `n − f ≥ q`). -/
def RowsBy (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (v : Time) (h : Nat)
    (E : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = E.root

theorem rowsBy_iff (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (v : Time) (h : Nat)
    (E : SA.Blk sp.n (List (FG.Att sp.n))) :
    RowsBy tr H v h E ↔
      ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = E.root :=
  Iff.rfl

/-- **The acquired path without its acquisition clause**, for a fixed witness
`(s, h, E, W, kW)`: the conjuncts of `AcquiredPath` other than the reports-or-rows clause. -/
def PathAt (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (Gp w : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (s h : Nat)
    (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat) : Prop :=
  (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
    tr.ProposesAt (sp.toParams.proposer s) kW W ∧ W.slot = s ∧ sp.toParams.proposer s ∈ H ∧
    EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
    w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
    (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) ∧
    ProtectedBranch tr H i₀ m c s W

theorem pathAt_iff (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (Gp w : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (s h : Nat)
    (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat) :
    PathAt tr H Gp w i₀ m c s h E W kW ↔
      (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
        tr.ProposesAt (sp.toParams.proposer s) kW W ∧ W.slot = s ∧
        sp.toParams.proposer s ∈ H ∧
        EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
        w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
        (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) ∧
        ProtectedBranch tr H i₀ m c s W :=
  Iff.rfl

/-- The acquired path is a witness with `PathAt` and its reports or rows by `v = t_s + 6Δ`. -/
theorem acquiredPath_iff_exists (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (Gp w : Time)
    (i₀ m : Nat) (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) :
    AcquiredPath tr H Gp w i₀ m c ↔
      ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
        PathAt tr H Gp w i₀ m c s h E W kW ∧
          ReportsBy tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) h m c E W := by
  constructor
  · rintro ⟨s, h, E, W, kW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    exact ⟨s, h, E, W, kW, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15⟩, h13⟩
  · rintro ⟨s, h, E, W, kW, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15⟩, h13⟩
    exact ⟨s, h, E, W, kW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-- **HS.4 with the named branches**: settled at `w` in `(m, c)`, the phase has changed by
`w + D_HS` or the common path is acquired (`AcquiredPath`), and the client subclaim holds. -/
theorem common_path_acquisition' (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hset : SettledIn tr H g w i₀ m c) :
    ((∀ j', FirstCutAfter tr j' (w + D_HS sp Gp) → PhaseChanged tr.projFG H i₀ j') ∨
      AcquiredPath tr H Gp w i₀ m c) ∧ ClientProgress tr H i₀ m c :=
  common_path_acquisition sp ro dg H tr g ΔF Gp w i₀ m c hrun hs hc hp hset

/-! ### HS.5's consumption, one level down (proposed contract)

The paper orb's skeptical read-back of `consume_continue` names three steps that HS.1–HS.4 do not
export: (1) HS.4's source arm gives a source at a time `≤ v`, with no `i₀ ≤ k` and no
`EffAllowed`, so `ClientProgress` does not apply to it directly; (2) for the chosen height-`m`
proposal `Y` of the continuation, HS.3 exports only the votes and parent extension, not the rows;
(3) the FG inclusion and acceptance of the crossing (P3). They are stated over the data the
assembly has; their exact form is a proposed contract, not yet certified. -/

/-- **Current sources give matching rows** (`phase-service.md` §5 "an actual candidate passed to
the FG serves `E`", §6): for the acquired path's witness, every honest validator that has, in
`[t_s, v]`, `v = t_s + 6Δ`, received a source `C ⪰ W` of state height `h` with entry `E`, allowed
in the phase (HS.4's current-source arm, #88), has signed a matching row for `E` at `h` by `v`:
the `ac_to_fg` return is followed at once by the `fg_attest` of the same tick, at which
`ClientProgress` applies (the phase holds through `v`). Open: that source-to-attest transport. -/
theorem historical_source_rows (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hset : SettledIn tr H g w i₀ m c) (hcl : ClientProgress tr H i₀ m c) {s h : Nat}
    {E W : SA.Blk sp.n (List (FG.Att sp.n))} {kW : Nat}
    (hpath : PathAt tr H Gp w i₀ m c s h E W kW)
    (hrep : ReportsBy tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) h m c E W) :
    RowsBy tr H (sp.ts s + 6 * sp.Δ) h E := by
  sorry

/-- **Rows at `m` for a fixed upper proposal** (`phase-service.md` §8.1, the continuation, and
§5's upper-height case; proposed contract): settled at `w` in `(m, c)`, let `Y` be an honest
proposal of slot `s` with `t_s ≥ r` and state height `m`, on a protected branch (every honest
slot-`s` vote is exactly `Y`, later votes and proposal parents extend it until the phase end), in
the phase through `v = t_s + 6Δ`. Then `Y` has an entry `E` at `m` and every honest validator has
signed a matching row for `E` at `m` by `v`: at `v` every honest node holds `Y` as its regular
result and fresh fast lock (more than half the committee voted `Y`, no slot-`s` supporting head
strictly extends it, the write is not vetoed); a candidate extending `Y`, or an earlier reported
descendant suppressing it, has height `m` (no frontier rise) and `Y`'s entry; P1/P2 sign the
row. -/
theorem fixed_upper_proposal_rows (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hset : SettledIn tr H g w i₀ m c) (hcl : ClientProgress tr H i₀ m c) {s kY : Nat}
    {Y : SA.Blk sp.n (List (FG.Att sp.n))} (hY : tr.ProposesAt (sp.toParams.proposer s) kY Y)
    (hYs : Y.slot = s) (hpH : sp.toParams.proposer s ∈ H)
    (hYh : ((tr.post kY).fg.σ Y.root).h = m) (hr : rTime sp w ≤ sp.ts s)
    (hbr : ProtectedBranch tr H i₀ m c s Y)
    (hon : ∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) :
    ∃ E, EntryOf (tr.post kY).fg Y E m ∧ RowsBy tr H (sp.ts s + 6 * sp.Δ) m E := by
  sorry

/-- **Mature progress consumption** (P3 of workbench#6, included in HS.5: `phase-service.md` §6,
§7 HS.5, §8.1; proposed contract): settled at `w` in `(m, c)`, let `W` be an honest proposal of
slot `s` with `w ≤ t_s` on a protected branch, `E` its entry at a height `h ≥ ℓ`, with
matching rows from every honest validator by `v = t_s + 6Δ`, and
`b = max(v + Δ_F, t_{E.slot + δ_t}) + G_p + Δ`. Then after all events at `b` the phase has
changed, or the first honest ready inclusion proposal `X` after `max(v + Δ_F, t_{E.slot + δ_t})`
(slot `x`, `t_x + Δ ≤ b`) crosses `h` (state height `≥ h + 1`, also when its parent chain had
crossed `h` already), extends `W`, and is accepted by every honest node before `t_x + Δ`: the rows
reach the proposer's pool by `v + Δ_F` (GST delivery, old rows by the GST convention), honest
inclusion proposals until the crossing keep `E` and its progress bits, and the timeout arm fires
after `t_{E.slot + δ_t}` even when loose BJ blocks justification. -/
theorem mature_progress_consumption (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hset : SettledIn tr H g w i₀ m c) {s h kW : Nat} {E W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt (sp.toParams.proposer s) kW W) (hWs : W.slot = s)
    (hpH : sp.toParams.proposer s ∈ H) (hE : EntryOf (tr.post kW).fg W E h)
    (hh : phaseFloor m c ≤ h) (hws : w ≤ sp.ts s) (hbr : ProtectedBranch tr H i₀ m c s W)
    (hrows : RowsBy tr H (sp.ts s + 6 * sp.Δ) h E) (jb : Nat)
    (hjb : FirstCutAfter tr jb
      (max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) + Gp + sp.Δ)) :
    PhaseChanged tr.projFG H i₀ jb ∨
      ∃ (x kX : Nat) (X : SA.Blk sp.n (List (FG.Att sp.n))),
        ReadyProposal tr H (sp.toParams.proposer x) kX x X ∧
        max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) ≤ sp.ts x ∧
        sp.ts x + sp.Δ ≤
          max (sp.ts s + 6 * sp.Δ + ΔF) (sp.ts (E.slot + sp.toParams.δt : Nat)) + Gp + sp.Δ ∧
        h + 1 ≤ ((tr.post kX).fg.σ X.root).h ∧ Anc (tr.HonestBlocks H) W X ∧
        ∀ y ∈ H, ∃ k, tr.AcceptAt y k X ∧ tr.time k < sp.ts x + sp.Δ := by
  sorry

/-- **HS.5, consumption and continuation** (`phase-service.md` §6, §8.1; workbench#6 P3): from
the acquired path, a fresh honest ready inclusion proposal `X` (`Prop⁺` after
`max(v + Δ_F, t_{E.slot + δ_t})`) crosses `h` by `b`; if `h = m` the crossing changes the phase
within `C`; if `h = m − 1`, `X` has height `m` and is unanimous (HS.3 (b) with HS.2), and a second
proposal `Y` after `t_X + 8Δ` gives the upper-height service within a second `C`; so the phase
has changed by `w + A_HS`, `A = 2C + Δ`. It takes HS.1–HS.3 as hypotheses deliberately (the
paper orb's proposed contract, not yet certified).

Its proof is meant to assemble `historical_source_rows` (the witness's reports become rows),
`mature_progress_consumption` (the crossing proposal `X` by `b ≤ w + C`; at `h = m` a crossing
is a frontier rise), and, at `h = m − 1`, HS.3 (b) for `X` and for the next ready proposal `Y`
after `t_X + 8Δ` (with HS.2's lock premise), `fixed_upper_proposal_rows` for `Y` and
`mature_progress_consumption` again at `m` (by `t_X + Δ + C ≤ w + 2C`). The glue still open: a
crossing proposal of height `m + 1` accepted by an honest node changes the phase; `ht(Y) = m`
(it extends `X`, of height `m`, and the frontier is `m`); `E.slot ≤ s`; HS.3's timing premises
for `X` and `Y`; and the time arithmetic. -/
theorem consume_continue (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hret : ViableWitnessRetention) (hclean : CleanLockDrain) (hagree : FrozenTreeAgreement)
    (hset : SettledIn tr H g w i₀ m c) (hwit : AcquiredPath tr H Gp w i₀ m c)
    (hcl : ClientProgress tr H i₀ m c) (jA : Nat) (hjA : FirstCutAfter tr jA (w + A_HS sp ΔF Gp)) :
    PhaseChanged tr.projFG H i₀ jA := by
  sorry

end Contract

end Consensus.Goldilocks.Healing

end
