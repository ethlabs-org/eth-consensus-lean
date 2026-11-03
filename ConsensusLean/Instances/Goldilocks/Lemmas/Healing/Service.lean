module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Acquire
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Drain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeContinue
public import Mathlib.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF

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
  three steps that HS.1–HS.4 do not export are `historical_source_rows` (proved, `Source`),
  the rows of a fixed upper proposal (`fixed_upper_rows_of`, `ConsumeUpper`) and mature
  progress consumption (`mature_progress_of`, `ConsumeMature`) (over `ProtectedBranch`,
  `ReportsBy`, `RowsBy` and `PathAt`, the pieces of `AcquiredPath`).

HS.1, HS.2 and HS.4 are proved (`Retain`, `Drain`, `Acquire`), and HS.3 (b) is proved from HS.2
(`frozen_tree_agreement_clean`, `AgreeVotes`); HS.3 as a whole (`FrozenTreeAgreement`, with part
(a)) has no inhabitant. This is the paper orb's proposed contract, not yet certified.
`consume_continue` and its two steps are assembled in `ConsumeContinue`, `ConsumeUpper`
(`fixed_upper_rows_of`) and `ConsumeMature` (`mature_progress_of`) (`hs5-exact-helpers.md` §§2–4,
with `ConsumeCrossing` for §3.1, the sources of §§2.1–2.3 in `AcquireSources`), over HS.1 and
HS.2 as hypotheses (HS.3 (b) from HS.2). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **HS.1, effective-phase viable-witness retention** (`phase-service.md` §2 "Why lower finality
is benign", §7 HS.1; proved in `Retain`, `viable_witness_retention_of`). -/
theorem viable_witness_retention : ViableWitnessRetention :=
  fun _ _ _ _ _ _ _ _ hrun hs _ _ _ _ _ hon _ hy _ hW _ hz _ h1 h2 =>
    viable_witness_retention_of hrun hs hon hy hW hz h1 h2

/-- **HS.2, clean-lock transfer and two-window drain** (`phase-service.md` §4 "Clean evidence and
the two-window drain", §7 HS.2; `hs234-exact-interface.md` §3, assembled in `Drain`). -/
theorem clean_lock_drain : CleanLockDrain := by
  intro sp ro proposer dg H tr g ΔF Gp w i₀ m c hrun hs hc hp hw
  refine ⟨fun _ hx _ _ _ _ ho hj _ _ hy _ _ _ hv hjs hk => ⟨fun he =>
      clean_fast_next hrun hs hc hw hx ho hj hy hv he hk, fun _ =>
      clean_fast_later hrun hs hc hw hx ho hj hy hv hjs hk⟩,
    fun _ hx _ _ _ ho hj _ _ hy _ _ _ hv hjs hk => ⟨fun he =>
      clean_slow_next hrun hs hc hw hx ho hj hy hv he hk, fun _ =>
      clean_slow_later hrun hs hc hw hx ho hj hy hv hjs hk⟩,
    fun _ hy k _ _ hr _ _ hl => live_lock_clean hr (Compose.locksWF_state hrun hs.noColl hy k) hl,
    fun _ _ hP hr _ hy _ _ _ hv he hk _ hl hls _ hL hLr =>
      live_lock_below_proposal hrun hs hc hw hP hr hy hv he hk hl hls hL hLr⟩

/-- **HS.4, bounded common path and actual-report acquisition** (`phase-service.md` §5 "First
proposal, actual reports, and the one extra wait", §7 HS.4). -/
theorem common_path_acquisition : CommonPathAcquisition :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hrun hs hc hp hset =>
    ⟨acquired_or_changed hrun hs hc hp hset clean_lock_drain,
      client_progress hrun hs⟩

section Contract

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The acquired common path** (HS.4 (a)'s second branch): a slot `s` with `t_s ≥ r`, a height
`h ∈ {ℓ, m}` with `h ≥ 1`, an entry `E` at `h` and an honest proposal `W` of slot `s` extending
`E` with state height `h`, with `w ≤ t_s` and `v = t_s + 6Δ ≤ w + D`; the phase is still `(m, c)`
after all events at `v`; every honest slot-`s` vote is exactly `W` (viable or at or below
`fc_root`); by `v` every honest validator has received a source with entry `E` at `h` or signed a
matching row; and until the phase end every later honest vote and honest proposal parent extends
`W`. -/
def AcquiredPath (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (Gp w : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) : Prop :=
  ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
    (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
    tr.ProposesAt (proposer s) kW W ∧ W.slot = s ∧ proposer s ∈ H ∧
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
      tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H →
      PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr

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

/-! ### The pieces of the acquired path that HS.5's consumption reads -/

/-- **The protected branch** of an honest proposal `W` of slot `s` (HS.4 (a), HS.3 (b)): every
honest slot-`s` vote is exactly `W` (viable or at or below `fc_root`), and until the phase end
every later honest vote and every honest proposal parent of a later slot extends `W`. -/
def ProtectedBranch (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (s : Nat)
    (W : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
    e.msg.head = W.root ∧
    (W ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
      Anc (tr.HonestBlocks H) W ℓ.frame.fcRoot)) ∧
  (∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
    PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg W) ∧
  ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' → P'.slot = s' →
    tr.ProposesAt (proposer s') k' P' → proposer s' ∈ H →
    PhaseOn tr.projFG H i₀ k' m c →
    ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) W Pr

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

/-- **Rows by `v`**: every honest validator has signed a matching row for `E` at `h` by `v` (so
the matching rows have weight `n − f ≥ q`). -/
def RowsBy (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (v : Time) (h : Nat)
    (E : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ v ∧ att.h = h ∧ att.T = E.root

/-- **The acquired path without its acquisition clause**, for a fixed witness
`(s, h, E, W, kW)`: the conjuncts of `AcquiredPath` other than the reports-or-rows clause. -/
def PathAt (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (Gp w : Time) (i₀ m : Nat)
    (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) (s h : Nat)
    (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat) : Prop :=
  (h = phaseFloor m c ∨ h = m) ∧ 1 ≤ h ∧
    tr.ProposesAt (proposer s) kW W ∧ W.slot = s ∧ proposer s ∈ H ∧
    EntryOf (tr.post kW).fg W E h ∧ ((tr.post kW).fg.σ W.root).h = h ∧
    w ≤ sp.ts s ∧ rTime sp w ≤ sp.ts s ∧ sp.ts s + 6 * sp.Δ ≤ w + D_HS sp Gp ∧
    (∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) ∧
    ProtectedBranch tr H proposer i₀ m c s W

/-- The acquired path is a witness with `PathAt` and its reports or rows by `v = t_s + 6Δ`. -/
theorem acquiredPath_iff_exists (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (Gp w : Time)
    (i₀ m : Nat) (c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))) :
    AcquiredPath tr H proposer Gp w i₀ m c ↔
      ∃ (s h : Nat) (E W : SA.Blk sp.n (List (FG.Att sp.n))) (kW : Nat),
        PathAt tr H proposer Gp w i₀ m c s h E W kW ∧
          ReportsBy tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) h m c E W := by
  constructor
  · rintro ⟨s, h, E, W, kW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    exact ⟨s, h, E, W, kW, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15⟩, h13⟩
  · rintro ⟨s, h, E, W, kW, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15⟩, h13⟩
    exact ⟨s, h, E, W, kW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-- **HS.4 with the named branches**: settled at `w` in `(m, c)`, the phase has changed by
`w + D_HS` or the common path is acquired (`AcquiredPath`), and the client subclaim holds. -/
theorem common_path_acquisition' (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H proposer g Gp)
    (hset : SettledIn tr H g w i₀ m c) :
    ((∀ j', FirstCutAfter tr j' (w + D_HS sp Gp) → PhaseChanged tr.projFG H i₀ j') ∨
      AcquiredPath tr H proposer Gp w i₀ m c) ∧ ClientProgress tr H i₀ m c :=
  common_path_acquisition sp ro proposer dg H tr g ΔF Gp w i₀ m c hrun hs hc hp hset

/-! ### HS.5's consumption, one level down (proposed contract)

The paper orb's skeptical read-back of `consume_continue` names three steps that HS.1–HS.4 do not
export: (1) the row of a current source (HS.4's source arm, #88: a source in `[t_s, v]`, allowed in
the phase), from the `fg_attest` of the same tick and `ClientProgress`; (2) for the chosen
height-`m` proposal `Y` of the continuation, HS.3 exports only the votes and parent extension, not
the rows; (3) the FG inclusion and acceptance of the crossing (P3). They are stated over the data
the assembly has; their exact form is a proposed contract, not yet certified. -/

/-- **Current sources give matching rows** (`phase-service.md` §5 "an actual candidate passed to
the FG serves `E`", §6): for the acquired path's witness, every honest validator that has, in
`[t_s, v]`, `v = t_s + 6Δ`, received a source `C ⪰ W` of state height `h` with entry `E`, allowed
in the phase (HS.4's current-source arm, #88), has signed a matching row for `E` at `h` by `v`:
the `ac_to_fg` return is followed at once by the `fg_attest` of the same tick, at which
`ClientProgress` applies (the phase holds through `v`; `toFG_attest` for the transport). -/
theorem historical_source_rows (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF)
    (_hc : CatchRun tr H g (2 * sp.Δ)) (_hp : PropPlus tr H proposer g Gp)
    (hset : SettledIn tr H g w i₀ m c) (hcl : ClientProgress tr H i₀ m c) {s h : Nat}
    {E W : SA.Blk sp.n (List (FG.Att sp.n))} {kW : Nat}
    (hpath : PathAt tr H proposer Gp w i₀ m c s h E W kW)
    (hrep : ReportsBy tr H (sp.ts s) (sp.ts s + 6 * sp.Δ) h m c E W) :
    RowsBy tr H (sp.ts s + 6 * sp.Δ) h E := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hws, -, -, hon, -⟩ := hpath
  intro y hy
  rcases hrep y hy with ⟨k, ℓ, C, ⟨hcall, hto, hC⟩, hu, hv, -, hE, hCh, hall⟩ | hrow
  · -- the source is attested in the same tick, at the same FG state
    rw [Compose.projAC_state hrun.toLocalRun hy] at hC
    obtain ⟨sg, hatt, ht, hfg⟩ :=
      toFG_attest hrun.toLocalRun hy (Compose.projAC_callAt.1 hcall) hto hC
    rw [← hfg] at hE hCh hall
    -- the attest cut lies in the phase: after `i₀` (at a time `≥ w`) and before the first cut
    -- after `v`
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    have hlate := hset.1.late
    have hmax := le_max_right (gbar g + 2 * sp.Δ) (gbar g + 8 * sp.Δ)
    have hex : ∃ i, sp.ts s + 6 * sp.Δ < tr.time i := by
      obtain ⟨i, -, hi⟩ := hrun.awake_in_horizon y hy (sp.ts s + 6 * sp.Δ + 1)
        (hs.healthy.2.1 y hy _ (by change gbar g ≤ _; linarith))
      exact ⟨i, by linarith⟩
    have hjv : FirstCutAfter tr (Nat.find hex) (sp.ts s + 6 * sp.Δ) :=
      ⟨fun k hk => not_lt.1 (Nat.find_min hex hk), Nat.find_spec hex⟩
    have hkv : k + 1 ≤ Nat.find hex := by
      by_contra hlt
      have := hrun.time_mono (show Nat.find hex ≤ k by omega)
      linarith [hjv.2]
    have hi₀ : i₀ ≤ k + 1 := by
      by_contra hlt
      have := hset.2.1.2 (k + 1) (by omega)
      linarith
    rcases hcl y hy (k + 1) C sg hatt hi₀ (fun k' h₁ h₂ => hon _ hjv k' h₁ (h₂.trans hkv))
        E h hE hCh (hCh ▸ hall.2.1) hall with
      ⟨att, rfl, hah, haT⟩ | ⟨k', hk', att, hsa, hah, haT⟩
    · exact ⟨k + 1, att, ⟨C, hatt⟩, by rw [ht]; exact hv, hah, haT⟩
    · exact ⟨k', att, hsa, (hrun.time_mono hk'.le).trans (by rw [ht]; exact hv), hah, haT⟩
  · exact hrow

/-- **HS.5, consumption and continuation** (`phase-service.md` §6, §8.1; workbench#6 P3): from
the acquired path, a fresh honest ready inclusion proposal `X` (`Prop⁺` after
`max(v + Δ_F, t_{E.slot + δ_t})`) crosses `h` by `b`; if `h = m` the crossing changes the phase
within `C`; if `h = m − 1`, `X` has height `m` and is unanimous (HS.3 (b) with HS.2), and a second
proposal `Y` after `t_X + 8Δ` gives the upper-height service within a second `C`; so the phase
has changed by `w + A_HS`, `A = 2C + Δ`. It takes HS.1 and HS.2 as hypotheses deliberately (the
paper orb's proposed contract, not yet certified); HS.3 (b) follows from HS.2
(`frozen_tree_agreement_clean`).

Its proof is meant to assemble `historical_source_rows` (the witness's reports become rows),
`mature_progress_of` (the crossing proposal `X` by `b ≤ w + C`; at `h = m` a crossing
is a frontier rise), and, at `h = m − 1`, HS.3 (b) for `X` and for the next ready proposal `Y`
after `t_X + 8Δ` (with HS.2's lock premise), `fixed_upper_rows_of` for `Y` and
`mature_progress_of` again at `m` (by `t_X + Δ + C ≤ w + 2C`). The glue (a crossing
proposal of height `m + 1` accepted in the phase is a frontier rise; `ht(Y) = m`; `E.slot ≤ s`;
HS.3's timing premises for `X` and `Y`; the time arithmetic, with index inclusion of first cuts)
is proved in `ConsumeContinue` (`consume_continue_of`, `hs5-exact-helpers.md` §4). -/
theorem consume_continue (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H proposer g Gp)
    (hret : ViableWitnessRetention) (hclean : CleanLockDrain)
    (hset : SettledIn tr H g w i₀ m c) (hwit : AcquiredPath tr H proposer Gp w i₀ m c)
    (hcl : ClientProgress tr H i₀ m c) (jA : Nat) (hjA : FirstCutAfter tr jA (w + A_HS sp ΔF Gp)) :
    PhaseChanged tr.projFG H i₀ jA := by
  obtain ⟨s, h, E, W, kW, hpath, hrep⟩ :=
    (acquiredPath_iff_exists tr H proposer Gp w i₀ m c).1 hwit
  have hrows := historical_source_rows hrun hs hc hp hset hcl hpath hrep
  obtain ⟨h1, -, hW, hWs, hpH, hE, -, hws, hr, hvD, -, hbr⟩ := hpath
  by_contra hnc
  exact consume_continue_of hrun hs hc hp hret hclean hset hcl h1 hW hWs hpH hE hws hr hvD
    hbr.2.2 hrows hjA (phaseOn_of_not_changed hrun hs hset hnc)

end Contract

end Consensus.Goldilocks.Healing

end
