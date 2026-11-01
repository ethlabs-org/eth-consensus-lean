module
public import AvailableChainFGSAProofs.Proofs.Shared.Gate
public import AvailableChainFGSAProofs.Proofs.Shared.KeepExact

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem openingSource_fastWriteAt_eq {n : Nat} (st : State n) (s : Slot) :
    fastWriteAt st s = (st.fastWrite.find? (fun row => row.1 == s)).map Prod.snd := rfl

set_option maxHeartbeats 800000 in
-- The adapter compares the nested gate, clock, and tick state projections.
/-- 6c / F1b.9, R15; 21 H.17 and 22 FF1: service at the opening gate
supplies the action's fresh candidate. DC: RecoveryCapturedActionCarrier.lean:30,
`actionStoreAt_eq_update_confirmation_confStore`. INTENTIONAL: FG-SA reads
the scheduled fast-write set with a live lease, with no root fallback
(spec 1472–1483). The gate and action share one clock step, so no restart,
reconcile, or release step occurs between them. No new run premise is used. -/
theorem openingSource_candidate_of_gateService (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (r : Nat) (D : Block)
    (ht : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hEnabled : enabledGateAt p c E rho i x (r * p.R))
    (hservice : Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x D) :
    D ∈ sourceCandidates p (((fgsa p c).clock
      (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st) := by
  have hlive : p.actionTime r < SA.gateTime p.toParams (r * p.R) + SA.lifetime p.toParams := by
    have hp : 0 < SA.lifetime p.toParams := by
      change 0 < (4 * (p.k : Time) - 1) * p.Δ
      have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
      have hpos : 0 < 4 * (p.k : Time) - 1 := by linarith
      exact mul_pos hpos p.deltaPos
    change SA.gateTime p.toParams (r * p.R) < _
    exact lt_add_of_pos_right _ hp
  let nd : Node p := V2.D.Run.stateBefore E rho i x
  let st := ((fgsa p c).clock nd (p.actionTime r)).st
  have hf := fgsa_gate_fresh E rho hs ht
  have hinv := (storeBundle_postClock E rho i x (p.actionTime r)).cstore
  obtain ⟨C, _, _, _, hfast, d, hd, hlease⟩ := hservice
  have hpost : (V2.D.Run.stateBefore E rho (i + 1) x).st = st := by
    rw [V2.D.Run.stateBefore_succ E rho ht]
    simp only [V2.D.World.step, Function.update_self]
    exact tick_st (c := c) E rho nd x (p.actionTime r)
  change (D, SA.releaseThreshold p.toParams, d) ∈
    (V2.D.Run.stateBefore E rho (i + 1) x).st.base.obligations at hlease
  rw [hpost] at hlease
  have hfastEq : st.fastWrite =
      nd.st.fastWrite ++ [(r * p.R, (fgsaAC E rho).fast i (r * p.R) x)] := by
    have hb := congrArg State.fastWrite (fgsa_gate_clock_bridge E rho hs ht
      (fgsa_gate_joined_of_enabled E rho hEnabled))
    rw [normalizeS_fields] at hb
    change st.fastWrite = nd.st.fastWrite ++ [(r * p.R,
      fastSet p (eraseFG nd.st.fg.F)
        (actView (clockPre p nd.st (p.actionTime r))) (r * p.R))] at hb
    have hf' : GridCO.savedGenuine (clockPre p nd.st (p.actionTime r)).base (r * p.R) = none := by
      unfold GridCO.savedGenuine
      rw [clockPre_genuine]
      exact hf
    have hr : (fgsaAC E rho).fast i (r * p.R) x =
        fastSet p (eraseFG nd.st.fg.F)
          (actView (clockPre p nd.st (p.actionTime r))) (r * p.R) := by
      change (if (GridCO.savedGenuine (clockPre p nd.st (p.actionTime r)).base
        (r * p.R)).isSome then [] else _) = _
      rw [hf']
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false, clockPre_fg]
      rfl
    rw [hr]
    exact hb
  have hrow : (r * p.R, (fgsaAC E rho).fast i (r * p.R) x) ∈ st.fastWrite := by
    rw [hfastEq]
    exact List.mem_append_right _ (by simp)
  have hfind : st.fastWrite.find? (fun row => row.1 == r * p.R) =
      some (r * p.R, (fgsaAC E rho).fast i (r * p.R) x) := by
    cases he : st.fastWrite.find? (fun row => row.1 == r * p.R) with
    | none => have hn := List.find?_eq_none.mp he _ hrow; simp at hn
    | some row =>
      have hk : row.1 = r * p.R := by simpa using List.find?_some he
      have heq := List.inj_on_of_nodup_map hinv.fastDom.1
        (List.mem_of_find?_eq_some he) hrow hk
      exact congrArg some heq
  have hleaseFind : st.base.obligations.find? (fun row => row.1 == D) =
      some (D, SA.releaseThreshold p.toParams, d) := by
    cases he : st.base.obligations.find? (fun row => row.1 == D) with
    | none => have hn := List.find?_eq_none.mp he _ hlease; simp at hn
    | some row =>
      have hk : row.1 = D := by simpa using List.find?_some he
      have heq := List.inj_on_of_nodup_map hinv.leaseKeys.1
        (List.mem_of_find?_eq_some he) hlease hk
      exact congrArg some heq
  change D ∈ sourceCandidates p st
  rw [sourceCandidates_def, (fgsa_action_slot_round nd r).2]
  apply Finset.mem_filter.mpr
  constructor
  · rw [openingSource_fastWriteAt_eq]
    simpa only [hfind, Option.map_some, Option.getD_some, List.mem_toFinset] using hfast
  · change ((st.base.obligations.find? (fun row => row.1 == D)).map
      (fun row => row.2.2)).any (fun d => decide (st.base.now < d)) = true
    rw [hleaseFind]
    simp only [Option.map_some, Option.any_some, decide_eq_true_eq]
    have hn := (fgsa_postClock_slot (c := c) nd (p.actionTime r)).1
    change st.base.now = p.actionTime r at hn
    rw [hn]
    exact lt_of_lt_of_le hlive hd

/-- The domain branch of F1b.8 G31, for an active body above both covered
roots. DC: no direct FJ duty-domain counterpart. INTENTIONAL: the FJ
filtered domain and its cause alternatives are from 21 H.13–H.14 / S1c P6.
The phase caller rules out the conflicting-source cause; the floor witness excludes the split
cause. This does not identify `Kept`
with membership: its two covered-root alternatives must also be excluded. -/
theorem openingSource_domain_of_kept_or_cause
    (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n))) (D W : FGBlock (Fin p.n))
    (hD : D ∈ X) (hW : W ∈ X) (hDW : FGBlock.Preceq D W)
    (hlo : (R_at p c E rho i x).lo ≤ hOf p.E p.cfg W)
    (hcontrolSource : ∀ K ∈ [(storeAt p c E rho i x).fg.F, (R_at p c E rho i x).Z],
      ¬ (FGBlock.Preceq K D ∨ FGBlock.Preceq D K) →
      ∃ C s, SourceBefore p c E rho i C s ∧
        FGBlock.Preceq K C ∧ hOf p.E p.cfg D ≤ hOf p.E p.cfg C)
    (hnotZ : ¬ FGBlock.Preceq D (R_at p c E rho i x).Z)
    (hnotF : ¬ FGBlock.Preceq D (storeAt p c E rho i x).fg.F)
    (hnoConflict : ∀ C s, SourceBefore p c E rho i C s →
      hOf p.E p.cfg D ≤ hOf p.E p.cfg C → Block.Compatible (eraseFG D) (eraseFG C)) :
    D ∈ D_at p c E rho i x X := by
  have h := kept_or_conflict p c E rho i x X D W hD hW hDW hlo hcontrolSource
  rcases h with hkeep | ⟨C, s, hsrc, hbad, hheight⟩
  · rcases hkeep with hZ | hm | hF
    · exact (hnotZ hZ).elim
    · exact hm
    · exact (hnotF hF).elim
  · exact (hbad (hnoConflict C s hsrc hheight)).elim

private theorem opening_pair (Λ : Record) (h : Height) (T : BlockId)
    (fp : Option FinalityPair)
    (hpermit : Λ.timeout h = true ∨ own_lock Λ h fp = none ∨ own_lock Λ h fp = some T) :
    namedEntry (height_pair Λ (some (h, T)) fp) = some (h, T) := by
  change namedEntry (if Λ.timeout h then .vote h T true else
    match own_lock Λ h fp with
    | some locked => if locked = T then .vote h T false else .empty
    | none => match Λ.target h with
      | some recorded => if recorded = T then .vote h T false else .vote h T true
      | none => .vote h T false) = _
  by_cases ht : Λ.timeout h = true
  · rw [ht, ite_eq_left (rfl : true = true), namedEntry_def]
  · have ht' : Λ.timeout h = false := Bool.eq_false_of_not_eq_true ht
    rw [ht', ite_eq_right Bool.false_ne_true]
    rcases hpermit with hf | hn | he
    · exact (ht hf).elim
    · rw [hn]
      cases Λ.target h with
      | none => rw [namedEntry_def]
      | some recorded => by_cases he : recorded = T <;>
          simp only [he, ite_true, ite_false] <;> rw [namedEntry_def]
    · rw [he]
      simp only [ite_true]
      rw [namedEntry_def]

private theorem opening_time_bound (q r : Nat)
    (hle : q ≤ r * p.R) (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r') :
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ := by
  have hlt : r * p.R < q + p.R := by
    by_cases hz : r = 0
    · subst r; have := p.RLarge; omega
    · have hn : ¬ q ≤ (r - 1) * p.R := by intro h; have := hfirst (r - 1) h; omega
      have he : r * p.R = (r - 1) * p.R + p.R := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
  have ha : (q : Time) ≤ (r * p.R : Nat) := by exact_mod_cast hle
  have hb : ((r * p.R : Nat) : Time) ≤ (q : Time) + (p.R : Time) - 1 := by
    have hc : r * p.R + 1 ≤ q + p.R := hlt
    exact_mod_cast (show (r * p.R : Int) ≤ (q : Int) + (p.R : Int) - 1 by omega)
  change 0 ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ -
    (4 * p.Δ * (q : Time) + 6 * p.Δ) ∧
    4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ -
    (4 * p.Δ * (q : Time) + 6 * p.Δ) ≤ 4 * (p.R : Time) * p.Δ - 4 * p.Δ
  have := p.deltaPos
  constructor <;> nlinarith

/-- R15 / S1c P5 covering composition. DC: no direct counterpart for the
FG-SA first-opening fast-write selector. INTENTIONAL: the scheduled set
and lease test are FG-SA-specific (spec 1472–1483). The time premise says
that r is the first opening at or after q. The local domain premise is
the retained branch supplied by `kept_or_cause`; the caller must resolve
its covered-root and cause alternatives. Domain retention is R2 KEEP;
the cap is the frontier cap (S1c P5 Cap(y−1,·)); permission is R16. Permission includes the
timeout branch, so it is
weaker than requiring an absent or matching lock unconditionally.
GateService at rR is a caller premise. It comes from gate_of_coveringBatch (F1b.7) at the opening,
in F4 FF1 / F5 H.9-Q, H.17.
06 send-once: the last conjunct is the client's computed height pair; createRowOnce may still
suppress the row, so no emission is claimed (permission ≠ emission). -/
theorem openingSource_firstOpening (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (q r m : Nat) (D : FGBlock (Fin p.n))
    (ht : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hEnabled : enabledGateAt p c E rho i x (r * p.R))
    (hle : q ≤ r * p.R) (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r')
    (hservice : Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x (eraseFG D)) :
    let nd : Node p := V2.D.Run.stateBefore E rho i x
    let st := ((fgsa p c).clock nd (p.actionTime r)).st
    D ∈ domainR p st (treeT p st) →
    m ≤ hOf p.E p.cfg D + 1 →
    (∀ C ∈ domainR p st (treeT p st), hOf p.E p.cfg C ≤ m) →
    (∀ C ∈ domainR p st (treeT p st), eraseFG C ∈ sourceCandidates p st →
      FGBlock.Preceq D C →
      nd.record.toRecord.timeout (hOf p.E p.cfg C) = true ∨
      own_lock nd.record.toRecord (hOf p.E p.cfg C)
        (finality_pair nd.record.toRecord (fgInputs p st).2) = none ∨
      own_lock nd.record.toRecord (hOf p.E p.cfg C)
        (finality_pair nd.record.toRecord (fgInputs p st).2) =
        some (derive p.E p.cfg C).T_h.root) →
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
    p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
    ∃ C, FGSA.fgSource p st = some C ∧ FGBlock.Preceq D C ∧
      (hOf p.E p.cfg C = hOf p.E p.cfg D ∨ hOf p.E p.cfg C = m) ∧
      (hOf p.E p.cfg C = hOf p.E p.cfg D →
        (derive p.E p.cfg C).T_h = (derive p.E p.cfg D).T_h) ∧
      namedEntry (height_pair nd.record.toRecord
        ((FGSA.fgSource p st).map (fun C => (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root)))
        (finality_pair nd.record.toRecord (fgInputs p st).2)) =
        some (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) := by
  intro nd st hkept hgap hcap hpermit
  have hserved := openingSource_candidate_of_gateService E rho hs i x r
    (eraseFG D) ht hEnabled hservice
  obtain ⟨C, hC, hDC⟩ := openingSource_extends_served E rho i x r D hkept hserved
  have hm := hC
  rw [fgSource_eq_jointSource] at hm
  have hmem := Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hm).1
  have hcand : eraseFG C ∈ sourceCandidates p st := of_decide_eq_true hmem.2
  have hlo := KitFG.h_mono p.E p.cfg hDC
  change hOf p.E p.cfg D ≤ hOf p.E p.cfg C at hlo
  have hhi := hcap C hmem.1
  have hrange : hOf p.E p.cfg C = hOf p.E p.cfg D ∨ hOf p.E p.cfg C = m := by
    rcases Nat.eq_or_lt_of_le hlo with he | hlt
    · exact Or.inl he.symm
    · exact Or.inr (Nat.le_antisymm hhi (by omega))
  refine ⟨(opening_time_bound q r hle hfirst).1, (opening_time_bound q r hle hfirst).2,
    C, hC, hDC, hrange, ?_, ?_⟩
  · intro he
    exact (KitFG.entry_eq_on_plateau p.E p.cfg hDC he.symm).symm
  · rw [hC]
    exact opening_pair nd.record.toRecord _ _ _ (hpermit C hmem.1 hcand hDC)

/-- R15 exact variant, 21 H.17 / H.9-Q / 22 FF1. DC: no direct
counterpart for the FG-SA deepest fresh selector. INTENTIONAL: the
no-strict-extension supplier is precisely the selector condition from
22 FF1:858–862; this lemma composes it with the scheduled gate adapter. -/
theorem openingSource_exact_of_gateService (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (r : Nat) (Q : FGBlock (Fin p.n))
    (ht : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hEnabled : enabledGateAt p c E rho i x (r * p.R))
    (hservice : Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x (eraseFG Q)) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
    Q ∈ domainR p st (treeT p st) →
    (∀ C, C ∈ domainR p st (treeT p st) → eraseFG C ∈ sourceCandidates p st →
      FGBlock.Preceq Q C → C = Q) →
    FGSA.fgSource p st = some Q := by
  intro st hkept hmax
  exact openingSource_eq_of_no_strict_extension E rho i x r Q hkept
    (openingSource_candidate_of_gateService E rho hs i x r (eraseFG Q) ht hEnabled hservice) hmax

/-- The exact R15 composed form. DC: no direct FG-SA first-opening
counterpart. INTENTIONAL: 21 H.17 / H.9-Q and 22 FF1 use the exact
opening proposal and its client permission. Equality supplies its height
and entry without a separate cap premise. The nonempty pair is the actual
local action body; emission remains a separate obligation, including the revised send-once guards.
GateService at rR is a caller premise. It comes from gate_of_coveringBatch (F1b.7) at the opening,
in F4 FF1 / F5 H.9-Q, H.17.
06 send-once: the last conjunct is the client's computed height pair; createRowOnce may still
suppress the row, so no emission is claimed (permission ≠ emission). -/
theorem openingSource_firstOpening_exact (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (q r : Nat) (Q : FGBlock (Fin p.n))
    (ht : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hEnabled : enabledGateAt p c E rho i x (r * p.R))
    (hle : q ≤ r * p.R) (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r')
    (hservice : Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x (eraseFG Q)) :
    let nd : Node p := V2.D.Run.stateBefore E rho i x
    let st := ((fgsa p c).clock nd (p.actionTime r)).st
    Q ∈ domainR p st (treeT p st) →
    (∀ C, C ∈ domainR p st (treeT p st) → eraseFG C ∈ sourceCandidates p st →
      FGBlock.Preceq Q C → C = Q) →
    (nd.record.toRecord.timeout (hOf p.E p.cfg Q) = true ∨
      own_lock nd.record.toRecord (hOf p.E p.cfg Q)
        (finality_pair nd.record.toRecord (fgInputs p st).2) = none ∨
      own_lock nd.record.toRecord (hOf p.E p.cfg Q)
        (finality_pair nd.record.toRecord (fgInputs p st).2) =
        some (derive p.E p.cfg Q).T_h.root) →
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
    p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
    FGSA.fgSource p st = some Q ∧
    namedEntry (height_pair nd.record.toRecord
        ((FGSA.fgSource p st).map (fun C => (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root)))
        (finality_pair nd.record.toRecord (fgInputs p st).2)) =
      some (hOf p.E p.cfg Q, (derive p.E p.cfg Q).T_h.root) := by
  intro nd st hkept hmax hpermit
  have hQ := openingSource_exact_of_gateService E rho hs i x r Q ht hEnabled hservice hkept hmax
  refine ⟨(opening_time_bound q r hle hfirst).1, (opening_time_bound q r hle hfirst).2, hQ, ?_⟩
  rw [hQ]
  exact opening_pair nd.record.toRecord _ _ _ hpermit

end AvailableChain.FGSA.Run
