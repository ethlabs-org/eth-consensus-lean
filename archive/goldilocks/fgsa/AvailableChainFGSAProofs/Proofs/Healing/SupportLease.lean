module
public import AvailableChainFGSARun.Proofs.AncestorDeadlinesStore
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel
public import AvailableChainFGSAProofs.Proofs.Healing.SupportGate
public import AvailableChainFGSAProofs.Proofs.Healing.SupportHeads

-- ROOT-DIGEST-2: private matcher copy; equality is checked by the kernel (BUILD B3).
namespace AvailableChain.FGSA
open AvailableChain.Generic AvailableChain.SimplexFG

private def hygiene_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

private theorem hygiene_admitBlock_eq : @admitBlock = @hygiene_admitBlock := rfl

end AvailableChain.FGSA

public section

/-! H-SUPPORT H.2 lease premise (plan §3, §4 steps 5–7; G5, G8). Each live lease at an
honest HEAD read after s+1 is compatible with a fast-written B. The private helpers
restate private helpers of Foundations/Leases.lean, which this lane may not import (B27). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Fast support services are restricted to one source label and one interval. -/
structure FastSupportScope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (s : Slot) (v : Time) (x : V) : Prop where
  source : ∀ ix, IsGateTick p c rho ix x s → enabledGateAt p c E rho ix x s
  first : ∀ ix iy y, y ∈ rho.honest →
    IsGateTick p c rho ix x s →
    rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    SA.voteTime p.toParams (s + 1) ≤ v →
    enabledGateAt p c E rho ix x s →
    joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
    FirstTransferScope E rho ix iy x y s
  next : ∀ w, s + 1 ≤ w → SA.voteTime p.toParams (w + 1) ≤ v →
    ∀ iy y, y ∈ rho.honest →
    rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (w + 1))) →
    joinedAt p E rho y (w + 1) (SA.voteTime p.toParams (w + 1)) →
    NextTransferScope E rho iy y w
  gates : ∀ w, s + 1 ≤ w → SA.gateTime p.toParams w ≤ v →
    ∀ j y, y ∈ rho.honest → IsGateTick p c rho j y w →
    enabledGateAt p c E rho j y w →
    ∀ B, GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)) w B →
    SupportGateScope E rho j y w
  carriers : ∀ w, s + 1 ≤ w →
    ∀ iy y t, t ≤ v → HealingCarriersAt E rho w iy y t
  sameLabel : SameLabelServiceScope E rho s

/-- Restricting the interval keeps the same object services and exact epochs. -/
theorem FastSupportScope.cut_mono {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {s : Slot} {u v : Time} {x : V} (h : FastSupportScope E rho s v x) (huv : u ≤ v) :
    FastSupportScope E rho s u x :=
  ⟨h.source, fun ix iy y hy hi hj ht hg hJ =>
      h.first ix iy y hy hi hj (ht.trans huv) hg hJ,
    fun w hw ht => h.next w hw (ht.trans huv),
    fun w hw ht => h.gates w hw (ht.trans huv),
    fun w hw iy y t ht => h.carriers w hw iy y t (ht.trans huv), h.sameLabel⟩

/-- The first-transfer adapter uses the actual joined read and bounded endpoint. -/
theorem FastSupportScope.firstOn {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {s : Slot} {v : Time} {x : V} (h : FastSupportScope E rho s v x)
    (ix iy : Nat) (y : V) (hy : y ∈ rho.honest)
    (hi : IsGateTick p c rho ix x s)
    (hj : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (ht : SA.voteTime p.toParams (s + 1) ≤ v)
    (hJoin : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1))) :
    FirstTransferScope E rho ix iy x y s :=
  h.first ix iy y hy hi hj ht (h.source ix hi) hJoin

/-- Recovery produces label-local service, including a prefix with no gate demand. -/
theorem healing_recovery_same_label [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (s : Slot)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) : SameLabelServiceScope E rho s := by
  have hV := hrec.base.valid
  by_cases hh : SA.gateTime p.toParams s ≤ rho.horizon
  · apply fgsa_sameLabel_serviceScope E rho hV hrec.base.restartsAtWakes hrec.base.delta
    have hd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
      rw [hrec.base.delta]
      change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]
    exact Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
      hrec.sync (fgsaDelay_nonrow E.Δ _) hSync hd hh
  · have noGate : ∀ i x, ¬ enabledGateAt p c E rho i x s := by
      intro i x hg
      exact hh (hV.in_horizon _ (List.mem_of_getElem? hg.1)).2
    refine ⟨?_, ?_, ?_⟩
    · intro i x hg
      exact (noGate i x hg).elim
    · intro i x hg
      exact (noGate i x hg).elim
    · intro ia ib x y hx hy hia
      exact (noGate ia x hia).elim

private def lease_source (st : State p.n) (t : Time) (row : Block × Nat × Time) : Prop :=
  ∃ s B, t = SA.gateTime p.toParams s ∧
    let pre := clockPre p st t
    GridCO.savedGenuine pre.base s = none ∧
    SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s = some B ∧
    (actView pre).obligations.any (fun r => !Block.compatible r.1 B) = false ∧
    Block.Preceq row.1 B ∧
    (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView pre) s B ∧ row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams

private theorem lease_rows_admitRows (rows : List (RowWire p.n)) (st : State p.n) :
    (rows.foldl (admitRow p) st).base.obligations = st.base.obligations := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    rw [List.foldl_cons, ih]
    rcases admitRow_eq p st a with h | h <;> rw [h]

private theorem lease_rows_process (st : State p.n) (o : Wire p.n) :
    (process p st o).base.obligations ⊆ st.base.obligations := by
  change (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | none => st).base.obligations ⊆ st.base.obligations
  cases o.decode with
  | none => exact List.Subset.refl _
  | some a =>
    cases a <;> dsimp only
    case vote s i b => rw [admitHead_obligations]
    case row i body =>
      rcases admitRow_eq p st ⟨o.auth, body⟩ with h | h <;> rw [h]
    case block s N =>
      cases hn : namedParentHeld st N with
      | false => rw [admitBlock_refused p st s N (Or.inl hn)]
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
        | some P =>
          cases ha : blockAccepted p st s N P with
          | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
          | true =>
            rw [hygiene_admitBlock_eq]
            unfold hygiene_admitBlock
            simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
            rw [hp]
            dsimp only
            rw [ha, ite_eq_left rfl, lease_rows_admitRows]
            split
            · dsimp only
              rw [admitProposal_obligations_slow]
            · rw [reconcile_obligations]
              intro row hr
              have hm := (List.mem_filter.mp hr).1
              rwa [admitProposal_obligations_slow] at hm

private theorem lease_rows_clock (st : State p.n) (t : Time) (row : Block × Nat × Time)
    (hm : row ∈ (clock p st t).base.obligations) :
    row ∈ st.base.obligations ∨ lease_source st t row := by
  change row ∈ (if isGateTime p t then
    gateStep p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    else clockPre p st t).base.obligations at hm
  split at hm
  · rename_i ht
    let s := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    let pre := clockPre p st t
    have htime : t = SA.gateTime p.toParams s := by
      exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
    cases hs : GridCO.savedGenuine pre.base s with
    | some saved =>
      rw [gateStep_saved p pre s (by rw [hs]; rfl), normalizeS_fields] at hm
      exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)
    | none =>
      by_cases hj : joinedNow p pre = true
      swap
      · rw [gateStep_unjoined_eq p pre s hs (Bool.eq_false_of_ne_true hj), normalizeS_fields]
          at hm
        change row ∈ pre.base.obligations at hm
        exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)
      have he : (gateStep p pre s).base.obligations =
          (SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) (actView pre) s).obligations := by
        unfold gateStep
        rw [normalizeS_fields]
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false,
          hj, Bool.not_true]
        rfl
      rw [he] at hm
      cases hc : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s with
      | none =>
        unfold SA.Root.gateFrom GridCO.gateFrom at hm
        rw [show GridCO.confirmationFrom p.toParams.engine
          (eraseFG pre.fg.F) (actView pre) s = none from hc] at hm
        exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)
      | some B =>
        cases hg : (actView pre).obligations.any (fun r => !Block.compatible r.1 B) with
        | true =>
          unfold SA.Root.gateFrom GridCO.gateFrom at hm
          rw [show GridCO.confirmationFrom p.toParams.engine
            (eraseFG pre.fg.F) (actView pre) s = some B from hc] at hm
          dsimp only at hm
          rw [hg, ite_eq_left rfl] at hm
          exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)
        | false =>
          have he := @gateFrom_eq_writeKeys_fgsa p.toParams p.n
            (eraseFG pre.fg.F) (actView pre) s B hc hg
          change SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) (actView pre) s = _ at he
          rw [he] at hm
          rcases writeKeys_row_cases _ _ _ row hm with hold | ⟨hk, hd⟩
          · exact Or.inl ((clockPre_obligations_sublist p st t).subset hold)
          · have hkey := hk
            obtain ⟨A, hA, hmap⟩ := List.mem_flatMap.mp hk
            obtain ⟨g, _, heq⟩ := List.mem_map.mp hmap
            have hAB : A = row.1 := congrArg Prod.fst heq
            have hpre := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hA).2).2
            rw [hAB] at hpre
            exact Or.inr ⟨s, B, htime, hs, hc, hg, hpre, hkey, hd⟩
  · exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)

private theorem lease_gate_result (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {s : Slot} {B : Block}
    (ht : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)))
    (hGuard : enabledGateAt p c E rho j x s)
    (hc : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (V2.D.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (V2.D.Run.stateBefore E rho j x).st
        (SA.gateTime p.toParams s))) s = some B) :
    gateResultAt p c E rho j = some (some B) := by
  rw [gateResultAt_eq_gateResult p c E rho hs ht, gateResult_eq_saved p c E rho hs ht]
  have hsaved := fgsa_gate_saved_result E rho hs ht
    (fgsa_gate_joined_of_enabled E rho hGuard)
  rw [clockPre_fg] at hc
  exact hsaved.trans (congrArg some hc)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:689–699; plan H-SUPPORT §3.
DC: SAME a clock step at a time that is not a gate time writes no lease row. -/
theorem healing_lease_clock_nongate (st : State p.n) (t : Time)
    (ht : ∀ w : Slot, t ≠ SA.gateTime p.toParams w) (row : Block × Nat × Time)
    (hm : row ∈ (clock p st t).base.obligations) : row ∈ st.base.obligations := by
  rcases lease_rows_clock st t row hm with h | ⟨w, _, htime, _⟩
  · exact h
  · exact absurd htime (ht w)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Two grid times with integer coefficients agree only for equal coefficients. -/
private theorem lease_time_cancel {a b : Int} (h : a * p.Δ = b * p.Δ) : a = b :=
  Int.eq_of_mul_eq_mul_right (ne_of_gt p.deltaPos) h

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Two ticks of one node are in time order exactly when they are in index order. -/
private theorem lease_idx_lt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {a b : Nat} {y : V} {ta tb : Time}
    (ha : rho.events[a]? = some (.tick y ta)) (hb : rho.events[b]? = some (.tick y tb))
    (hlt : ta < tb) : a < b := by
  rcases lt_trichotomy a b with h | h | h
  · exact h
  · subst h
    rw [ha] at hb
    cases hb
    exact absurd hlt (lt_irrefl _)
  · exact absurd (fgsa_tick_time_strict E rho hs hb ha h) (not_lt.mpr hlt.le)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:689–699 (lease survival), IF.1; plan H-SUPPORT §3.
DC: SAME a lease row whose deadline names gate w, and whose gate tick is before index a,
is present at every index between a and a later index that holds it. No later step can
write the same row again. -/
theorem healing_lease_persist (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j a b : Nat} {x : V} {w : Slot}
    (ht : IsGateTick p c rho j x w) (hja : j < a) (hab : a ≤ b)
    (row : Block × Nat × Time)
    (hd : row.2.2 = SA.gateTime p.toParams w + SA.lifetime p.toParams)
    (hb : row ∈ (storeAt p c E rho b x).base.obligations) :
    row ∈ (storeAt p c E rho a x).base.obligations := by
  by_contra hna
  let Q := fun nd : Node p => row ∉ nd.st.base.obligations
  have h := V2.D.Engine.stateBefore_step_induction E rho Q hab x ?_ hna
  · exact h hb
  intro k e hak _ he hv hQ
  cases e with
  | restart y t =>
    change y = x at hv
    subst y
    simp only [Q, V2.D.World.step, Function.update_self]
    change row ∉ (acRestart p (rho.stateBefore E k x).st t).base.obligations
    rw [acRestart_obligations]
    exact hQ
  | deliver y o t =>
    change y = x at hv
    subst y
    simp only [Q, V2.D.World.step, Function.update_self]
    intro hr
    exact hQ (lease_rows_process _ (toWire p o) hr)
  | tick y t =>
    change y = x at hv
    subst y
    simp only [Q, V2.D.World.step, Function.update_self]
    intro hr
    rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t] at hr
    rcases lease_rows_clock _ t row hr with hold | ⟨w', C, htime, _, _, _, _, _, hd'⟩
    · exact hQ hold
    · have hlt := fgsa_tick_time_strict E rho hs ht he (by omega)
      have hw : SA.gateTime p.toParams w' = SA.gateTime p.toParams w := by
        rw [hd] at hd'
        exact (add_right_cancel hd').symm
      rw [htime, hw] at hlt
      exact lt_irrefl _ hlt

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:620–650 (H.4 fast body); plan H-SUPPORT §4 step 1.
DC: INTENTIONAL the decoded fast body. The source gate has a raw confirmation h ⪰ B, and
B passes the fast threshold in the source gate view. -/
theorem healing_fast_source (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {B : Block} {x : V} {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    (hGuard : ∀ ix, rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)) →
      enabledGateAt p c E rho ix x s) :
    ∃ ix h, rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      gateResult p c E rho x s = some (some h) ∧ Block.Preceq B h ∧
      SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s B := by
  classical
  rw [postClock_def, preTick_def] at hnd
  cases hix' : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none => rw [hix'] at hnd; cases hnd
  | some ix =>
  rw [hix'] at hnd
  have hix := V2.D.Run.tickIdx?_spec hix'
  have hnd' := Option.some.inj hnd
  subst hnd'
  rw [healing_support_fastWrite p c E rho hs hix
    (fgsa_gate_joined_of_enabled E rho (hGuard ix hix))] at hB
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  unfold fastSet at hB
  cases hconf : SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p c E rho ix x).fg.F) src
      s with
  | none => rw [hconf] at hB; exact absurd hB List.not_mem_nil
  | some h =>
  rw [hconf] at hB
  dsimp only at hB
  split at hB
  · exact absurd hB List.not_mem_nil
  obtain ⟨_, hb⟩ := List.mem_filter.mp hB
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨_, hBh⟩, hτ⟩ := hb
  refine ⟨ix, h, hix, ?_, hBh, hτ⟩
  rw [gateResult_eq_saved p c E rho hs hix]
  exact (fgsa_gate_saved_result E rho hs hix
    (fgsa_gate_joined_of_enabled E rho (hGuard ix hix))).trans (congrArg some hconf)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:689–715 (H.1 release, H.2 S1), IF.1, IF.6; plan H-SUPPORT §4 steps
5–8,
G5, G7, G8. DC: INTENTIONAL the lease invariant for a fast body. A row at an honest read
after the q_(s+1) tick has its last write at a gate w before the read. If w < s, the row
was live at the q_(s+1) release, which removes rows that conflict with B (G5). If w = s,
same-label compatibility with the source result applies. If w > s, the honest batch of
label w makes the gate result cover B. `writes` is the S3 hypothesis (B27, inline). -/
theorem healing_fast_lease_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {s : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hgs : SA.gateTime p.toParams s ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    {T : Time} (hTh : T ≤ rho.horizon)
    (hScopes : FastSupportScope E rho s T x)
    (hCut : E.t_GST ≤ slotStartZ p (s : Int))
    (hcov : ∀ w, s + 1 ≤ w → SA.gateTime p.toParams w ≤ T → ∀ z ∈ rho.honest, ∀ K,
      headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {a iq : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiq : rho.events[iq]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hqa : iq < a)
    (hT : ∀ j t, j < a → rho.events[j]? = some (.tick y t) → t ≤ T)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho a y).fg.F) B) :
    ∀ row ∈ (storeAt p c E rho a y).base.obligations, Block.Compatible row.1 B := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hFmono {a b : Nat} (hab : a ≤ b) (hFb : Block.Preceq
      (eraseFG (storeAt p c E rho b y).fg.F) B) :
      Block.Preceq (eraseFG (storeAt p c E rho a y).fg.F) B :=
    Gen.Pure.block_preceq_trans (eraseFG_preceq (mono a b y hy hab).1) hFb
  have hcompat {A C : Block} (hAC : Block.Preceq A C) (hCB : Block.Compatible C B) :
      Block.Compatible A B := by
    rcases Bool.or_eq_true_iff.mp hCB with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_preceq_trans hAC h))
    · exact Gen.Pure.block_compatible_of_common hAC h
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hgs
  intro row hr0
  obtain ⟨j, hj, w, C, ht, _, hres, hrowC, _, hdl, _, _⟩ := writes a y row hr0
  rcases lt_trichotomy (w : Nat) (s : Nat) with hws | hws | hws
  · -- An old lease survives the q_(s+1) release (G5).
    have hjq : j < iq := lease_idx_lt E rho hS ht hiq (by
      change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      have : (w : Int) + 1 ≤ (s : Int) := by exact_mod_cast hws
      push_cast
      nlinarith)
    have hkeep := healing_lease_persist E rho hS ht (Nat.lt_succ_of_lt hjq) hqa row hdl hr0
    have hpost : storeAt p c E rho (iq + 1) y =
        FGSA.clock p (storeAt p c E rho iq y) (SA.voteTime p.toParams (s + 1)) := by
      change (V2.D.Run.stateBefore E rho (iq + 1) y).st = _
      rw [V2.D.Run.stateBefore_succ E rho hiq]
      simp only [V2.D.World.step, Function.update_self]
      exact tick_st (c := c) E rho _ y _
    rw [hpost] at hkeep
    obtain ⟨ix, h, hix, _, _, hτ⟩ := healing_fast_source (c := c) E rho hS hnd hB hScopes.source
    exact healing_support_release_compat (hroots := hrec.base.receiptIdealization)
      E rho hE hDelta s hSync hx hy hix hiq (hScopes.firstOn ix iq y hy hix hiq (hT iq _ hqa hiq)
        (healing_recovery_next_vote_joined_of_cut E rho hrec hCut hy hiq)) hτ
      (hFmono hqa.le hFB) row hkeep
  · -- The same label as the source gate.
    have hws' : w = s := hws
    subst hws'
    obtain ⟨ix, h, _, hxh, hBh, _⟩ := healing_fast_source (c := c) E rho hS hnd hB hScopes.source
    have hyC : gateResult p c E rho y w = some (some C) :=
      (gateResultAt_eq_gateResult p c E rho hS ht).symm.trans hres
    have hhC := fgsa_sameLabel_on p c E rho hE w hScopes.sameLabel hrec.base.idealization
        x y h C hx hy hxh hyC
    refine hcompat hrowC ?_
    rcases Bool.or_eq_true_iff.mp hhC with hh | hh
    · exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_trans hBh hh))
    · exact Gen.Pure.block_compatible_of_common hh hBh
  · -- A later label: the honest batch of label w makes the gate result cover B.
    have hgw : E.t_GST ≤ SA.voteTime p.toParams w := by
      refine hgst.trans ?_
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
      have : (s : Int) ≤ (w : Int) := by exact_mod_cast hws.le
      nlinarith
    have hwT := hT j _ hj ht
    have hFw : Block.Preceq (eraseFG (clockPre p (storeAt p c E rho j y)
        (SA.gateTime p.toParams w)).fg.F) B := by
      rw [clockPre_fg]
      exact hFmono hj.le hFB
    have hw1 : (s : Int) + 1 ≤ (w : Int) := by
      have : (s : Int) < (w : Int) := by exact_mod_cast hws
      omega
    obtain ⟨C', hC', hBC'⟩ := healing_support_gate_cover E rho hrec hgw
      (hwT.trans hTh)
      (hcov w (by exact_mod_cast hw1) hwT) ht
      ((hScopes.gates w (by exact_mod_cast hw1) hwT) j y hy ht
        (healing_gate_enabled_of_result E rho hS ht hres) B
        (healing_support_gate_geometry E rho hS (hcov w (by exact_mod_cast hw1) hwT) hFw)) hFw
    have hCC : C = C' := by
      have h2 := lease_gate_result (c := c) E rho hS ht
        ((hScopes.gates w (by exact_mod_cast hw1) hwT) j y hy ht
        (healing_gate_enabled_of_result E rho hS ht hres) B
        (healing_support_gate_geometry E rho hS (hcov w (by exact_mod_cast hw1) hwT)
          hFw)).enabled hC'
      rw [hres] at h2
      exact Option.some.inj (Option.some.inj h2)
    subst hCC
    exact hcompat hrowC (Bool.or_eq_true_iff.mpr (Or.inr hBC'))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:689–715 (H.1 release, H.2 S1); plan H-SUPPORT §4 steps 5–7, G5, G8.
DC: INTENTIONAL the lease premise of the H.2 step for a fast body, at the q_(i+1) read:
`healing_fast_lease_at` with the bound q_(i+1); the clock at q_(i+1) writes no row. -/
theorem healing_fast_lease [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {s : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    {i : Slot} (hi : s + 1 ≤ i) (hvh : SA.voteTime p.toParams (i + 1) ≤ rho.horizon)
    (hScopes : FastSupportScope E rho s (SA.voteTime p.toParams (i + 1)) x)
    (hCut : E.t_GST ≤ slotStartZ p (s : Int))
    (hcov : ∀ w, s + 1 ≤ w → w ≤ i → ∀ z ∈ rho.honest, ∀ K,
      headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B) :
    ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hiI : (s : Int) + 1 ≤ (i : Int) := by exact_mod_cast hi
  intro row hrow
  rcases lease_rows_clock _ _ row hrow with hr0 | ⟨w', _, htime, _⟩
  swap
  · exfalso
    have h : (4 * ((i + 1 : Nat) : Int) + 1) * p.Δ = (4 * (w' : Int) + 6) * p.Δ := by
      change 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (w' : Int) + 6 * p.Δ at htime
      linarith
    have := lease_time_cancel h
    omega
  have hqh : SA.voteTime p.toParams (s + 1) ≤ rho.horizon := by
    refine le_trans ?_ hvh
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    nlinarith
  have hgs : SA.gateTime p.toParams s ≤ rho.horizon := by
    refine le_trans ?_ hvh
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    nlinarith
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hy (s + 1) hqh
    (hrec.awake y hy _ (by
      refine hgst.trans ?_
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      push_cast
      nlinarith) hqh)
  have hqy : iq < iy := lease_idx_lt E rho hS hiq hiy (by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    nlinarith)
  refine healing_fast_lease_at E rho hrec mono writes hgst hgs hx hnd hB hvh hScopes hCut ?_
    hy hiq hqy
    (fun j t hj ht => (fgsa_tick_time_strict E rho hS ht hiy hj).le) hFB row hr0
  intro w hw hwT
  refine hcov w hw ?_
  have h : (4 * (w : Int) + 6) * p.Δ ≤ (4 * ((i + 1 : Nat) : Int) + 1) * p.Δ := by
    change 4 * p.Δ * (w : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ at hwT
    linarith
  have h2 : 4 * (w : Int) + 6 ≤ 4 * ((i + 1 : Nat) : Int) + 1 := le_of_mul_le_mul_right h hd
  push_cast at h2
  exact_mod_cast (show (w : Int) ≤ i by omega)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:620–715 (H.1 + H.2 S1, fast arm); plan H-SUPPORT §4 steps 1–7.
DC: INTENTIONAL the S1 HEAD clause of Transfers for a fast PhaseBody arm. The lease
premise of each H.2 step comes from `healing_fast_lease` and the earlier labels. -/
theorem healing_fast_heads [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    (hScopes : FastSupportScope E rho s v x)
    (hCut : HealingWindow p E 1 s) :
    ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K := by
  have hd := p.deltaPos
  have hvmono {a b : Slot} (hab : (a : Int) ≤ (b : Int)) :
      SA.voteTime p.toParams a ≤ SA.voteTime p.toParams b := by
    change 4 * p.Δ * (a : Int) + p.Δ ≤ 4 * p.Δ * (b : Int) + p.Δ
    nlinarith
  have hs0 : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg _
  suffices h : ∀ n : Nat, ∀ i : Slot, s + 1 ≤ i → (i : Int) ≤ (s : Int) + 1 + n →
      SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K by
    intro i hi
    exact h i i hi (by have : (0 : Int) ≤ (i : Int) := Int.natCast_nonneg _; omega)
  intro n
  induction n with
  | zero =>
    intro i hi hin hv z hz K hK
    have hiI : (s : Int) + 1 ≤ (i : Int) := by exact_mod_cast hi
    have hi' : i = s + 1 := by
      exact_mod_cast (show (i : Int) = (s : Int) + 1 by push_cast at hin; omega)
    subst hi'
    exact healing_first_transfer_fast E rho hrec.toRecovery₂ (fun _ => mono) crossing
      hgst hphase hhead hgate hx hnd hB hz hv
      (fun ix iy hi hj => hScopes.firstOn ix iy z hz hi hj hv
        (healing_recovery_joined_next E rho hrec hCut hz
          (by change 4 * p.Δ * (s : Int) + p.Δ ≤
                4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
              push_cast; linarith [p.deltaPos]) (hv.trans hphase.2.1))) hK
  | succ n ih =>
    intro i hi hin hv z hz K hK
    have hiI : (s : Int) + 1 ≤ (i : Int) := by exact_mod_cast hi
    by_cases hlow : (i : Int) ≤ (s : Int) + 1 + n
    · exact ih i hi hlow hv z hz K hK
    have hpos : 0 < i := by exact_mod_cast (show (0 : Int) < (i : Int) by omega)
    obtain ⟨i', rfl⟩ : ∃ i' : Slot, i = i' + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hlow' : (s : Int) + 1 ≤ (i' : Int) := by push_cast at hlow hin; omega
    have hi' : s + 1 ≤ i' := by exact_mod_cast hlow'
    have hcov : ∀ w, s + 1 ≤ w → w ≤ i' → ∀ z ∈ rho.honest, ∀ K,
        headAtLabel p c E rho z w = some K → Block.Preceq B K := by
      intro w hw1 hw2
      have hw2I : (w : Int) ≤ (i' : Int) := by exact_mod_cast hw2
      refine ih w hw1 (by push_cast at hin; omega) ?_
      exact (hvmono hw2I).trans ((hvmono (by push_cast; omega)).trans hv)
    unfold headAtLabel at hK
    rw [postClock_def, preTick_def] at hK
    cases hiz' : V2.D.Run.tickIdx? rho z (SA.voteTime p.toParams (i' + 1)) with
    | none => rw [hiz'] at hK; cases hK
    | some iz =>
    rw [hiz'] at hK
    have hiz := V2.D.Run.tickIdx?_spec hiz'
    have hKeq := Option.some.inj hK
    subst hKeq
    have hsi : SA.voteTime p.toParams s ≤ SA.voteTime p.toParams i' := hvmono (by omega)
    exact healing_next_transfer_core E rho hrec (fun _ => mono) crossing
      hgst hphase (hhead.trans hsi)
      (hcov i' hi' le_rfl) hz hiz
      (hScopes.next i' hi' hv iz z hz hiz
        (healing_recovery_joined_next E rho hrec (hCut.cut_mono ((Nat.le_succ s).trans hi')) hz
          (by change 4 * p.Δ * (i' : Int) + p.Δ ≤
                4 * p.Δ * ((i' + 1 : Nat) : Int) + p.Δ
              push_cast; linarith [p.deltaPos]) (hv.trans hphase.2.1)))
      (hCut.cut_mono ((Nat.le_succ s).trans hi')) hv
      (healing_fast_lease E rho hrec mono writes (hgst.trans hhead) hx hnd hB hi'
        (hv.trans hphase.2.1) (hScopes.cut_mono hv)
        (healing_gate_cut_of_batch_cut E s hCut.2) hcov hz hiz)

end AvailableChain.FGSA.Run
end
