module
public import AvailableChainFGSAProofs.Proofs.Clean.Chain
public import AvailableChainFGSAProofs.Proofs.Clean.StateEpoch
public import AvailableChainFGSAProofs.Proofs.Clean.StateGate
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSARun.Proofs.ClientTrace
public import AvailableChainFGSARun.Proofs.AC
public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A non-gate event adds no completed result. -/
theorem cleanResults_eq_of_noGate {i : Nat}
    (hn : ∀ x s, ¬ IsGateTick p c rho i x s) :
    cleanResults p c E rho (i + 1) = cleanResults p c E rho i := by
  ext ⟨s, B⟩
  rw [cleanResults_mem_succ_iff]
  constructor
  · rintro (h | ⟨x, hx, _⟩)
    · exact h
    · exact (hn x s hx.1).elim
  · exact Or.inl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
All four history fields persist at a non-gate event. -/
theorem cleanHist_step_of_noGate {i : Nat}
    (hn : ∀ x s, ¬ IsGateTick p c rho i x s)
    (hh : CleanHist p c E rho i) : CleanHist p c E rho (i + 1) := by
  have he := cleanResults_eq_of_noGate (E := E) hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [he] using hh.ordered
  · simpa only [he] using hh.same
  · intro j x s hj hx
    have hji : j < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact h
      · exact (hn x s hx.1).elim
    exact hh.nonempty j x s hji hx
  · intro j k x y s B hj hk hx hy hJ hB
    have hji : j < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact h
      · exact (hn x s hx).elim
    exact hh.continues j k x y s B hji hk hx hy hJ hB

omit [DecidableEq V] in
private theorem delivery_noGate {i : Nat} {v : V} {o} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    ∀ x s, ¬ IsGateTick p c rho i x s := by
  intro x s hx
  change rho.events[i]? = some (.tick x _) at hx
  rw [he] at hx
  cases hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every delivery, including an admitted block, preserves history. -/
theorem cleanHist_step_delivery {i : Nat} {v : V} {o} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (hh : CleanHist p c E rho i) : CleanHist p c E rho (i + 1) :=
  cleanHist_step_of_noGate (delivery_noGate he) hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A tick without a gate preserves the completed history. -/
theorem cleanHist_step_noGateTick {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hn : isGateTime p t = false)
    (hh : CleanHist p c E rho i) : CleanHist p c E rho (i + 1) := by
  apply cleanHist_step_of_noGate ?_ hh
  intro x s hx
  change rho.events[i]? = some (.tick x _) at hx
  have ht := (V2.Event.tick.inj (Option.some.inj (he.symm.trans hx))).2
  have hg := (isGateTime_iff p t).mpr ⟨s, ht.symm⟩
  rw [hn] at hg
  cases hg

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. A vote, row, or refused block keeps every state field used by the SA origins.
The vote case uses the FG-SA store wrappers for GridCO admission. -/
theorem clean_delivery_fields {j : Nat} {v : V} {o} {t : Time}
    (he : rho.events[j]? = some (.deliver v o t))
    (href : ∀ s N P,
      (toWire p o).decode = some (.block s N) →
      namedParentHeld (storeAt p c E rho j v) N = true →
      parentFG (storeAt p c E rho j v) N.erase = some P →
      blockAccepted p (storeAt p c E rho j v) s N P = false) :
    let a := storeAt p c E rho j v
    let b := storeAt p c E rho (j + 1) v
    b.fg = a.fg ∧ b.base.stableRecord = a.base.stableRecord ∧
      b.base.obligations = a.base.obligations ∧ b.base.genuine = a.base.genuine ∧
      b.fastWrite = a.fastWrite := by
  have hstore : storeAt p c E rho (j + 1) v =
      FGSA.process p (storeAt p c E rho j v) (toWire p o) := by
    change (V2.D.Run.stateBefore E rho (j + 1) v).st = _
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_self]
    rfl
  dsimp only
  rw [hstore]
  generalize hw : toWire p o = w at href ⊢
  change (let b := match w.decode with
    | some (.vote s k B) => admitHead p (storeAt p c E rho j v) s k B
    | some (.row _ body) => admitRow p (storeAt p c E rho j v) ⟨w.auth, body⟩
    | some (.block s N) => admitBlock p (storeAt p c E rho j v) s N
    | none => storeAt p c E rho j v
    b.fg = _ ∧ b.base.stableRecord = _ ∧ b.base.obligations = _ ∧
      b.base.genuine = _ ∧ b.fastWrite = _)
  cases hd : w.decode with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some input =>
    cases input with
    | vote s k B =>
      exact ⟨admitHead_fg p _ s k B, admitHead_base_stable p _ s k B,
        admitHead_obligations p _ s k B, admitHead_genuine p _ s k B,
        admitHead_fastWrite p _ s k B⟩
    | row k body =>
      dsimp only
      rcases admitRow_eq p (storeAt p c E rho j v) ⟨w.auth, body⟩ with hr | hr <;>
        rw [hr] <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | block s N =>
      have hr : admitBlock p (storeAt p c E rho j v) s N =
          storeAt p c E rho j v := by
        apply admitBlock_refused
        cases hn : namedParentHeld (storeAt p c E rho j v) N with
        | false => exact Or.inl rfl
        | true =>
          apply Or.inr
          cases hP : parentFG (storeAt p c E rho j v) N.erase with
          | none => exact Or.inl rfl
          | some P => exact Or.inr ⟨P, rfl, href s N P hd hn hP⟩
      dsimp only
      rw [hr]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. K1 lifted to an admitted block event. The three compatibility premises
are the obligations left for the source-origin argument. Due rows are included. -/
theorem clean_block_reconcile {j : Nat} {v : V} {o} {t : Time}
    {s : Slot} {N : NamedProposal p.n} {P : FGBlock (Fin p.n)}
    (he : rho.events[j]? = some (.deliver v o t))
    (hd : (toWire p o).decode = some (.block s N))
    (hNamed : namedParentHeld (storeAt p c E rho j v) N = true)
    (hP : parentFG (storeAt p c E rho j v) N.erase = some P)
    (ha : blockAccepted p (storeAt p c E rho j v) s N P = true)
    (hL : ∀ row ∈ (storeAt p c E rho j v).base.obligations,
      Block.Compatible row.1 (F_at p c E rho (j + 1) v))
    (hG : ∀ r C, (r, some C) ∈ (storeAt p c E rho j v).base.genuine →
      Block.Compatible C (F_at p c E rho (j + 1) v))
    (hS : Block.Compatible (S_at p c E rho j v) (F_at p c E rho (j + 1) v)) :
    (storeAt p c E rho (j + 1) v).base.obligations = (storeAt p c E rho j v).base.obligations ∧
    (storeAt p c E rho (j + 1) v).base.genuine = (storeAt p c E rho j v).base.genuine ∧
    (storeAt p c E rho (j + 1) v).fastWrite = (storeAt p c E rho j v).fastWrite ∧
    Block.Preceq (S_at p c E rho j v) (S_at p c E rho (j + 1) v) := by
  have hstore : storeAt p c E rho (j + 1) v =
      admitBlock p (storeAt p c E rho j v) s N := by
    change (V2.D.Run.stateBefore E rho (j + 1) v).st = _
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_self]
    change (match (toWire p o).decode with
      | some (.vote r k b) => admitHead p (storeAt p c E rho j v) r k b
      | some (.row _ body) => admitRow p (storeAt p c E rho j v) ⟨(toWire p o).auth, body⟩
      | some (.block r M) => admitBlock p (storeAt p c E rho j v) r M
      | none => storeAt p c E rho j v) = _
    rw [hd]
  change (∀ row ∈ (storeAt p c E rho j v).base.obligations,
    Block.Compatible row.1 (eraseFG (storeAt p c E rho (j + 1) v).fg.F)) at hL
  change (∀ r C, (r, some C) ∈ (storeAt p c E rho j v).base.genuine →
    Block.Compatible C (eraseFG (storeAt p c E rho (j + 1) v).fg.F)) at hG
  rw [S_at_def] at hS
  change Block.Compatible (storeAt p c E rho j v).base.stableRecord
    (eraseFG (storeAt p c E rho (j + 1) v).fg.F) at hS
  simp only [S_at_def]
  rw [hstore] at hL hG hS ⊢
  exact admitBlock_reconcile_harmless p _ (cstoreInv_stateBefore E rho j v)
    s N P hNamed hP ha hL hG hS

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Expiry and release remove targets. Cache and own-record writes keep the
FG state, output, genuine results, and fast-write history. -/
theorem clean_noGate_fields {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t)) (hn : isGateTime p t = false) :
    let a := storeAt p c E rho j v
    let b := storeAt p c E rho (j + 1) v
    b.fg = a.fg ∧ b.base.stableRecord = a.base.stableRecord ∧
      b.base.obligations.Sublist a.base.obligations ∧ b.base.genuine = a.base.genuine ∧
      b.fastWrite = a.fastWrite := by
  have hstore : storeAt p c E rho (j + 1) v = clockPre p (storeAt p c E rho j v) t := by
    change (V2.D.Run.stateBefore E rho (j + 1) v).st = _
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_self]
    rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho j v) v t]
    change (if isGateTime p t then _ else _) = _
    rw [hn]
    rfl
  dsimp only
  rw [hstore]
  exact ⟨clockPre_fg p _ t, clockPre_stable p _ t, clockPre_obligations_sublist p _ t,
    clockPre_genuine p _ t, clockPre_fastWrite p _ t⟩

variable [Fintype V]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
These state fields hold at every index, independently of Clean history.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanState_index_facts {b₀ : Time} (h : CleanCutSet p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) (i : Nat) :
    (∀ v, v ∈ rho.honest → FGSA.NestOK (storeAt p c E rho i v)) ∧
    (∀ v, v ∈ rho.honest → FGSA.CStoreInv p (storeAt p c E rho i v)) ∧
    (∀ v, v ∈ rho.honest → FGSA.controls p (storeAt p c E rho i v) =
      KitFG.treeFjControlsView (heightView p)
        (storeAt p c E rho i v).fg.F (storeAt p c E rho i v).fg.TF) ∧
    (∀ v, v ∈ rho.honest → EmittedRowsNoSlash p c E rho v) := by
  exact ⟨fun v _ => nestOK_stateBefore E rho i v,
    fun v hv => (hf.store i v hv).1,
    fun v hv => (hf.frame.1 i v hv).1,
    emittedRowsNoSlash E rho h.base.linked⟩


omit [Fintype V] in
private theorem clean_row_tick {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) := ha.2.1

omit [Fintype V] in
private theorem clean_rows_step {j : Nat}
    (hs : CleanRowSources p c E rho j)
    (hn : ∀ x r, rho.events[j]? ≠ some (.tick x (p.actionTime r))) :
    CleanRowSources p c E rho (j + 1) := by
  rw [CleanRowSources_def] at hs ⊢
  intro k x r a e hk ha he
  have hkj : k < j := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h | rfl
    · exact h
    · exact (hn x r (clean_row_tick ha)).elim
  obtain ⟨C, hc, heq, hp, hb⟩ := hs k x r a e hkj ha he
  exact ⟨C, hc, heq, hp, belowLabel_mono_index (Nat.le_succ j) hb⟩

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. bp02 §5.3: the F1 certificate channel and exact row names give all
certificate sources. DC's GST-zero proof has no FG-SA row-source field. -/
theorem clean_certSources_of_rows {i : Nat} (hf : FGFoundation p c E rho)
    (hr : CleanRowSources p c E rho i)
    (hroots : NamedRootCollisionFree p c E rho) : CleanCertSources p c E rho i := by
  rw [CleanRowSources_def] at hr
  rw [CleanCertSources_def]
  intro x W e hx hW he hne
  obtain ⟨y, r, a, ⟨j, hj, ha⟩, hn⟩ := hf.strat i x W hx hW e he hne
  rw [← KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hn
  obtain ⟨C, hc, heq, hpre, hb⟩ := hr j y r a _ hj ha hn
  have heC : e = (derive p.E p.cfg C).T_h :=
    rootScope_eq hroots
      (rootScope_ancestor (rootScope_store hx hW) (certified_preceq he))
      (rootScope_ancestor (rootScope_source ha.1 hc) (KitFG.entry_preceq p.E p.cfg C))
      (congrArg Prod.snd heq)
  exact ⟨j, y, r, a, C, hj, ha, hn, hc, heC ▸ hpre, hb⟩

omit [Fintype V] in
private theorem clean_frame_from_rows (hf : FGFoundation p c E rho)
    (hroots : NamedRootCollisionFree p c E rho) {i k : Nat} (hki : k ≤ i) (hr : CleanRowSources p
      c E rho i)
    (Φ : Block → Prop) (hg : Φ .genesis)
    (hp : ∀ X Y, Block.Preceq X Y → Φ Y → Φ X)
    (hrow : ∀ j x r a (C : FGBlock (Fin p.n)), j < k → HonestRowAt p c E rho j x r a →
      BelowLabel p c E rho i (r * p.R) (eraseFG C) → Φ (eraseFG C))
    (v : V) (hv : v ∈ rho.honest) :
    Φ (F_at p c E rho k v) ∧ Φ (J_at p c E rho k v) := by
  rw [CleanRowSources_def] at hr
  have hc : AncestorClosed p (fun e => Φ (eraseFG e)) :=
    ⟨fun X Y hXY hY => hp _ _ (eraseFG_preceq hXY) hY⟩
  have hh := (srcFrameAbove_scoped p c E rho hf.store hf.strat (fun e => Φ (eraseFG e)) 0 hc (fun
    _ => hg) k v hv ?_).2
  · exact ⟨hh.1 (Nat.zero_le _), hh.2.1 (Nat.zero_le _)⟩
  · intro y r a e ha hn heScope _
    obtain ⟨j, hj, hem⟩ := ha
    obtain ⟨C, hcSource, heq, hpre, hb⟩ := hr j y r a _ (Nat.lt_of_lt_of_le hj hki) hem hn
    have heC : e = (derive p.E p.cfg C).T_h :=
      rootScope_eq hroots heScope
        (rootScope_ancestor (rootScope_source hem.1 hcSource) (KitFG.entry_preceq p.E p.cfg C))
        (congrArg Prod.snd heq)
    exact hp _ _ (eraseFG_preceq (heC ▸ hpre)) (hrow j y r a C hj hem hb)

omit [Fintype V] in
private theorem clean_dishonest_initial (hsch : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (v : V) (hv : v ∉ rho.honest) :
    storeAt p c E rho i v = FGSA.initial p.n := by
  change (V2.D.Run.stateBefore E rho i v).st = _
  rw [V2.D.Run.stateBefore_eq_of_node_ne E rho (Nat.zero_le i) ?_]
  · rfl
  · intro k e _ _ he hnode
    exact hv (hnode ▸ hsch.honest_only e (List.mem_of_getElem? he))

omit [Fintype V] in
private theorem clean_row_label {i j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (hsch : V2.D.ScheduleWellFormed E rho) (hj : j < i)
    (ha : HonestRowAt p c E rho j x r a) : r * p.R ≤ labelBoundAt p c rho i := by
  have he := clean_row_tick ha
  have htime : p.actionTime r ≤
      (match rho.events[i]? with | some e => e.time | none => rho.horizon) := by
    cases hi : rho.events[i]? with
    | none => exact (hsch.in_horizon _ (List.mem_of_getElem? he)).2
    | some e =>
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) j i hjl hil hj
      rw [hje, hie] at hkey
      exact V2.D.Engine.time_le_of_key_le _ _ hkey
  have hd : (0 : Int) < 4 * p.Δ := by have := p.deltaPos; positivity
  have hdiv : (r * p.R : Nat) ≤
      ((match rho.events[i]? with | some e => e.time | none => rho.horizon) - 6 * p.Δ) /
        (4 * p.Δ) := by
    apply (Int.le_ediv_iff_mul_le hd).mpr
    change 4 * p.Δ * (r * p.R : Nat) + 6 * p.Δ ≤ _ at htime
    nlinarith
  have hnat := Int.toNat_le_toNat hdiv
  dsimp only [labelBoundAt]
  cases hi : rho.events[i]? <;> rw [hi, Int.toNat_natCast] at hnat <;> exact hnat


omit [Fintype V] in
private theorem clean_fOrigin_from_rows (hf : FGFoundation p c E rho) {i : Nat}
    (hsch : V2.D.ScheduleWellFormed E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho) (hr : CleanRowSources p c E rho i)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ v, BelowLabel p c E rho i (labelBoundAt p c rho i) (F_at p c E rho i v) ∧
      BelowLabel p c E rho i (labelBoundAt p c rho i) (J_at p c E rho i v) := by
  intro v
  by_cases hv : v ∈ rho.honest
  · exact clean_frame_from_rows (hroots := hroots) hf (Nat.le_refl i) hr _
      (belowLabel_genesis _ _)
      (fun _ _ => belowLabel_of_preceq)
      (fun _ _ _ _ _ hj ha hb => belowLabel_mono_label (clean_row_label hsch hj ha) hb) v hv
  · have he := clean_dishonest_initial hsch i v hv
    change BelowLabel _ _ _ _ _ _ (eraseFG (storeAt p c E rho i v).fg.F) ∧
      BelowLabel _ _ _ _ _ _ (eraseFG (storeAt p c E rho i v).fg.J)
    rw [he]
    exact ⟨belowLabel_genesis _ _, belowLabel_genesis _ _⟩


omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. bp02 §5.4: gate inputs use only rows before the gate time.
DC GSTZeroSafety has no FG-SA labelled gate-input field. -/
theorem clean_gateInputs_from_rows (hf : FGFoundation p c E rho) {i : Nat}
    (hsch : V2.D.ScheduleWellFormed E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho) (hr : CleanRowSources p c E rho i)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ v s, IsGateTick p c rho i v s →
      let below := fun X => X = .genesis ∨
        ∃ r B, (r, B) ∈ cleanResults p c E rho i ∧ r < s ∧ Block.Preceq X B
      below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) := by
  intro v s ht
  let k := V2.D.Run.idxBefore rho (SA.gateTime p.toParams s)
  have hki : k ≤ i := by
    by_contra hn
    have hbad := (Gen.V2.Duty.index_lt_idxBefore_iff hsch ht (SA.gateTime p.toParams s)).1
      (Nat.lt_of_not_ge hn)
    exact (lt_irrefl _ hbad)
  have hv := hsch.honest_only _ (List.mem_of_getElem? ht)
  let Φ := fun X => X = .genesis ∨
    ∃ r B, (r, B) ∈ cleanResults p c E rho i ∧ r < s ∧ Block.Preceq X B
  have hp : ∀ X Y, Block.Preceq X Y → Φ Y → Φ X := by
    intro X Y hXY hY
    rcases hY with rfl | ⟨r, B, hB, hrs, hYB⟩
    · exact Or.inl (Gen.Pure.block_preceq_antisymm hXY (Gen.Pure.block_genesis_preceq X))
    · exact Or.inr ⟨r, B, hB, hrs, Gen.Pure.block_preceq_trans hXY hYB⟩
  have hrow : ∀ j x r a (C : FGBlock (Fin p.n)), j < k →
      HonestRowAt p c E rho j x r a →
      BelowLabel p c E rho i (r * p.R) (eraseFG C) → Φ (eraseFG C) := by
    intro j x r a C hj ha hb
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch (clean_row_tick ha)
      (SA.gateTime p.toParams s)).1 hj
    have hlabel : r * p.R < s := by
      change 4 * p.Δ * (r * p.R : Nat) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ at htime
      have hd := p.deltaPos
      have hh : (r * p.R : Nat) < (s : Int) := by nlinarith
      exact_mod_cast hh
    rcases hb with hg | ⟨r', B, hB, hrr, hCB⟩
    · exact Or.inl hg
    · exact Or.inr ⟨r', B, hB, Nat.lt_of_le_of_lt hrr hlabel, hCB⟩
  have hh := clean_frame_from_rows (hroots := hroots) hf hki hr Φ (Or.inl rfl) hp hrow v hv
  have he : (storeAt p c E rho i v).fg = (storeAt p c E rho k v).fg := by
    have hb := clean_gate_fg_before_time hsch ht
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.gateTime p.toParams s) hsch] at hb
    exact hb
  change Φ (eraseFG (storeAt p c E rho i v).fg.F) ∧
    Φ (eraseFG (storeAt p c E rho i v).fg.J)
  rw [he]
  exact hh


omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.2: a delivery emits no new row. DC GSTZeroSafety uses a
whole-run statement; this is an FG-SA source-preservation substep. -/
theorem clean_delivery_rowSources {j : Nat} {v : V} {o} {t : Time}
    (he : rho.events[j]? = some (.deliver v o t))
    (hr : CleanRowSources p c E rho j) : CleanRowSources p c E rho (j + 1) := by
  apply clean_rows_step hr
  intro x r ht
  rw [he] at ht
  cases ht

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.2: all action times are gate times, so this tick emits no row.
DC GSTZeroSafety has no FG-SA action-row predicate. -/
theorem clean_noGate_rowSources {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t)) (hn : isGateTime p t = false)
    (hr : CleanRowSources p c E rho j) : CleanRowSources p c E rho (j + 1) := by
  apply clean_rows_step hr
  intro x r ht
  have htime := (V2.Event.tick.inj (Option.some.inj (he.symm.trans ht))).2
  have hg : isGateTime p t = true := (isGateTime_iff p t).mpr ⟨r * p.R, htime.symm⟩
  rw [hn] at hg
  cases hg

omit [Fintype V] in
private theorem clean_saved_of_member {st : State p.n} (hs : CStoreInv p st)
    {r : Slot} {C : Block} (hm : (r, some C) ∈ st.base.genuine) :
    GridCO.savedGenuine st.base r = some (some C) := by
  change (st.base.genuine.find? (fun row => row.1 == r)).map Prod.snd = _
  cases hf : st.base.genuine.find? (fun row => row.1 == r) with
  | none =>
    have hbad := (List.find?_eq_none.mp hf) _ hm
    exact (hbad (by simp only [beq_self_eq_true])).elim
  | some row =>
    have hmem := List.mem_of_find?_eq_some hf
    have hkeyB : (row.1 == r) = true :=
      List.find?_some (p := fun row : Slot × Option Block => row.1 == r) hf
    have hkey : row.1 = r := beq_iff_eq.mp hkeyB
    have he : row = (r, some C) := List.inj_on_of_nodup_map hs.genuineKeys hmem hm hkey
    rw [he]
    rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. bp02 §5.3 steps 3–6: CleanState supplies all three K1 premises.
Every obligation row is included, even if its deadline is due. DC's clean
stable-record proof has no FG-SA reconcile handler or obligation rows.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_block_reconcile_state {b₀ : Time} {i j : Nat} {v : V} {o} {t : Time}
    {s : Slot} {N : NamedProposal p.n} {P : FGBlock (Fin p.n)}
    (h : CleanCutSet p c E rho b₀ ΔF) (hf : FGFoundation p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho)
    (hji : j < i) (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (he : rho.events[j]? = some (.deliver v o t))
    (hd : (toWire p o).decode = some (.block s N))
    (hNamed : namedParentHeld (storeAt p c E rho j v) N = true)
    (hP : parentFG (storeAt p c E rho j v) N.erase = some P)
    (ha : blockAccepted p (storeAt p c E rho j v) s N P = true) :
    (storeAt p c E rho (j + 1) v).base.obligations = (storeAt p c E rho j v).base.obligations ∧
    (storeAt p c E rho (j + 1) v).base.genuine = (storeAt p c E rho j v).base.genuine ∧
    (storeAt p c E rho (j + 1) v).fastWrite = (storeAt p c E rho j v).fastWrite ∧
    Block.Preceq (S_at p c E rho j v) (S_at p c E rho (j + 1) v) := by
  have hv := h.base.valid.honest_only _ (List.mem_of_getElem? he)
  have hr := clean_delivery_rowSources he hs.sources.1
  let Φ := fun X => ∃ r, BelowLabel p c E rho (j + 1) r X
  have hfg := clean_frame_from_rows (hroots := h.base.idealization) hf
    (Nat.le_refl (j + 1)) hr Φ
    ⟨0, belowLabel_genesis _ _⟩
    (fun X Y hXY ⟨r, hY⟩ => ⟨r, belowLabel_of_preceq hXY hY⟩)
    (fun _ _ r _ _ _ _ hb => ⟨r * p.R, hb⟩) v hv
  obtain ⟨rF, hF⟩ := hfg.1
  have hFi := belowLabel_mono_index (Nat.succ_le_of_lt hji) hF
  apply clean_block_reconcile he hd hNamed hP ha
  · intro row hrow
    obtain ⟨k, hk, r, C, hkt, _, hC, hpre⟩ := hs.leases v row hrow
    exact Gen.Pure.block_compatible_of_preceq_compatible hpre
      (cleanHist_belowLabel_compatible hh
        (belowLabel_of_gateResultAt h.base.valid.toScheduleWellFormed
          (Nat.lt_trans hk hji) hkt hC (Nat.le_refl r)) hFi)
  · intro r C hC
    obtain ⟨k, hk, hRF, hkt, hresult⟩ := hs.savedOnly v r C
      (clean_saved_of_member (cstoreInv_stateBefore E rho j v) hC)
    exact cleanHist_belowLabel_compatible hh
      (belowLabel_of_gateResultAt h.base.valid.toScheduleWellFormed
        (Nat.lt_trans hk hji) hkt.1 hresult (Nat.le_refl r)) hFi
  · rcases hs.sOrigin v with hg | ⟨k, hk, r, hkt, hC⟩ | ⟨k, hk, hSF⟩
    · rw [hg]
      exact Gen.Pure.block_compatible_of_common
        (Gen.Pure.block_genesis_preceq _) (Gen.Pure.block_preceq_refl _)
    · exact cleanHist_belowLabel_compatible hh
        (belowLabel_of_gateResultAt h.base.valid.toScheduleWellFormed
          (Nat.lt_trans hk hji) hkt hC (Nat.le_refl r)) hFi
    · rw [hSF]
      have hmono := eraseFG_preceq (hf.mono k j v hv hk).1
      exact cleanHist_belowLabel_compatible hh
        (belowLabel_mono_index (Nat.le_of_lt hji)
          (belowLabel_of_preceq hmono (hs.fOrigin v).1)) hFi


private theorem clean_state_unchanged {b₀ : Time} {j : Nat}
    (h : CleanCutSet p c E rho b₀ ΔF) (hf : FGFoundation p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (hs : CleanState p c E rho j)
    (hr : CleanRowSources p c E rho (j + 1))
    (hn : ∀ v s, ¬ IsGateTick p c rho j v s)
    (hN : ∀ v t, rho.events[j]? ≠ some (.restart v t))
    (he : ∀ v, let a := storeAt p c E rho j v
      let b := storeAt p c E rho (j + 1) v
      b.fg = a.fg ∧ b.base.stableRecord = a.base.stableRecord ∧
        b.base.obligations.Sublist a.base.obligations ∧ b.base.genuine = a.base.genuine ∧
        b.fastWrite = a.fastWrite) : CleanState p c E rho (j + 1) := by
  obtain ⟨hnest, hstore, hframe, hclient⟩ := cleanState_index_facts h hf (j + 1)
  have hS (v : V) : S_at p c E rho (j + 1) v = S_at p c E rho j v := (he v).2.1
  refine ⟨⟨hr, clean_certSources_of_rows (hroots := h.base.idealization) hf hr⟩,
    clean_fOrigin_from_rows (hroots := h.base.idealization) hf h.base.valid.toScheduleWellFormed
      hsrc hr,
    clean_gateInputs_from_rows (hroots := h.base.idealization) hf
      h.base.valid.toScheduleWellFormed hsrc hr,
    ?_, ?_, ?_, ?_, ?_, ?_, hnest, hstore, hframe, hclient, ?_⟩
  · intro v row hrow
    obtain ⟨k, hk, r, C, hkt, hp, hC, hpre⟩ := hs.leases v row ((he v).2.2.1.subset hrow)
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, C, hkt, hp, hC, hpre⟩
  · intro v k r C hk hkt hRF hActive hC
    have hkj : k < j := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · exact hk
      · exact (hn v r hkt.1).elim
    change ((storeAt p c E rho (j + 1) v).base.genuine.find? _).map _ = _
    rw [(he v).2.2.2.1]
    have hA : activeCompatible (storeAt p c E rho j v) C = true := by
      change Block.compatible C (eraseFG (storeAt p c E rho (j + 1) v).fg.F) = true at hActive
      rw [(he v).1] at hActive
      exact hActive
    exact hs.saved v k r C hkj hkt (hRF.mono le_rfl (Nat.le_succ j)) hA hC
  · intro v r C hC
    change ((storeAt p c E rho (j + 1) v).base.genuine.find? _).map _ = _ at hC
    rw [(he v).2.2.2.1] at hC
    obtain ⟨k, hk, hRF, hkt, hresult⟩ := hs.savedOnly v r C hC
    have hRF' := clean_restartFree_succ hRF (hN v)
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), hRF', hkt, hresult⟩
  · intro v r X hX
    change X ∈ (((storeAt p c E rho (j + 1) v).fastWrite.find? _).map _).getD [] at hX
    rw [(he v).2.2.2.2] at hX
    obtain ⟨k, hk, hRF, hkt, hp, C, hC, hpre, hfast⟩ := hs.fastWrite v r X hX
    have hRF' := clean_restartFree_succ hRF (hN v)
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), hRF', hkt, hp, C, hC, hpre, hfast⟩
  · intro v
    rw [hS]
    rcases hs.sOrigin v with hg | ⟨k, hk, r, hkt, hC⟩ | ⟨k, hk, hF⟩
    · exact Or.inl hg
    · exact Or.inr (Or.inl ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, hkt, hC⟩)
    · exact Or.inr (Or.inr ⟨k, Nat.le_trans hk (Nat.le_succ j), hF⟩)
  · intro k v o t hk hv hdel hmov
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
    · exact hs.harmless k v o t hk hv hdel hmov
    · have hm := hmov.2
      rw [FAdvance_def] at hm
      exact (hm (congrArg Store.F (he v).1).symm).elim
  · intro v k l hkl hlj
    rcases Nat.lt_or_eq_of_le hlj with hl | rfl
    · exact hs.sExtends v k l hkl (Nat.le_of_lt_succ hl)
    · rcases Nat.lt_or_eq_of_le hkl with hk | rfl
      · rw [hS]; exact hs.sExtends v k j (Nat.le_of_lt_succ hk) (Nat.le_refl j)
      · exact Gen.Pure.block_preceq_refl _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.2: ordinary delivery preserves the full state at every node.
DC GSTZeroSafety is a whole-run result; this is an FG-SA event substep.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_deliveryStateStep {b₀ : Time} : CleanDeliveryStateStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanDeliveryStateStep_def (ΔF := ΔF), CleanStateStep_def (ΔF := ΔF)]
  intro h _ hf hsrc i _ _ j _ he hs
  rw [CleanOrdinaryDelivery_def] at he
  obtain ⟨v, o, t, he, href⟩ := he
  apply clean_state_unchanged h hf hsrc hs (clean_delivery_rowSources he hs.sources.1)
    (delivery_noGate he) (by intro w t hn; rw [he] at hn; cases hn)
  intro w
  by_cases hw : w = v
  · subst w
    obtain ⟨hfg, hS, hL, hG, hfw⟩ := clean_delivery_fields he href
    exact ⟨hfg, hS, hL ▸ List.Sublist.refl _, hG, hfw⟩
  · have hh : storeAt p c E rho (j + 1) w = storeAt p c E rho j w := by
      change (V2.D.Run.stateBefore E rho (j + 1) w).st = _
      rw [V2.D.Run.stateBefore_succ E rho he]
      simp only [V2.D.World.step, Function.update_of_ne hw]
      rfl
    dsimp only
    rw [hh]
    exact ⟨rfl, rfl, List.Sublist.refl _, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.2: a non-gate tick preserves the full state at every node.
DC GSTZeroSafety has no separate FG-SA clock-handler predicate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_noGateStateStep {b₀ : Time} : CleanNoGateStateStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanNoGateStateStep_def (ΔF := ΔF), CleanStateStep_def (ΔF := ΔF)]
  intro h _ hf hsrc i _ _ j _ he hs
  rw [CleanNoGateTick_def] at he
  obtain ⟨v, t, he, hn⟩ := he
  refine clean_state_unchanged h hf hsrc hs (clean_noGate_rowSources he hn hs.sources.1)
    ?_ (by intro w t hn; rw [he] at hn; cases hn) ?_
  · intro w s hgate
    change rho.events[j]? = some (.tick w _) at hgate
    have htime := (V2.Event.tick.inj (Option.some.inj (he.symm.trans hgate))).2
    have hg := (isGateTime_iff p t).mpr ⟨s, htime.symm⟩
    rw [hn] at hg
    cases hg
  · intro w
    by_cases hw : w = v
    · subst w; exact clean_noGate_fields he hn
    · have hh : storeAt p c E rho (j + 1) w = storeAt p c E rho j w := by
        change (V2.D.Run.stateBefore E rho (j + 1) w).st = _
        rw [V2.D.Run.stateBefore_succ E rho he]
        simp only [V2.D.World.step, Function.update_of_ne hw]
        rfl
      dsimp only
      rw [hh]
      exact ⟨rfl, rfl, List.Sublist.refl _, rfl, rfl⟩


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. bp02 §5.3: admission, certificate origins, and harmless reconcile
preserve every CleanState field at every node. DC clean stable safety has
no FG-SA admission/reconcile event predicate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_blockStateStep {b₀ : Time} : CleanBlockStateStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanBlockStateStep_def (ΔF := ΔF), CleanStateStep_def (ΔF := ΔF)]
  intro h _ hf hsrc i _ hh j hji he hs
  rw [CleanBlockDelivery_def] at he
  obtain ⟨v, o, t, s, N, P, he, hd, hNamed, hP, ha⟩ := he
  have hr := clean_delivery_rowSources he hs.sources.1
  have hkeep (w : V) :
      (storeAt p c E rho (j + 1) w).base.obligations =
        (storeAt p c E rho j w).base.obligations ∧
      (storeAt p c E rho (j + 1) w).base.genuine =
        (storeAt p c E rho j w).base.genuine ∧
      (storeAt p c E rho (j + 1) w).fastWrite = (storeAt p c E rho j w).fastWrite ∧
      Block.Preceq (S_at p c E rho j w) (S_at p c E rho (j + 1) w) := by
    by_cases hw : w = v
    · subst w; exact clean_block_reconcile_state h hf hsrc hji hh hs he hd hNamed hP ha
    · have hstore : storeAt p c E rho (j + 1) w = storeAt p c E rho j w := by
        change (V2.D.Run.stateBefore E rho (j + 1) w).st = _
        rw [V2.D.Run.stateBefore_succ E rho he]
        simp only [V2.D.World.step, Function.update_of_ne hw]
        rfl
      simp only [S_at_def]
      rw [hstore]
      exact ⟨rfl, rfl, rfl, Gen.Pure.block_preceq_refl _⟩
  obtain ⟨hnest, hstore, hframe, hclient⟩ := cleanState_index_facts h hf (j + 1)
  refine ⟨⟨hr, clean_certSources_of_rows (hroots := h.base.idealization) hf hr⟩,
    clean_fOrigin_from_rows (hroots := h.base.idealization) hf h.base.valid.toScheduleWellFormed
      hsrc hr,
    clean_gateInputs_from_rows (hroots := h.base.idealization) hf
      h.base.valid.toScheduleWellFormed hsrc hr,
    ?_, ?_, ?_, ?_, ?_, ?_, hnest, hstore, hframe, hclient, ?_⟩
  · intro w row hrow
    rw [(hkeep w).1] at hrow
    obtain ⟨k, hk, r, C, hkt, hp, hC, hpre⟩ := hs.leases w row hrow
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, C, hkt, hp, hC, hpre⟩
  · intro w k r C hk hkt hRF hActive hC
    have hkj : k < j := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · exact hk
      · exact (delivery_noGate he w r hkt.1).elim
    change ((storeAt p c E rho (j + 1) w).base.genuine.find? _).map _ = _
    rw [(hkeep w).2.1]
    have hA : activeCompatible (storeAt p c E rho j w) C = true := by
      exact cleanHist_belowLabel_compatible hh
        (belowLabel_of_gateResultAt h.base.valid.toScheduleWellFormed
          (Nat.lt_trans hkj hji) hkt.1 hC le_rfl)
        (belowLabel_mono_index (Nat.le_of_lt hji) (hs.fOrigin w).1)
    exact hs.saved w k r C hkj hkt (hRF.mono le_rfl (Nat.le_succ j)) hA hC
  · intro w r C hC
    change ((storeAt p c E rho (j + 1) w).base.genuine.find? _).map _ = _ at hC
    rw [(hkeep w).2.1] at hC
    obtain ⟨k, hk, hRF, hkt, hresult⟩ := hs.savedOnly w r C hC
    have hRF' := clean_restartFree_succ hRF (by intro t hn; rw [he] at hn; cases hn)
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), hRF', hkt, hresult⟩
  · intro w r X hX
    change X ∈ (((storeAt p c E rho (j + 1) w).fastWrite.find? _).map _).getD [] at hX
    rw [(hkeep w).2.2.1] at hX
    obtain ⟨k, hk, hRF, hkt, hp, C, hC, hpre, hfast⟩ := hs.fastWrite w r X hX
    have hRF' := clean_restartFree_succ hRF (by intro t hn; rw [he] at hn; cases hn)
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), hRF', hkt, hp, C, hC, hpre, hfast⟩
  · intro w
    have horigin : S_at p c E rho (j + 1) w = S_at p c E rho j w ∨
        S_at p c E rho (j + 1) w = F_at p c E rho (j + 1) w := by
      rcases fgsaAC_output_step E rho j w with heq | hgate | hrec | ⟨t', hrest, _⟩
      · exact Or.inl heq
      · rw [Gen.AC.Duty.GateWrite_def] at hgate
        obtain ⟨r, hgate⟩ := hgate
        rw [he] at hgate
        cases hgate
      · rw [Gen.AC.Duty.Reconcile_def] at hrec
        obtain ⟨_, _, _, _, _, _, hout⟩ := hrec
        change (storeAt p c E rho (j + 1) w).base.stableRecord =
          Gen.AC.normalizeOutput (F_at p c E rho (j + 1) w)
            (storeAt p c E rho j w).base.stableRecord at hout
        rw [← S_at_def p c E rho (j + 1) w, ← S_at_def p c E rho j w] at hout
        rw [Gen.AC.normalizeOutput_def] at hout
        split at hout
        · exact Or.inl hout
        · exact Or.inr hout
      · rw [he] at hrest
        cases hrest
    rcases horigin with heq | hF
    · rw [heq]
      rcases hs.sOrigin w with hg | ⟨k, hk, r, hkt, hC⟩ | ⟨k, hk, hF⟩
      · exact Or.inl hg
      · exact Or.inr (Or.inl ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, hkt, hC⟩)
      · exact Or.inr (Or.inr ⟨k, Nat.le_trans hk (Nat.le_succ j), hF⟩)
    · exact Or.inr (Or.inr ⟨j + 1, Nat.le_refl _, hF⟩)
  · intro k w o' t' hk hw hdel hmov
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
    · exact hs.harmless k w o' t' hk hw hdel hmov
    · exact ⟨(hkeep w).1, (hkeep w).2.1, (hkeep w).2.2.1⟩
  · intro w k l hkl hlj
    rcases Nat.lt_or_eq_of_le hlj with hl | rfl
    · exact hs.sExtends w k l hkl (Nat.le_of_lt_succ hl)
    · rcases Nat.lt_or_eq_of_le hkl with hk | rfl
      · exact Gen.Pure.block_preceq_trans
          (hs.sExtends w k j (Nat.le_of_lt_succ hk) (Nat.le_refl j)) (hkeep w).2.2.2
      · exact Gen.Pure.block_preceq_refl _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. bp02 §§5.5–5.6: the gate state closes once the action supplies its
row sources. This is not the frozen CleanGateStateStep Prop: the action
substep remains separate as required by S3. DC has no FG-SA action rows.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_state_of_rows {b₀ : Time} {i j : Nat} {v : V} {s : Slot}
    (h : CleanCutSet p c E rho b₀ ΔF) (hf : FGFoundation p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) (hr : CleanRowSources p c E rho (j + 1)) :
    CleanState p c E rho (j + 1) := by
  obtain ⟨hL, hG, hOnly, hFast, hOrigin, hS⟩ :=
    clean_gate_fields_all h.base.valid.toScheduleWellFormed hji hh hs ht
  obtain ⟨hnest, hstore, hframe, hclient⟩ := cleanState_index_facts h hf (j + 1)
  refine ⟨⟨hr, clean_certSources_of_rows (hroots := h.base.idealization) hf hr⟩,
    clean_fOrigin_from_rows (hroots := h.base.idealization) hf h.base.valid.toScheduleWellFormed
      hsrc hr,
    clean_gateInputs_from_rows (hroots := h.base.idealization) hf
      h.base.valid.toScheduleWellFormed hsrc hr,
    hL, hG, hOnly, hFast, hOrigin, ?_, hnest, hstore, hframe, hclient, hS⟩
  intro k w o t hk hw he hmov
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
  · exact hs.harmless k w o t hk hw he hmov
  · exact (delivery_noGate he v s ht).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.2: the delivery case of the prefix history induction.
DC GSTZeroSafety is a whole-run safety result; this is its FG-SA event substep.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_deliveryHistStep {b₀ : Time} : CleanDeliveryHistStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanDeliveryHistStep_def (ΔF := ΔF), CleanHistStep_def (ΔF := ΔF)]
  intro _ _ _ _ i _ he hh _
  rw [CleanOrdinaryDelivery_def] at he
  obtain ⟨v, o, t, he, _⟩ := he
  exact cleanHist_step_delivery he hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.3: block admission changes no completed gate history.
DC GSTZeroSafety has no separate FG-SA block-handler predicate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_blockHistStep {b₀ : Time} : CleanBlockHistStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanBlockHistStep_def (ΔF := ΔF), CleanHistStep_def (ΔF := ΔF)]
  intro _ _ _ _ i _ he hh _
  rw [CleanBlockDelivery_def] at he
  obtain ⟨v, o, t, _, _, _, he, _⟩ := he
  exact cleanHist_step_delivery he hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.2: a tick without a gate changes no completed history.
DC GSTZeroSafety has no separate FG-SA clock-handler predicate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_noGateHistStep {b₀ : Time} : CleanNoGateHistStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanNoGateHistStep_def (ΔF := ΔF), CleanHistStep_def (ΔF := ΔF)]
  intro _ _ _ _ i _ he hh _
  rw [CleanNoGateTick_def] at he
  obtain ⟨v, t, he, hn⟩ := he
  exact cleanHist_step_noGateTick he hn hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.2: the initial state has no sources or saved gate writes.
DC GSTZeroSafety uses a genesis execution; this is the FG-SA initial state.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanState_zero {b₀ : Time} (h : CleanCutSet p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) : CleanState p c E rho 0 := by
  obtain ⟨hnest, hstore, hframe, hclient⟩ := cleanState_index_facts h hf 0
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hnest, hstore, hframe, hclient, ?_⟩
  · rw [CleanRowSources_def]
    intro j x r a e hj
    exact (Nat.not_lt_zero j hj).elim
  · rw [CleanCertSources_def]
    intro x W e _ hW he hne
    have hw : W = .genesis := by
      change W ∈ ({.genesis} : Finset _) at hW
      exact Finset.mem_singleton.mp hW
    subst W
    rw [certified_def] at he
    obtain ⟨U, hU, he⟩ := he
    have hu : U = .genesis := KitFG.preceq_antisymm hU (KitFG.genesis_preceq U)
    subst U
    rcases he with he | he | ⟨he, _⟩ <;> exact (hne he).elim
  · intro v
    exact ⟨belowLabel_genesis _ _, belowLabel_genesis _ _⟩
  · intro v s _
    exact ⟨Or.inl rfl, Or.inl rfl⟩
  · intro v row hr
    change row ∈ ([] : List (Block × Nat × Time)) at hr
    cases hr
  · intro v j s C hj
    exact (Nat.not_lt_zero j hj).elim
  · intro v s C hc
    change (none : Option (Option Block)) = some (some C) at hc
    cases hc
  · intro v s X hx
    change X ∈ ([] : List Block) at hx
    cases hx
  · intro v
    exact Or.inl rfl
  · intro j v o t hj
    exact (Nat.not_lt_zero j hj).elim
  · intro v j k hj hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero (hj.trans hk)
    subst j; subst k
    exact Gen.Pure.block_preceq_refl _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 §§8.2, 8.4, 8.7; bp02 §§5.5–5.6; lead R2(b).
DC counterpart: none; FG-SA's action shares the gate tick. The action
premise supplies successor row sources from the given prior state.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gateStateStep_of_action {b₀ : Time}
    (hact : CleanActionStep (ΔF := ΔF) p c E rho b₀) :
    CleanGateStateStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanActionStep_def (ΔF := ΔF)] at hact
  rw [CleanGateStateStep_def (ΔF := ΔF), CleanStateStep_def (ΔF := ΔF)]
  intro h hq hf hsrc i hi hh j hji ht hs
  rw [CleanGateTick_def] at ht
  obtain ⟨v, s, ht⟩ := ht
  apply clean_gate_state_of_rows h hf hsrc hji hh hs ht
  by_cases ha : ∃ x r, rho.events[j]? = some (.tick x (p.actionTime r))
  · obtain ⟨x, r, ha⟩ := ha
    exact hact h hq hf hsrc j x r (Nat.lt_of_lt_of_le hji hi) ha
      (cleanHist_restrict (Nat.succ_le_of_lt hji) hh) hs
  · exact clean_rows_step hs.sources.1 (fun x r he => ha ⟨x, r, he⟩)

/-- A wake restart keeps durable origins and starts new local saved histories. -/
theorem clean_restartStateStep {b₀ : Time} {j : Nat} {v : V} {t : Time}
    (h : CleanCutSet p c E rho b₀ ΔF) (hf : FGFoundation p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (hs : CleanState p c E rho j)
    (he : rho.events[j]? = some (.restart v t)) : CleanState p c E rho (j + 1) := by
  have other (w : V) (hw : w ≠ v) :
      storeAt p c E rho (j + 1) w = storeAt p c E rho j w := by
    change (V2.D.Run.stateBefore E rho (j + 1) w).st = _
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_of_ne hw]
    rfl
  have hkeep (w : V) :
      (storeAt p c E rho (j + 1) w).fg = (storeAt p c E rho j w).fg ∧
      S_at p c E rho (j + 1) w = S_at p c E rho j w ∧
      (storeAt p c E rho (j + 1) w).base.obligations =
        (storeAt p c E rho j w).base.obligations := by
    by_cases hw : w = v
    · subst w
      have hb := clean_restart_fields (E := E) he
      exact ⟨hb.1, hb.2.2.2.1, hb.2.2.1⟩
    · rw [S_at_def, S_at_def, other w hw]
      exact ⟨rfl, rfl, rfl⟩
  have hN (w : V) (hw : w ≠ v) : ∀ u, rho.events[j]? ≠ some (.restart w u) := by
    intro u hu
    rw [he] at hu
    exact hw (V2.Event.restart.inj (Option.some.inj hu)).1.symm
  have hr : CleanRowSources p c E rho (j + 1) := by
    apply clean_rows_step hs.sources.1
    intro x r hx
    rw [he] at hx
    cases hx
  obtain ⟨hnest, hstore, hframe, hclient⟩ := cleanState_index_facts h hf (j + 1)
  refine ⟨⟨hr, clean_certSources_of_rows (hroots := h.base.idealization) hf hr⟩,
    clean_fOrigin_from_rows (hroots := h.base.idealization) hf h.base.valid.toScheduleWellFormed
      hsrc hr,
    clean_gateInputs_from_rows (hroots := h.base.idealization) hf
      h.base.valid.toScheduleWellFormed hsrc hr,
    ?_, ?_, ?_, ?_, ?_, ?_, hnest, hstore, hframe, hclient, ?_⟩
  · intro w row hrow
    rw [(hkeep w).2.2] at hrow
    obtain ⟨k, hk, r, C, hkt, hp, hC, hpre⟩ := hs.leases w row hrow
    exact ⟨k, hk.trans (Nat.lt_succ_self j), r, C, hkt, hp, hC, hpre⟩
  · intro w k r C hk hkt hRF hA hC
    by_cases hw : w = v
    · subst w
      exact (hRF j t (Nat.le_of_lt_succ hk) (Nat.lt_succ_self j) he).elim
    · rw [other w hw]
      rw [other w hw] at hA
      have hkj : k < j := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
        · exact hk
        · have ht := hkt.1
          change rho.events[k]? = some (.tick w (SA.gateTime p.toParams r)) at ht
          rw [he] at ht
          cases ht
      exact hs.saved w k r C hkj hkt (hRF.mono le_rfl (Nat.le_succ j)) hA hC
  · intro w r C hC
    by_cases hw : w = v
    · subst w
      change ((storeAt p c E rho (j + 1) v).base.genuine.find? _).map _ = _ at hC
      rw [(clean_restart_fields (E := E) he).2.2.2.2.1] at hC
      cases hC
    · rw [other w hw] at hC
      obtain ⟨k, hk, hRF, hkt, hC⟩ := hs.savedOnly w r C hC
      exact ⟨k, hk.trans (Nat.lt_succ_self j), clean_restartFree_succ hRF (hN w hw), hkt, hC⟩
  · intro w r X hX
    by_cases hw : w = v
    · subst w
      change X ∈ (((storeAt p c E rho (j + 1) v).fastWrite.find? _).map _).getD [] at hX
      rw [(clean_restart_fields (E := E) he).2.2.2.2.2.1] at hX
      exact (List.not_mem_nil hX).elim
    · rw [other w hw] at hX
      obtain ⟨k, hk, hRF, hkt, hp, C, hC, hpre, hfast⟩ := hs.fastWrite w r X hX
      exact ⟨k, hk.trans (Nat.lt_succ_self j), clean_restartFree_succ hRF (hN w hw),
        hkt, hp, C, hC, hpre, hfast⟩
  · intro w
    rw [(hkeep w).2.1]
    rcases hs.sOrigin w with hg | ⟨k, hk, r, hkt, hC⟩ | ⟨k, hk, hF⟩
    · exact Or.inl hg
    · exact Or.inr (Or.inl ⟨k, hk.trans (Nat.lt_succ_self j), r, hkt, hC⟩)
    · exact Or.inr (Or.inr ⟨k, hk.trans (Nat.le_succ j), hF⟩)
  · intro k w o u hk hw hd hm
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
    · exact hs.harmless k w o u hk hw hd hm
    · rw [he] at hd
      cases hd
  · intro w k l hkl hlj
    rcases Nat.lt_or_eq_of_le hlj with hl | rfl
    · exact hs.sExtends w k l hkl (Nat.le_of_lt_succ hl)
    · rcases Nat.lt_or_eq_of_le hkl with hk | rfl
      · rw [(hkeep w).2.1]
        exact hs.sExtends w k j (Nat.le_of_lt_succ hk) le_rfl
      · exact Gen.Pure.block_preceq_refl _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 §§8.2–8.4, 8.7; bp02 §5; lead R2(c), S2 and S3.
DC counterpart: none for this fixed-history state predicate. DC's
Protocol/ChainState/Chain.lean carries the chain-order bundle; FG-SA
instead derives the full state over event indices from a fixed history
and the separate action step.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanState_of_hist {b₀ : Time} {i : Nat}
    (h : CleanCutSet p c E rho b₀ ΔF) (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hact : CleanActionStep (ΔF := ΔF) p c E rho b₀)
    (hi : i ≤ timeIdx rho b₀) (hh : CleanHist p c E rho i) : CleanState p c E rho i := by
  have hd := clean_deliveryStateStep (ΔF := ΔF) (p := p) (c := c) (E := E) (rho := rho) (b₀ := b₀)
  have hb := clean_blockStateStep (ΔF := ΔF) (p := p) (c := c) (E := E) (rho := rho) (b₀ := b₀)
  have hn := clean_noGateStateStep (ΔF := ΔF) (p := p) (c := c) (E := E) (rho := rho) (b₀ := b₀)
  have hg := clean_gateStateStep_of_action hact
  rw [CleanDeliveryStateStep_def (ΔF := ΔF), CleanStateStep_def (ΔF := ΔF)] at hd
  rw [CleanBlockStateStep_def (ΔF := ΔF), CleanStateStep_def (ΔF := ΔF)] at hb
  rw [CleanNoGateStateStep_def (ΔF := ΔF), CleanStateStep_def (ΔF := ΔF)] at hn
  rw [CleanGateStateStep_def (ΔF := ΔF), CleanStateStep_def (ΔF := ΔF)] at hg
  have hall : ∀ j, j ≤ i → CleanState p c E rho j := by
    intro j
    induction j with
    | zero => intro _; exact cleanState_zero h hf
    | succ j ih =>
      intro hsucc
      have hji : j < i := Nat.lt_of_succ_le hsucc
      have hs := ih (Nat.le_of_lt hji)
      have hjlen : j < rho.events.length := by
        have hlen : timeIdx rho b₀ ≤ rho.events.length := by
          dsimp only [timeIdx]
          exact List.length_filter_le ..
        exact Nat.lt_of_lt_of_le hji (hi.trans hlen)
      obtain ⟨e, he⟩ : ∃ e, rho.events[j]? = some e :=
        ⟨rho.events[j], List.getElem?_eq_some_iff.mpr ⟨hjlen, rfl⟩⟩
      cases e with
      | restart v t => exact clean_restartStateStep h hf hsrc hs he
      | tick v t =>
        cases ht : isGateTime p t with
        | false =>
          apply hn h hq hf hsrc i hi hh j hji ?_ hs
          rw [CleanNoGateTick_def]
          exact ⟨v, t, he, ht⟩
        | true =>
          obtain ⟨s, hsTime⟩ := (isGateTime_iff p t).mp ht
          apply hg h hq hf hsrc i hi hh j hji ?_ hs
          rw [CleanGateTick_def]
          refine ⟨v, s, ?_⟩
          change rho.events[j]? = some (.tick v (SA.gateTime p.toParams s))
          rw [hsTime]
          exact he
      | deliver v o t =>
        by_cases ha : ∃ s N P,
            (toWire p o).decode = some (.block s N) ∧
            namedParentHeld (storeAt p c E rho j v) N = true ∧
            parentFG (storeAt p c E rho j v) N.erase = some P ∧
            blockAccepted p (storeAt p c E rho j v) s N P = true
        · obtain ⟨s, N, P, hdec, hNamed, hparent, hacc⟩ := ha
          apply hb h hq hf hsrc i hi hh j hji ?_ hs
          rw [CleanBlockDelivery_def]
          exact ⟨v, o, t, s, N, P, he, hdec, hNamed, hparent, hacc⟩
        · apply hd h hq hf hsrc i hi hh j hji ?_ hs
          rw [CleanOrdinaryDelivery_def]
          refine ⟨v, o, t, he, ?_⟩
          intro s N P hdec hNamed hparent
          cases hacc : blockAccepted p (storeAt p c E rho j v) s N P with
          | false => rfl
          | true => exact (ha ⟨s, N, P, hdec, hNamed, hparent, hacc⟩).elim
  exact hall i (Nat.le_refl i)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 §8.2, §8.7; bp02 §5.5; lead R2(b), S2.
DC counterpart: Generic/Properties.lean MonotoneFrom. This event-index
form uses a fixed CleanHist and an explicit action step, which F2.6
discharges before the whole-run monotonicity result.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem sExtends_upTo_of_action {b₀ : Time} {i : Nat}
    (h : CleanCutSet p c E rho b₀ ΔF) (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hact : CleanActionStep (ΔF := ΔF) p c E rho b₀)
    (hi : i ≤ timeIdx rho b₀) (hh : CleanHist p c E rho i) :
    ∀ v j k, j ≤ k → k ≤ i →
      Block.Preceq (S_at p c E rho j v) (S_at p c E rho k v) :=
  (cleanState_of_hist h hq hf hsrc hact hi hh).sExtends

end AvailableChain.FGSA.Run
end
