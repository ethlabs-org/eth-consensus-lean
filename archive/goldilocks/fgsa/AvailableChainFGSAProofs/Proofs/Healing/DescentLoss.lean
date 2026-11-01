module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTransfer
public import AvailableChainFGSAProofs.Proofs.Shared.Compose
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel
public import AvailableChainFGSAProofs.Proofs.Healing.Time
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery

public section

/-! H-DESCENT D2 (H.13): the concrete loss predicate, and the `same` and
`support` inputs of `healing_high_source_first_failure` at c₀ = μ + 1.
Every source and loss witness is an event of the finite run. The Foundations
source facts are inline hypotheses: `sourceDiscipline_emittedNonempty` in its
exact statement form, and the projection of `sourceDiscipline_emittedName` to
the window height (`heightView_eq_simplex`), so that no statement here reads
the old `SimplexFG.derive` (old-read audit). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B (definitions); blueprint 21:2718–2723.
DC: INTENTIONAL finite-run source. A source whose row is an event of the run. -/
def SrcN (B : FGBlock (Fin p.n)) (s : Slot) : Prop :=
  SourceBefore p c E rho rho.events.length B s

theorem SrcN_def (B : FGBlock (Fin p.n)) (s : Slot) :
    SrcN p c E rho B s = SourceBefore p c E rho rho.events.length B s := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B (definitions); blueprint 21:2718–2723.
DC: INTENTIONAL high source at c₀ = μ + 1; the H0Reset bound gives M + 1 later. -/
def HighSrcN (B : FGBlock (Fin p.n)) (s : Slot) : Prop :=
  SrcN p c E rho B s ∧ muOf p c E rho + 1 ≤ (heightView p B).h

theorem HighSrcN_def (B : FGBlock (Fin p.n)) (s : Slot) :
    HighSrcN p c E rho B s =
      (SrcN p c E rho B s ∧ muOf p c E rho + 1 ≤ (heightView p B).h) := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B (definitions); blueprint 21:2718–2741 (fj.descent.v3).
DC: INTENTIONAL global event-index measure. The high source B of label sB is
lost at event k: k is an honest HEAD tick at v_l with sB + 1 ≤ l, and the HEAD
on the post-clock state of exactly event k does not extend B. The row of B need
not precede k (blocker B2: the first transfer is at v_(sB+1) < d_sB). -/
def Lost (B : FGBlock (Fin p.n)) (sB : Slot) (k : Nat) : Prop :=
  HighSrcN p c E rho B sB ∧ ∃ x l, x ∈ rho.honest ∧ sB + 1 ≤ l ∧
    rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)) ∧
    ¬ Block.Preceq (eraseFG B) (headAtIdx p c E rho k l)

theorem Lost_def (B : FGBlock (Fin p.n)) (sB : Slot) (k : Nat) :
    Lost p c E rho B sB k =
      (HighSrcN p c E rho B sB ∧ ∃ x l, x ∈ rho.honest ∧ sB + 1 ≤ l ∧
        rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)) ∧
        ¬ Block.Preceq (eraseFG B) (headAtIdx p c E rho k l)) := by rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B (definitions). DC: SAME finite run.
A source row before any index is an event of the run. -/
theorem healing_srcN_of_source {i : Nat} {B : FGBlock (Fin p.n)} {s : Slot}
    (h : SourceBefore p c E rho i B s) : SrcN p c E rho B s := by
  obtain ⟨j, y, r, a, _, ha, hB, hs⟩ := h
  have hj : j < rho.events.length := by
    by_contra hn
    have hz := List.getElem?_eq_none (l := rho.events) (Nat.le_of_not_lt hn)
    have hj := ha.2.1
    rw [hz] at hj
    cases hj
  exact ⟨j, y, r, a, hj, ha, hB, hs⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The HEAD read at a tick index is the HEAD of that tick's post-clock state. -/
theorem healing_headAtIdx_tick {k : Nat} {z : V} {t : Time}
    (hk : rho.events[k]? = some (.tick z t)) (l : Slot) :
    headAtIdx p c E rho k l =
      FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k z) t).st l := by
  delta headAtIdx
  rw [hk]

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:2640–2653; plan fgsa-s5-m5-d2d4 B (invalid shortcut: event
order alone gives no strict time order). DC: SAME schedule order. An event of
strictly smaller time has a strictly smaller index. -/
theorem healing_idx_lt_of_time_lt (hs : V2.D.ScheduleWellFormed E rho)
    {a b : Nat} {ea eb : V2.Event V (fgsa p c).Object}
    (ha : rho.events[a]? = some ea) (hb : rho.events[b]? = some eb)
    (ht : ea.time < eb.time) : a < b := by
  by_contra hn
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hn) with hlt | heq
  · obtain ⟨hal, hae⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨hbl, hbe⟩ := List.getElem?_eq_some_iff.mp hb
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) b a hbl hal hlt
    rw [hae, hbe] at hk
    exact absurd (V2.D.Engine.time_le_of_key_le _ _ hk) (not_le.mpr ht)
  · subst heq
    rw [ha] at hb
    cases Option.some.inj hb
    exact lt_irrefl _ ht

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `same` step 1. DC: SAME source discipline.
The inline Foundations facts decode a source row: its emitted name is the
height of the source, and the source gate has a genuine result above it and
passes the fast test at it. -/
theorem healing_source_decode
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {j : Nat} {y : V} {r : Nat} {a : RowWire p.n} {K : FGBlock (Fin p.n)}
    (ha : HonestRowAt p c E rho j y r a)
    (hK : actionSourceFG p c E rho y r = some (some K)) :
    ∃ e G, namedEntry a.payload.height_pair = some ((heightView p K).h, e) ∧
      gateResult p c E rho y (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG K) G ∧ fastAt p c E rho y (r * p.R) (eraseFG K) := by
  obtain ⟨e, he⟩ := emittedNonempty ha
  obtain ⟨C, G, hC, he1, hG, hCG, hfast⟩ := emittedName ha he
  rw [hK] at hC
  cases Option.some.inj (Option.some.inj hC)
  refine ⟨e.2, G, ?_, hG, hCG, hfast⟩
  rw [he, ← he1]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `same` step 2; blueprint 21:1579–1582 (H.11 μ).
DC: INTENTIONAL μ excludes sources before recoveryStart. A source above μ votes
at or after recoveryStart: otherwise its emitted name is an old row height, at most μ. -/
theorem healing_high_source_recoveryStart
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot}
    (hK : SourceBefore p c E rho i K s) (hc : muOf p c E rho + 1 ≤ (heightView p K).h) :
    recoveryStart p E ≤ SA.voteTime p.toParams s := by
  obtain ⟨j, y, r, a, -, ha, hKs, rfl⟩ := hK
  obtain ⟨e, -, he, -⟩ := healing_source_decode p c E rho emittedNonempty emittedName ha hKs
  by_contra hlt
  have hold : (heightView p K).h ∈ oldRowHeights p c E rho :=
    ⟨j, y, r, a, e, ha, he,
      lt_of_not_ge hlt⟩
  have hμ := (muOf_spec p c E rho).2.2.2.1 _ hold
  omega

omit [DecidableEq V] in
/-- A vote after the recovery start has the current batch's prior-slot cutoff. -/
theorem healing_window_of_recoveryStart {s : Slot}
    (h : recoveryStart p E ≤ SA.voteTime p.toParams s) : HealingWindow p E 1 s := by
  let a : Int := max 0 E.t_GST + 4 * p.Δ - 1
  have hdelta : (1 : Int) ≤ p.Δ := by
    have hp : (0 : Int) < p.Δ := p.deltaPos
    omega
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have ha : 0 ≤ a := by dsimp [a]; linarith [le_max_left 0 E.t_GST, p.deltaPos]
  have hq := Int.ediv_nonneg ha hd.le
  have hm := Int.emod_lt_of_pos a hd
  have he := Int.mul_ediv_add_emod a (4 * p.Δ)
  change 4 * p.Δ * ((a / (4 * p.Δ)).toNat : Int) + 6 * p.Δ ≤
    4 * p.Δ * (s : Int) + p.Δ at h
  rw [Int.toNat_of_nonneg hq] at h
  have hs : a / (4 * p.Δ) + 2 ≤ (s : Int) := by
    by_contra hn
    have : (s : Int) ≤ a / (4 * p.Δ) + 1 := by
      dsimp [Time] at *
      omega
    nlinarith [p.deltaPos]
  refine ⟨by dsimp [Time] at *; omega, ?_⟩
  change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
  dsimp [a] at he hm
  nlinarith [le_max_right 0 E.t_GST]

theorem healing_high_source_sync
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot}
    (hK : SourceBefore p c E rho i K s) (hc : muOf p c E rho + 1 ≤ (heightView p K).h) :
    E.t_GST ≤ SA.voteTime p.toParams s :=
  (healing_recoveryStart_ge p E).trans
    (healing_high_source_recoveryStart p c E rho emittedNonempty emittedName hK hc)

theorem healing_high_source_window
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot}
    (hK : SourceBefore p c E rho i K s) (hc : muOf p c E rho + 1 ≤ (heightView p K).h) :
    HealingWindow p E 1 s :=
  healing_window_of_recoveryStart p E
    (healing_high_source_recoveryStart p c E rho emittedNonempty emittedName hK hc)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `same` step 3. DC: SAME label-local synchrony.
A source label of a high source is synchronized on [v_s, d_s]: its action
event is in the run, so d_s is inside the horizon. -/
theorem healing_high_source_labelSync [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot}
    (hK : SourceBefore p c E rho i K s) (hc : muOf p c E rho + 1 ≤ (heightView p K).h) :
    Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams s) (SA.gateTime p.toParams s) := by
  have hgst := healing_high_source_sync p c E rho emittedNonempty emittedName hK hc
  obtain ⟨j, y, r, a, -, ha, -, rfl⟩ := hK
  have hmem := List.mem_of_getElem? ha.2.1
  have hh := (hrec.base.valid.toScheduleWellFormed.in_horizon _ hmem).2
  change p.actionTime r ≤ rho.horizon at hh
  have hvd : SA.voteTime p.toParams (r * p.R) + E.Δ ≤ SA.gateTime p.toParams (r * p.R) := by
    rw [hrec.base.delta]
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ + p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `same` (steps 1–3); blueprint 21:620–631 (IF.6),
2730–2737. DC: INTENTIONAL synchronous same-label gate compatibility.
Two high sources of one label are compatible: both are synchronous, and their
genuine gate results are compatible by IF.6 (`fgsa_sameLabel`). This is the
`same` input of `healing_high_source_first_failure` at c₀ = μ + 1. -/
theorem healing_loss_same [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hScopes : ∀ i K K' s, SourceBefore p c E rho i K s →
      SourceBefore p c E rho i K' s → muOf p c E rho + 1 ≤ (heightView p K).h →
      muOf p c E rho + 1 ≤ (heightView p K').h → SameLabelServiceScope E rho s) :
    ∀ i K K' s, SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s →
      muOf p c E rho + 1 ≤ (heightView p K).h → muOf p c E rho + 1 ≤ (heightView p K').h →
      Block.Compatible (eraseFG K) (eraseFG K') := by
  intro i K K' s hK hK' hc hc'
  have hScope := hScopes i K K' s hK hK' hc hc'
  obtain ⟨j, y, r, a, -, ha, hKs, hs⟩ := hK
  obtain ⟨j', y', r', a', -, ha', hKs', hs'⟩ := hK'
  obtain ⟨-, G, -, hG, hKG, -⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hKs
  obtain ⟨-, G', -, hG', hKG', -⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha' hKs'
  rw [← hs] at hG
  rw [← hs'] at hG'
  have hGG := fgsa_sameLabel_on p c E rho hrec.base.valid s hScope hrec.base.idealization
    y y' G G' ha.1 ha'.1 hG hG'
  change (Block.preceq G G' || Block.preceq G' G) = true at hGG
  rcases Bool.or_eq_true_iff.mp hGG with h | h
  · exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_trans hKG h) hKG'
  · exact Gen.Pure.block_compatible_of_common hKG (Gen.Pure.block_preceq_trans hKG' h)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `support` steps 1–2; blueprint 21:620–631, 673–676.
DC: INTENTIONAL actual honest supporter. A source of label s with a row in the
run has an honest supporter whose HEAD tick at v_s extends the source. The tick
is strictly earlier than every event of time above v_s, in particular than the
source row at d_s; `healing_support_honest_head` does not return this order. -/
theorem healing_source_supporter [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot} (hK : SourceBefore p c E rho i K s) :
    ∃ k z, z ∈ rho.honest ∧ rho.events[k]? = some (.tick z (SA.voteTime p.toParams s)) ∧
      Block.Preceq (eraseFG K) (headAtIdx p c E rho k s) ∧
      ∀ k' (ev : V2.Event V (fgsa p c).Object), rho.events[k']? = some ev →
        SA.voteTime p.toParams s < ev.time → k < k' := by
  have hE := hrec.base.valid
  obtain ⟨j, y, r, a, -, ha, hKs, rfl⟩ := hK
  obtain ⟨-, -, -, -, -, st, hst, hτ⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hKs
  rw [gateIn_def, preTick_def] at hst
  cases hix' : V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams (r * p.R)) with
  | none => rw [hix'] at hst; cases hst
  | some ix =>
  rw [hix'] at hst
  have hst' := Option.some.inj hst
  subst hst'
  obtain ⟨k, o, hkh, ho, hko, hsup⟩ :=
    healing_support_honest_seat rho hrec.base.cstar hrec.fault _ _ _ hτ
  obtain ⟨H, hK', hKm, _, _, hov, hol⟩ := healing_support_clean_target E rho o ho
  obtain ⟨k', hk', ht⟩ := healing_support_honest_head E rho hE hov hol hko hkh
  refine ⟨k', _, hkh, hk', ?_, fun k'' ev hev hlt =>
    healing_idx_lt_of_time_lt p c E rho hE.toScheduleWellFormed hk' hev hlt⟩
  change Gen.AC.Root.voteSupports
    (GridCO.resolutionTree (actView (clockPre p (storeAt p c E rho ix y)
      (SA.gateTime p.toParams (r * p.R))))) (eraseFG K) o = true at hsup
  rw [Gen.AC.Root.voteSupports_def, resolvedHead_target _ o hK'] at hsup
  have hH := (Bool.and_eq_true_iff.mp hsup).2
  rw [healing_headAtIdx_tick p c E rho hk']
  have he := stored_eq_headVote E rho hrec.base.idealization ix y hKm k'
    (rho.seatOf (.base (.head (r * p.R))) k) (SA.voteTime p.toParams (r * p.R)) (r * p.R)
    (Option.some.inj ((resolvedHead_root _ o hK').symm.trans ht))
  exact he ▸ hH

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `support` step 3; blueprint 21:2730–2737.
DC: INTENTIONAL global event-index measure. If a high source B of label sB is
incompatible with a source K of a later label s, the HEAD of an honest
supporter of K at v_s extends K and not B: this is a loss of B at that tick. -/
theorem healing_loss_of_supporter [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {K B : FGBlock (Fin p.n)} {s sB : Slot} (hK : SourceBefore p c E rho i K s)
    (hB : HighSrcN p c E rho B sB) (hlt : sB < s)
    (hn : ¬ Block.Compatible (eraseFG B) (eraseFG K)) :
    ∃ k, Lost p c E rho B sB k ∧
      ∀ k' (ev : V2.Event V (fgsa p c).Object), rho.events[k']? = some ev →
        SA.voteTime p.toParams s < ev.time → k < k' := by
  obtain ⟨k, z, hz, hk, hKH, hord⟩ :=
    healing_source_supporter p c E rho hrec emittedNonempty emittedName hK
  refine ⟨k, ⟨hB, z, s, hz, hlt, hk, fun hBH => hn ?_⟩, hord⟩
  exact Gen.Pure.block_compatible_of_common hBH hKH

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `support` (corrected signature, blocker B1);
blueprint 21:2730–2737. DC: INTENTIONAL global event-index measure. This is
the corrected `support` input of `healing_high_source_first_failure` at
c₀ = μ + 1: B is a high source with a row before i. The loss is at the HEAD
tick of an honest supporter of K at v_s, before the row of K at d_s < i. -/
theorem healing_loss_support [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    ∀ i K s B sB, SourceBefore p c E rho i K s → muOf p c E rho + 1 ≤ (heightView p K).h →
      SourceBefore p c E rho i B sB → muOf p c E rho + 1 ≤ (heightView p B).h →
      sB < s → ¬ Block.Compatible (eraseFG B) (eraseFG K) →
      ∃ k < i, Lost p c E rho B sB k := by
  intro i K s B sB hK _ hB hcB hlt hn
  obtain ⟨k, hL, hord⟩ := healing_loss_of_supporter p c E rho hrec emittedNonempty
    emittedName hK ⟨healing_srcN_of_source p c E rho hB, hcB⟩ hlt hn
  obtain ⟨j, y, r, a, hji, ha, -, rfl⟩ := hK
  have hd : SA.voteTime p.toParams (r * p.R) < (V2.Event.tick y (p.actionTime r) :
      V2.Event V (fgsa p c).Object).time := by
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ <
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact ⟨k, lt_trans (hord j _ ha.2.1 hd) hji, hL⟩

end AvailableChain.FGSA.Run
end
