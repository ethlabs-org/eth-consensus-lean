module
public import AvailableChainFGSAProofs.Proofs.Finality.RecordInv
public import AvailableChainKitFG.HeightHistoryTransfer

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem ktail_clock_read (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ j, rho.events[j]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) t = nd := by
  rw [postClock_def, preTick_def] at hnd
  cases hj : V2.D.Run.tickIdx? rho x t with
  | none => rw [hj] at hnd; cases hnd
  | some j =>
      rw [hj] at hnd
      exact ⟨j, V2.D.Run.tickIdx?_spec hj, Option.some.inj hnd⟩

/-! ### Plateau action head with independent heights -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1993–1996 (FT-Tail-W: "the cap and the action-head argument after Q0
give a common pending (h_K, K)"), plan §2 "Plateau head". The full action walk covers
D. Under the source-height cap the head stays on D's plateau, so it keeps D's
justification (hK, K) and entry. hK and K are free: no finality bound is imposed.
DC: INTENTIONAL: height plateau; the finality split is separate (TailSplit). -/
theorem ktail_plateau_action_head
    (k : Nat) (x : V) (q sourceH : Nat) (D : FGBlock (Fin p.n))
    (nd : Node p) (raw support : List (GridCO.Wire p.n .root))
    (seats : Finset (Fin p.n)) (m : Nat)
    (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hread : storeAt p c E rho k x = nd.st)
    (hwalk : TWalk p c E rho)
    (hhead : FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support)
    (hcount : Gen.Pure.Batch seats.card m)
    (hD : D ∈ FGSA.fullTree p nd.st)
    (hcompat : Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG D))
    (hbatch : WalkBatch p c rho nd.st (q * p.R + 1)
      raw support (eraseFG D) seats m)
    (hDh : (heightView p D).h = sourceH)
    (hcap : ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ sourceH) :
    ∃ H : FGBlock (Fin p.n),
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      H ∈ nd.st.fg.TF ∧ FGBlock.Preceq D H ∧
      (heightView p H).h = sourceH ∧
      (heightView p H).J = (heightView p D).J ∧
      (heightView p H).h_j = (heightView p D).h_j ∧
      (heightView p H).T_h = (heightView p D).T_h := by
  obtain ⟨j, _hj, hclock⟩ := ktail_clock_read p c E rho x (p.actionTime q) nd hnd
  have hinv : CStoreInv p nd.st := by
    rw [← hclock]
    exact (storeBundle_postClock E rho j x (p.actionTime q)).cstore
  have hcover := (hwalk k x (q * p.R + 1) raw support D seats m hx hcount
    (by simpa only [hread] using hD) (by simpa only [hread] using hcompat)
    (by simpa only [hread] using hbatch)).1
  rw [hread, ← hhead] at hcover
  obtain ⟨H, hH, hHe⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
  have hdecode := (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hH, hHe⟩
  have hDmem : D ∈ nd.st.fg.TF := (Finset.filter_subset _ _) hD
  have hDH := preceq_of_eraseFG_preceq (viewRootInj_TF p nd.st hinv)
    ⟨D, hDmem, KitFG.preceq_refl D⟩ ⟨H, hH, KitFG.preceq_refl H⟩
    (by simpa only [hHe] using hcover)
  have hlaws := (fgCertificateLaws p).height
  have hHh : (heightView p H).h = sourceH :=
    Nat.le_antisymm (hcap H hH) (hDh ▸ hlaws.h_mono hDH)
  have hplateau := KitFG.justification_eq_on_plateau_of_bridge p.E p.cfg
    (heightView p) (heightView_bridge p) hDH (hDh.trans hHh.symm)
  exact ⟨H, hdecode, hH, hDH, hHh, hplateau.1, hplateau.2,
    (hlaws.entry_plateau hDH (hDh.trans hHh.symm)).symm⟩

/-! ### Fresh rows with independent source and certificate heights -/

private theorem ktail_release (sourceH hK : Nat) (hlt : hK < sourceH)
    (K C : FGBlock (Fin p.n)) (st : State p.n) (Λ : RecordOnce)
    (hsource : FGSA.fgSource p st = some C) (hC : (heightView p C).h = sourceH)
    (hfields : (FGSA.fgInputs p st).2.h_j = hK ∧
      (FGSA.fgInputs p st).2.J = K.root ∧ (FGSA.fgInputs p st).2.h_F < hK)
    (hrecord : (Λ.target hK = none ∨ Λ.target hK = some K.root) ∧
      Λ.timeout hK = false ∧ (Λ.lock hK = none ∨ Λ.lock hK = some K.root) ∧
      Λ.target sourceH = none ∧ Λ.timeout sourceH = false ∧
      Λ.lock sourceH = none ∧
      (∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ NamedHeightPair.vote sourceH T timeout)) :
    (attest p st Λ ⟨0, p.nPos⟩).1 =
      some (.vote ⟨.vote sourceH (heightView p C).T_h.root false, some ⟨hK, K.root⟩⟩) := by
  obtain ⟨ht, hto, hl, htn, hton, hln, hsent⟩ := hrecord
  have hfp : finality_pair Λ.toRecord (FGSA.fgInputs p st).2 = some ⟨hK, K.root⟩ := by
    delta finality_pair
    simp only [hfields.1, hfields.2.1, hfields.2.2, ht, hto, hl,
      and_self, ↓reduceIte]
  have hsrc : (FGSA.fgInputs p st).1 = some C := hsource
  have hne : hK ≠ sourceH := Nat.ne_of_lt hlt
  have hhp : height_pair Λ.toRecord
      ((FGSA.fgInputs p st).1.map
        (fun C => ((heightView p C).h, (heightView p C).T_h.root)))
      (some ⟨hK, K.root⟩) = .vote sourceH (heightView p C).T_h.root false := by
    simp only [hsrc, Option.map_some, hC, height_pair, own_lock, hton, Bool.false_eq_true,
      ↓reduceIte, hne, hln, htn]
  have hsame : sameHeightOnce Λ sourceH (heightView p C).T_h.root false = false := by
    delta sameHeightOnce
    rw [List.any_eq_false]
    intro b hb
    cases hh : b.1 with
    | empty => simp only [Bool.false_eq_true, not_false_eq_true]
    | vote h T timeout =>
        have hne' : h ≠ sourceH := by
          intro he
          exact hsent b hb T timeout
            (hh.trans (congrArg (fun k => NamedHeightPair.vote k T timeout) he))
        simp only [hne', decide_false, Bool.false_and, Bool.false_eq_true,
          not_false_eq_true]
  have hkey : (NamedHeightPair.vote sourceH (heightView p C).T_h.root false,
      some (FinalityPair.mk hK K.root)) ∉ Λ.sent := by
    intro hm
    exact hsent _ hm _ false rfl
  dsimp only [attest]
  rw [createRowOnce_def, attest_source_heightView, hfp]
  dsimp only
  rw [hhp]
  delta Row.onceKey RowBody.ofRow
  simp only [hsame, Bool.false_eq_true, ↓reduceIte,
    Option.filter_some, hlt, decide_true, hkey, Option.map_some]

private theorem ktail_honestSeats_eq : honestSeats p c rho = by
    classical
    exact Finset.univ.filter (fun i => rho.seatOf (.base .fg) i ∈ rho.honest) := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1997–2000 (FT-Tail-W: "fresh height e+1 ensures that send-once suppresses
none. Each honest identity sends the exact finality pair in its new higher-height
row"), plan §2 schema. Awake actions with a fresh source at sourceH and the pending head
fields (hK, K) release complete rows: height sourceH with D's entry and finality pair
(hK, K). hK < sourceH is the only height relation.
DC: INTENTIONAL: durable record and both send-once checks; source ancestry fixes the
entry. The output is not FreshFinalityRows_W when sourceH ≠ hK + 1. -/
theorem ktail_fresh_rows
    (q sourceH hK : Nat) (hlt : hK < sourceH) (D K : FGBlock (Fin p.n))
    (S : Finset (Fin p.n))
    (hS : S ⊆ honestSeats p c rho)
    (hDh : (heightView p D).h = sourceH)
    (hreads : ∀ i ∈ S, ∃ nd C,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd ∧
      E.awake (rho.seatOf (.base .fg) i) (p.actionTime q) = true ∧
      FGSA.fgSource p nd.st = some C ∧
      FGBlock.Preceq D C ∧ (heightView p C).h = sourceH)
    (hfields : ∀ i ∈ S, ∀ nd,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd →
      (FGSA.fgInputs p nd.st).2.h_j = hK ∧
      (FGSA.fgInputs p nd.st).2.J = K.root ∧
      (FGSA.fgInputs p nd.st).2.h_F < hK)
    (hrecord : ∀ i ∈ S, ∀ nd,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd →
      (nd.record.target hK = none ∨ nd.record.target hK = some K.root) ∧
      nd.record.timeout hK = false ∧
      (nd.record.lock hK = none ∨ nd.record.lock hK = some K.root) ∧
      nd.record.target sourceH = none ∧
      nd.record.timeout sourceH = false ∧
      nd.record.lock sourceH = none ∧
      (∀ b ∈ nd.record.sent, ∀ T timeout,
        b.1 ≠ NamedHeightPair.vote sourceH T timeout))
    (hearlier : ∀ i ∈ S, ∀ j r a h, r < q →
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) r a →
      rowHeight a = some h → h < sourceH) :
    ∃ rows : Fin p.n → RowWire p.n, ∀ i ∈ S, ∃ j C,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) q (rows i) ∧
      RowComplete p c rho (rho.seatOf (.base .fg) i) (rows i) ∧
      (rows i).auth = .seat .fg i ∧
      rowHeight (rows i) = some sourceH ∧
      FinalityNames p (rows i) hK K ∧
      actionSourceFG p c E rho (rho.seatOf (.base .fg) i) q = some (some C) ∧
      (heightView p C).h = sourceH ∧
      (rows i).payload.height_pair =
        NamedHeightPair.vote sourceH (heightView p D).T_h.root false ∧
      (∀ j' r a h, r < q →
        HonestRowAt p c E rho j' (rho.seatOf (.base .fg) i) r a →
        rowHeight a = some h → h < sourceH) := by
  classical
  let body : RowPayload := .vote
    ⟨.vote sourceH (heightView p D).T_h.root false, some ⟨hK, K.root⟩⟩
  let rows : Fin p.n → RowWire p.n := fun i => ⟨.seat .fg i, body⟩
  refine ⟨rows, ?_⟩
  intro i hi
  obtain ⟨nd, C, hnd, hawake, hsource, hDC, hCh⟩ := hreads i hi
  have hentry := (fgCertificateLaws p).height.entry_plateau hDC (hDh.trans hCh.symm)
  have hem := ktail_release p sourceH hK hlt K C nd.st nd.record hsource hCh
    (hfields i hi nd hnd) (hrecord i hi nd hnd)
  rw [← hentry] at hem
  obtain ⟨j, hj, hclock⟩ := ktail_clock_read p c E rho
    (rho.seatOf (.base .fg) i) (p.actionTime q) nd hnd
  have hrelease : ofRow p (rows i) ∈ V2.D.Run.emitsAt E rho j := by
    apply (fgsa_emitsAt_row E rho j _ _ hj i body).mpr
    refine ⟨hawake, rfl, q, rfl, ?_⟩
    have hs := congrArg Node.st hclock
    have hr : (V2.D.Run.stateBefore E rho j (rho.seatOf (.base .fg) i)).record =
        nd.record := by
      exact (clock_rec (c := c)
        (V2.D.Run.stateBefore E rho j (rho.seatOf (.base .fg) i)) (p.actionTime q)).symm.trans
        (congrArg Node.record hclock)
    rw [show (FGSA.clock p _ _ ) = nd.st from hs, hr]
    exact hem
  have hhonest : rho.seatOf (.base .fg) i ∈ rho.honest := by
    have hmem := hS hi
    rw [ktail_honestSeats_eq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨j, C, ?_, ?_, rfl, rfl, ?_, ?_, hCh, rfl, hearlier i hi⟩
  · rw [HonestRowAt_def]
    exact ⟨hhonest, hj, hrelease⟩
  · change (decide (1 ≤ sourceH) && decide (hK < sourceH)) = true ∧
      RowSigner p c rho (rows i) (rho.seatOf (.base .fg) i)
    refine ⟨by simp only [Nat.one_le_of_lt hlt, hlt, decide_true, Bool.and_self], ?_⟩
    rw [RowSigner_def]
    exact ⟨i, rfl, rfl⟩
  · rw [FinalityNames_def]
    rfl
  · rw [actionSourceFG_def, hnd]
    change some (FGSA.fgSource p nd.st) = some (some C)
    rw [hsource]

/-! ### FF2 record guards with independent heights -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1997–2000 (FT-Tail-W: "FF2 permits finality; fresh height e+1 ensures that
send-once suppresses none"), plan §2 "hrecord". At the actual action read: the three FF2
guards at the stored block's latest pair (hK, K), and freshness at sourceH. The key
is bound to an honest source behind its justification QC, not to the Tail target.
DC: INTENTIONAL: H1 and QC origin replace a fixed-root window premise; the round cut
becomes a prefix cut by strict tick time; clock_rec transports the record. -/
theorem ktail_record_guards_at_action (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hs : V2.D.ScheduleWellFormed E rho)
    (i₀ : Nat) (x₀ : V) (W : FGBlock (Fin p.n)) (hx₀ : x₀ ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i₀ x₀).fg.TF)
    (hhigh : w.M + 1 ≤ (heightView p W).h_j)
    (sourceH : Nat) (q : Nat) (x : V) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, r < q → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h < sourceH) :
    ∀ nd, postClock E rho x (p.actionTime q) = some nd →
      (nd.record.target (heightView p W).h_j = none ∨
        nd.record.target (heightView p W).h_j = some (heightView p W).J.root) ∧
      nd.record.timeout (heightView p W).h_j = false ∧
      (nd.record.lock (heightView p W).h_j = none ∨
        nd.record.lock (heightView p W).h_j = some (heightView p W).J.root) ∧
      nd.record.target sourceH = none ∧ nd.record.timeout sourceH = false ∧
      nd.record.lock sourceH = none ∧
      ∀ b ∈ nd.record.sent, ∀ T timeout, b.1 ≠ .vote sourceH T timeout := by
  obtain ⟨entry, hsrc, hguards⟩ := high_entry_record_invariant p c E rho w hh hqc hnames
  obtain ⟨_, -, hid⟩ := ff2_high_qc_identity p c E rho w hh hqc hnames
  obtain ⟨-, z, r, C, hz, hsC, hcC, hCh, hJC⟩ := (hid i₀ x₀ W hx₀ hW).2.1 hhigh
  have hentry : entry (heightView p W).h_j = (heightView p W).J.root := by
    rw [← hCh, hsrc z r C hz hsC hcC, hJC]
  intro nd hnd
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime q) with
  | none => simp only [hi, Option.map_none] at hnd; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hnd
    have hj := V2.D.Run.tickIdx?_spec hi
    have hr : (V2.D.Run.stateBefore E rho i x).record = nd.record :=
      (clock_rec (c := c) (V2.D.Run.stateBefore E rho i x) (p.actionTime q)).symm.trans
        (congrArg Node.record hnd)
    have hg := hguards i x (heightView p W).h_j hx hhigh
    have hf := high_record_fresh_at_cut p c E rho i x sourceH hx (by
      intro j r a h hji ha hah
      have ht := fgsa_tick_time_strict E rho hs ha.2.1 hj hji
      have hrq : r < q := by
        by_contra hn
        have hmul : ((q * p.R : Nat) : Time) ≤ ((r * p.R : Nat) : Time) := by
          exact_mod_cast Nat.mul_le_mul_right p.R (show q ≤ r by omega)
        change 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ <
          4 * p.Δ * ((q * p.R : Nat) : Time) + 6 * p.Δ at ht
        have := p.deltaPos
        nlinarith
      exact hbefore j r a h hrq ha hah)
    change (let Λ := (V2.D.Run.stateBefore E rho i x).record; _) at hg
    change (let Λ := (V2.D.Run.stateBefore E rho i x).record; _) at hf
    simp only [hr, hentry] at hg hf
    exact ⟨hg.1, hg.2.1, hg.2.2.1, hf⟩

end AvailableChain.FGSA.Run
end
