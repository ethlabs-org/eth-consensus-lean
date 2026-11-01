module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint
public import AvailableChainFGSAProofs.Proofs.Shared.ProposalRead
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposal
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalHistory
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalReceipts
-- shake keep reason: facade coverage of the RegimesService production module.
public import AvailableChainFGSAProofs.Proofs.Shared.RegimesService -- shake: keep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-! ### Times -/

private theorem iexact_gate_ne_vote (p : Params) (r s : Slot) :
    SA.gateTime p.toParams r ≠ SA.voteTime p.toParams s := by
  intro h
  change 4 * p.Δ * (r : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + p.Δ at h
  have hd := p.deltaPos
  have h2 : (4 * (r : Int) + 5 - 4 * (s : Int)) * p.Δ = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · omega
  · exact absurd h3 (ne_of_gt hd)

private theorem iexact_gate_ne_proposal (p : Params) (r s : Slot) :
    SA.gateTime p.toParams r ≠ SA.proposalTime p.toParams s := by
  intro h
  change 4 * p.Δ * (r : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) at h
  have hd := p.deltaPos
  have h2 : (4 * (r : Int) + 6 - 4 * (s : Int)) * p.Δ = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · omega
  · exact absurd h3 (ne_of_gt hd)

private theorem iexact_gate_label (p : Params) (r s : Slot)
    (h : SA.gateTime p.toParams r < SA.voteTime p.toParams s) : r + 2 ≤ s := by
  change 4 * p.Δ * (r : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + p.Δ at h
  have hd := p.deltaPos
  have hlt : (4 * (r : Int) + 6) * p.Δ < (4 * (s : Int) + 1) * p.Δ := by
    have e1 : (4 * (r : Int) + 6) * p.Δ = 4 * p.Δ * (r : Int) + 6 * p.Δ := by ring
    have e2 : (4 * (s : Int) + 1) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ := by ring
    rw [e1, e2]
    exact h
  have h4 : 4 * (r : Int) + 6 < 4 * (s : Int) + 1 := lt_of_mul_lt_mul_right hlt hd.le
  have h5 : (r : Int) + 2 ≤ (s : Int) := by omega
  exact_mod_cast h5

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 683–694; plan I-EXACT, G1 step 3.
Class (iii). DC: INTENTIONAL; off the gate times the tick is the pre-gate tick. -/
theorem inclusion_clock_offGate (p : Params) (st : State p.n) (t : Time)
    (h : ∀ r : Slot, SA.gateTime p.toParams r ≠ t) : clock p st t = clockPre p st t := by
  have hc : ¬ ((decide (0 ≤ t - 6 * p.Δ) &&
      t == SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) = true) := by
    intro hg
    obtain ⟨r, hr⟩ := (isGateTime_iff p t).mp hg
    exact h r hr
  unfold clock
  rw [ite_eq_right hc]

/-! ### Event cuts -/

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; plan I-EXACT, G1 step 3. Class (iii).
DC: INTENTIONAL; events before a tick are not later than that tick. -/
theorem inclusion_time_le_of_tick {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {z : V} {u : Time}
    (hi : rho.events[i]? = some (.tick z u)) :
    ∀ j < i, ∀ e, rho.events[j]? = some e → e.time ≤ u := by
  intro j hj e he
  by_contra hn
  have := V2.D.Engine.eventIndex_lt_of_time_lt hs hi he (lt_of_not_ge hn)
  omega

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; plan I-EXACT, G1 step 3. Class (iii).
DC: INTENTIONAL; a scheduled tick within the horizon is inside the Clean cut. -/
theorem inclusion_tick_le_timeIdx {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {z : V} {u : Time}
    (hi : rho.events[i]? = some (.tick z u)) (hu : u ≤ rho.horizon) :
    i ≤ timeIdx rho rho.horizon :=
  ((V2.D.Engine.index_lt_read_length_iff hs rho.horizon hi).mpr hu).le

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; plan I-EXACT, G1 step 3. Class (iii).
DC: INTENTIONAL; the strict cut before the vote is inside the Clean cut. -/
theorem inclusion_idxBefore_le_timeIdx (rho : V2.D.Run V (fgsa p c)) {u : Time}
    (hu : u ≤ rho.horizon) : V2.D.Run.idxBefore rho u ≤ timeIdx rho rho.horizon := by
  rw [V2.D.Run.idxBefore_def]
  unfold timeIdx
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    ((of_decide_eq_true he).le.trans hu))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; plan I-EXACT, G1 steps 2–3. Class (iii).
DC: INTENTIONAL; a gate result read by v_s was computed strictly before v_s,
so its label is at most s − 2 and it is in the strict comparison history. -/
theorem inclusion_results_before {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (s : Slot) {i : Nat}
    (hi : ∀ j < i, ∀ e, rho.events[j]? = some e → e.time ≤ SA.voteTime p.toParams s)
    {r : Slot} {B : Block} (hB : (r, B) ∈ cleanResults p c E rho i) :
    (r, B) ∈ cleanResults p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)) ∧
      r + 2 ≤ s := by
  obtain ⟨j, hj, x, hgt, hguard, hres⟩ := hB
  have hgt' : rho.events[j]? = some (.tick x (SA.gateTime p.toParams r)) := hgt
  have hle : SA.gateTime p.toParams r ≤ SA.voteTime p.toParams s := hi j hj _ hgt'
  have hlt := lt_of_le_of_ne hle (iexact_gate_ne_vote p r s)
  exact ⟨⟨j, (Gen.V2.Duty.index_lt_idxBefore_iff hs hgt' _).mpr hlt, x, hgt, hguard, hres⟩,
    iexact_gate_label p r s hlt⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; plan I-EXACT, G1 steps 2–3. Class (iii).
DC: INTENTIONAL; labelled origins read by v_s move to the comparison history. -/
theorem inclusion_belowLabel_before {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (s : Slot) {i : Nat}
    (hi : ∀ j < i, ∀ e, rho.events[j]? = some e → e.time ≤ SA.voteTime p.toParams s)
    {r : Slot} {X : Block} (hX : BelowLabel p c E rho i r X) :
    BelowLabel p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)) (s - 2) X := by
  rcases hX with hX | ⟨r', B, hB, _, hXB⟩
  · exact Or.inl hX
  · obtain ⟨hB', hl⟩ := inclusion_results_before hs s hi hB
    exact Or.inr ⟨r', B, hB', by simp only [Slot] at hl ⊢; omega, hXB⟩

/-! ### Comparison prefix, lift and frame -/

private theorem iexact_lift {n : Nat} {A B : FGBlock (Fin n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, G1 step 2.
Class (iii). DC: INTENTIONAL; a genuine gate result is the erasure of a
stored FG block of its gate node, so the comparison prefix has an FG lift. -/
theorem inclusion_comparison_lift (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {r : Slot} {D0 : Block} (hD : (r, D0) ∈ cleanResults p c E rho i) :
    ∃ D : FGBlock (Fin p.n), eraseFG D = D0 := by
  obtain ⟨j, _, x, hgt, hguard, hres⟩ := hD
  have hgt' : rho.events[j]? = some (.tick x (SA.gateTime p.toParams r)) := hgt
  rw [inclusion_gate_raw_at_tick E rho hs ⟨hgt, hguard⟩] at hres
  have hc := Option.some.inj hres
  let st := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams r)
  have hinv : CStoreInv p st := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x) _
  obtain ⟨B, _, he⟩ := (hinv.baseTree D0).mp (compat_of_confirmation p st hinv hc).2
  exact ⟨B, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, G1 step 3.
Class (iii). DC: INTENTIONAL; row origins and the comparison maximum put every
honest named entry read by v_s below the FG lift D of the comparison prefix. -/
theorem inclusion_entries_below (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (s : Slot) (D0 : Block) (D : FGBlock (Fin p.n)) (hD : eraseFG D = D0)
    (hmax : ∀ X, BelowLabel p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s))
      (s - 2) X → Block.Preceq X D0)
    {i : Nat} (hiT : i ≤ timeIdx rho rho.horizon)
    (hi : ∀ j < i, ∀ e, rho.events[j]? = some e → e.time ≤ SA.voteTime p.toParams s) :
    ∀ y r (a : RowWire p.n) e, HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some e → EntryBelow p e D := by
  intro y r a e ha he
  obtain ⟨j, hj, hrow⟩ := ha
  obtain ⟨C, _, ⟨X, hXC, hXe⟩, hC⟩ := hrows i j y r a e hiT hj hrow he
  have hCD := hmax _ (inclusion_belowLabel_before hs s hi hC)
  rw [← hD] at hCD
  exact ⟨X, KitFG.preceq_trans hXC (iexact_lift hCD), hXe⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:354–416; spec 2548–2551, 2557–2571; plan I-EXACT, G1 step 3.
Class (iii). DC: INTENTIONAL; cpPrefix_of_srcFrame at the FG lift D: F and Z
are below D and the floor is at most the height of D. -/
theorem inclusion_frame_below (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho) (hs : V2.D.ScheduleWellFormed E rho)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (s : Slot) (D0 : Block) (D : FGBlock (Fin p.n)) (hD : eraseFG D = D0)
    (hmax : ∀ X, BelowLabel p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s))
      (s - 2) X → Block.Preceq X D0)
    {i : Nat} (hiT : i ≤ timeIdx rho rho.horizon)
    (hi : ∀ j < i, ∀ e, rho.events[j]? = some e → e.time ≤ SA.voteTime p.toParams s)
    {z : V} (hz : z ∈ rho.honest) (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) (hScope : RootBlockInRun p c E rho (eraseFG D)) :
    FGBlock.Preceq (storeAt p c E rho i z).fg.F D ∧
      FGBlock.Preceq (controls p (storeAt p c E rho i z)).Z D ∧
      (controls p (storeAt p c E rho i z)).lo ≤ (heightView p D).h := by
  have _hcanonicalFrame := hframe
  have hcp := fgsa_cpPrefix_of_srcFrame p c E rho hstore hroots hstrat
  rw [CPPrefix_def] at hcp
  obtain ⟨_, hF, _, hZ, _, hlo⟩ := hcp i z D hz hScope
    (inclusion_entries_below E rho hs hrows s D0 D hD hmax hiT hi)
  exact ⟨hF, hZ, hlo⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:783–795; spec 648–655; plan I-EXACT, G1 step 3.
Class (iii). DC: INTENTIONAL; the live root is the FG root or a lease target,
so a common upper bound of both bounds the live root. -/
theorem inclusion_liveRoot_le (p : Params) (st : State p.n) (D : Block)
    (hz : Block.Preceq (eraseFG (controls p st).Z) D)
    (hobl : ∀ row ∈ st.base.obligations, Block.Preceq row.1 D) :
    Block.Preceq (liveRoot p st) D := by
  have key : ∀ (l : List Block) (init : Block), Block.Preceq init D →
      (∀ b ∈ l, Block.Preceq b D) →
      Block.Preceq (l.foldl (fun best b =>
        if best.depth < b.depth || (best.depth == b.depth && best.root < b.root) then b
        else best) init) D := by
    intro l
    induction l with
    | nil => intro init h _; exact h
    | cons a l ih =>
      intro init h hl
      rw [List.foldl_cons]
      apply ih _ _ (fun b hb => hl b (List.mem_cons_of_mem a hb))
      split
      · exact hl a (by simp)
      · exact h
  unfold liveRoot
  apply key _ _ hz
  intro b hb
  obtain ⟨row, hrow, hb⟩ := List.mem_filterMap.mp hb
  split at hb
  · cases hb
    exact hobl row hrow
  · cases hb

/-! ### Honest HEADs above the comparison prefix -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416, 02 §4.2; plan I-EXACT, G1 step 4. Class (iii).
DC: INTENTIONAL; htransfer at label q (vHead reads label q + 1), with hordered
for an older comparison result. Every honest label-(q+1) HEAD extends D0. -/
theorem inclusion_head_extends [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {ΔF : Time} (hset : CleanSet p c E rho ΔF)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (q : Slot) (hhor : SA.voteTime p.toParams (q + 2) ≤ rho.horizon)
    {x0 : V} (_hx0 : x0 ∈ rho.honest) (D0 : Block)
    (hD0 : D0 = .genesis ∨ ∃ r, (r, D0) ∈ cleanResults p c E rho
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (q + 2))))
    {y : V} (hy : y ∈ rho.honest) {k : Nat}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (q + 1))))
    (hJ : joinedAt p E rho y (q + 1) (SA.voteTime p.toParams (q + 1))) :
    Block.Preceq D0 (headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (q + 1))).st (q + 1)) := by
  have hs := hset.pre.base.valid.toScheduleWellFormed
  rcases hD0 with rfl | ⟨r, j, hj, x, hgt, hguard, hres⟩
  · exact block_genesis_preceq _
  have hvh := vHead_eq_headAtIdx p c E rho hs hk
  have hread : headAtIdx p c E rho k (q + 1) = headVote p ((fgsa p c).clock
      (V2.D.Run.stateBefore E rho k y) (SA.voteTime p.toParams (q + 1))).st (q + 1) := by
    delta headAtIdx
    rw [hk]
  rw [hread] at hvh
  have hgt' : rho.events[j]? = some (.tick x (SA.gateTime p.toParams r)) := hgt
  have htime : SA.gateTime p.toParams r < SA.voteTime p.toParams (q + 2) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hgt' _).mp hj
  have hle : r ≤ q := by
    have := iexact_gate_label p r (q + 2) htime
    simp only [Slot] at this ⊢
    omega
  have hx := hs.honest_only _ (List.mem_of_getElem? hgt')
  have hgr : gateResult p c E rho x r = some (some D0) :=
    (gateResultAt_eq_gateResult p c E rho hs hgt) ▸ hres
  have hg : SA.gateTime p.toParams r ≤ rho.horizon := htime.le.trans hhor
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · have hgq : SA.gateTime p.toParams q ≤ rho.horizon := by
      refine le_trans ?_ hhor
      change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((q + 2 : Nat) : Int) + p.Δ
      push_cast
      linarith [p.deltaPos]
    have heq : ((4 * q + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams q := by
      change ((4 * q + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (q : Int) + 6 * p.Δ
      push_cast
      ring
    obtain ⟨z, hz, _, _, j0, hG⟩ := inclusion_joined_gate_witness E rho hset q hgq
    have hj0 := hG.1
    obtain ⟨C, hC, _⟩ := hnonempty j0 z q
      ((V2.D.Engine.index_lt_read_length_iff hs rho.horizon hj0).mpr hgq) hz hG
    have hCq : gateResult p c E rho z q = some (some C) :=
      (gateResultAt_eq_gateResult p c E rho hs (show IsGateTick p c rho j0 z q from hj0)) ▸ hC
    exact block_preceq_trans ((hordered x z r q D0 C hx hz hg hgq hgr hCq).1 hlt)
      (htransfer z y q C _ hz hy hgq hCq hJ hvh)
  · exact htransfer x y r D0 _ hx hy hg hgr hJ hvh

/-! ### G1: retained read premises for every honest reader -/

private theorem iexact_not_prec_of_eq {A B : Block} (h : A = B) : ¬ Block.Prec A B := by
  intro hp
  have hn := (Bool.and_eq_true_iff.mp hp).1
  simp only [h, decide_true, Bool.not_true, Bool.false_eq_true] at hn

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:341–416, 21 H.17:2958–3012; spec 1063–1114, 1276–1302;
plan I-EXACT, G1 steps 2–7. Class (iii). DC: INTENTIONAL; produce the
retained read premises from the field-level Clean history, not from assumed
geometry. D is the FG lift of the deepest genuine result read before v_s.
cpPrefix_of_srcFrame bounds F, Z and the floor of every honest store by D.
Lease origins bound both live roots by D. Honest label-(s−1) HEADs extend D
by htransfer, so D has prior support in the proposer pools and the target
scores in each reader pool. fgsa_retainedReads_H17 assembles the fields.
parent_height uses the stored source parent Q. Readers have the exact joined guard. -/
theorem inclusion_retained_cone [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (s : Slot) (hhor : SA.voteTime p.toParams s ≤ rho.horizon)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hstrat : RStrat p c E rho) :
    ∃ D0 : Block, ∃ D : FGBlock (Fin p.n),
      BelowLabel p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)) (s - 2) D0 ∧
      (∀ X, BelowLabel p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s))
        (s - 2) X → Block.Preceq X D0) ∧
      eraseFG D = D0 ∧
      ∀ y ∈ rho.honest, ∀ ih,
        rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
        joinedAt p E rho y s (SA.voteTime p.toParams s) →
        RetainedConeInput p
          (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
          (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D := by
  classical
  have hE := hset.pre.base.valid
  have hDelta := hset.pre.base.delta
  have hC := hset.pre.base.cstar
  have hs := hE.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  obtain ⟨D0, hBL, hmax⟩ := inclusion_comparison_prefix E rho hs hordered
    (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)) (s - 2)
  have hD0 : D0 = .genesis ∨ ∃ r, (r, D0) ∈ cleanResults p c E rho
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)) := by
    rcases hBL with h | ⟨r, B, hB, hr, hDB⟩
    · exact Or.inl h
    · have hBD := hmax B (Or.inr ⟨r, B, hB, hr, block_preceq_refl B⟩)
      rw [block_preceq_antisymm hDB hBD]
      exact Or.inr ⟨r, hB⟩
  obtain ⟨D, hD⟩ : ∃ D : FGBlock (Fin p.n), eraseFG D = D0 := by
    rcases hD0 with h | ⟨r, hm⟩
    · exact ⟨.genesis, by rw [h]; rfl⟩
    · exact inclusion_comparison_lift E rho hs hm
  have hScope : RootBlockInRun p c E rho (eraseFG D) := by
    rw [hD]
    exact rootScope_belowLabel hE hx hBL
  refine ⟨D0, D, hBL, hmax, hD, ?_⟩
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith
  have hipCut : ∀ j < ip, ∀ e, rho.events[j]? = some e →
      e.time ≤ SA.voteTime p.toParams s :=
    fun j hj e he => (inclusion_time_le_of_tick hs hip j hj e he).trans htv
  have hipT := inclusion_tick_le_timeIdx hs hip (htv.trans hhor)
  obtain ⟨hFx, hZx, hlox⟩ := inclusion_frame_below (hroots := hset.pre.base.idealization)
    (hstrat := hstrat) (hScope := hScope) E rho hstore hframe hsrc hs hrows s D0 D hD
    hmax hipT hipCut hx
  let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
  have hsrcCtrl : controls p src = controls p (storeAt p c E rho ip x) :=
    congrArg (KitFG.treeStoreControlsView (heightView p)) (clock_fg p _ _)
  have hzsrc : Block.Preceq (RetainedWalk.z p src) D0 := by
    change Block.Preceq (eraseFG (controls p src).Z) D0
    rw [hsrcCtrl, ← hD]
    exact eraseFG_preceq hZx
  have hap : Block.Preceq (RetainedWalk.ap p src) D0 := by
    apply inclusion_liveRoot_le p src D0 hzsrc
    intro row hrow
    have hrow' : row ∈ (storeAt p c E rho ip x).base.obligations := by
      change row ∈ (clock p (storeAt p c E rho ip x) _).base.obligations at hrow
      rw [inclusion_clock_offGate p _ _ (fun r => iexact_gate_ne_proposal p r s)] at hrow
      exact (clockPre_obligations_sublist p _ _).subset hrow
    exact hmax _ (inclusion_belowLabel_before hs s hipCut (hleases ip x hipT hx row hrow'))
  have hsfloor : (controls p src).lo ≤ (heightView p D).h := by
    rw [hsrcCtrl]
    exact hlox
  have hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s) :=
    Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho (fun o => ¬ isRowObject o) rho.horizon _ _
      hset.pre.healthy (fgsaDelay_nonrow E.Δ ΔF) (by
        rw [hDelta]
        change 4 * p.Δ * (s : Int) - p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
        linarith) hhor le_rfl
  intro y hy ih hih hJ
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
  have hihCut := inclusion_time_le_of_tick hs hih
  have hihT := inclusion_tick_le_timeIdx hs hih hhor
  obtain ⟨hFy, hZy, hloy⟩ := inclusion_frame_below (hroots := hset.pre.base.idealization)
    (hstrat := hstrat) (hScope := hScope) E rho hstore hframe hsrc hs hrows s D0 D hD
    hmax hihT hihCut hy
  have hdstCtrl : controls p dst = controls p (storeAt p c E rho ih y) :=
    congrArg (KitFG.treeStoreControlsView (heightView p)) (clock_fg p _ _)
  have hzdst : Block.Preceq (eraseFG (controls p dst).Z) D0 := by
    rw [hdstCtrl, ← hD]
    exact eraseFG_preceq hZy
  have hay : Block.Preceq (RetainedWalk.ay p dst) D0 := by
    apply inclusion_liveRoot_le p dst D0 hzdst
    intro row hrow
    have hrow' : row ∈ (storeAt p c E rho ih y).base.obligations := by
      change row ∈ (clock p (storeAt p c E rho ih y) _).base.obligations at hrow
      rw [inclusion_clock_offGate p _ _ (fun r => iexact_gate_ne_vote p r s)] at hrow
      exact (clockPre_obligations_sublist p _ _).subset hrow
    exact hmax _ (inclusion_belowLabel_before hs s hihCut (hleases ih y hihT hy row hrow'))
  have htfloor : (controls p dst).lo ≤ (heightView p D).h := by
    rw [hdstCtrl]
    exact hloy
  have hDD : Block.Preceq (eraseFG D) D0 := by
    rw [hD]
    exact block_preceq_refl _
  rcases hD0 with hg | ⟨r, hm⟩
  · have hle0 : ∀ X, Block.Preceq X D0 → X = .genesis := fun X h =>
      block_preceq_antisymm (hg ▸ h) (block_genesis_preceq X)
    refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_, hsfloor, htfloor, ?_⟩
    · rw [hle0 _ hap]
      exact block_genesis_preceq _
    · rw [hle0 _ hay]
      exact block_genesis_preceq _
    · rw [hle0 _ hDD]
      exact block_genesis_preceq _
    · intro L hL hprec
      have hL0 : L = .genesis := by
        rcases hL with rfl | rfl
        · exact hle0 _ hzsrc
        · exact hle0 _ hDD
      exact (iexact_not_prec_of_eq ((hle0 _ hay).trans hL0.symm) hprec).elim
  -- A genuine comparison result needs s = q + 2.
  obtain ⟨_, hr2⟩ := inclusion_results_before hs s
    (fun j hj e he => ((Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mp hj).le) hm
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by simp only [Slot] at hr2 ⊢; omega⟩
  have hvt1 : ((4 * (q + 1) + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams (q + 1) := by
    change ((4 * (q + 1) + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  have het1 : ((4 * (q + 1) + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams (q + 1) := by
    change ((4 * (q + 1) + 2 : Nat) : Int) * p.Δ = 4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
    push_cast
    ring
  have hev : SA.earlyTime p.toParams (q + 1) < SA.proposalTime p.toParams (q + 2) := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ < 4 * p.Δ * ((q + 2 : Nat) : Int)
    push_cast
    linarith
  have hevs := hev.trans_le htv
  have hv1 : SA.voteTime p.toParams (q + 1) < SA.earlyTime p.toParams (q + 1) := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
    linarith
  have hef : SA.earlyTime p.toParams (q + 1) < SA.freezeTime p.toParams (q + 1) := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ < 4 * p.Δ * ((q + 1 : Nat) : Int) + 3 * p.Δ
    linarith
  have he1 : SA.earlyTime p.toParams (q + 1) ≤ rho.horizon := (hevs.trans_le hhor).le
  have hpart := hset.sleepPre.sleepPre.joinedPartBefore (SA.voteTime p.toParams (q + 1)) (by
      change 0 ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
      positivity) ((hv1.trans hevs).trans_le hhor)
  obtain ⟨H, hH, hbatch⟩ := inclusion_joined_head_seats E rho hC (q + 1) ⟨hpart⟩
  have hSyncE : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (q + 1)) (SA.earlyTime p.toParams (q + 1)) :=
    Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho (fun o => ¬ isRowObject o) rho.horizon _ _
      hset.pre.healthy (fgsaDelay_nonrow E.Δ ΔF) (by
        rw [hDelta]
        change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ + p.Δ ≤
          4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
        linarith) he1 le_rfl
  have hvoter : ∀ w ∈ H, ∃ K kk, rho.events[kk]? = some (.tick
      (rho.seatOf (.base (.head (q + 1))) w) (SA.voteTime p.toParams (q + 1))) ∧
      headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho kk
        (rho.seatOf (.base (.head (q + 1))) w)) (SA.voteTime p.toParams (q + 1))).st
        (q + 1) = K ∧ Block.Preceq D0 K := by
    intro w hw
    have hyw := ((hH w).mp hw).1
    obtain ⟨kk, hkk, _⟩ := fgsa_tick_total E rho hs hDelta _ hyw (4 * (q + 1) + 1)
      (hvt1 ▸ (hv1.trans hevs).le.trans hhor)
      (hvt1 ▸ ((hH w).mp hw).2.1)
    rw [hvt1] at hkk
    exact ⟨_, kk, hkk, rfl, inclusion_head_extends E rho hset hordered hnonempty
      htransfer q hhor hx D0 (Or.inr ⟨r, hm⟩) hyw hkk ((hH w).mp hw).2⟩
  -- Proposer pools.
  have hJP := inclusion_joinedAt_of_proposal E rho hE hip N hem
  have hax : E.awake x (SA.earlyTime p.toParams (q + 1)) = true := by
    apply fgsa_awake_of_joinedAt E rho x (q + 2) _ _ hJP
    · change 0 ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ; positivity
    · change 4 * p.Δ * (((q + 2 : Nat) : Int) - 1) ≤
        4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
      push_cast; linarith
    · exact hev.le
  obtain ⟨jx, hjx, _⟩ := fgsa_tick_total E rho hs hDelta x hx
    (4 * (q + 1) + 2) (het1 ▸ he1) (het1 ▸ hax)
  rw [het1] at hjx
  obtain ⟨hFjx, -, -⟩ := inclusion_frame_below (hroots := hset.pre.base.idealization)
    (hstrat := hstrat) (hScope := hScope) E rho hstore hframe hsrc hs hrows (q + 2) D0 D hD
    hmax (inclusion_tick_le_timeIdx hs hjx he1)
    (fun j hj e he => (inclusion_time_le_of_tick hs hjx j hj e he).trans hevs.le) hx
  have hjxip : jx < ip := V2.D.Engine.eventIndex_lt_of_time_lt hs hjx hip hev
  have hEpochx := inclusion_epoch_of_joined_tick E rho hs hip hJP
    (a := SA.earlyTime p.toParams (q + 1)) (by
      change 4 * p.Δ * (((q + 2 : Nat) : Int) - 1) <
        4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
      push_cast; linarith)
  have hCutx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams (q + 1)) ≤ jx := by
    apply Nat.le_of_not_gt
    intro hn
    exact (lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hs hjx _).mp hn)).elim
  have hrecP : ∀ w ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (q + 2 - 1))) w)
        (ofHead p ⟨.seat (.head (q + 2 - 1)) w, K.root⟩) t ∧
      baseVote (⟨.seat (.head (q + 2 - 1)) w, K.root⟩ : HeadWire p.n) ∈ src.base.votes ∧
      K ∈ (actView src).blocks ∧ K.slot ≤ q + 2 - 1 ∧ Block.Preceq D0 K := by
    intro w hw
    obtain ⟨hyw, haw⟩ := (hH w).mp hw
    obtain ⟨K, kk, hkk, hK, hDK⟩ := hvoter w hw
    have hFK : Block.Preceq (eraseFG (storeAt p c E rho jx x).fg.F) K :=
      block_preceq_trans (hD ▸ eraseFG_preceq hFjx) hDK
    have hemK : ofHead p ⟨.seat (.head (q + 1)) w, K.root⟩ ∈ rho.emitsAt E kk := by
      rw [(V2.D.Run.step_tick_eq E rho hkk).2]
      exact (fgsa_emits_head E rho _ _ _ (q + 1) w K.root).mpr
        ⟨haw.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hkk haw,
          congrArg Block.root hK.symm⟩
    obtain ⟨hHS, hBS⟩ := hInputs.early (q + 1) _ x (Or.inl rfl) (htv.trans hhor)
      (inclusion_clean_vote_gst hset _) ⟨hx, hJP⟩ jx hjx
      w K hyw ⟨kk, q + 1, w, hkk, hemK, rfl, hK.symm⟩ hFK
    obtain ⟨hem', hv, _, hKb, _, hslot⟩ :=
      inclusion_head_receipt_early_on E rho hE (q + 1) hjx w hyw haw hkk K hK
        hHS.some hBS (hEpochx.mono le_rfl hjxip.le) hset.pre.base.receiptIdealization
    have hkeep := inclusion_stamps_kept_on E rho hjxip.le x
      (hEpochx.mono hCutx le_rfl) _ K hv hKb
    refine ⟨K, _, hem', ?_, ?_, hslot, hDK⟩
    · change _ ∈ (clock p (storeAt p c E rho ip x) _).base.votes
      rw [(clock_vn _ _).1]
      exact hkeep.1
    · apply (actView_blocks src K).mpr
      refine ⟨?_, ?_⟩
      · change K ∈ (clock p (storeAt p c E rho ip x) _).base.blocks
        rw [clock_base_blocks]
        exact hkeep.2.1
      · apply block_compatible_of_common (block_preceq_refl K)
        change Block.Preceq (eraseFG (clock p (storeAt p c E rho ip x) _).fg.F) K
        rw [clock_fg]
        exact block_preceq_trans (hD ▸ eraseFG_preceq hFx) hDK
  have hPP := inclusion_receiver_proposer_prior_on E rho hE hC (q + 2) ip x src (by
      change (clock p (storeAt p c E rho ip x) _).base.votes = _
      exact (clock_vn _ _).1) H hH hbatch D0 (by
        change Block.Preceq (eraseFG (clock p (storeAt p c E rho ip x) _).fg.F) D0
        rw [clock_fg]
        exact hD ▸ eraseFG_preceq hFx) (by
        intro seat hseat
        obtain ⟨K, t, he, hv, hK, hslot, hDK⟩ := hrecP seat hseat
        have hInv : CStoreInv p src :=
          cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
        have hdomain : src.base.headDomain = none :=
          base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ip x))
        exact ⟨K, t, he, hv, actView_resolve_target p src hInv hdomain _ hK rfl,
          resolvedTarget_of_mem _ (baseBlocks_rootInj p src hInv) _
            (List.mem_filter.mp hK).1 rfl, hslot, hDK⟩)
  have hDsrc : D ∈ src.fg.TF := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch.lt)
    obtain ⟨K, _, _, _, hK, _, hDK⟩ := hrecP w hw
    have hinv : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
    obtain ⟨B, hB, heB⟩ := (hinv.baseTree K).mp ((actView_blocks src K).mp hK).1
    obtain ⟨C, hC', heC⟩ := eraseFG_ancestor_mem hinv.fg.closed hB
      (show Block.Preceq (eraseFG D) (eraseFG B) by rw [hD, heB]; exact hDK)
    rwa [eraseFG_injective heC] at hC'
  have hRPS : ∀ L, Block.Preceq L D0 → RetainedPriorSupport p src (q + 2) L := by
    intro L hL
    obtain ⟨hmaj, hriv⟩ := hPP L hL
    exact ⟨block_compatible_of_common hzsrc hL, ⟨D, hDsrc, by rw [hD]; exact hL, hsfloor⟩,
      hmaj, hriv⟩
  -- Reader pools.
  have hayAw : E.awake y (SA.earlyTime p.toParams (q + 1)) = true := by
    apply fgsa_awake_of_joinedAt E rho y (q + 2) _ _ hJ
    · change 0 ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ; positivity
    · change 4 * p.Δ * (((q + 2 : Nat) : Int) - 1) ≤
        4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
      push_cast; linarith
    · exact hevs.le
  obtain ⟨jy, hjy, _⟩ := fgsa_tick_total E rho hs hDelta y hy
    (4 * (q + 1) + 2) (het1 ▸ he1) (het1 ▸ hayAw)
  rw [het1] at hjy
  obtain ⟨hFjy, -, -⟩ := inclusion_frame_below (hroots := hset.pre.base.idealization)
    (hstrat := hstrat) (hScope := hScope) E rho hstore hframe hsrc hs hrows (q + 2) D0 D hD
    hmax (inclusion_tick_le_timeIdx hs hjy he1)
    (fun j hj e he => (inclusion_time_le_of_tick hs hjy j hj e he).trans hevs.le) hy
  have hjyih : jy < ih := V2.D.Engine.eventIndex_lt_of_time_lt hs hjy hih hevs
  have hEpochy := inclusion_epoch_of_joined_tick E rho hs hih hJ
    (a := SA.earlyTime p.toParams (q + 1)) (by
      change 4 * p.Δ * (((q + 2 : Nat) : Int) - 1) <
        4 * p.Δ * ((q + 1 : Nat) : Int) + 2 * p.Δ
      push_cast; linarith)
  have hCuty : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams (q + 1)) ≤ jy := by
    apply Nat.le_of_not_gt
    intro hn
    exact (lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hs hjy _).mp hn)).elim
  have hrecR : ∀ w ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (q + 1))) w)
        (ofHead p ⟨.seat (.head (q + 1)) w, K.root⟩) t ∧
      baseVote (⟨.seat (.head (q + 1)) w, K.root⟩ : HeadWire p.n) ∈ headSupport p dst (q + 1 + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ q + 1 ∧ Block.Preceq D0 K := by
    intro w hw
    obtain ⟨hyw, haw⟩ := (hH w).mp hw
    obtain ⟨K, kk, hkk, hK, hDK⟩ := hvoter w hw
    have hFK : Block.Preceq (eraseFG (storeAt p c E rho jy y).fg.F) K :=
      block_preceq_trans (hD ▸ eraseFG_preceq hFjy) hDK
    have hemK : ofHead p ⟨.seat (.head (q + 1)) w, K.root⟩ ∈ rho.emitsAt E kk := by
      rw [(V2.D.Run.step_tick_eq E rho hkk).2]
      exact (fgsa_emits_head E rho _ _ _ (q + 1) w K.root).mpr
        ⟨haw.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hkk haw,
          congrArg Block.root hK.symm⟩
    obtain ⟨hHS, hBS⟩ := hInputs.early (q + 1) _ y (Or.inr rfl) hhor
      (inclusion_clean_vote_gst hset _) ⟨hy, hJ⟩ jy hjy
      w K hyw ⟨kk, q + 1, w, hkk, hemK, rfl, hK.symm⟩ hFK
    obtain ⟨hem', hv, hvs, hKb, hbs, hslot⟩ :=
      inclusion_head_receipt_early_on E rho hE (q + 1) hjy w hyw haw hkk K hK
        hHS.some hBS (hEpochy.mono le_rfl hjyih.le) hset.pre.base.receiptIdealization
    have hkeep := inclusion_stamps_kept_on E rho hjyih.le y
      (hEpochy.mono hCuty le_rfl) _ K hv hKb
    let o := baseVote (⟨.seat (.head (q + 1)) w, K.root⟩ : HeadWire p.n)
    have hvd : o ∈ dst.base.votes := by
      change _ ∈ (clock p (storeAt p c E rho ih y) _).base.votes
      rw [(clock_vn _ _).1]
      exact hkeep.1
    have hKd : K ∈ dst.base.blocks := by
      change K ∈ (clock p (storeAt p c E rho ih y) _).base.blocks
      rw [clock_base_blocks]
      exact hkeep.2.1
    have hvsd : GridCO.stampVote (actView dst) o < SA.freezeTime p.toParams (q + 1) := by
      change GridCO.stampVote (clock p (storeAt p c E rho ih y) _).base o < _
      have hkey : o ∈ (storeAt p c E rho ih y).base.voteStamp.map Prod.fst := by
        change o ∈ (V2.D.Run.stateBefore E rho ih y).st.base.voteStamp.map Prod.fst
        rw [fgsa_vote_stamp_keys E rho ih y]
        exact hkeep.1
      rw [inclusion_stampVote_of_prefix
        (by rw [(clock_cumulative p _ _).2.2.2.1]) hkey, hkeep.2.2.1]
      exact hvs.trans hef
    have hbsd : GridCO.stampBlock (actView dst) K < SA.freezeTime p.toParams (q + 1) := by
      change GridCO.stampBlock (clock p (storeAt p c E rho ih y) _).base K < _
      have hkey : K ∈ (storeAt p c E rho ih y).base.blockStamp.map Prod.fst := by
        change K ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blockStamp.map Prod.fst
        rw [(storeBundle_stateBefore E rho ih y).«meta».stampKeys]
        exact hkeep.2.1
      rw [inclusion_stampBlock_of_prefix
        (by rw [(clock_cumulative p _ _).2.2.1]) hkey, hkeep.2.2.2]
      exact hbs.trans hef
    have hKa : GridCO.blockKnown (actView dst) K = true := by
      apply decide_eq_true
      apply (actView_blocks dst K).mpr
      refine ⟨hKd, block_compatible_of_common (block_preceq_refl K) ?_⟩
      change Block.Preceq (eraseFG (clock p (storeAt p c E rho ih y) _).fg.F) K
      rw [clock_fg]
      exact block_preceq_trans (hD ▸ eraseFG_preceq hFy) hDK
    refine ⟨K, _, hem', ?_, hKd, hslot, hDK⟩
    unfold headSupport
    dsimp only
    rw [List.mem_eraseDups]
    apply List.mem_append_left
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨hvd, beq_self_eq_true _⟩, ?_⟩
    have hInv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
    have hres := actView_resolve_target p dst hInv
      (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ih y)))
      o (of_decide_eq_true hKa) rfl
    unfold GridCO.resolvedBefore
    rw [hres]
    change (decide (K.slot ≤ q + 1) &&
      decide (GridCO.stampVote (actView dst) o < SA.freezeTime p.toParams (q + 1)) &&
      decide (GridCO.stampBlock (actView dst) K < SA.freezeTime p.toParams (q + 1))) = true
    simp only [hslot, hvsd, hbsd, decide_true, Bool.and_self]
  have hRS := inclusion_receiver_scores_on E rho hE hC hDelta (q + 1) hih H hH hbatch D0 hrecR hy
    hJ
  refine ⟨Or.inr (hRPS _ hap), Or.inr (Or.inl (hRPS _ hay)), Or.inr (hRPS _ hDD),
    hsfloor, htfloor, ?_⟩
  intro L hL _
  rcases hL with rfl | rfl
  · exact hRS _ hzsrc
  · exact hRS _ hDD

section ConeFloor

open RetainedWalk

private theorem inclusion_cone_source_path (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (L W : FGBlock (Fin p.n)) (hW : W ∈ src.fg.TF)
    (hLW : FGBlock.Preceq L W) (hZL : FGBlock.Preceq (controls p src).Z L)
    (hlo : (controls p src).lo ≤ (heightView p W).h) : eraseFG L ∈ S p src := by
  have hFL : FGBlock.Preceq src.fg.F L := by
    have hFZ := fgsa_F_preceq_Z p src hs
    exact KitFG.preceq_trans hFZ hZL
  obtain ⟨Q, hQ, heQ⟩ := eraseFG_ancestor_mem hs.fg.closed hW (eraseFG_preceq hLW)
  have hL : L ∈ src.fg.TF := (eraseFG_injective heQ) ▸ hQ
  exact List.mem_filter.mpr ⟨(hs.baseTree _).mpr ⟨L, hL, rfl⟩,
    decide_eq_true ⟨L, (KitFG.mem_filteredFromView (heightView p) (controls p src)
      src.fg.TF L).mpr ⟨hL, hFL, hZL, W, hW, hLW, hlo⟩, rfl⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:937–942; H.6-S:1027–1029. Class (iii).
DC: INTENTIONAL; prior support covers a lease target from the ordinary root. -/
private theorem inclusion_cone_supported_cover (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (s : Slot) (L : Block)
    (h : RetainedPriorSupport p src s L) :
    Block.Preceq L (GridCO.ghost (z p src) (S p src) (ss src s) (es p src s)) := by
  let bare : State p.n := { src with base := { src.base with obligations := [] } }
  have ha : liveRoot p bare = z p src := by rfl
  have hpath : ∀ C, Block.Prec (liveRoot p bare) C → Block.Preceq C L →
      C ∈ S p src := by
    intro C hZC hCL
    obtain ⟨W, hW, hLW, hlo⟩ := h.witness
    obtain ⟨B, hB, heB⟩ := eraseFG_ancestor_mem hs.fg.closed hW
      (block_preceq_trans hCL hLW)
    rw [← heB]
    apply inclusion_cone_source_path p src hs B W hW
    · exact eraseFG_preceq_iff.mp (heB ▸ block_preceq_trans hCL hLW)
    · apply eraseFG_preceq_iff.mp
      rw [heB]
      exact (Bool.and_eq_true_iff.mp hZC).2
    · exact hlo
  have hc := fgsa_headInTree_covers_of_transfer p bare (S p src)
    (proposerVotes src s) (proposerSupport src s) L
    (ha ▸ h.root_compatible) hpath h.majority h.rivals
  exact hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–944. Class (iii).
DC: INTENTIONAL; a covered target needs no fresh support below the root. -/
private theorem inclusion_cone_prior_cover (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (s : Slot) (L : Block)
    (h : Block.Preceq L (z p src) ∨ RetainedPriorSupport p src s L) :
    Block.Preceq L (GridCO.ghost (z p src) (S p src) (ss src s) (es p src s)) := by
  rcases h with h | h
  · apply walk_covers_of_dominated_suffix _ _ _ _ _ (Bool.or_eq_true_iff.mpr (Or.inr h))
    rw [DominatedSuffix_def]
    intro C hZC hCL
    have he := block_preceq_antisymm (Bool.and_eq_true_iff.mp hZC).2
      (block_preceq_trans hCL h)
    have hn := (Bool.and_eq_true_iff.mp hZC).1
    simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
  · exact inclusion_cone_supported_cover p src hs s L h

private theorem inclusion_cone_height_mono (p : Params) {D B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG D) (eraseFG B)) : (heightView p D).h ≤ (heightView p B).h := by
  exact (Window.windowHeightLaws p p.K_W p.kWLarge).h_mono (eraseFG_preceq_iff.mp h)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2968–2985; HG.1:1557–1565; L4-R:2280–2290;
L2:2159–2162. Class (iii). DC: INTENTIONAL; derive starts and parent height from prior support. -/
private theorem inclusion_cone_cone_starts (p : Params) (src dst : State p.n)
    (hs : CStoreInv p src) (s : Slot) (D : FGBlock (Fin p.n)) (b : Block)
    (hp : getHead p src (proposerVotes src s) (proposerSupport src s) = b.parent)
    (h : RetainedConeInput p src dst s D) :
    BestAncestry (z p src) (ap p src) (S p src) (ss src s) (es p src s) ∧
    Block.Preceq (z p src) b.parent ∧ Block.Preceq (ay p dst) b.parent ∧
    Block.Preceq (eraseFG D) b.parent ∧
    ∃ A ∈ src.fg.TF, eraseFG A = b.parent ∧
      (controls p src).lo ≤ (heightView p A).h ∧
      (controls p dst).lo ≤ (heightView p A).h := by
  have hc := inclusion_cone_prior_cover p src hs s (ap p src) h.proposer_prior
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hc
  have ho := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _)
    (fgsa_Z_preceq_liveRoot p src) hprefix).trans hp
  have hz := inclusion_cone_prior_cover p src hs s (z p src) (Or.inl (block_preceq_refl _))
  have hD := inclusion_cone_prior_cover p src hs s (eraseFG D) h.pivot_prior
  rw [ho] at hz hD
  have hm : b.parent ∈ src.base.blocks := by
    rw [← hp]
    rcases fgsa_headInTree_mem_or_anchor p src (S p src)
      (proposerVotes src s) (proposerSupport src s) with he | hm
    · rw [show getHead p src (proposerVotes src s) (proposerSupport src s) = ap p src from he]
      exact liveRoot_stored p src hs
    · exact (List.mem_filter.mp hm).1
  obtain ⟨A, hA, heA⟩ := (hs.baseTree _).mp hm
  have hh := inclusion_cone_height_mono p (heA.symm ▸ hD)
  have haS := h.source_floor.trans hh
  have haT := h.target_floor.trans hh
  refine ⟨hprefix, hz, ?_, hD, A, hA, heA, haS, haT⟩
  rcases h.reader_prior with h | h | h
  · exact ho ▸ inclusion_cone_prior_cover p src hs s (ay p dst) (Or.inl h)
  · exact ho ▸ inclusion_cone_prior_cover p src hs s (ay p dst) (Or.inr h)
  · exact heA ▸ h A hA haS

/-- Prior support proves the receiver floor before the proposal receipt is requested. -/
theorem inclusion_cone_receiver_floor
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_hE : V2.D.ExecutionValid E rho) {s : Slot} {ip ih : Nat} {x y : V}
    (_hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip)
    {D : FGBlock (Fin p.n)}
    (hCone : RetainedConeInput p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D) :
    Block.Preceq (F_at p c E rho ih y) N.erase := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hm := hem
  rw [(rho.step_tick_eq E hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hstarts := inclusion_cone_cone_starts p src dst
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _) s D N.erase
    hparent.2.2.symm hCone
  have hf := F_preceq_liveRoot p dst
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _)
  have hFN := block_preceq_trans (block_preceq_trans hf hstarts.2.2.1)
    (fgsa_parent_preceq N.erase)
  change Block.Preceq (eraseFG (rho.stateBefore E ih y).st.fg.F) N.erase
  simpa only [dst, clock_fg] using hFN

end ConeFloor

/-- The scoped cone supplies the receiver floor before any proposal service is used. -/
theorem inclusion_retained_reads [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (s : Slot) (hhor : SA.voteTime p.toParams s ≤ rho.horizon)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hstrat : RStrat p c E rho) :
    ∃ D0 : Block, ∃ D : FGBlock (Fin p.n),
      BelowLabel p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)) (s - 2) D0 ∧
      (∀ X, BelowLabel p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s))
        (s - 2) X → Block.Preceq X D0) ∧
      eraseFG D = D0 ∧
      ∀ y ∈ rho.honest, ∀ ih,
        rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
        joinedAt p E rho y s (SA.voteTime p.toParams s) →
        ∃ Kc, RetainedReadPremises p
          (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
          (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc := by
  obtain ⟨D0, D, hBL, hmax, hD, hCone⟩ := inclusion_retained_cone
    E rho ΔF hset hInputs hstore hframe hsrc hordered hnonempty htransfer hleases hrows
    s hhor hx hip hseat N hem hstrat
  refine ⟨D0, D, hBL, hmax, hD, ?_⟩
  apply fgsa_retainedReads_H17_joined E rho hset.pre.base.valid s hx hip hseat N hem D hCone
    (hroots := hset.pre.base.receiptIdealization)
  intro y hy ih hih hJ
  have hFN := inclusion_cone_receiver_floor E rho hset.pre.base.valid hx hip N hem
    (hCone y hy ih hih hJ)
  exact fgsa_target_service_of_proposal E rho s N _ _ y
    (hInputs.retained s ip x N hx (inclusion_clean_vote_gst hset _)
      hip hem ih y ⟨hy, hJ⟩ hih hFN).proposal

/-! ### Exact proposal: receipt and HEAD -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1 step 1.
Class (iii). DC: INTENTIONAL; the honest proposal input: an honest proposer,
its proposal tick and the emitted slot-s proposal object. -/
theorem inclusion_proposal_emission (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (s : Slot) (P : Block)
    (hprop : HonestProposal E rho (fgsaInterface p c) s P) :
    rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ ∈ rho.honest ∧
    ∃ ip N, N.erase = P ∧
      rho.events[ip]? = some (.tick (rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩)
        (SA.proposalTime p.toParams s)) ∧
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip := by
  obtain ⟨ip, N, heN, hip, hem, _⟩ := proposal_read_named p c E rho hE.toScheduleWellFormed hprop
  exact ⟨hprop.1.2, ip, N, heN, hip, hem⟩

private theorem iexact_parent_preceq (b : Block) : Block.Preceq b.parent b := by
  cases b <;> first | exact block_preceq_refl _ |
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1 (compatibility).
Class (iii). DC: INTENTIONAL; discharge the r1 reader-compatibility premise
from the field-level Clean binders. The strict-before F of every honest
reader is below the comparison prefix D, and the produced pivot puts D below
the stored proposal parent. A counted joined vote reader supplies the pivot-parent fact. -/
theorem inclusion_exact_compat [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.voteTime p.toParams pt.s ≤ rho.horizon)
    (hstrat : RStrat p c E rho) :
    ∀ x ∈ rho.honest, Block.Compatible pt.P
      (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams pt.s) x).st.fg.F) := by
  have hE := hset.pre.base.valid
  have hs := hE.toScheduleWellFormed
  obtain ⟨hx, ip, N, heN, hip, hem⟩ := inclusion_proposal_emission E rho hE pt.s pt.P hprop
  rw [← heN]
  obtain ⟨D0, D, hBL, hmax, hD, hreads⟩ := inclusion_retained_reads (hstrat := hstrat) E rho ΔF
    hset hInputs hstore hframe
    hsrc hordered hnonempty htransfer hleases hrows pt.s hhor hx hip rfl N hem
  have hvt : ((4 * pt.s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams pt.s := by
    change ((4 * pt.s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (pt.s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨z, hz, hJ, ih, hih⟩ := inclusion_joined_vote_witness E rho hset pt.s hhor
  obtain ⟨Kc, hw⟩ := hreads z hz ih hih hJ
  intro x' hx'
  have hScope : RootBlockInRun p c E rho (eraseFG D) := by
    rw [hD]
    exact rootScope_belowLabel hset.pre.base.valid hx hBL
  obtain ⟨hF, -, -⟩ := inclusion_frame_below (hroots := hset.pre.base.idealization)
    (hstrat := hstrat) (hScope := hScope) E rho hstore hframe hsrc hs hrows pt.s D0 D hD hmax
    (inclusion_idxBefore_le_timeIdx rho hhor)
    (fun j hj e he => ((Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mp hj).le) hx'
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
  exact block_compatible_of_common (block_preceq_refl _)
    (block_preceq_trans (eraseFG_preceq hF)
      (block_preceq_trans hw.pivot_parent (iexact_parent_preceq _)))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1.
Class (iii). DC: INTENTIONAL; non-row traffic uses Delta independently of
the row delay. The block-stamp route gives an actual acceptance strictly
before v_s, for joined readers. Clean history enters only as the
field-level binders; compatibility is produced, not assumed.
Conclusion: E1 of ExactProposalAt, inline. -/
theorem inclusion_exact_receipt [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (_hstore : RStore p c E rho) (_hframe : RFrameExactNext p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho)
    (_hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (_hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (_htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (_hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (_hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.voteTime p.toParams pt.s ≤ rho.horizon)
    (_hstrat : RStrat p c E rho) :
    ∀ x, headReader p E rho x pt.s (SA.voteTime p.toParams pt.s) →
      ∃ o i t, (fgsaInterface p c).block o.payload = some pt.P ∧
      t < SA.voteTime p.toParams pt.s ∧ V2.D.Run.acceptsAt E rho i x o t :=
  inclusion_proposal_receipt E rho ΔF hset pt hprop (by
    intro N hEm y hY
    obtain ⟨ip, hip, hem⟩ := hEm
    obtain ⟨ih, hih⟩ := List.mem_iff_getElem?.mp
      (hset.pre.base.valid.tick_total y hY.1 _ (by
        refine ⟨4 * pt.s + 1, ?_⟩
        rw [hset.pre.base.delta]
        change 4 * p.Δ * (pt.s : Int) + p.Δ = ((4 * pt.s + 1 : Nat) : Int) * p.Δ
        push_cast; ring) (by
          change 0 ≤ 4 * p.Δ * (pt.s : Int) + p.Δ
          have hd := p.deltaPos; positivity) hhor hY.2.1)
    obtain ⟨_, D, _, _, _, hCone⟩ := inclusion_retained_cone E rho ΔF hset hInputs
      _hstore _hframe _hsrc _hordered _hnonempty _htransfer _hleases _hrows pt.s hhor
      hprop.1.2 hip rfl N hem _hstrat
    have hFN := inclusion_cone_receiver_floor E rho hset.pre.base.valid
      hprop.1.2 hip N hem (hCone y hY.1 ih hih hY.2)
    exact (hInputs.retained pt.s ip _ N hprop.1.2 (inclusion_clean_vote_gst hset _)
      hip hem ih y hY hih hFN).proposal)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X2.
Class (iii). DC: INTENTIONAL; the produced retained read premises give the
exact HEAD by the local retained service. The strict clocked read gives
it at v_s for joined honest readers.
Conclusion: E2 of ExactProposalAt, inline. -/
theorem inclusion_exact_head [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.voteTime p.toParams pt.s ≤ rho.horizon)
    (hstrat : RStrat p c E rho) :
    ∀ x ∈ rho.honest, joinedAt p E rho x pt.s (SA.voteTime p.toParams pt.s) →
      FGSA.headVote p ((fgsa p c).clock
      (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams pt.s) x)
      (SA.voteTime p.toParams pt.s)).st pt.s = pt.P := by
  have hE := hset.pre.base.valid
  obtain ⟨hx, ip, N, heN, hip, hem⟩ := inclusion_proposal_emission E rho hE pt.s pt.P hprop
  rw [← heN]
  obtain ⟨_, D, _, _, _, hreads⟩ := inclusion_retained_reads (hstrat := hstrat)
    E rho ΔF hset hInputs
    hstore hframe
    hsrc hordered hnonempty htransfer hleases hrows pt.s hhor hx hip rfl N hem
  have hgeom := fgsa_retainedExactHead_geometry_on_run_on
    (hroots := hset.pre.base.receiptIdealization) E rho hE pt.s hx hip rfl N hem D hreads
    (by
      intro y hy ih hih hJ
      obtain ⟨Kc, hr⟩ := hreads y hy ih hih hJ
      have hf := F_preceq_liveRoot p
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams pt.s))
        (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _)
      have hFN : Block.Preceq (F_at p c E rho ih y) N.erase := by
        change Block.Preceq (eraseFG (rho.stateBefore E ih y).st.fg.F) N.erase
        simpa only [clock_fg] using block_preceq_trans
          (block_preceq_trans hf hr.target_parent) (fgsa_parent_preceq N.erase)
      exact hInputs.retained pt.s ip _ N hx (inclusion_clean_vote_gst hset _)
        hip hem ih y ⟨hy, hJ⟩ hih hFN)
  have hhead := exactService_head_of_retained_proposal_on E rho hE hset.pre.base.delta
    pt.s hip N hem D hgeom hhor
  intro y hy hJ
  exact inclusion_head_read E rho hE.toScheduleWellFormed y pt.s N.erase hJ
    (hhead y hy hJ)

end AvailableChain.FGSA.Run
end
