module
public import AvailableChainSAPC.Statements.CleanInvariant
public import AvailableChainSAPC.Proofs.GateSources
public import AvailableChainSAPC.Proofs.BaseReceipts
public import AvailableChainGridCO.Proofs.RawHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

theorem CleanPath.advance {path : Block → Prop} (h : CleanPath path)
    (a b : Block) (ha : path a) (hb : path b) :
    path (GridCO.advance a b) ∧ Block.Preceq a (GridCO.advance a b) ∧
      Block.Preceq b (GridCO.advance a b) := by
  have hc := h.comparable a b ha hb
  unfold GridCO.advance
  split
  · exact ⟨ha, GridCO.block_preceq_self a, by assumption⟩
  · rename_i hn
    have hab : Block.Preceq a b := by
      simpa [Block.Compatible, Block.compatible, hn] using! hc
    exact ⟨hb, hab, GridCO.block_preceq_self b⟩

/-- Both records are retained or advanced by the raw result. The PC
prefix loop changes neither record, even when it writes new leases. -/
theorem gateWithPC_records (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) :
    ((gateWithPC p st r cert).stableRecord = st.stableRecord ∨
      ∃ b, SA.confirmation p st r = some b ∧
        (gateWithPC p st r cert).stableRecord = GridCO.advance st.stableRecord b) ∧
    ((gateWithPC p st r cert).goldfishRecord = st.goldfishRecord ∨
      ∃ b, SA.confirmation p st r = some b ∧
        (gateWithPC p st r cert).goldfishRecord = GridCO.advance st.goldfishRecord b) := by
  have hs (base : GridCO.State n) (prefixes : List Block) (levels : Block → List Nat)
      (deadline : Time) :
      (prefixes.foldl (fun acc b => (levels b).foldl (fun acc g =>
        GridCO.writeObligation acc b g deadline) acc) base).stableRecord = base.stableRecord :=
    fold_field GridCO.State.stableRecord _
      (fun _ _ => fold_field GridCO.State.stableRecord _ (by intros; rfl) _ _) _ _
  have hg (base : GridCO.State n) (prefixes : List Block) (levels : Block → List Nat)
      (deadline : Time) :
      (prefixes.foldl (fun acc b => (levels b).foldl (fun acc g =>
        GridCO.writeObligation acc b g deadline) acc) base).goldfishRecord = base.goldfishRecord :=
    fold_field GridCO.State.goldfishRecord _
      (fun _ _ => fold_field GridCO.State.goldfishRecord _ (by intros; rfl) _ _) _ _
  cases cert <;> cases hc : SA.confirmation p st r with
  | none => simp [gateWithPC, SA.gate, GridCO.gate, hc]
  | some b =>
    simp only [gateWithPC, SA.gate, GridCO.gate, hc]
    split
    · exact ⟨Or.inl rfl, Or.inr ⟨b, rfl, rfl⟩⟩
    · rw [hs, hg]
      first
      | exact ⟨Or.inr ⟨b, rfl, rfl⟩, Or.inr ⟨b, rfl, rfl⟩⟩
      | split <;> simp

/-- Gate preservation for the finite part of the joint invariant. Its
one induction obligation is that the raw result is on the common path.
No lease-below-S premise and no fault cap are used. -/
theorem gateWithPC_clean (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) {path : Block → Prop}
    (hc : CleanPath path) (hs : CleanStateOnPath path st)
    (hraw : ∀ b, SA.confirmation p st r = some b → path b) :
    CleanStateOnPath path (gateWithPC p st r cert) ∧
      Block.Preceq st.stableRecord (gateWithPC p st r cert).stableRecord := by
  have records := gateWithPC_records p st r cert
  have hstable : path (gateWithPC p st r cert).stableRecord ∧
      Block.Preceq st.stableRecord (gateWithPC p st r cert).stableRecord := by
    rcases records.1 with he | ⟨b, hb, he⟩
    · rw [he]; exact ⟨hs.stable, GridCO.block_preceq_self _⟩
    · rw [he]
      exact ⟨(hc.advance _ b hs.stable (hraw b hb)).1,
        (hc.advance _ b hs.stable (hraw b hb)).2.1⟩
  refine ⟨⟨hstable.1, ?_, ?_, ?_⟩, hstable.2⟩
  · rcases records.2 with he | ⟨b, hb, he⟩
    · exact he ▸ hs.goldfish
    · rw [he]; exact (hc.advance _ b hs.goldfish (hraw b hb)).1
  · intro b g d hm
    rcases gateWithPC_row_origin p st r cert b g d hm with hold | ⟨c, hresult, hp, _⟩
    · exact hs.finite b g d hold
    · exact hc.closed b c hp (hraw c hresult)
  · intro s b hm
    rw [gateWithPC_genuine] at hm
    rcases @GridCO.recordGenuine_origin GridCO.slowLeasePolicy n st r s
        (SA.confirmation p st r) (some b) hm with hold | ⟨_, he⟩
    · exact hs.saved s b hold
    · exact hraw b he.symm

theorem gate_clean (p : Params) {n : Nat} (st : State n) (r : Slot)
    {path : Block → Prop} (hc : CleanPath path) (hs : CleanStateOnPath path st.base)
    (hraw : ∀ b, SA.confirmation p st.base r = some b → path b) :
    CleanStateOnPath path (gate p st r).base ∧
      Block.Preceq (stable st) (stable (gate p st r)) :=
  gateWithPC_clean p st.base r _ hc hs hraw

/-- Within the path invariant, the stable and prefix PC guards all
pass. Thus the complete base gate, including its lease loop, equals SA. -/
theorem gateWithPC_eq_sa_of_path (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) {path : Block → Prop} (hc : CleanPath path)
    (hraw : ∀ b, SA.confirmation p st r = some b → path b)
    (hpc : ∀ c, cert = some c → path c.target) :
    gateWithPC p st r cert = SA.gate p st r := by
  cases cert with
  | none => rfl
  | some c =>
    cases hr : SA.confirmation p st r with
    | none => simp [gateWithPC, SA.gate, GridCO.gate, hr]
    | some b =>
      have hguard : pcOK (some c) b = true := hc.comparable b c.target (hraw b hr) (hpc c rfl)
      have hfilter : st.blocks.filter (fun a =>
          a != .genesis && Block.preceq a b && pcOK (some c) a) =
          st.blocks.filter (fun a => a != .genesis && Block.preceq a b) := by
        apply List.filter_congr
        intro a _
        by_cases ha : (a != .genesis && Block.preceq a b) = true
        · have hpa := (Bool.and_eq_true_iff.mp ha).2
          have hga : pcOK (some c) a = true :=
            hc.comparable a c.target (hc.closed a b hpa (hraw b hr)) (hpc c rfl)
          simp only [hga, Bool.and_true]
        · simp only [Bool.eq_false_iff.mpr ha, Bool.false_and]
      simp only [gateWithPC, SA.gate, GridCO.gate, hr, hguard, ↓reduceIte]
      split
      · rfl
      · simp only [hfilter]

/-- A genuine result on the path is included at this gate if the active
PC is also on the path. Admission levels do not enter this conclusion. -/
theorem gate_clean_includes (p : Params) {n : Nat} (st : State n) (r : Slot)
    {path : Block → Prop} (hc : CleanPath path) (hs : CleanStateOnPath path st.base)
    (b : Block) (hraw : SA.confirmation p st.base r = some b) (hb : path b)
    (hpc : ∀ c, capBroken p st = false → st.bestPC = some c → path c.target) :
    Block.Preceq b (stable (gate p st r)) := by
  have he := gateWithPC_eq_sa_of_path p st.base r
    (if capBroken p st then none else st.bestPC) hc
    (fun c h => by cases hraw.symm.trans h; exact hb) (by
      intro c h
      cases hm : capBroken p st with
      | true => simp [hm] at h
      | false => exact hpc c hm (by simpa [hm] using h))
  have hguard : st.base.obligations.any (fun (target, _, _) =>
      !Block.compatible target b) = false := by
    apply List.any_eq_false.mpr
    intro row hm
    have hcomp : Block.compatible row.1 b = true :=
      hc.comparable row.1 b (hs.finite row.1 row.2.1 row.2.2 hm) hb
    simp only [hcomp, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  change Block.Preceq b (gateWithPC p st.base r _).stableRecord
  rw [he]
  have hresult : (SA.gate p st.base r).stableRecord =
      GridCO.advance st.base.stableRecord b := by
    simp only [SA.gate, GridCO.gate, hraw, hguard, Bool.false_eq_true, ↓reduceIte]
    exact fold_field GridCO.State.stableRecord _
      (fun _ _ => fold_field GridCO.State.stableRecord _ (by intros; rfl) _ _) _ _
  rw [hresult]
  exact (hc.advance _ b hs.stable hb).2.2

theorem initial_clean {n : Nat} {path : Block → Prop} (hc : CleanPath path) :
    CleanStateOnPath path (initial n).base := by
  exact ⟨hc.genesis, hc.genesis, by simp [initial, GridCO.initial],
    by simp [initial, GridCO.initial]⟩

/-- Every delivery kind preserves the finite path fields. New PC
authority is a separate joint-induction obligation. -/
theorem process_clean (p : Params) {n : Nat} (st : State n) (o : Wire n)
    {path : Block → Prop} (h : CleanStateOnPath path st.base) :
    CleanStateOnPath path (process p st o).base := by
  apply process_base_invariant p (CleanStateOnPath path) _ _ st o h
  · intro acc obj ha
    unfold GridCO.admitVote
    split <;> (try dsimp only) <;> (try split_ifs) <;>
      exact ⟨ha.stable, ha.goldfish, ha.finite, ha.saved⟩
  · intro acc obj b ha
    unfold GridCO.admitProposal
    dsimp only
    split_ifs <;> exact ⟨ha.stable, ha.goldfish, ha.finite, ha.saved⟩

theorem expire_clean {n : Nat} (st : GridCO.State n) (t : Time)
    {path : Block → Prop} (h : CleanStateOnPath path st) :
    CleanStateOnPath path (GridCO.expire st t) :=
  ⟨h.stable, h.goldfish, fun b g d hm => h.finite b g d (List.mem_filter.mp hm).1, h.saved⟩

theorem release_clean (p : Params) {n : Nat} (st : GridCO.State n) (r : Slot)
    {path : Block → Prop} (h : CleanStateOnPath path st) :
    CleanStateOnPath path (GridCO.release p.engine st r) :=
  ⟨h.stable, h.goldfish, fun b g d hm => h.finite b g d (List.mem_filter.mp hm).1, h.saved⟩

theorem freeze_clean (p : Params) {n : Nat} (st : GridCO.State n) (r : Slot)
    {path : Block → Prop} (h : CleanStateOnPath path st) :
    CleanStateOnPath path (GridCO.freeze p.engine st r) := by
  exact ⟨h.stable, h.goldfish, h.finite, h.saved⟩

/-- The existing clock phases before the gate. This is a proof name for
the transition in `clock`, not a second protocol clock. -/
def clockPreGate (p : Params) {n : Nat} (st : State n) (t : Time) : State n :=
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    { st with base := GridCO.freeze p.engine st.base fSlot,
              frozenPC := if st.frozenPC.any (fun row => row.1 == fSlot)
                then st.frozenPC else st.frozenPC ++ [(fSlot, st.bestPC)] }
    else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    saveTimely p { st with base := { st.base with early := st.base.early ++
      [(eSlot, GridCO.earlyVotes p.engine st.base eSlot)] } } eSlot
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    { st with base := GridCO.release p.engine st.base qSlot } else st

theorem clock_eq_gate_prestate (p : Params) {n : Nat} (st : State n) (t : Time) :
    clock p st t =
      let r := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
      if 0 ≤ t - 6 * p.Δ && t == gateTime p r then
        gate p (clockPreGate p st t) r else clockPreGate p st t := rfl

theorem clockPreGate_base (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clockPreGate p st t).base = GridCO.clockPreGate p.engine st.base t := by
  have hsave (st : State n) (r : Slot) : (saveTimely p st r).base = st.base := by
    unfold saveTimely
    split <;> rfl
  unfold clockPreGate GridCO.clockPreGate
  dsimp only
  simp only [show p.engine.Δ = p.Δ from rfl,
    show GridCO.freezeTime p.engine = freezeTime p from rfl,
    show GridCO.releaseTime p.engine = releaseTime p from rfl]
  split_ifs <;> simp only [hsave]


theorem clockPreGate_clean (p : Params) {n : Nat} (st : State n) (t : Time)
    {path : Block → Prop} (h : CleanStateOnPath path st.base) :
    CleanStateOnPath path (clockPreGate p st t).base ∧
      (clockPreGate p st t).base.stableRecord = st.base.stableRecord := by
  rw [clockPreGate_base]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [GridCO.clockPreGate_stable] using h.stable
  · have he : (GridCO.clockPreGate p.engine st.base t).goldfishRecord =
        st.base.goldfishRecord := by
      unfold GridCO.clockPreGate
      dsimp only
      split_ifs <;> rfl
    rw [he]; exact h.goldfish
  · intro b g d hm
    exact h.finite b g d (GridCO.clockPreGate_obligations_subset p.engine st.base t _ hm)
  · simpa only [GridCO.clockPreGate_genuine] using h.saved
  · exact GridCO.clockPreGate_stable p.engine st.base t

/-- All tick phases preserve the finite invariant. At a gate, the only
remaining premise is its raw result on the path, in the strict input. -/
theorem clock_clean (p : Params) {n : Nat} (st : State n) (t : Time)
    {path : Block → Prop} (hc : CleanPath path) (hs : CleanStateOnPath path st.base)
    (hstamps : GridCO.ReceiptStamped st.base)
    (hraw : ∀ r b, t = gateTime p r → SA.confirmation p st.base r = some b → path b) :
    CleanStateOnPath path (clock p st t).base ∧
      Block.Preceq (stable st) (stable (clock p st t)) := by
  have hpre := clockPreGate_clean p st t hs
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · rename_i ht
    have htime : t = gateTime p (((t - 6 * p.Δ) / (4 * p.Δ)).toNat) := by
      simpa using (Bool.and_eq_true_iff.mp ht).2
    have hgate := gate_clean p (clockPreGate p st t) _ hc hpre.1 (by
      intro b hb
      rw [clockPreGate_base] at hb
      have he := @GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy
        p.engine n (GridCO.clockPreGate p.engine st.base t) st.base
        (GridCO.clockPreGate_receiptData p.engine st.base t) hstamps
      exact hraw _ b htime ((he _).symm.trans hb))
    exact ⟨hgate.1, by simpa only [stable, hpre.2] using hgate.2⟩
  · exact ⟨hpre.1, by simp only [stable, hpre.2]; exact GridCO.block_preceq_self _⟩

theorem process_stable (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    stable (process p st o) = stable st := by
  apply process_base_invariant p (fun acc => acc.stableRecord = st.base.stableRecord)
  · intro acc obj ha
    exact (GridCO.admitVote_stable p.engine acc obj).trans ha
  · intro acc obj b ha
    unfold GridCO.admitProposal
    dsimp only
    split_ifs <;> exact ha
  · rfl

end AvailableChain.SAPC
end
