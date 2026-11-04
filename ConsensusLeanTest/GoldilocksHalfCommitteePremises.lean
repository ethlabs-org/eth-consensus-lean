module
public import ConsensusLeanTest.GoldilocksHalfCommitteeSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
@[expose] public section

/-! # The halfCommittee run: every premise but `halfCommittee`, and its necessity

Kind (r), rejection: **premise necessity, not a counterexample**. `RecentSourceNextVote` is
proved (`recent_source_next_vote`); this module shows that its premise `halfCommittee` cannot
be dropped. In the rejection run of `GoldilocksHalfCommitteeRun` (`ctl = false`) the writer `a`
writes at its tick of `30` (`i₀ = i0 false`) the fast lock of slot `j = 6` on `B` with the
counted votes `CV = {a6, b6, f6}` (score `3`, expiry `8`), and `ac_to_fg` returns `B` at the next
cut (`i₀ + 1`, slot `7 = m`). Every premise of `PersistPremises … a i₀ 6 8 B CV` except
`halfCommittee` holds (`run_premisesExceptHalf`, for both variants; the test-local
`PersistPremisesExceptHalf` copies the other fields, with no edit to the statement):
`Sync[24, 33]` (`GoldilocksHalfCommitteeSync`), `Carry(6, CV, B)` (the slot-7 voters accepted `B`
at `24` and hold `CV` stamped `24 < 27`), `carryLater` (the slot-8 voters accepted `B` by `28` and
hold the slot-7 votes stamped `29 < 31`; no slot-9 vote), `f < h_t` (`a, b` are awake and joined),
`NoColl`, and `Clean`: (K0) the caches are genesis, (K1) every honest signature names genesis,
so the namers of `V` are the faulty `f` alone (`1 < q = 4`), (K2) `B` is in every slot-7 and
slot-8 voter block tree.

`halfCommittee` fails: the honest slot-7 voters are `a, b` (`c` restarted at `28` and is not
joined in slot 7, `d` sleeps), and `5 ≤ 2 · 2` is false (`rejection_not_halfCommittee`). The
conclusion fails too: `c` keeps its slow lock `(V, 4, slow, 8)` through its restart, and at `33`
(slot `8`, expiry inclusive) its unlock against the opponents `{a7, b7}` (`2 · 2 < 5`) keeps it
on `V`, so `c` votes `V`, which does not extend `B` (`rejection_c_votes_V`). The rejection
`halfCommittee_necessary` bundles the run, the other premises, the source event and the failing
conclusion; the corollary `rejection_not_persistPremises` derives `¬ PersistPremises` from the
proved theorem. The run reprocesses at `28` (`GoldilocksHalfCommitteeRun`): `c`'s new pool
entries and acceptance at `28` oblige `a, b` to process `B, a6, b6, f6` again. -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA Compose

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **`PersistPremises` without `halfCommittee`**: a test-local copy of the other fields of
`Compose.PersistPremises` (`Statements/Compose/Persist`), with no edit to the statement. -/
structure PersistPremisesExceptHalf (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (ΔF : Time) (x : Fin sp.n) (i₀ s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n)))
    (CV : Set (Vote sp.n)) : Prop where
  /-- The writer is honest. -/
  writer_honest : x ∈ H
  /-- The stored fast lock. -/
  fastLock : StoredFastLockAt tr x i₀ s B CV
  /-- The writer is joined at the write. -/
  writer_joined : SA.joined sp (tr.state x i₀).ac (tr.time i₀)
  /-- `s < m`. -/
  lt : s < m
  /-- `Sync[t_s, t_m + Δ]`. -/
  sync : tr.SyncRun H ΔF (sp.ts s) (sp.ts m + sp.Δ)
  /-- `Carry(s, S, B)`. -/
  carry : SA.Carry tr.projAC H (tr.HonestBlocks H) s CV
  /-- `Carry(s', S_{s'}, B)` for every slot `s' ∈ (s, m]`. -/
  carryLater : ∀ s', s < s' → s' ≤ m →
    SA.Carry tr.projAC H (tr.HonestBlocks H) s' (honestVotes tr H s')
  /-- `f < h_t` at every honest vote time in `(t_s, t_m + Δ]`. -/
  faultBound : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → sp.ts s < tr.time i →
    tr.time i ≤ sp.ts m + sp.Δ → tr.FaultBound H (tr.time i)
  /-- `NoColl`. -/
  noColl : NoCollRun dg tr
  /-- `Clean(s, m, B)`. -/
  clean : Clean tr H s m B

/-- The field `halfCommittee` of `PersistPremises`. -/
def HalfCommitteeHolds (s m : Nat) : Prop :=
  ∀ s', s < s' → s' ≤ m →
    sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard

variable {tr H}

/-- `PersistPremises` is the copy and `halfCommittee`. -/
theorem persistPremises_iff {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {ΔF : Time}
    {x : Fin sp.n} {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} :
    PersistPremises tr H dg ΔF x i₀ s m B CV ↔
      PersistPremisesExceptHalf tr H dg ΔF x i₀ s m B CV ∧ HalfCommitteeHolds tr H s m :=
  ⟨fun p => ⟨⟨p.writer_honest, p.fastLock, p.writer_joined, p.lt, p.sync, p.carry, p.carryLater,
      p.faultBound, p.noColl, p.clean⟩, p.halfCommittee⟩,
    fun ⟨p, h⟩ => ⟨p.writer_honest, p.fastLock, p.writer_joined, p.lt, p.sync, p.carry, h,
      p.carryLater, p.faultBound, p.noColl, p.clean⟩⟩

end Consensus.Goldilocks.Test.HalfCommittee

namespace Consensus.Goldilocks.Test.HalfCommittee.Five

open SA Fix ScheduleRun Compose

/-! ## The source and the checks on data -/

/-- The counted votes of the source: `a6, b6, f6`, all with head `B`. -/
def cvL : List X.V := [vt va 6 1, vt vb 6 1, vt vf 6 1]

/-- The counted votes as a set. -/
def CV : Set (Vote 5) := {v | v ∈ cvL}

/-- The block `B`. -/
abbrev Bk : X.Blk := X.blk 1

/-- The writer's tick at `30`: its first cut at `30`. -/
def i0 (ctl : Bool) : Nat := (rowsD ctl).findIdx fun r => r.node == va && r.time == 30

/-- `c`'s tick at `33`: its first cut at `33`. -/
def kc (ctl : Bool) : Nat := (rowsD ctl).findIdx fun r => r.node == vc && r.time == 33

/-- A placeholder row. -/
def row0 : RowD := ⟨0, 0, va, 0, .fgAtt (att va), NodeD.init X, NodeD.init X⟩

/-- Row `i`. -/
def rowI (ctl : Bool) (i : Nat) : RowD := (rowsD ctl).getD i row0

/-- The tree of a tick cut. -/
def tickM : CutD X → Option (List Nat)
  | .ac .tick M _ => some M
  | _ => none

/-- The tree of an `ac_to_fg` cut. -/
def toFGM : CutD X → Option (List Nat)
  | .ac .toFG M _ => some M
  | _ => none

/-- The emissions of a cut. -/
def emsD : CutD X → List X.EmD
  | .ac _ _ ems => ems
  | _ => []

/-- The fast test's selection on the path of `c` (the deepest unvetoed path block that passes the
fast test of slot `s`). -/
def fastSelD (a : X.ACD) (M : List Nat) (t : Int) (s c : Nat) : Option Nat :=
  X.deep (((X.chain c).filter
    (fun b => decide (b ≠ X.g ∧ X.conflictsD a.locks M t b = false))).filter
    (fun b => decide (X.sp.n ≤ 2 * a.confScore M s b)))

/-- The fast test's counted votes for `b` in slot `s`. -/
def cvD (a : X.ACD) (M : List Nat) (s b : Nat) : List X.V :=
  (a.pool s).filter fun v => decide (v.val ∉ eqv (a.pool s)) &&
    decide (a.res M v < ETime.of (4 * (s : Int) + 2)) && decide (v.head ∈ M ∧ b ∈ X.chain v.head)

/-- The source: `a`'s tick at `30` writes the fast lock of slot `6` on `B` counting `cvL`, and
its `ac_to_fg` at the next cut returns `B`. -/
def SourceD (ctl : Bool) : Prop :=
  i0 ctl + 1 < (rowsD ctl).length ∧ (rowI ctl (i0 ctl)).node = va ∧
    (rowI ctl (i0 ctl)).time = 30 ∧ tickM (rowI ctl (i0 ctl)).cut = some [1, 2] ∧
    (rowI ctl (i0 ctl)).pre.ac.getConf [1, 2] 6 = some 1 ∧
    fastSelD (rowI ctl (i0 ctl)).pre.ac [1, 2] 30 6 1 = some 1 ∧
    (rowI ctl (i0 ctl)).pre.ac.joinedB 30 = true ∧ cvD (rowI ctl (i0 ctl)).pre.ac [1, 2] 6 1 = cvL ∧
    (rowI ctl (i0 ctl + 1)).node = va ∧ (rowI ctl (i0 ctl + 1)).time = 30 ∧
    toFGM (rowI ctl (i0 ctl + 1)).cut = some [1, 2] ∧
    ((rowI ctl (i0 ctl + 1)).pre.ac.toFG [1, 2] 30).2 = some 1

instance (ctl : Bool) : Decidable (SourceD ctl) := by unfold SourceD; infer_instance

/-- An `ac_on_block(B)` cut. -/
def blockOne : CutD X → Bool
  | .ac (.block b) _ _ => b == 1
  | _ => false

/-- `y` accepts `B` (an `ac_on_block(B)` cut) before `T`. -/
def accB (ctl : Bool) (y : Fin 5) (T : Nat) : Bool :=
  (rowsD ctl).any fun r => r.node == y && decide (r.time < T) && blockOne r.cut

/-- The honest votes of slot `σ`. -/
def votesD (ctl : Bool) (σ : Nat) : List X.V :=
  (rowsD ctl).flatMap fun r => ((emsD r.cut).map EmD.vote).filter (·.slot == σ)

/-- The read point `rp` holds `v`, received before `T`. -/
def heldD (rp : X.ACD) (v : X.V) (T : Int) : Bool :=
  (rp.pool v.slot).contains v && decide (rp.stampV v < ETime.of T)

/-- The checks at a vote of slot `7` or `8` (and no vote of a later slot): joined, `Carry`,
`B` accepted before `t_{s−1} + 3` and in the voter block tree. -/
def voteD (ctl : Bool) (r : RowD) (M : List Nat) (em : X.EmD) : Bool :=
  if em.vote.slot = 7 then em.rp.joinedB r.time && cvL.all (heldD em.rp · 27) &&
    accB ctl r.node 27 && decide (1 ∈ em.rp.vbt M 7)
  else if em.vote.slot = 8 then em.rp.joinedB r.time &&
    (votesD ctl 7).all (fun v => v.head == 1 && heldD em.rp v 31) && accB ctl r.node 31 &&
    decide (1 ∈ em.rp.vbt M 8)
  else decide (em.vote.slot < 7)

/-- The checks on the rows: honest nodes, the fragment, the votes (with the frame tree of the
call the node's tree), the signatures (all name genesis), no restart of `a` or `b`. -/
def rowsChk (ctl : Bool) : Bool :=
  (rowsD ctl).all fun r => r.node != vf && decide (X.Frag r.post) &&
    (match r.cut with
      | .ac _ M ems => M == r.post.fg.tree && ems.all (voteD ctl r M)
      | .fgAttest _ (some a) => a.T == 2
      | _ => true) &&
    !(isRestartCut r.cut && (r.node == va || r.node == vb))

/-- `c`'s vote at `33`: slot `8`, head `cHead ctl` (`V` in the rejection run, `B` in the
control), with the live lock `(V, 4, slow, 8)` in the rejection run and `(G, 4, slow, 8)`
(unlocked) in the control at its read point. -/
def CVoteD (ctl : Bool) : Prop :=
  kc ctl < (rowsD ctl).length ∧ (rowI ctl (kc ctl)).node = vc ∧ (rowI ctl (kc ctl)).time = 33 ∧
    ∃ em ∈ emsD (rowI ctl (kc ctl)).cut, em.vote = vt vc 8 (cHead ctl) ∧
      (⟨if ctl then 2 else 3, 4, false, 8⟩ : Lock) ∈ em.rp.locks

instance (ctl : Bool) : Decidable (CVoteD ctl) := by unfold CVoteD; infer_instance

/-- The honest voters of slot `σ`. -/
def votersD (ctl : Bool) (σ : Nat) : List (Fin 5) :=
  (rowsD ctl).filterMap fun r =>
    if (emsD r.cut).any (fun em => em.vote.slot == σ) then some r.node else none

theorem checks_true : ∀ ctl, SourceD ctl ∧ rowsChk ctl = true ∧ CVoteD ctl ∧
    1 ∈ (stateD ctl va (rowsD ctl).length).fg.tree := by
  decide +kernel

theorem voters_checks : votersD false 7 ⊆ [va, vb] ∧ [va, vb, vd] ⊆ votersD true 7 ∧
    [va, vb, vd] ⊆ votersD true 8 := by
  decide +kernel


/-! ## The run on data -/

theorem rowsChk_row {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    r.node ≠ vf ∧ X.Frag r.post ∧
      (match r.cut with
        | .ac _ M ems => M == r.post.fg.tree && ems.all (voteD ctl r M)
        | .fgAttest _ (some a) => a.T == 2
        | _ => true) = true ∧
      (isRestartCut r.cut && (r.node == va || r.node == vb)) = false := by
  have h := List.all_eq_true.1 (checks_true ctl).2.1 r (List.mem_of_getElem? hr)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem row_honest {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    r.node ∈ H := (rowsChk_row hr).1

theorem acRow_chk {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r)
    {call : CallD X} {M : List Nat} {ems : List X.EmD} (hc : r.cut = .ac call M ems) :
    M = r.post.fg.tree ∧ ∀ em ∈ ems, voteD ctl r M em = true := by
  have h := (rowsChk_row hr).2.2.1
  rw [hc] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h

theorem localRun (ctl : Bool) :
    Node.LocalRun proposer dg H (fun v : Vote X.sp.n => v.val) (tr ctl) :=
  (run_goldilocksRun ctl).toLocalRun

theorem projAC_call {ctl : Bool} {y : Fin 5} {i : Nat} {ℓ : ACLabel N5}
    (h : (tr ctl).projAC.CallAt y i ℓ) : (tr ctl).CallAt y i (.ac ℓ) := by
  obtain ⟨hn, hl⟩ := h
  refine ⟨hn, ?_⟩
  change ((tr ctl).label i).bind RunTrace.acLabel = some ℓ at hl
  cases hc : (tr ctl).label i with
  | none => rw [hc] at hl; cases hl
  | some c => rw [hc] at hl; cases c <;> simp [RunTrace.acLabel] at hl; rw [hl]

theorem projAC_call_of {ctl : Bool} {y : Fin 5} {i : Nat} {ℓ : ACLabel N5}
    (h : (tr ctl).CallAt y i (.ac ℓ)) : (tr ctl).projAC.CallAt y i ℓ :=
  ⟨h.1, by change ((tr ctl).label i).bind RunTrace.acLabel = _; rw [h.2]; rfl⟩

/-- An AC call of the projection is an AC row. -/
theorem acRow {ctl : Bool} {y : Fin 5} {i : Nat} {ℓ : ACLabel N5}
    (h : (tr ctl).projAC.CallAt y i ℓ) :
    ∃ r, (rowsD ctl)[i]? = some r ∧ r.node = y ∧ ∃ call M ems, r.cut = .ac call M ems ∧
      ℓ = ⟨call.interp ro, X.frameOf M, ems.map EmD.interp⟩ := by
  have hc := projAC_call h
  obtain ⟨r, hr, hcut⟩ := label_row hc.2
  exact ⟨r, hr, (trace_row hr).1 ▸ hc.1, cut_ac hcut⟩

theorem acRow_of {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r)
    {call : CallD X} {M : List Nat} {ems : List X.EmD} (hc : r.cut = .ac call M ems) :
    (tr ctl).projAC.CallAt r.node i ⟨call.interp ro, X.frameOf M, ems.map EmD.interp⟩ := by
  have h := callAt_row hr
  rw [hc] at h
  exact projAC_call_of h

theorem acState {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    (tr ctl).projAC.state r.node i = r.pre.ac.interp := by
  rw [projAC_state (localRun ctl) (row_honest hr), (trace_row hr).2.2.2.2]; rfl

/-- A vote of the projection is an emission of an AC row, with its checks. -/
theorem voteAt_row {ctl : Bool} {y : Fin 5} {i : Nat} {e : SA.Em X.sp (List (FG.Att X.sp.n))}
    (h : SA.VoteAt (tr ctl).projAC y i e) :
    ∃ r, (rowsD ctl)[i]? = some r ∧ r.node = y ∧ ∃ call M ems, r.cut = .ac call M ems ∧
      ∃ em ∈ ems, e = em.interp ∧ voteD ctl r M em = true ∧ M = r.post.fg.tree := by
  obtain ⟨ℓ, hc, he⟩ := h
  obtain ⟨r, hr, hn, call, M, ems, hcut, rfl⟩ := acRow hc
  obtain ⟨em, hem, rfl⟩ := List.mem_map.1 he
  have := acRow_chk hr hcut
  exact ⟨r, hr, hn, call, M, ems, hcut, em, hem, rfl, this.2 em hem, this.1⟩

theorem voteAt_of {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r)
    {call : CallD X} {M : List Nat} {ems : List X.EmD} (hc : r.cut = .ac call M ems)
    {em : X.EmD} (hem : em ∈ ems) : SA.VoteAt (tr ctl).projAC r.node i em.interp :=
  ⟨_, acRow_of hr hc, List.mem_map_of_mem hem⟩

/-! ## The honest blocks -/

/-- The roots of the table with genesis. -/
def allR : List Nat := [2, 1, 3]

theorem allR_closed : X.Closed allR := by decide

theorem frag_fold (y : Fin 5) :
    ∀ (L : List RowD), (∀ r ∈ L, X.Frag r.post) → ∀ d, X.Frag d →
      X.Frag (L.foldl (fun d r => if r.node = y then r.post else d) d)
  | [], _, _, hd => hd
  | r :: L, hL, d, hd => by
    simp only [List.foldl_cons]
    refine frag_fold y L (fun r' h => hL r' (List.mem_cons_of_mem _ h)) _ ?_
    split_ifs
    · exact hL r List.mem_cons_self
    · exact hd

theorem frag_stateD (ctl : Bool) (y : Fin 5) (c : Nat) : X.Frag (stateD ctl y c) := by
  refine frag_fold y _ (fun r hr => ?_) _ (frag_init X)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take hr)
  exact (rowsChk_row (List.getElem?_eq_getElem hi)).2.1

theorem trace_tree (ctl : Bool) (y : Fin 5) (c : Nat) :
    ((tr ctl).state y c).fg.tree = X.T (stateD ctl y c).fg.tree := by
  rw [trace_state]; exact tree_interp (frag_stateD ctl y c).1

theorem honest_sub {ctl : Bool} {B : X.Blk} (hB : B ∈ (tr ctl).HonestBlocks H) :
    ∃ r ∈ allR, B = X.blk r := by
  obtain ⟨y, -, i, hB⟩ := hB
  rw [trace_tree] at hB
  obtain ⟨r, hr, rfl⟩ := hB
  refine ⟨r, ?_, rfl⟩
  rcases (frag_stateD ctl y i).1.valid r hr with rfl | h
  · exact List.mem_cons_self
  · have key : ∀ r, r ∈ X.roots → r ∈ allR := by decide
    exact key r h

theorem honest_T (ctl : Bool) : (tr ctl).HonestBlocks H ⊆ X.T allR := fun _ hB => honest_sub hB

theorem anc_honest {ctl : Bool} {A C : X.Blk} (h : Anc ((tr ctl).HonestBlocks H) A C) :
    Anc (X.T allR) A C := by
  induction h with
  | refl => exact .refl
  | tail _ hp ih => exact ih.tail ⟨honest_T ctl hp.1, honest_T ctl hp.2.1, hp.2.2⟩

theorem blk_honest (ctl : Bool) {r : Nat} (hr : r = 1 ∨ r = 2) :
    X.blk r ∈ (tr ctl).HonestBlocks H := by
  refine ⟨va, show va ≠ vf by decide, (rowsD ctl).length, ?_⟩
  rw [trace_tree]
  refine blk_mem_T ?_
  rcases hr with rfl | rfl
  · exact (checks_true ctl).2.2.2
  · exact (frag_stateD ctl va _).1.g_mem

theorem gBlk_honest (ctl : Bool) : X.gBlk ∈ (tr ctl).HonestBlocks H :=
  blk_g hX ▸ blk_honest ctl (Or.inr rfl)

/-- The ancestors of `B` inside the honest blocks: `B` and genesis. -/
theorem anc_Bk {ctl : Bool} {A : X.Blk} (h : Anc ((tr ctl).HonestBlocks H) A Bk) :
    A = X.blk 1 ∨ A = X.blk 2 := by
  obtain ⟨a, ha, rfl⟩ := (anc_T hX allR_closed (b := 1) (by decide)).1 (anc_honest h)
  have hc : X.chain 1 = [1, 2] := by decide
  rw [hc] at ha
  rcases List.mem_pair.1 ha with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gBlk_anc_Bk (ctl : Bool) : Anc ((tr ctl).HonestBlocks H) X.gBlk Bk :=
  Relation.ReflTransGen.single ⟨gBlk_honest ctl, blk_honest ctl (Or.inl rfl), rfl⟩

/-- **`c`'s head `V` does not extend `B`** inside the honest blocks. -/
theorem not_extends_V (ctl : Bool) {v : Vote 5} (hv : v.head = 3) :
    ¬ SA.VoteExtends ((tr ctl).HonestBlocks H) v Bk := by
  rintro ⟨Hd, hHd, hroot, hanc⟩
  obtain ⟨r, hr, rfl⟩ := honest_sub hHd
  have hr3 : r = 3 := by rw [← hv, ← hroot, blk_root (allR_closed.valid r hr)]
  subst hr3
  have := (anc_T_blk hX allR_closed (a := 1) (b := 3) (Or.inr (by decide)) (by decide)).1
    (anc_honest hanc)
  revert this; decide

/-! ## The source -/

theorem rowI_eq {ctl : Bool} {i : Nat} (h : i < (rowsD ctl).length) :
    (rowsD ctl)[i]? = some (rowI ctl i) := by
  rw [rowI, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem tickM_some {c : CutD X} {M : List Nat} (h : tickM c = some M) :
    ∃ ems, c = .ac .tick M ems := by
  cases c with
  | ac call M' ems => cases call <;> simp_all [tickM]
  | _ => simp [tickM] at h

theorem toFGM_some {c : CutD X} {M : List Nat} (h : toFGM c = some M) :
    ∃ ems, c = .ac .toFG M ems := by
  cases c with
  | ac call M' ems => cases call <;> simp_all [toFGM]
  | _ => simp [toFGM] at h

/-- The source on data: the rows of `a`'s tick and `ac_to_fg` at `30`. -/
theorem source_rows (ctl : Bool) :
    ∃ r₀ r₁ ems₀ ems₁, (rowsD ctl)[i0 ctl]? = some r₀ ∧ (rowsD ctl)[i0 ctl + 1]? = some r₁ ∧
      r₀.node = va ∧ r₀.time = 30 ∧ r₀.cut = .ac .tick [1, 2] ems₀ ∧
      r₀.pre.ac.getConf [1, 2] 6 = some 1 ∧ fastSelD r₀.pre.ac [1, 2] 30 6 1 = some 1 ∧
      r₀.pre.ac.joinedB 30 = true ∧ cvD r₀.pre.ac [1, 2] 6 1 = cvL ∧ r₁.node = va ∧
      r₁.time = 30 ∧ r₁.cut = .ac .toFG [1, 2] ems₁ ∧ (r₁.pre.ac.toFG [1, 2] 30).2 = some 1 := by
  obtain ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12⟩ := (checks_true ctl).1
  obtain ⟨ems₀, he₀⟩ := tickM_some h3
  obtain ⟨ems₁, he₁⟩ := toFGM_some h11
  exact ⟨_, _, ems₀, ems₁, rowI_eq (by omega), rowI_eq hlt, h1, h2, he₀, h4, h5, h6, h7, h9, h10,
    he₁, h12⟩

theorem closed12 : X.Closed [1, 2] := by decide

theorem fastSelect_eq {M : List Nat} (hM : X.Closed M) (a : X.ACD) (t : Int) (s : Nat) {c : Nat}
    (hcM : c ∈ M) :
    deepest (X.frameOf M) {B | B ∈ confirmationPath X.sp (X.frameOf M) (X.blk c) ∧
      ¬ conflictsWithLock X.sp {l | l ∈ a.locks} (X.frameOf M) t B ∧
      FastTest X.sp a.interp (X.frameOf M) s B} = (fastSelD a M t s c).map X.blk := by
  have hch := chain_sub hX hM hcM
  refine deepest_eq hX hM (fun r hr => hch r (List.mem_filter.1 (List.mem_filter.1 hr).1).1)
    fun B => ?_
  simp only [Set.mem_ofPred_eq, ← and_assoc, path_mem hX hM hcM, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hf⟩
    rw [FastTest, confirmationScore_eq hX hM a s (hM.valid r (hch r hr.1.1))] at hf
    exact ⟨r, ⟨hr, hf⟩, rfl⟩
  · rintro ⟨r, ⟨hr, hf⟩, rfl⟩
    refine ⟨⟨r, hr, rfl⟩, ?_⟩
    rwa [FastTest, confirmationScore_eq hX hM a s (hM.valid r (hch r hr.1.1))]

theorem fastCounted_eq {M : List Nat} (hM : X.Closed M) (a : X.ACD) (s : Nat) {b : Nat}
    (hb : X.Valid b) :
    fastCounted X.sp a.interp (X.frameOf M) s (X.blk b) = {v | v ∈ cvD a M s b} := by
  have he : ∀ i, i ∈ equivocators {x | x ∈ a.pool s} ↔ i ∈ eqv (a.pool s) := fun i => by
    rw [equivocators_eq]; rfl
  have hd : sp5.Δ = 1 := rfl
  ext v
  simp only [fastCounted, interp_pool]
  simp [cvD, he, resolutionTime_interp hM, ancR_frameOf hX hM hb, SAParams.ts, hd, and_assoc]

/-- **The source**: `a` writes the fast lock of slot `6` on `B` with the counted votes `CV` at
its tick of `30` (`i₀ = i0 ctl`), joined, and `ac_to_fg` returns `B` at the next cut, in slot
`7`. -/
theorem source (ctl : Bool) :
    StoredFastLockAt (tr ctl) va (i0 ctl) 6 Bk CV ∧
      SA.joined X.sp ((tr ctl).state va (i0 ctl)).ac ((tr ctl).time (i0 ctl)) ∧
      ∃ ℓ, SA.ToFGAt (tr ctl).projAC va (i0 ctl + 1) ℓ Bk ∧
        X.sp.slot ((tr ctl).time (i0 ctl + 1)) = 7 := by
  obtain ⟨r₀, r₁, ems₀, ems₁, h₀, h₁, hn₀, ht₀, hc₀, hg, hf, hj, hcv, hn₁, ht₁, hc₁, htf⟩ :=
    source_rows ctl
  have hs₀ := acState h₀
  have hs₁ := acState h₁
  rw [hn₀] at hs₀; rw [hn₁] at hs₁
  have hT₀ : (tr ctl).time (i0 ctl) = 30 := by rw [rowsD_time h₀, ht₀]; rfl
  have hT₁ : (tr ctl).time (i0 ctl + 1) = 30 := by rw [rowsD_time h₁, ht₁]; rfl
  have hjoin : SA.joined X.sp r₀.pre.ac.interp 30 := (joined_interp _ _).2 hj
  refine ⟨⟨_, Bk, hn₀ ▸ acRow_of h₀ hc₀, Or.inl ⟨_, Bk, ⟨hn₀ ▸ acRow_of h₀ hc₀, rfl, ?_, ?_⟩,
    ?_, ?_, ?_⟩, ?_⟩, ?_, _, ⟨hn₁ ▸ acRow_of h₁ hc₁, rfl, ?_⟩, ?_⟩
  · change (tr ctl).time (i0 ctl) = _; rw [hT₀]; rfl
  · change SA.joined X.sp ((tr ctl).projAC.state va (i0 ctl)) ((tr ctl).time (i0 ctl))
    rw [hs₀, hT₀]; exact hjoin
  · rw [hs₀]; change getConfirmation X.sp _ (X.frameOf [1, 2]) 6 = _
    rw [getConfirmation_eq hX closed12, hg]; rfl
  · change deepest _ {X_1 | _ ∧ ¬ conflictsWithLock X.sp ((tr ctl).projAC.state va (i0 ctl)).locks
      _ ((tr ctl).time (i0 ctl)) X_1 ∧ _} = _
    rw [hs₀, hT₀]
    exact (fastSelect_eq closed12 r₀.pre.ac 30 6 (by decide)).trans (by rw [hf]; rfl)
  · rw [hs₀, fastCounted_eq closed12 _ _ (Or.inr (by decide)), hcv]; rfl
  · exact (viableAncestor_frameOf hX closed12 (blk_mem_T (by decide))).symm
  · have hst := (trace_row h₀).2.2.2.2
    rw [hn₀] at hst
    rw [hst, hT₀]; exact hjoin
  · change (acToFG X.sp ((tr ctl).projAC.state va (i0 ctl + 1)) (X.frameOf [1, 2])
      ((tr ctl).time (i0 ctl + 1))).2 = _
    rw [hs₁, hT₁]
    rw [acToFG_eq hX closed12, resF, htf]; rfl
  · rw [hT₁, Fix.slot_eq]; rfl

/-! ## Carry, the fault bound, `NoColl`, `Clean` -/

theorem accepted_of {ctl : Bool} {y : Fin 5} {T : Nat} (h : accB ctl y T = true) :
    ∃ k, (tr ctl).projAC.AcceptAt y k Bk ∧ (tr ctl).time k < T := by
  obtain ⟨r, hm, hr⟩ := List.any_eq_true.1 h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  have hrk := List.getElem?_eq_getElem hk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
  obtain ⟨⟨hn, ht⟩, hb⟩ := hr
  refine ⟨k, ?_, by rw [rowsD_time hrk]; exact_mod_cast ht⟩
  obtain ⟨M, ems, hc⟩ : ∃ M ems, (rowsD ctl)[k].cut = .ac (.block 1) M ems := by
    revert hb
    cases (rowsD ctl)[k].cut with
    | ac call M ems => cases call <;> simp [blockOne]
    | _ => simp [blockOne]
  exact ⟨_, hn ▸ acRow_of hrk hc, rfl⟩

/-- `Carry_y` at a vote whose counted votes have head `B`, are held before `T` at the read point,
with `B` accepted before `T`. -/
theorem carryAt_mk {ctl : Bool} {y : Fin 5} (hy : y ∈ H) {i : Nat}
    {e : SA.Em X.sp (List (FG.Att X.sp.n))} (hv : SA.VoteAt (tr ctl).projAC y i e) {s T : Nat}
    (hT : X.sp.ts s + 3 * X.sp.Δ = T) (S : Set (Vote 5))
    (hj : SA.joined X.sp e.readPoint ((tr ctl).time i))
    (hS : ∀ v ∈ S, v.head = 1 ∧ SA.HeldBefore e.readPoint v T) (hacc : accB ctl y T = true) :
    SA.CarryAt (tr ctl).projAC ((tr ctl).HonestBlocks H) y i e s S where
  awake := by
    obtain ⟨ℓ, hc, -⟩ := hv
    exact (localRun ctl).awake_of_call y hy i ⟨_, projAC_call hc⟩
  joined := hj
  heads v hvS := by
    refine ⟨Bk, blk_honest ctl (Or.inl rfl), by rw [(hS v hvS).1]; rfl, fun X' hX' => ?_⟩
    rcases anc_Bk hX' with rfl | rfl
    · obtain ⟨k, hk, htk⟩ := accepted_of hacc
      refine Or.inr ⟨k, hk, ?_⟩
      rw [hT]; exact htk
    · exact Or.inl rfl
  holds v hvS := by rw [hT]; exact Or.inl (hS v hvS).2

theorem heldD_spec {rp : X.ACD} {v : X.V} {T : Int} (h : heldD rp v T = true) :
    SA.HeldBefore rp.interp v T := by
  simp only [heldD, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  exact h

theorem voteD_slot7 {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true)
    (hs : em.vote.slot = 7) : em.rp.joinedB r.time = true ∧ (∀ v ∈ cvL, heldD em.rp v 27 = true) ∧
      accB ctl r.node 27 = true ∧ 1 ∈ em.rp.vbt M 7 := by
  simp only [voteD, hs, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem voteD_slot8 {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true)
    (hs : em.vote.slot = 8) : em.rp.joinedB r.time = true ∧
      (∀ v ∈ votesD ctl 7, v.head = 1 ∧ heldD em.rp v 31 = true) ∧
      accB ctl r.node 31 = true ∧ 1 ∈ em.rp.vbt M 8 := by
  have h87 : ((8 : Nat) = 7) = False := by decide
  simp only [voteD, hs, h87, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem voteD_slot {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true) :
    em.vote.slot ≤ 8 := by
  unfold voteD at h
  split_ifs at h with h7 h8
  · omega
  · omega
  · simp only [decide_eq_true_eq] at h; omega

theorem joined_row {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) {em : X.EmD}
    (hj : em.rp.joinedB r.time = true) :
    SA.joined X.sp em.interp.readPoint ((tr ctl).time i) := by
  rw [rowsD_time hr]; exact (joined_interp _ _).2 hj

theorem mem_votesD {ctl : Bool} {v : Vote 5} (h : v ∈ honestVotes (tr ctl) H 7) :
    v ∈ votesD ctl 7 := by
  obtain ⟨x, -, j, e', hv, rfl, hs⟩ := h
  obtain ⟨r, hr, -, call, M, ems, hc, em, hem, rfl, -⟩ := voteAt_row hv
  exact List.mem_flatMap.2 ⟨r, List.mem_of_getElem? hr, List.mem_filter.2
    ⟨List.mem_map_of_mem (by rw [hc]; exact hem), by simpa using hs⟩⟩

/-- **`Carry(6, CV, B)`**, in both variants. -/
theorem run_carry (ctl : Bool) : SA.Carry (tr ctl).projAC H ((tr ctl).HonestBlocks H) 6 CV := by
  intro y hy i e hv hs
  obtain ⟨r, hr, hn, call, M, ems, hc, em, hem, rfl, hchk, -⟩ := voteAt_row hv
  obtain ⟨hj, hheld, hacc, -⟩ := voteD_slot7 hchk hs
  refine carryAt_mk hy hv rfl CV (joined_row hr hj) (fun v hvS => ⟨?_, heldD_spec (hheld v hvS)⟩)
    (by rw [← hn]; exact hacc)
  have key : ∀ v ∈ cvL, v.head = 1 := by decide
  exact key v hvS

/-- **`carryLater`**: `Carry(7, S_7, B)` and (vacuously: no slot-9 vote) `Carry(8, S_8, B)`. -/
theorem run_carryLater (ctl : Bool) : ∀ s', 6 < s' → s' ≤ 8 →
    SA.Carry (tr ctl).projAC H ((tr ctl).HonestBlocks H) s' (honestVotes (tr ctl) H s') := by
  intro s' h1 h2 y hy i e hv hs
  obtain ⟨r, hr, hn, call, M, ems, hc, em, hem, rfl, hchk, -⟩ := voteAt_row hv
  have hle := voteD_slot hchk
  change em.vote.slot = s' + 1 at hs
  obtain rfl : s' = 7 := by omega
  obtain ⟨hj, hheld, hacc, -⟩ := voteD_slot8 hchk hs
  refine carryAt_mk hy hv rfl _ (joined_row hr hj) (fun v hvS => ?_) (by rw [← hn]; exact hacc)
  exact ⟨(hheld v (mem_votesD hvS)).1, heldD_spec (hheld v (mem_votesD hvS)).2⟩

theorem awakeB_ab : ∀ ctl, ∀ n < 36, awakeB ctl va n = true ∧ awakeB ctl vb n = true := by decide

theorem joinedAt_ab {ctl : Bool} {y : Fin 5} (hy : y = va ∨ y = vb) (t : Time) :
    (tr ctl).JoinedAt y t := by
  intro k hk
  obtain ⟨r, hr, rfl, hres⟩ := restartAt_iff.1 hk
  have := (rowsChk_row hr).2.2.2
  rw [hres] at this
  rcases hy with h | h <;> simp [h] at this

/-- `f < h_t` on `[0, 35]`: `a` and `b` are awake and joined. -/
theorem faultBound_at (ctl : Bool) {t : Int} (h0 : 0 ≤ t) (h35 : t ≤ 35) :
    (tr ctl).FaultBound H t := by
  have hc : Hᶜ = {vf} := by ext y; simp [H]
  have hsub : ({va, vb} : Set (Fin 5)) ⊆
      {y | y ∈ H ∧ (tr ctl).awake y t ∧ (tr ctl).JoinedAt y t} := by
    have hab := awakeB_ab ctl t.toNat (by omega)
    rintro y (rfl | rfl)
    · exact ⟨show va ≠ vf by decide, ⟨h0, hab.1⟩, joinedAt_ab (Or.inl rfl) t⟩
    · exact ⟨show vb ≠ vf by decide, ⟨h0, hab.2⟩, joinedAt_ab (Or.inr rfl) t⟩
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined
  rw [hc, Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair (by decide)] at this
  exact lt_of_lt_of_le one_lt_two this

theorem run_faultBound (ctl : Bool) : ∀ y ∈ H, ∀ i e, SA.VoteAt (tr ctl).projAC y i e →
    X.sp.ts 6 < (tr ctl).time i → (tr ctl).time i ≤ X.sp.ts 8 + X.sp.Δ →
    (tr ctl).FaultBound H ((tr ctl).time i) := by
  intro y _ i e _ h1 h2
  have h1' : (24 : Int) < (tr ctl).time i := h1
  have h2' : (tr ctl).time i ≤ (33 : Int) := h2
  exact faultBound_at ctl (le_of_lt (lt_trans (by norm_num) h1')) (le_trans h2' (by norm_num))

/-- **`NoColl`**: the blocks of the run are genesis, `B` and `V`, with distinct digests. -/
theorem run_noColl (ctl : Bool) : NoCollRun dg (tr ctl) := by
  have cls : ∀ B ∈ insert (X.sp.toParams.genesisBlock N5.genesisPayload) {B | (tr ctl).Occurs B},
      B = X.sp.toParams.genesisBlock N5.genesisPayload ∨ B = X.blk 1 ∨ B = X.blk 3 := by
    rintro B (rfl | ⟨y, k, hB⟩)
    · exact Or.inl rfl
    · obtain ⟨b, hb, rfl⟩ := fgBlock_ok hB
      rcases hb with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  intro B hB C hC h
  rcases cls B hB with rfl | rfl | rfl <;> rcases cls C hC with rfl | rfl | rfl <;>
    revert h <;> decide

theorem projFG_call {ctl : Bool} {y : Fin 5} {i : Nat} {ℓ : FGLabel X.sp.toParams N5.Payload}
    (h : (tr ctl).projFG.CallAt y i ℓ) : (tr ctl).CallAt y i (.fg ℓ) := by
  obtain ⟨hn, hl⟩ := h
  refine ⟨hn, ?_⟩
  change ((tr ctl).label i).bind RunTrace.fgLabel = some ℓ at hl
  cases hc : (tr ctl).label i with
  | none => rw [hc] at hl; cases hl
  | some c => rw [hc] at hl; cases c <;> simp [RunTrace.fgLabel] at hl; rw [hl]

theorem cut_fgAttest {c : CutD X} {B : X.Blk} {a : FG.Att X.sp.n}
    (h : c.interp ro = .fg (.attest B (some a))) : ∃ b, c = .fgAttest b (some a) := by
  cases c <;> simp_all [CutD.interp]

/-- An honest signature names genesis. -/
theorem signAt_T {ctl : Bool} {v : Fin 5} {j : Nat} {a : FG.Att X.sp.n}
    (h : (tr ctl).projFG.SignAt v j a) : a.T = 2 := by
  obtain ⟨src, hc⟩ := h
  obtain ⟨r, hr, hcut⟩ := label_row (projFG_call hc).2
  obtain ⟨b, hb⟩ := cut_fgAttest hcut
  have := (rowsChk_row hr).2.2.1
  rw [hb] at this
  simpa using this

/-- **`Clean(6, 8, B)`**, in both variants. -/
theorem run_clean (ctl : Bool) : Clean (tr ctl) H 6 8 Bk where
  caches y _ j _ := by
    rw [trace_state]
    exact ⟨Or.inl (gBlk_anc_Bk ctl), Or.inl (gBlk_anc_Bk ctl)⟩
  fgAttCut E' hE' := by
    obtain ⟨-, y, -, j, -, hanc, hne⟩ := hE'
    rw [trace_state] at hanc hne
    change Anc _ X.gBlk E' at hanc
    change E' ≠ X.gBlk at hne
    have hE : E' ∈ (tr ctl).HonestBlocks H := by
      rcases Relation.ReflTransGen.cases_tail hanc with h | ⟨b, -, hp⟩
      · exact absurd h hne
      · exact hp.2.1
    obtain ⟨r, hr, rfl⟩ := honest_sub hE
    have hr2 : r ≠ 2 := fun h => hne (by rw [h]; exact blk_g hX)
    have hsub : Store.namers X.sp.toParams (Payload X.sp.n) H (tr ctl).projFG
        (X.sp.ts (6 + 1 : Nat) + X.sp.Δ) (X.blk r) ⊆ Hᶜ := by
      rintro v (hv | ⟨j, a, hs, -, hT⟩)
      · exact hv
      · rw [signAt_T hs, blk_root (allR_closed.valid r hr)] at hT
        exact absurd hT.symm hr2
    have hc : Hᶜ = {vf} := by ext y; simp [H]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hc, Set.ncard_singleton] at this
    change _ < 4
    omega
  heightLead y _ i ℓ e hc h1 h2 := by
    obtain ⟨hca, he⟩ := hc
    obtain ⟨r, hr, hn, call, M, ems, hcut, rfl⟩ := acRow hca
    obtain ⟨em, hem, rfl⟩ := List.mem_map.1 he
    obtain ⟨hM, hchk⟩ := acRow_chk hr hcut
    have hcl : X.Closed M := hM ▸ (rowsChk_row hr).2.1.1
    have hvbt : 1 ∈ em.rp.vbt M em.vote.slot := by
      have h1' : 6 < em.vote.slot := h1
      have h2' : em.vote.slot ≤ 8 := h2
      rcases (show em.vote.slot = 7 ∨ em.vote.slot = 8 by omega) with hs | hs
      · rw [hs]; exact (voteD_slot7 (hchk em hem) hs).2.2.2
      · rw [hs]; exact (voteD_slot8 (hchk em hem) hs).2.2.2
    refine Or.inl ⟨Bk, ?_, .refl, ?_⟩
    · change Bk ∈ voterBlockTree X.sp em.rp.interp (X.frameOf M) em.vote.slot
      rw [voterBlockTree_eq hX hcl]; exact blk_mem_T hvbt
    · rw [trace_state]; exact isViable_interp _ _

/-- **Every premise of `PersistPremises` but `halfCommittee`**, for the source of `a` (`i₀`,
slot `6`, `B`, `CV`) and the slot `m + 1 = 8`, in both variants. -/
theorem run_premisesExceptHalf (ctl : Bool) :
    PersistPremisesExceptHalf (tr ctl) H dg 1 va (i0 ctl) 6 8 Bk CV where
  writer_honest := show va ≠ vf by decide
  fastLock := (source ctl).1
  writer_joined := (source ctl).2.1
  lt := by decide
  sync := run_sync ctl
  carry := run_carry ctl
  carryLater := run_carryLater ctl
  faultBound := run_faultBound ctl
  noColl := run_noColl ctl
  clean := run_clean ctl

/-! ## The failure of `halfCommittee` and of the conclusion -/

theorem emsD_mem {c : CutD X} {em : X.EmD} (h : em ∈ emsD c) :
    ∃ call M ems, c = .ac call M ems ∧ em ∈ ems := by
  cases c <;> simp_all [emsD]

theorem votersD_iff {ctl : Bool} {σ : Nat} {y : Fin 5} :
    y ∈ votersD ctl σ ↔ ∃ j e, SA.VoteAt (tr ctl).projAC y j e ∧ e.msg.slot = σ := by
  constructor
  · intro h
    obtain ⟨r, hm, hr⟩ := List.mem_filterMap.1 h
    split_ifs at hr with hany
    cases hr
    obtain ⟨em, hem, hs⟩ := List.any_eq_true.1 hany
    obtain ⟨call, M, ems, hc, hem'⟩ := emsD_mem hem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    exact ⟨j, _, voteAt_of (List.getElem?_eq_getElem hj) hc hem', beq_iff_eq.1 hs⟩
  · rintro ⟨j, e, hv, hs⟩
    obtain ⟨r, hr, rfl, call, M, ems, hc, em, hem, rfl, -⟩ := voteAt_row hv
    refine List.mem_filterMap.2 ⟨r, List.mem_of_getElem? hr, ?_⟩
    have hany : (emsD r.cut).any (fun em => em.vote.slot == σ) = true :=
      List.any_eq_true.2 ⟨em, by rw [hc]; exact hem, beq_iff_eq.2 hs⟩
    simp only [hany, ↓reduceIte]

/-- The honest voters of slot `σ` as a set. -/
theorem voters_eq (ctl : Bool) (σ : Nat) :
    {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt (tr ctl).projAC x' j e' ∧ e'.msg.slot = σ} =
      {x' | x' ∈ votersD ctl σ} := by
  ext y
  simp only [Set.mem_ofPred_eq, votersD_iff]
  constructor
  · exact fun h => h.2
  · rintro ⟨j, e, hv, hs⟩
    obtain ⟨r, hr, rfl, -⟩ := voteAt_row hv
    exact ⟨row_honest hr, j, e, hv, hs⟩

/-- **`halfCommittee` fails in the rejection run**: the honest slot-7 voters are `a, b`, and
`5 ≤ 2 · 2` is false. -/
theorem rejection_not_halfCommittee : ¬ HalfCommitteeHolds (tr false) H 6 8 := by
  intro h
  have h7 := h 7 (by decide) (by decide)
  rw [voters_eq] at h7
  have hsub : {x' | x' ∈ votersD false 7} ⊆ ({va, vb} : Set (Fin 5)) := by
    intro y hy
    have hy' : y ∈ votersD false 7 := hy
    rcases List.mem_pair.1 (voters_checks.1 hy') with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair (by decide)] at this
  change 5 ≤ _ at h7
  omega

theorem cVote_row (ctl : Bool) :
    ∃ k e, SA.VoteAt (tr ctl).projAC vc k e ∧ e.msg = vt vc 8 (cHead ctl) ∧
      (⟨if ctl then 2 else 3, 4, false, 8⟩ : Lock) ∈ e.readPoint.locks := by
  obtain ⟨hlt, hn, -, em, hem, hv, hl⟩ := (checks_true ctl).2.2.1
  obtain ⟨call, M, ems, hc, hem'⟩ := emsD_mem hem
  have hr := rowI_eq hlt
  have := voteAt_of hr hc hem'
  rw [hn] at this
  exact ⟨_, _, this, hv, hl⟩

/-- **`c` votes `V` in slot `8`** in the rejection run, its lock `(V, 4, slow, 8)` kept by the
unlock (opponents `{a, b}`, `2 · 2 < 5`): the vote does not extend `B`. -/
theorem rejection_c_votes_V : ∃ k e, SA.VoteAt (tr false).projAC vc k e ∧ e.msg.slot = 8 ∧
    e.msg.head = 3 ∧ (⟨3, 4, false, 8⟩ : Lock) ∈ e.readPoint.locks ∧
    ¬ SA.VoteExtends ((tr false).HonestBlocks H) e.msg Bk := by
  obtain ⟨k, e, hv, hm, hl⟩ := cVote_row false
  exact ⟨k, e, hv, by rw [hm]; rfl, by rw [hm]; rfl, hl, not_extends_V false (by rw [hm]; rfl)⟩

/-- **(r) `halfCommittee` is necessary in `RecentSourceNextVote`**: a Goldilocks run with every
other premise of `PersistPremises` (`PersistPremisesExceptHalf`) for the fast lock of slot
`j = 6` on `B` written by `a` at `i₀`, `ac_to_fg` returning `B` at `i` in slot `m = 7`
(`j ≤ m ≤ j + 2`), `halfCommittee` false, and an honest vote of slot `m + 1` that does not extend
`B`. -/
theorem halfCommittee_necessary :
    ∃ (tr' : GoldilocksTrace X.sp ro) (i₀ i : Nat) (ℓ : ACLabel (goldilocksNode X.sp ro)),
      GoldilocksRun proposer dg H tr' ∧ PersistPremisesExceptHalf tr' H dg 1 va i₀ 6 (7 + 1) Bk CV ∧
      ¬ HalfCommitteeHolds tr' H 6 (7 + 1) ∧ SA.ToFGAt tr'.projAC va i ℓ Bk ∧
      X.sp.slot (tr'.time i) = 7 ∧ 6 ≤ 7 ∧ 7 ≤ 6 + 2 ∧
      ∃ y ∈ H, ∃ k e, SA.VoteAt tr'.projAC y k e ∧ e.msg.slot = 7 + 1 ∧
        ¬ SA.VoteExtends (tr'.HonestBlocks H) e.msg Bk := by
  obtain ⟨ℓ, htf, hsl⟩ := (source false).2.2
  obtain ⟨k, e, hv, hs, -, -, hne⟩ := rejection_c_votes_V
  exact ⟨tr false, i0 false, i0 false + 1, ℓ, run_goldilocksRun false, run_premisesExceptHalf false,
    rejection_not_halfCommittee, htf, hsl, by decide, by decide, vc, show vc ≠ vf by decide, k, e,
    hv, hs, hne⟩

/-- **The corollary**: by the proved `recent_source_next_vote`, the premises `PersistPremises`
fail in the rejection run (this is premise necessity, not a counterexample to the theorem). -/
theorem rejection_not_persistPremises :
    ¬ PersistPremises (tr false) H dg 1 va (i0 false) 6 8 Bk CV := by
  intro hp
  obtain ⟨ℓ, htf, hsl⟩ := (source false).2.2
  obtain ⟨k, e, hv, hs, -, -, hne⟩ := rejection_c_votes_V
  exact hne (recent_source_next_vote X.sp ro dg H (tr false) 1 va (i0 false) (i0 false + 1) 6 7 ℓ
    Bk CV proposer (run_goldilocksRun false) hp htf hsl (by decide) (by decide) vc
    (show vc ≠ vf by decide) k e hv hs)

end Consensus.Goldilocks.Test.HalfCommittee.Five

end
