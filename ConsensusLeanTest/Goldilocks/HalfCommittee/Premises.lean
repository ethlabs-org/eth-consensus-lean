module
public import ConsensusLeanTest.Goldilocks.HalfCommittee.Run
public import ConsensusLeanTest.Goldilocks.Runs.Data.Premises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
@[expose] public section

/-! # The halfCommittee run: every premise but `halfCommittee`, and its necessity

Kind (r), rejection: **premise necessity, not a counterexample**. `RecentSourceNextVote` is
proved (`recent_source_next_vote`); this module shows that its premise `halfCommittee` cannot
be dropped. In the rejection run of `Goldilocks/HalfCommittee/Run` (`ctl = false`) the writer `a`
writes at its tick of `30` (`i₀ = i0 false`) the fast lock of slot `j = 6` on `B` with the
counted votes `CV = {a6, b6, f6}` (score `3`, expiry `8`), and `ac_to_fg` returns `B` at the next
cut (`i₀ + 1`, slot `7 = m`). Every premise of `PersistPremises … a i₀ 6 8 B CV` except
`halfCommittee` holds (`run_premisesExceptHalf`, for both variants; the test-local
`PersistPremisesExceptHalf` copies the other fields, with no edit to the statement):
`Sync[24, 33]` (`run_sync`), `Carry(6, CV, B)` (the slot-7 voters accepted `B`
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
proved theorem. The run reprocesses at `28` (`Goldilocks/HalfCommittee/Run`): `c`'s new pool
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
  /-- The stock committee. -/
  stock : sp.committeeSize = sp.n

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
      p.faultBound, p.noColl, p.clean, p.stock⟩, p.halfCommittee⟩,
    fun ⟨p, h⟩ => ⟨p.writer_honest, p.fastLock, p.writer_joined, p.lt, p.sync, p.carry, h,
      p.carryLater, p.faultBound, p.noColl, p.clean, p.stock⟩⟩

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
def i0 (ctl : Bool) : Nat := (dataRows ctl).findIdx fun r => r.node == va && r.time == 30

/-- `c`'s tick at `33`: its first cut at `33`. -/
def kc (ctl : Bool) : Nat := (dataRows ctl).findIdx fun r => r.node == vc && r.time == 33

/-- Row `i`. -/
def dataRowAt (ctl : Bool) (i : Nat) : DataRow := DataRun.rowI (dataD ctl) i

open DataRun (tickM toFGM emsD fastSelD cvD heldD isRestartCut)

/-- The source: `a`'s tick at `30` writes the fast lock of slot `6` on `B` counting `cvL`, and
its `ac_to_fg` at the next cut returns `B`. -/
def SourceD (ctl : Bool) : Prop :=
  i0 ctl + 1 < (dataRows ctl).length ∧ (dataRowAt ctl (i0 ctl)).node = va ∧
    (dataRowAt ctl (i0 ctl)).time = 30 ∧ tickM (dataRowAt ctl (i0 ctl)).cut = some [1, 2] ∧
    (dataRowAt ctl (i0 ctl)).pre.ac.getConf [1, 2] 6 = some 1 ∧
    fastSelD (dataRowAt ctl (i0 ctl)).pre.ac [1, 2] 30 6 1 = some 1 ∧
    (dataRowAt ctl (i0 ctl)).pre.ac.joinedB 30 = true ∧
    cvD (dataRowAt ctl (i0 ctl)).pre.ac [1, 2] 6 1 = cvL ∧
    (dataRowAt ctl (i0 ctl + 1)).node = va ∧ (dataRowAt ctl (i0 ctl + 1)).time = 30 ∧
    toFGM (dataRowAt ctl (i0 ctl + 1)).cut = some [1, 2] ∧
    ((dataRowAt ctl (i0 ctl + 1)).pre.ac.toFG [1, 2] 30).2 = some 1

instance (ctl : Bool) : Decidable (SourceD ctl) := by unfold SourceD; infer_instance

/-- An `ac_on_block(B)` cut. -/
abbrev acceptsB : CutD X → Bool := DataRun.blockIs 1

/-- `y` accepts `B` (an `ac_on_block(B)` cut) before `T`. -/
def accB (ctl : Bool) (y : Fin 5) (T : Nat) : Bool :=
  (dataRows ctl).any fun r => r.node == y && decide (r.time < T) && acceptsB r.cut

/-- The honest votes of slot `σ`. -/
abbrev votesD (ctl : Bool) (σ : Nat) : List X.V := DataRun.votesD (dataD ctl) σ

/-- The checks at a vote of slot `7` or `8` (and no vote of a later slot): joined, `Carry`,
`B` accepted before `t_{s−1} + 3` and in the voter block tree. -/
def voteChecks (ctl : Bool) (r : DataRow) (M : List Nat) (em : X.EmD) : Bool :=
  if em.vote.slot = 7 then em.rp.joinedB r.time && cvL.all (heldD em.rp · 27) &&
    accB ctl r.node 27 && decide (1 ∈ em.rp.vbt M 7)
  else if em.vote.slot = 8 then em.rp.joinedB r.time &&
    (votesD ctl 7).all (fun v => v.head == 1 && heldD em.rp v 31) && accB ctl r.node 31 &&
    decide (1 ∈ em.rp.vbt M 8)
  else decide (em.vote.slot < 7)

/-- The checks on the rows: honest nodes, the fragment, the votes (with the frame tree of the
call the node's tree), the signatures (all name genesis), no restart of `a` or `b`. -/
def rowsChk (ctl : Bool) : Bool :=
  (dataRows ctl).all fun r => r.node != vf && decide (X.Frag r.post) &&
    (match r.cut with
      | .ac _ M ems => M == r.post.fg.tree && ems.all (voteChecks ctl r M)
      | .fgAttest _ (some a) => a.T == 2
      | _ => true) &&
    !(isRestartCut r.cut && (r.node == va || r.node == vb))

/-- `c`'s vote at `33`: slot `8`, head `cHead ctl` (`V` in the rejection run, `B` in the
control), with the live lock `(V, 4, slow, 8)` in the rejection run and `(G, 4, slow, 8)`
(unlocked) in the control at its read point. -/
def CVoteD (ctl : Bool) : Prop :=
  kc ctl < (dataRows ctl).length ∧ (dataRowAt ctl (kc ctl)).node = vc ∧
    (dataRowAt ctl (kc ctl)).time = 33 ∧
    ∃ em ∈ emsD (dataRowAt ctl (kc ctl)).cut, em.vote = vt vc 8 (cHead ctl) ∧
      (⟨if ctl then 2 else 3, 4, false, 8⟩ : Lock) ∈ em.rp.locks

instance (ctl : Bool) : Decidable (CVoteD ctl) := by unfold CVoteD; infer_instance

/-- The honest voters of slot `σ`. -/
abbrev votersD (ctl : Bool) (σ : Nat) : List (Fin 5) := DataRun.votersD (dataD ctl) σ

private theorem premiseChecks : (∀ ctl, SourceD ctl ∧ rowsChk ctl = true ∧ CVoteD ctl ∧
    1 ∈ (stateD ctl va (dataRows ctl).length).fg.tree) ∧
    votersD false 7 ⊆ [va, vb] ∧ [va, vb, vd] ⊆ votersD true 7 ∧
    [va, vb, vd] ⊆ votersD true 8 := by
  decide +kernel

private theorem checks_true : ∀ ctl, SourceD ctl ∧ rowsChk ctl = true ∧ CVoteD ctl ∧
    1 ∈ (stateD ctl va (dataRows ctl).length).fg.tree := premiseChecks.1

theorem voters_checks : votersD false 7 ⊆ [va, vb] ∧ [va, vb, vd] ⊆ votersD true 7 ∧
    [va, vb, vd] ⊆ votersD true 8 := premiseChecks.2


/-! ## The run on data -/

private theorem rowsChk_row {ctl : Bool} {i : Nat} {r : DataRow}
    (hr : (dataRows ctl)[i]? = some r) :
    r.node ≠ vf ∧ X.Frag r.post ∧
      (match r.cut with
        | .ac _ M ems => M == r.post.fg.tree && ems.all (voteChecks ctl r M)
        | .fgAttest _ (some a) => a.T == 2
        | _ => true) = true ∧
      (isRestartCut r.cut && (r.node == va || r.node == vb)) = false := by
  have h := List.all_eq_true.1 (checks_true ctl).2.1 r (List.mem_of_getElem? hr)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem row_honest {ctl : Bool} {i : Nat} {r : DataRow} (hr : (dataRows ctl)[i]? = some r) :
    r.node ∈ H := (rowsChk_row hr).1

private theorem acRow_chk {ctl : Bool} {i : Nat} {r : DataRow} (hr : (dataRows ctl)[i]? = some r)
    {call : CallD X} {M : List Nat} {ems : List X.EmD} (hc : r.cut = .ac call M ems) :
    M = r.post.fg.tree ∧ ∀ em ∈ ems, voteChecks ctl r M em = true := by
  have h := (rowsChk_row hr).2.2.1
  rw [hc] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h

theorem localRun (ctl : Bool) :
    Node.LocalRun proposer dg H (fun v : Vote X.sp.n => v.val) (tr ctl) :=
  (run_goldilocksRun ctl).toLocalRun

/-- A vote of the projection is an emission of an AC row, with its checks. -/
private theorem voteAt_row {ctl : Bool} {y : Fin 5} {i : Nat}
    {e : SA.Em X.sp (List (FG.Att X.sp.n))}
    (h : SA.VoteAt (tr ctl).projAC y i e) :
    ∃ r, (dataRows ctl)[i]? = some r ∧ r.node = y ∧ ∃ call M ems, r.cut = .ac call M ems ∧
      ∃ em ∈ ems, e = em.interp ∧ voteChecks ctl r M em = true ∧ M = r.post.fg.tree := by
  obtain ⟨r, hr, hn, call, M, ems, hcut, em, hem, rfl⟩ := DataRun.voteAt_row (runD ctl) h
  have := acRow_chk hr hcut
  exact ⟨r, hr, hn, call, M, ems, hcut, em, hem, rfl, this.2 em hem, this.1⟩

/-! ## The honest blocks -/

private theorem frag_rows {ctl : Bool} : ∀ r ∈ dataRows ctl, X.Frag r.post := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  exact (rowsChk_row (List.getElem?_eq_getElem hi)).2.1

theorem blk_honest (ctl : Bool) {r : Nat} (hr : r = 1 ∨ r = 2) :
    X.blk r ∈ (tr ctl).HonestBlocks H := by
  refine DataRun.blk_honest (runD ctl) frag_rows (show va ≠ vf by decide)
    (c := (dataRows ctl).length) ?_
  rcases hr with rfl | rfl
  · exact (checks_true ctl).2.2.2
  · exact (DataRun.frag_stateD frag_rows va _).1.g_mem

theorem gBlk_honest (ctl : Bool) : X.gBlk ∈ (tr ctl).HonestBlocks H :=
  blk_g hX ▸ blk_honest ctl (Or.inr rfl)

/-- The ancestors of `B` inside the honest blocks: `B` and genesis. -/
theorem anc_Bk {ctl : Bool} {A : X.Blk} (h : Anc ((tr ctl).HonestBlocks H) A Bk) :
    A = X.blk 1 ∨ A = X.blk 2 := by
  obtain ⟨a, ha, rfl⟩ := DataRun.anc_chain (runD ctl) hX frag_rows (by decide) h
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
  exact DataRun.not_extends (runD ctl) hX frag_rows (by decide) (by rw [hv]; decide)

/-! ## The source -/

/-- The source on data: the rows of `a`'s tick and `ac_to_fg` at `30`. -/
private theorem source_rows (ctl : Bool) :
    ∃ r₀ r₁ ems₀ ems₁, (dataRows ctl)[i0 ctl]? = some r₀ ∧ (dataRows ctl)[i0 ctl + 1]? = some r₁ ∧
      r₀.node = va ∧ r₀.time = 30 ∧ r₀.cut = .ac .tick [1, 2] ems₀ ∧
      r₀.pre.ac.getConf [1, 2] 6 = some 1 ∧ fastSelD r₀.pre.ac [1, 2] 30 6 1 = some 1 ∧
      r₀.pre.ac.joinedB 30 = true ∧ cvD r₀.pre.ac [1, 2] 6 1 = cvL ∧ r₁.node = va ∧
      r₁.time = 30 ∧ r₁.cut = .ac .toFG [1, 2] ems₁ ∧ (r₁.pre.ac.toFG [1, 2] 30).2 = some 1 := by
  obtain ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12⟩ := (checks_true ctl).1
  obtain ⟨ems₀, he₀⟩ := DataRun.tickM_some h3
  obtain ⟨ems₁, he₁⟩ := DataRun.toFGM_some h11
  have hr₀ : (dataRows ctl)[i0 ctl]? = some (dataRowAt ctl (i0 ctl)) :=
    DataRun.rowI_eq (Nat.lt_of_succ_lt hlt)
  have hr₁ : (dataRows ctl)[i0 ctl + 1]? = some (dataRowAt ctl (i0 ctl + 1)) := DataRun.rowI_eq hlt
  exact ⟨_, _, ems₀, ems₁, hr₀, hr₁, h1, h2, he₀, h4, h5, h6, h7, h9, h10,
    he₁, h12⟩

theorem closed12 : X.Closed [1, 2] := by decide

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
  obtain ⟨hlock, hjoin, ⟨ℓ, htf⟩, htime⟩ := DataRun.source_mk (runD ctl)
    (run_goldilocksRun ctl) hX (show va ≠ vf by decide) closed12 (t := 30) (s := 6)
    (c := 1) (b := 1) rfl h₀ h₁ hn₀ ht₀ hc₀ (by decide) (by decide) hg hf hj hcv
    hn₁ ht₁ hc₁ htf
  refine ⟨hlock, hjoin, ℓ, htf, ?_⟩
  change X.sp.slot ((runD ctl).tr.time (i0 ctl + 1)) = 7
  rw [htime, Fix.slot_eq]; rfl

/-! ## Carry, the fault bound, `NoColl`, `Clean` -/

theorem accepted_of {ctl : Bool} {y : Fin 5} {T : Nat} (h : accB ctl y T = true) :
    ∃ k, (tr ctl).projAC.AcceptAt y k Bk ∧ (tr ctl).time k < T := by
  obtain ⟨r, hm, hr⟩ := List.any_eq_true.1 h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  have hrk := List.getElem?_eq_getElem hk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
  obtain ⟨⟨hn, ht⟩, hb⟩ := hr
  refine ⟨k, ?_, ?_⟩
  · obtain ⟨M, ems, hc⟩ : ∃ M ems, (dataRows ctl)[k].cut = .ac (.block 1) M ems := by
      exact DataRun.blockIs_true hb
    exact ⟨_, hn ▸ DataRun.acRow_of (runD ctl) hrk hc, rfl⟩
  · change (runD ctl).tr.time k < (T : Int)
    rw [DataRun.rowsD_time (runD ctl) hrk]; exact_mod_cast ht

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
    exact (localRun ctl).awake_of_call y hy i ⟨_, DataRun.projAC_call (runD ctl) hc⟩
  joined := hj
  heads v hvS := by
    refine ⟨Bk, blk_honest ctl (Or.inl rfl), by rw [(hS v hvS).1]; rfl, fun X' hX' => ?_⟩
    rcases anc_Bk hX' with rfl | rfl
    · obtain ⟨k, hk, htk⟩ := accepted_of hacc
      refine Or.inr ⟨k, hk, ?_⟩
      rw [hT]; exact htk
    · exact Or.inl rfl
  holds v hvS := by rw [hT]; exact Or.inl (hS v hvS).2

private theorem voteD_slot7 {ctl : Bool} {r : DataRow} {M : List Nat} {em : X.EmD}
    (h : voteChecks ctl r M em = true)
    (hs : em.vote.slot = 7) : em.rp.joinedB r.time = true ∧ (∀ v ∈ cvL, heldD em.rp v 27 = true) ∧
      accB ctl r.node 27 = true ∧ 1 ∈ em.rp.vbt M 7 := by
  simp only [voteChecks, hs, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem voteD_slot8 {ctl : Bool} {r : DataRow} {M : List Nat} {em : X.EmD}
    (h : voteChecks ctl r M em = true)
    (hs : em.vote.slot = 8) : em.rp.joinedB r.time = true ∧
      (∀ v ∈ votesD ctl 7, v.head = 1 ∧ heldD em.rp v 31 = true) ∧
      accB ctl r.node 31 = true ∧ 1 ∈ em.rp.vbt M 8 := by
  have h87 : ((8 : Nat) = 7) = False := by decide
  simp only [voteChecks, hs, h87, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem voteD_slot {ctl : Bool} {r : DataRow} {M : List Nat} {em : X.EmD}
    (h : voteChecks ctl r M em = true) :
    em.vote.slot ≤ 8 := by
  unfold voteChecks at h
  split_ifs at h with h7 h8
  · omega
  · omega
  · simp only [decide_eq_true_eq] at h; omega

/-- **`Carry(6, CV, B)`**, in both variants. -/
theorem run_carry (ctl : Bool) : SA.Carry (tr ctl).projAC H ((tr ctl).HonestBlocks H) 6 CV := by
  intro y hy i e hv hs
  obtain ⟨r, hr, hn, call, M, ems, hc, em, hem, rfl, hchk, -⟩ := voteAt_row hv
  obtain ⟨hj, hheld, hacc, -⟩ := voteD_slot7 hchk hs
  refine carryAt_mk hy hv rfl CV (DataRun.joined_row (runD ctl) hr hj)
    (fun v hvS => ⟨?_, DataRun.heldD_spec (hheld v hvS)⟩)
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
  refine carryAt_mk hy hv rfl _ (DataRun.joined_row (runD ctl) hr hj)
    (fun v hvS => ?_) (by rw [← hn]; exact hacc)
  exact ⟨(hheld v (DataRun.mem_votesD (runD ctl) hvS)).1,
    DataRun.heldD_spec (hheld v (DataRun.mem_votesD (runD ctl) hvS)).2⟩

theorem awakeB_ab : ∀ ctl, ∀ n < 36, awakeB ctl va n = true ∧ awakeB ctl vb n = true := by decide

theorem joinedAt_ab {ctl : Bool} {y : Fin 5} (hy : y = va ∨ y = vb) (t : Time) :
    (tr ctl).JoinedAt y t := by
  intro k hk
  obtain ⟨r, hr, rfl, hres⟩ := (DataRun.restartAt_iff (runD ctl)).1 hk
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
    · obtain ⟨b, hb, rfl⟩ := DataRun.fgBlock_ok (runD ctl) (dataRowLaws ctl) hB
      have hb' : b = 1 ∨ b = 3 := by simpa [Fix.roots, X, rowB, rowV] using hb
      rcases hb' with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  intro B hB C hC h
  rcases cls B hB with rfl | rfl | rfl <;> rcases cls C hC with rfl | rfl | rfl <;>
    revert h <;> decide

/-- An honest signature names genesis. -/
theorem signAt_T {ctl : Bool} {v : Fin 5} {j : Nat} {a : FG.Att X.sp.n}
    (h : (tr ctl).projFG.SignAt v j a) : a.T = 2 := by
  obtain ⟨r, hr, b, hb⟩ := DataRun.signAt_row (runD ctl) h
  have := (rowsChk_row hr).2.2.1
  rw [hb] at this
  simpa using this

/-- **`Clean(6, 8, B)`**, in both variants. -/
theorem run_clean (ctl : Bool) : Clean (tr ctl) H 6 8 Bk where
  caches := DataRun.clean_caches (runD ctl) (gBlk_anc_Bk ctl)
  fgAttCut E' hE' := by
    have hsub : Store.namers X.sp.toParams (Payload X.sp.n) H (tr ctl).projFG
        (X.sp.ts (6 + 1 : Nat) + X.sp.Δ) E' ⊆ Hᶜ :=
      DataRun.namers_sub (runD ctl) hX frag_rows (fun r hr b a hc => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
        have h := (rowsChk_row (List.getElem?_eq_getElem hi)).2.2.1
        simpa [hc] using h) E' hE'
    have hc : Hᶜ = {vf} := by ext y; simp [H]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hc, Set.ncard_singleton] at this
    change _ < 4
    omega
  heightLead := DataRun.heightLead_mk (runD ctl) hX fun i r call M ems em hr hcut hem h1 h2 => by
    obtain ⟨hM, hchk⟩ := acRow_chk hr hcut
    refine ⟨hM ▸ (rowsChk_row hr).2.1.1, ?_⟩
    rcases (show em.vote.slot = 7 ∨ em.vote.slot = 8 by omega) with hs | hs
    · rw [hs]; exact (voteD_slot7 (hchk em hem) hs).2.2.2
    · rw [hs]; exact (voteD_slot8 (hchk em hem) hs).2.2.2

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
  stock := rfl

/-! ## The failure of `halfCommittee` and of the conclusion -/

theorem votersD_iff {ctl : Bool} {σ : Nat} {y : Fin 5} :
    y ∈ votersD ctl σ ↔ ∃ j e, SA.VoteAt (tr ctl).projAC y j e ∧ e.msg.slot = σ :=
  DataRun.mem_votersD (runD ctl)

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
  obtain ⟨call, M, ems, hc, hem'⟩ := DataRun.emsD_mem hem
  have hr : (dataRows ctl)[kc ctl]? = some (dataRowAt ctl (kc ctl)) := DataRun.rowI_eq hlt
  have := DataRun.voteAt_of (runD ctl) hr hc hem'
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
