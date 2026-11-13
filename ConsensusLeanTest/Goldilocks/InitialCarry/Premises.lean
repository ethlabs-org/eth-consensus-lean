module
public import ConsensusLeanTest.Goldilocks.InitialCarry.Run
public import ConsensusLeanTest.Goldilocks.Runs.Data.Premises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
@[expose] public section

/-! # The Initial-Carry run: every premise but the initial `Carry`

Kind (r) and (control), shared part: **premise necessity, not a counterexample**.
`RecentSourceNextVote` is proved (`recent_source_next_vote`); the witness shows that its premise
`carry` (the initial `Carry(s, CV, B)`) cannot be dropped. In both variants of the run of
`Goldilocks/InitialCarry/Run`, the writer `a` writes at its tick of `30` (`i₀ = i0 ctl`) the fast
lock of slot `j = 6` on `B` with the counted votes `CV = {f6, a6, b6}` (heads `B`, `Da`, `Db`:
each extends `B`), and `ac_to_fg` returns `B` at the next cut (`i₀ + 1`, slot `7 = m`). Every
field of `PersistPremises … a i₀ 6 8 B CV` except `carry` holds (`run_premisesExceptCarry`, both
variants; the test-local `PersistPremisesExceptCarry` copies the other fields in the order of
`Statements/Compose/Persist`, with no edit to the statement, and `persistPremises_iff_carry`
splits `PersistPremises` into it and `CarryHolds`):
`Sync[24, 33]` (`run_sync`); `halfCommittee` (the honest voters of slots `7` and `8` include
`a, b, c`, and `5 ≤ 2 · 3`); `carryLater` (the slot-8 voters hold the slot-7 votes stamped
`29 < 31` and accepted their head chains, `B, G` and `V, G`, before `31`; no slot-9 vote);
`f < h_t` (`a, b` are awake and joined); `NoColl` over the five contents of genesis, `B`, `V`,
`Da`, `Db`; and `Clean`: (K0) the caches are genesis, (K1) every honest signature names genesis,
(K2) `B` is in every slot-7 and slot-8 voter block tree.

The checks on data are bundled in `checks_true` (the source, the vote checks of every row, `c`'s
votes of slots `7` and `8`, the honest trees) and `voters_checks`. The heads of the counted votes
sit at two levels above genesis (`Da → B → G`, `Db → B → G`): `carryAt_mk` takes the head chains
(`X.chain`, by `anc_T` inside the honest blocks `allR`) instead of the single head `B` of
stage 2.

The fixture-free row, source and head-chain lemmas come from
`Goldilocks/Runs/Data/Premises`; this file supplies the fixture's checks and their reading.
`PersistPremisesExceptCarry` drops a different field from `PersistPremisesExceptHalf`.

Finite horizon (as in stage 2): the run ends at `35`; `carryLater` at `s' = 8` is vacuous (no
slot-9 vote). -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Heads

open SA Compose

section Generic

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **`PersistPremises` without the initial `carry`**: a test-local copy of the other fields of
`Compose.PersistPremises` (`Statements/Compose/Persist`), in its field order, with no edit to the
statement. -/
structure PersistPremisesExceptCarry (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
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
  /-- At least half of the committee votes honestly in every slot `s' ∈ (s, m]`. -/
  halfCommittee : ∀ s', s < s' → s' ≤ m →
    sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard
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

/-- The field `carry` of `PersistPremises`: the initial `Carry(s, CV, B)`. -/
def CarryHolds (s : Nat) (CV : Set (Vote sp.n)) : Prop :=
  SA.Carry tr.projAC H (tr.HonestBlocks H) s CV

variable {tr H}

/-- `PersistPremises` is the copy and the initial `Carry`. -/
theorem persistPremises_iff_carry {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {ΔF : Time}
    {x : Fin sp.n} {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} :
    PersistPremises tr H dg ΔF x i₀ s m B CV ↔
      PersistPremisesExceptCarry tr H dg ΔF x i₀ s m B CV ∧ CarryHolds tr H s CV :=
  ⟨fun p => ⟨⟨p.writer_honest, p.fastLock, p.writer_joined, p.lt, p.sync, p.halfCommittee,
      p.carryLater, p.faultBound, p.noColl, p.clean, p.stock⟩, p.carry⟩,
    fun ⟨p, h⟩ => ⟨p.writer_honest, p.fastLock, p.writer_joined, p.lt, p.sync, h,
      p.halfCommittee, p.carryLater, p.faultBound, p.noColl, p.clean, p.stock⟩⟩

end Generic

open Fix ScheduleRun
open Five (va vb vc vd vf H honest)

/-! ## The source and the checks on data -/

/-- The counted votes of the source, in `a`'s pool order: `f6` (head `B`), `a6` (head `Da`),
`b6` (head `Db`). -/
def cvL : List X.V := [vt vf 6 1, vt va 6 4, vt vb 6 5]

/-- The counted votes as a set. -/
def CV : Set (Vote 5) := {v | v ∈ cvL}

/-- The block `B`. -/
abbrev Bk : X.Blk := X.blk 1

/-- The roots of the table with genesis. -/
def allR : List Nat := [2, 1, 3, 4, 5]

theorem allR_closed : X.Closed allR := by decide

/-- `a`'s tree at its tick of `30`: genesis, `B`, `Da`, `Db`. -/
def Ma : List Nat := [5, 4, 1, 2]

theorem closedMa : X.Closed Ma := by decide

/-- The first cut of `y` at `t`. -/
def kAt (ctl : Bool) (y : Fin 5) (t : Nat) : Nat :=
  DataRun.kAt (dataD ctl) y t

/-- The writer's tick at `30`. -/
def i0 (ctl : Bool) : Nat := kAt ctl va 30

/-- Row `i`. -/
def rowI (ctl : Bool) (i : Nat) : RowD := DataRun.rowI (dataD ctl) i

open DataRun (tickM toFGM emsD fastSelD cvD heldD blockIs)

/-- The source: `a`'s tick at `30` writes the fast lock of slot `6` on `B` counting `cvL`, and
its `ac_to_fg` at the next cut returns `B`. -/
def SourceD (ctl : Bool) : Prop :=
  i0 ctl + 1 < (rowsD ctl).length ∧ (rowI ctl (i0 ctl)).node = va ∧
    (rowI ctl (i0 ctl)).time = 30 ∧ tickM (rowI ctl (i0 ctl)).cut = some Ma ∧
    (rowI ctl (i0 ctl)).pre.ac.getConf Ma 6 = some 1 ∧
    fastSelD (rowI ctl (i0 ctl)).pre.ac Ma 30 6 1 = some 1 ∧
    (rowI ctl (i0 ctl)).pre.ac.joinedB 30 = true ∧ cvD (rowI ctl (i0 ctl)).pre.ac Ma 6 1 = cvL ∧
    (rowI ctl (i0 ctl + 1)).node = va ∧ (rowI ctl (i0 ctl + 1)).time = 30 ∧
    toFGM (rowI ctl (i0 ctl + 1)).cut = some Ma ∧
    ((rowI ctl (i0 ctl + 1)).pre.ac.toFG Ma 30).2 = some 1

instance (ctl : Bool) : Decidable (SourceD ctl) := by unfold SourceD; infer_instance

/-- `y` accepted the root `b` (an `ac_on_block` cut) before `T`, or `b` is genesis. -/
abbrev accR (ctl : Bool) (y : Fin 5) (b T : Nat) : Bool := DataRun.accR (dataD ctl) y b T

/-- `y` accepted the chain of the root `h` (`h` and its ancestors) before `T`. -/
abbrev chainAcc (ctl : Bool) (y : Fin 5) (h T : Nat) : Bool := DataRun.chainAcc (dataD ctl) y h T

/-- The honest votes of slot `σ`. -/
abbrev votesD (ctl : Bool) (σ : Nat) : List X.V := DataRun.votesD (dataD ctl) σ

/-- The checks at a vote of slot `7` or `8` (and no vote of a later slot). Slot `7`: joined, the
counted votes held before `t_6 + 3 = 27`, `B` in the voter block tree, and, in the control only,
the head chains of the counted votes accepted before `27` (the initial `Carry`'s `heads`, which
fails at `c` in the rejection run). Slot `8`: joined, every slot-7 vote held before
`t_7 + 3 = 31` with its head chain accepted before `31`, `B` in the voter block tree. -/
def voteD (ctl : Bool) (r : RowD) (M : List Nat) (em : X.EmD) : Bool :=
  if em.vote.slot = 7 then em.rp.joinedB r.time && cvL.all (heldD em.rp · 27) &&
    (!ctl || cvL.all fun v => chainAcc ctl r.node v.head 27) && decide (1 ∈ em.rp.vbt M 7)
  else if em.vote.slot = 8 then em.rp.joinedB r.time &&
    (votesD ctl 7).all (fun v => decide (v.head ∈ allR) && heldD em.rp v 31 &&
      chainAcc ctl r.node v.head 31) && decide (1 ∈ em.rp.vbt M 8)
  else decide (em.vote.slot < 7)

/-- The checks on the rows: honest nodes, the fragment, the votes (with the frame tree of the
call the node's tree), the signatures (all name genesis). -/
def rowsChk (ctl : Bool) : Bool :=
  (rowsD ctl).all fun r => r.node != vf && decide (X.Frag r.post) &&
    (match r.cut with
      | .ac _ M ems => M == r.post.fg.tree && ems.all (voteD ctl r M)
      | .fgAttest _ (some a) => a.T == 2
      | _ => true)

/-- The first cut of `y` at `t` emits the vote `v` with an emission satisfying `P`. -/
def VoteRowD (ctl : Bool) (y : Fin 5) (t : Nat) (v : X.V) (P : X.EmD → Bool) : Prop :=
  kAt ctl y t < (rowsD ctl).length ∧ (rowI ctl (kAt ctl y t)).node = y ∧
    ∃ em ∈ emsD (rowI ctl (kAt ctl y t)).cut, em.vote = v ∧ P em = true

instance (ctl : Bool) (y : Fin 5) (t : Nat) (v : X.V) (P : X.EmD → Bool) :
    Decidable (VoteRowD ctl y t v P) := by unfold VoteRowD; infer_instance

/-- `c`'s lock `(V, 4, slow, 8)` at the read point (checked in the rejection run only). -/
def lockV (ctl : Bool) (em : X.EmD) : Bool :=
  ctl || decide ((⟨3, 4, false, 8⟩ : Lock) ∈ em.rp.locks)

/-- The honest voters of slot `σ`. -/
abbrev votersD (ctl : Bool) (σ : Nat) : List (Fin 5) := DataRun.votersD (dataD ctl) σ

private theorem premiseChecks : (∀ ctl, SourceD ctl ∧ rowsChk ctl = true ∧
    VoteRowD ctl vc 29 (vt vc 7 (cHead ctl)) (fun _ => true) ∧
    VoteRowD ctl vc 33 (vt vc 8 (cHead ctl)) (lockV ctl) ∧
    allR.all (· ∈ (stateD ctl va (rowsD ctl).length).fg.tree) = true) ∧
    (∀ ctl, [va, vb, vc] ⊆ votersD ctl 7 ∧ [va, vb, vc] ⊆ votersD ctl 8) := by
  decide +kernel

/-- The checks on data: the source; the rows; `c`'s votes at `29` (slot `7`) and `33` (slot `8`)
with head `cHead ctl`, and the lock `(V, 4, slow, 8)` at the slot-8 vote of the rejection run;
every root of `allR` in `a`'s final tree. -/
theorem checks_true : ∀ ctl, SourceD ctl ∧ rowsChk ctl = true ∧
    VoteRowD ctl vc 29 (vt vc 7 (cHead ctl)) (fun _ => true) ∧
    VoteRowD ctl vc 33 (vt vc 8 (cHead ctl)) (lockV ctl) ∧
    allR.all (· ∈ (stateD ctl va (rowsD ctl).length).fg.tree) = true := premiseChecks.1

theorem voters_checks : ∀ ctl, [va, vb, vc] ⊆ votersD ctl 7 ∧ [va, vb, vc] ⊆ votersD ctl 8 :=
  premiseChecks.2

/-! ## The run on data -/

theorem rowsChk_row {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    r.node ≠ vf ∧ X.Frag r.post ∧
      (match r.cut with
        | .ac _ M ems => M == r.post.fg.tree && ems.all (voteD ctl r M)
        | .fgAttest _ (some a) => a.T == 2
        | _ => true) = true := by
  have h := List.all_eq_true.1 (checks_true ctl).2.1 r (List.mem_of_getElem? hr)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem row_honest {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r) :
    r.node ∈ H := (rowsChk_row hr).1

theorem acRow_chk {ctl : Bool} {i : Nat} {r : RowD} (hr : (rowsD ctl)[i]? = some r)
    {call : CallD X} {M : List Nat} {ems : List X.EmD} (hc : r.cut = .ac call M ems) :
    M = r.post.fg.tree ∧ ∀ em ∈ ems, voteD ctl r M em = true := by
  have h := (rowsChk_row hr).2.2
  rw [hc] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h

theorem localRun (ctl : Bool) :
    Node.LocalRun proposer dg H (fun v : Vote X.sp.n => v.val) (tr ctl) :=
  (run_goldilocksRun ctl).toLocalRun

/-- A vote of the projection is an emission of an AC row, with its checks. -/
theorem voteAt_row {ctl : Bool} {y : Fin 5} {i : Nat} {e : SA.Em X.sp (List (FG.Att X.sp.n))}
    (h : SA.VoteAt (tr ctl).projAC y i e) :
    ∃ r, (rowsD ctl)[i]? = some r ∧ r.node = y ∧ ∃ call M ems, r.cut = .ac call M ems ∧
      ∃ em ∈ ems, e = em.interp ∧ voteD ctl r M em = true ∧ M = r.post.fg.tree := by
  obtain ⟨r, hr, hn, call, M, ems, hcut, em, hem, rfl⟩ := DataRun.voteAt_row (runD ctl) h
  have := acRow_chk hr hcut
  exact ⟨r, hr, hn, call, M, ems, hcut, em, hem, rfl, this.2 em hem, this.1⟩

/-- A vote row on data is a vote of the projection. -/
theorem voteRow_spec {ctl : Bool} {y : Fin 5} {t : Nat} {v : X.V} {P : X.EmD → Bool}
    (h : VoteRowD ctl y t v P) :
    ∃ k em, SA.VoteAt (tr ctl).projAC y k em.interp ∧ em.vote = v ∧ P em = true := by
  obtain ⟨hlt, hn, em, hem, hv, hP⟩ := h
  obtain ⟨call, M, ems, hc, hem'⟩ := DataRun.emsD_mem hem
  have hr : (rowsD ctl)[kAt ctl y t]? = some (rowI ctl (kAt ctl y t)) := DataRun.rowI_eq hlt
  have := DataRun.voteAt_of (runD ctl) hr hc hem'
  rw [hn] at this
  exact ⟨_, em, this, hv, hP⟩

/-! ## The honest blocks -/

theorem frag_rows {ctl : Bool} : ∀ r ∈ rowsD ctl, X.Frag r.post := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  exact (rowsChk_row (List.getElem?_eq_getElem hi)).2.1

/-- Every root of the table, and genesis, is an honest block: all are in `a`'s final tree. -/
theorem blk_honest (ctl : Bool) {r : Nat} (hr : r ∈ allR) : X.blk r ∈ (tr ctl).HonestBlocks H := by
  exact DataRun.blk_honest (runD ctl) frag_rows (show va ≠ vf by decide)
    (List.all_eq_true.1 (checks_true ctl).2.2.2.2 r hr |> of_decide_eq_true)

theorem gBlk_honest (ctl : Bool) : X.gBlk ∈ (tr ctl).HonestBlocks H :=
  blk_g hX ▸ blk_honest ctl (by decide)

theorem chain_Da : X.chain 4 = [4, 1, 2] := rfl
theorem chain_Db : X.chain 5 = [5, 1, 2] := rfl

theorem gBlk_anc_Bk (ctl : Bool) : Anc ((tr ctl).HonestBlocks H) X.gBlk Bk :=
  Relation.ReflTransGen.single ⟨gBlk_honest ctl, blk_honest ctl (by decide), rfl⟩

/-- **A vote with head `V` does not extend `B`** inside the honest blocks. -/
theorem not_extends_V (ctl : Bool) {v : Vote 5} (hv : v.head = 3) :
    ¬ SA.VoteExtends ((tr ctl).HonestBlocks H) v Bk := by
  exact DataRun.not_extends (runD ctl) hX frag_rows (by decide) (by rw [hv]; decide)

/-! ## The source -/

/-- The source on data: the rows of `a`'s tick and `ac_to_fg` at `30`. -/
private theorem source_rows (ctl : Bool) :
    ∃ r₀ r₁ ems₀ ems₁, (rowsD ctl)[i0 ctl]? = some r₀ ∧ (rowsD ctl)[i0 ctl + 1]? = some r₁ ∧
      r₀.node = va ∧ r₀.time = 30 ∧ r₀.cut = .ac .tick Ma ems₀ ∧
      r₀.pre.ac.getConf Ma 6 = some 1 ∧ fastSelD r₀.pre.ac Ma 30 6 1 = some 1 ∧
      r₀.pre.ac.joinedB 30 = true ∧ cvD r₀.pre.ac Ma 6 1 = cvL ∧ r₁.node = va ∧
      r₁.time = 30 ∧ r₁.cut = .ac .toFG Ma ems₁ ∧ (r₁.pre.ac.toFG Ma 30).2 = some 1 := by
  obtain ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12⟩ := (checks_true ctl).1
  obtain ⟨ems₀, he₀⟩ := DataRun.tickM_some h3
  obtain ⟨ems₁, he₁⟩ := DataRun.toFGM_some h11
  have hr₀ : (rowsD ctl)[i0 ctl]? = some (rowI ctl (i0 ctl)) :=
    DataRun.rowI_eq (Nat.lt_of_succ_lt hlt)
  have hr₁ : (rowsD ctl)[i0 ctl + 1]? = some (rowI ctl (i0 ctl + 1)) := DataRun.rowI_eq hlt
  exact ⟨_, _, ems₀, ems₁, hr₀, hr₁, h1, h2, he₀, h4, h5, h6, h7, h9, h10,
    he₁, h12⟩

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
    (run_goldilocksRun ctl) hX (show va ≠ vf by decide) closedMa (t := 30) (s := 6)
    (c := 1) (b := 1) rfl h₀ h₁ hn₀ ht₀ hc₀ (by decide) (by decide) hg hf hj hcv
    hn₁ ht₁ hc₁ htf rfl
  refine ⟨hlock, hjoin, ℓ, htf, ?_⟩
  change X.sp.slot ((runD ctl).tr.time (i0 ctl + 1)) = 7
  rw [htime, Fix.slot_eq]; rfl

/-! ## `Carry` from the checks -/

/-- **`Carry_y` from the head chains**: at a vote of `y` whose counted votes `S` have heads in
`allR`, are held before `T` at the read point, and whose head chains `y` accepted before `T`. -/
theorem carryAt_mk {ctl : Bool} {y : Fin 5} (hy : y ∈ H) {i : Nat}
    {e : SA.Em X.sp (List (FG.Att X.sp.n))} (hv : SA.VoteAt (tr ctl).projAC y i e) {s T : Nat}
    (hT : X.sp.ts s + 3 * X.sp.Δ = T) (S : Set (Vote 5))
    (hj : SA.joined X.sp e.readPoint ((tr ctl).time i))
    (hS : ∀ v ∈ S, v.head ∈ allR ∧ chainAcc ctl y v.head T = true ∧
      SA.HeldBefore e.readPoint v T) :
    SA.CarryAt (tr ctl).projAC ((tr ctl).HonestBlocks H) y i e s S := by
  refine DataRun.carryAt_mk (runD ctl) (run_goldilocksRun ctl) hX frag_rows
    (fun r hr => blk_honest ctl (DataRun.mem_allR.2 hr)) hy hv hT S hj fun v hvS => ?_
  exact ⟨allR_closed.valid _ (hS v hvS).1, (hS v hvS).2⟩

theorem voteChecks_slot7 {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true) (hs : em.vote.slot = 7) :
    em.rp.joinedB r.time = true ∧ (∀ v ∈ cvL, heldD em.rp v 27 = true) ∧
      (ctl = true → ∀ v ∈ cvL, chainAcc ctl r.node v.head 27 = true) ∧ 1 ∈ em.rp.vbt M 7 := by
  simp only [voteD, hs, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1.1.1, h.1.1.2, fun hc => ?_, h.2⟩
  rcases h.1.2 with h' | h'
  · rw [hc] at h'; cases h'
  · exact h'

private theorem voteD_slot8 {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true) (hs : em.vote.slot = 8) : em.rp.joinedB r.time = true ∧
      (∀ v ∈ votesD ctl 7, v.head ∈ allR ∧ heldD em.rp v 31 = true ∧
        chainAcc ctl r.node v.head 31 = true) ∧ 1 ∈ em.rp.vbt M 8 := by
  have h87 : ((8 : Nat) = 7) = False := by decide
  simp only [voteD, hs, h87, ↓reduceIte, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.1, fun v hv => ⟨(h.1.2 v hv).1.1, (h.1.2 v hv).1.2, (h.1.2 v hv).2⟩, h.2⟩

theorem voteD_slot {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true) : em.vote.slot ≤ 8 := by
  unfold voteD at h
  split_ifs at h with h7 h8
  · omega
  · omega
  · simp only [decide_eq_true_eq] at h; omega

/-! ## The premises other than the initial `Carry` -/

/-- The honest voters of slot `σ` as a set. -/
theorem voters_eq (ctl : Bool) (σ : Nat) :
    {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt (tr ctl).projAC x' j e' ∧ e'.msg.slot = σ} =
      {x' | x' ∈ votersD ctl σ} := by
  ext y
  constructor
  · exact fun h => (DataRun.mem_votersD (runD ctl)).2 h.2
  · intro h
    obtain ⟨j, e, hv, hs⟩ := (DataRun.mem_votersD (runD ctl)).1 h
    obtain ⟨r, hr, rfl, -⟩ := voteAt_row hv
    exact ⟨row_honest hr, j, e, hv, hs⟩

/-- **`halfCommittee`**, in both variants: the honest voters of slots `7` and `8` include
`a, b, c`, and `5 ≤ 2 · 3`. -/
theorem run_halfCommittee (ctl : Bool) : ∀ s', 6 < s' → s' ≤ 8 →
    X.sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt (tr ctl).projAC x' j e' ∧
      e'.msg.slot = s'}.ncard := by
  intro s' h1 h2
  rw [voters_eq]
  have hsub : ({va, vb, vc} : Set (Fin 5)) ⊆ {x' | x' ∈ votersD ctl s'} := by
    have hL : [va, vb, vc] ⊆ votersD ctl s' := by
      rcases (show s' = 7 ∨ s' = 8 by omega) with rfl | rfl
      · exact (voters_checks ctl).1
      · exact (voters_checks ctl).2
    rintro y (rfl | rfl | rfl)
    · exact hL (by decide)
    · exact hL (by decide)
    · exact hL (by decide)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by decide), Set.ncard_pair (by decide)] at this
  change 5 ≤ _
  omega

/-- **`carryLater`**, in both variants: `Carry(7, S_7, B)` (the slot-8 voters hold the slot-7
votes stamped `29 < 31` and accepted their head chains before `31`) and, vacuously (no slot-9
vote within the horizon), `Carry(8, S_8, B)`. -/
theorem run_carryLater (ctl : Bool) : ∀ s', 6 < s' → s' ≤ 8 →
    SA.Carry (tr ctl).projAC H ((tr ctl).HonestBlocks H) s' (honestVotes (tr ctl) H s') := by
  intro s' h1 h2 y hy i e hv hs
  obtain ⟨r, hr, hn, call, M, ems, hc, em, hem, rfl, hchk, -⟩ := voteAt_row hv
  have hle := voteD_slot hchk
  change em.vote.slot = s' + 1 at hs
  obtain rfl : s' = 7 := by omega
  obtain ⟨hj, hheld, -⟩ := voteD_slot8 hchk hs
  refine carryAt_mk hy hv rfl _ (DataRun.joined_row (runD ctl) hr hj) fun v hvS => ?_
  obtain ⟨hR, hh, hacc⟩ := hheld v (DataRun.mem_votesD (runD ctl) hvS)
  exact ⟨hR, hn ▸ hacc, DataRun.heldD_spec hh⟩

theorem joinedAt_all (ctl : Bool) (y : Fin 5) (t : Time) : (tr ctl).JoinedAt y t :=
  fun k hk => absurd hk (not_restartAt ctl y k)

/-- `f < h_t` on `[0, 35]`: `a` and `b` are awake and joined. -/
theorem faultBound_at (ctl : Bool) {t : Int} (h0 : 0 ≤ t) (h35 : t ≤ 35) :
    (tr ctl).FaultBound H t := by
  have hc : Hᶜ = {vf} := by ext y; simp [H]
  have hsub : ({va, vb} : Set (Fin 5)) ⊆
      {y | y ∈ H ∧ (tr ctl).awake y t ∧ (tr ctl).JoinedAt y t} := by
    have hab : awakeB va t.toNat = true ∧ awakeB vb t.toNat = true := by
      simp only [awakeB, Bool.and_eq_true, decide_eq_true_eq]; omega
    rintro y (rfl | rfl)
    · exact ⟨show va ≠ vf by decide, ⟨h0, hab.1⟩, joinedAt_all ctl va t⟩
    · exact ⟨show vb ≠ vf by decide, ⟨h0, hab.2⟩, joinedAt_all ctl vb t⟩
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined
  rw [hc, Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair (by decide)] at this
  exact lt_of_lt_of_le one_lt_two this

/-- **`f < h_t`** at every honest vote time in `(24, 33]`, in both variants. -/
theorem run_faultBound (ctl : Bool) : ∀ y ∈ H, ∀ i e, SA.VoteAt (tr ctl).projAC y i e →
    X.sp.ts 6 < (tr ctl).time i → (tr ctl).time i ≤ X.sp.ts 8 + X.sp.Δ →
    (tr ctl).FaultBound H ((tr ctl).time i) := by
  intro y _ i e _ h1 h2
  have h1' : (24 : Int) < (tr ctl).time i := h1
  have h2' : (tr ctl).time i ≤ (33 : Int) := h2
  exact faultBound_at ctl (le_of_lt (lt_trans (by norm_num) h1')) (le_trans h2' (by norm_num))

/-- **`NoColl` over the five contents**: the blocks of the run are genesis, `B`, `V`, `Da` and
`Db`, with the distinct digests `2, 1, 3, 4, 5`, in both variants. -/
theorem run_noColl (ctl : Bool) : NoCollRun dg (tr ctl) := by
  have cls : ∀ B ∈ insert (X.sp.toParams.genesisBlock N5.genesisPayload) {B | (tr ctl).Occurs B},
      B = X.sp.toParams.genesisBlock N5.genesisPayload ∨ B = X.blk 1 ∨ B = X.blk 3 ∨
        B = X.blk 4 ∨ B = X.blk 5 := by
    rintro B (rfl | ⟨y, k, hB⟩)
    · exact Or.inl rfl
    · obtain ⟨b, hb, rfl⟩ := fgBlock_ok hB
      rw [roots_eq] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  intro B hB C hC h
  rcases cls B hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases cls C hC with rfl | rfl | rfl | rfl | rfl <;> revert h <;> decide

/-- An honest signature names genesis. -/
theorem signAt_T {ctl : Bool} {v : Fin 5} {j : Nat} {a : FG.Att X.sp.n}
    (h : (tr ctl).projFG.SignAt v j a) : a.T = 2 := by
  obtain ⟨r, hr, b, hb⟩ := DataRun.signAt_row (runD ctl) h
  have := (rowsChk_row hr).2.2
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
        have h := (rowsChk_row (List.getElem?_eq_getElem hi)).2.2
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
    · rw [hs]; exact (voteChecks_slot7 (hchk em hem) hs).2.2.2
    · rw [hs]; exact (voteD_slot8 (hchk em hem) hs).2.2

/-- **(ii) Every premise of `PersistPremises` but the initial `Carry`**, for the source of `a`
(`i₀`, slot `6`, `B`, `CV`) and the slot `m + 1 = 8`, in both variants. -/
theorem run_premisesExceptCarry (ctl : Bool) :
    PersistPremisesExceptCarry (tr ctl) H dg 1 va (i0 ctl) 6 8 Bk CV where
  writer_honest := show va ≠ vf by decide
  fastLock := (source ctl).1
  writer_joined := (source ctl).2.1
  lt := by decide
  sync := run_sync ctl
  halfCommittee := run_halfCommittee ctl
  carryLater := run_carryLater ctl
  faultBound := run_faultBound ctl
  noColl := run_noColl ctl
  clean := run_clean ctl
  stock := rfl

end Consensus.Goldilocks.Test.HalfCommittee.Heads

end
