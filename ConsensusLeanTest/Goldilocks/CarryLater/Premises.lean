module
public import ConsensusLeanTest.Goldilocks.CarryLater.Run
public import ConsensusLeanTest.Goldilocks.Runs.Data.Premises
@[expose] public section

/-! # The later-Carry run: every premise but `carryLater`

Kind (r) and (control), shared part: **premise necessity, not a counterexample**.
`RecentSourceNextVote` is proved (`recent_source_next_vote`); the witness shows that its premise
`carryLater` (`Carry(s', S_{s'}, B)` for the honest votes `S_{s'}` of every slot `s' ∈ (j, m + 1]`)
cannot be dropped. In both variants of the run of `Goldilocks/CarryLater/Run`, the writer `a`
writes at its tick of `30` (`i₀ = i0 ctl`) the fast lock of slot `j = 6` on `B` with the counted
votes `CV = {a6, b6, d6}` (heads `Y`, `Y`, `B`: each extends `B`; the confirmation is `Y`, which
fails the fast test, so the selection is `B`), and `ac_to_fg` returns `B` at the next cut
(`i₀ + 1`, slot `7 = m`). Every field of `PersistPremises … a i₀ 6 8 B CV` except `carryLater`
holds (`run_premisesExceptCarryLater`, both variants; the test-local
`PersistPremisesExceptCarryLater` copies the other fields in the order of
`Statements/Compose/Persist`, with no edit to the statement, and `persistPremises_iff_carryLater`
splits `PersistPremises` into it and `CarryLaterHolds`):
`Sync[24, 33]` (`run_sync`); the initial `Carry(6, CV, B)` (`run_carry`: the slot-7 voters `a, b,
d` accepted the head chains `Y → B → G` and `B → G` before `27` and hold `a6, b6, d6` received
before `27`; `c` restarted at `25` and is not joined in slot `7`, so the initial `Carry` says
nothing about it); `halfCommittee` (`run_halfCommittee`: the honest voters of slot `7` include
`a, b, d`, those of slot `8` include `a, b, c, d`, and `5 ≤ 2 · 3`); `f < h_t`
(`run_faultBound`: only `c` restarts, so `a, b, d` are joined at every time, `joinedAt_abd`, and
awake on `[0, 39]`); `NoColl` over the four contents of genesis, `B`, `Y`, `W` (`run_noColl`);
and `Clean` (`run_clean`): (K0) the caches are genesis at every cut, also for `c`, which sleeps
at `t_6` and holds the initial state there (`DataRun.caches_genesis`), (K1) every honest
signature names genesis, so an excluded entry, which strictly extends genesis, is named by `f`
only, (K2) `B` is in every slot-7 and slot-8 voter block tree, also in `c`'s.

The checks on data are bundled in `checks_true` (the source, the vote checks of every row, the
votes of `a` and `c` the rejection and the control name, the honest trees, the voters of slots
`7` and `8`). The vote checks of slots `8` and `9` (`voteD`) record what `carryLater` needs at
the slot-`s'+1` votes for `s' ∈ {7, 8}`: every honest slot-`s'` vote held before `t_{s'} + 3`,
and, in the control only, its head chain accepted before `t_{s'} + 3`; this fails at `c` in the
rejection run (`Goldilocks/CarryLater/Reject`).

The fixture-free row lemmas are those of `Goldilocks/Runs/Data/Premises`, so this file holds
only the fixture's checks and their reading.

Finite horizon: the run ends at `39`; slot-`9` votes exist (at `37`), so `carryLater` at
`s' = 8` is not vacuous; there is no slot-`10` vote. -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Later

open SA Compose

section Generic

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **`PersistPremises` without `carryLater`**: a test-local copy of the other fields of
`Compose.PersistPremises` (`Statements/Compose/Persist`), in its field order, with no edit to the
statement. -/
structure PersistPremisesExceptCarryLater (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
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
  /-- At least half of the committee votes honestly in every slot `s' ∈ (s, m]`. -/
  halfCommittee : ∀ s', s < s' → s' ≤ m →
    sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard
  /-- `f < h_t` at every honest vote time in `(t_s, t_m + Δ]`. -/
  faultBound : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → sp.ts s < tr.time i →
    tr.time i ≤ sp.ts m + sp.Δ → tr.FaultBound H (tr.time i)
  /-- `NoColl`. -/
  noColl : NoCollRun dg tr
  /-- `Clean(s, m, B)`. -/
  clean : Clean tr H s m B
  /-- The stock committee. -/
  stock : sp.committeeSize = sp.n

/-- The field `carryLater` of `PersistPremises`: `Carry(s', S_{s'}, B)` for the honest votes
`S_{s'}` of every slot `s' ∈ (s, m]`. -/
def CarryLaterHolds (s m : Nat) : Prop :=
  ∀ s', s < s' → s' ≤ m → SA.Carry tr.projAC H (tr.HonestBlocks H) s' (honestVotes tr H s')

variable {tr H}

/-- `PersistPremises` is the copy and `carryLater`. -/
theorem persistPremises_iff_carryLater {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} :
    PersistPremises tr H dg ΔF x i₀ s m B CV ↔
      PersistPremisesExceptCarryLater tr H dg ΔF x i₀ s m B CV ∧ CarryLaterHolds tr H s m :=
  ⟨fun p => ⟨⟨p.writer_honest, p.fastLock, p.writer_joined, p.lt, p.sync, p.carry,
      p.halfCommittee, p.faultBound, p.noColl, p.clean, p.stock⟩, p.carryLater⟩,
    fun ⟨p, h⟩ => ⟨p.writer_honest, p.fastLock, p.writer_joined, p.lt, p.sync, p.carry,
      p.halfCommittee, h, p.faultBound, p.noColl, p.clean, p.stock⟩⟩

end Generic

open Fix ScheduleRun
open Five (va vb vc vd vf H honest)

/-! ## The source and the checks on data -/

/-- The counted votes of the source, in `a`'s pool order: `a6`, `b6` (head `Y`), `d6` (head
`B`). -/
def cvL : List X.V := [vt va 6 3, vt vb 6 3, vt vd 6 1]

/-- The counted votes as a set. -/
def CV : Set (Vote 5) := {v | v ∈ cvL}

/-- The block `B`. -/
abbrev Bk : X.Blk := X.blk 1

/-- `a`'s tree at its tick of `30`: genesis, `B`, `Y`. -/
def Ma : List Nat := [3, 1, 2]

theorem closedMa : X.Closed Ma := by decide

/-- The writer's tick at `30`. -/
def i0 (ctl : Bool) : Nat := DataRun.kAt (dataD ctl) va 30

/-- Row `i`. -/
def rowI (ctl : Bool) (i : Nat) : RowD := DataRun.rowI (dataD ctl) i

/-- The source: `a`'s tick at `30` confirms `Y` in slot `6`, its fast test selects `B` counting
`cvL`, and its `ac_to_fg` at the next cut returns `B`. -/
def SourceD (ctl : Bool) : Prop :=
  i0 ctl + 1 < (rowsD ctl).length ∧ (rowI ctl (i0 ctl)).node = va ∧
    (rowI ctl (i0 ctl)).time = 30 ∧ DataRun.tickM (rowI ctl (i0 ctl)).cut = some Ma ∧
    (rowI ctl (i0 ctl)).pre.ac.getConf Ma 6 = some 3 ∧
    DataRun.fastSelD (rowI ctl (i0 ctl)).pre.ac Ma ((30 : Nat) : Int) 6 3 = some 1 ∧
    (rowI ctl (i0 ctl)).pre.ac.joinedB ((30 : Nat) : Int) = true ∧
    DataRun.cvD (rowI ctl (i0 ctl)).pre.ac Ma 6 1 = cvL ∧
    (rowI ctl (i0 ctl + 1)).node = va ∧ (rowI ctl (i0 ctl + 1)).time = 30 ∧
    DataRun.toFGM (rowI ctl (i0 ctl + 1)).cut = some Ma ∧
    ((rowI ctl (i0 ctl + 1)).pre.ac.toFG Ma ((30 : Nat) : Int)).2 = some 1

instance (ctl : Bool) : Decidable (SourceD ctl) := by unfold SourceD; infer_instance

/-- The checks at a vote of slot `7`, `8` or `9` (and no vote of a later slot). Slot `7`
(the initial `Carry`): joined, the counted votes held before `t_6 + 3 = 27` with their head
chains accepted before `27`, `B` in the voter block tree. Slot `σ + 1 ∈ {8, 9}` (`carryLater` at
`σ`): joined, every honest slot-`σ` vote with a valid head and held before `t_σ + 3`, its head
chain accepted before `t_σ + 3` in the control only (this fails at `c` in the rejection run), and,
in slot `8`, `B` in the voter block tree. -/
def voteD (ctl : Bool) (r : RowD) (M : List Nat) (em : X.EmD) : Bool :=
  if em.vote.slot = 7 then em.rp.joinedB r.time &&
    cvL.all (fun v => DataRun.heldD em.rp v 27 && DataRun.chainAcc (dataD ctl) r.node v.head 27) &&
    decide (1 ∈ em.rp.vbt M 7)
  else if em.vote.slot = 8 then em.rp.joinedB r.time &&
    (DataRun.votesD (dataD ctl) 7).all (fun v => decide (X.Valid v.head) &&
      DataRun.heldD em.rp v 31 && (!ctl || DataRun.chainAcc (dataD ctl) r.node v.head 31)) &&
    decide (1 ∈ em.rp.vbt M 8)
  else if em.vote.slot = 9 then em.rp.joinedB r.time &&
    (DataRun.votesD (dataD ctl) 8).all (fun v => decide (X.Valid v.head) &&
      DataRun.heldD em.rp v 35 && (!ctl || DataRun.chainAcc (dataD ctl) r.node v.head 35))
  else decide (em.vote.slot < 7)

/-- The checks on the rows: honest nodes, the fragment, the votes (with the frame tree of the
call the node's tree), the signatures (all name genesis). -/
def rowsChk (ctl : Bool) : Bool :=
  (rowsD ctl).all fun r => r.node != vf && decide (X.Frag r.post) &&
    (match r.cut with
      | .ac _ M ems => M == r.post.fg.tree && ems.all (voteD ctl r M)
      | .fgAttest _ (some a) => a.T == 2
      | _ => true)

/-- The head of `c`'s slot-9 vote checked: `Y` in the control (any head in the rejection run). -/
def cVote9 (ctl : Bool) (em : X.EmD) : Bool :=
  decide (em.vote.val = vc ∧ em.vote.slot = 9) && (!ctl || decide (em.vote.head = 3))

/-- **The checks on data**: the source; the rows; `a`'s votes `a7`, `a8` (head `Y`); `c`'s
slot-8 vote with head `cHead ctl` and its slot-9 vote (head `Y` in the control); every root of
the table and genesis in `a`'s final tree; the honest voters `a, b, d` of slot `7` and `a, b, c,
d` of slot `8`. -/
theorem checks_true : ∀ ctl, SourceD ctl ∧ rowsChk ctl = true ∧
    DataRun.voteAnyD (dataD ctl) va (fun em => decide (em.vote = vt va 7 3)) = true ∧
    DataRun.voteAnyD (dataD ctl) va (fun em => decide (em.vote = vt va 8 3)) = true ∧
    DataRun.voteAnyD (dataD ctl) vc (fun em => decide (em.vote = vt vc 8 (cHead ctl))) = true ∧
    DataRun.voteAnyD (dataD ctl) vc (cVote9 ctl) = true ∧
    (DataRun.allR X).all (· ∈ (DataRun.stateD (runD ctl).D va (rowsD ctl).length).fg.tree) =
      true ∧
    [va, vb, vd] ⊆ DataRun.votersD (dataD ctl) 7 ∧
    [va, vb, vc, vd] ⊆ DataRun.votersD (dataD ctl) 8 := by
  decide +kernel

/-! ## The run on data -/

theorem rowsChk_row {ctl : Bool} {r : RowD} (hr : r ∈ rowsD ctl) :
    r.node ≠ vf ∧ X.Frag r.post ∧
      (match r.cut with
        | .ac _ M ems => M == r.post.fg.tree && ems.all (voteD ctl r M)
        | .fgAttest _ (some a) => a.T == 2
        | _ => true) = true := by
  have h := List.all_eq_true.1 (checks_true ctl).2.1 r hr
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem row_honest {ctl : Bool} : ∀ r ∈ rowsD ctl, r.node ∈ H := fun _ hr => (rowsChk_row hr).1

theorem frag_rows {ctl : Bool} : ∀ r ∈ rowsD ctl, X.Frag r.post :=
  fun _ hr => (rowsChk_row hr).2.1

theorem acRow_chk {ctl : Bool} {r : RowD} (hr : r ∈ rowsD ctl) {call : CallD X} {M : List Nat}
    {ems : List X.EmD} (hc : r.cut = .ac call M ems) :
    M = r.post.fg.tree ∧ ∀ em ∈ ems, voteD ctl r M em = true := by
  have h := (rowsChk_row hr).2.2
  rw [hc] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h

theorem sign_G {ctl : Bool} :
    ∀ r ∈ rowsD ctl, ∀ b a, r.cut = .fgAttest b (some a) → a.T = X.g := by
  intro r hr b a hc
  have h := (rowsChk_row hr).2.2
  rw [hc] at h
  simpa using h

/-- A vote of the projection is an emission of an AC row, with its checks. -/
theorem voteAt_chk {ctl : Bool} {y : Fin 5} {i : Nat} {e : SA.Em X.sp (List (FG.Att X.sp.n))}
    (h : SA.VoteAt (tr ctl).projAC y i e) :
    ∃ r, (rowsD ctl)[i]? = some r ∧ r.node = y ∧ ∃ call M ems, r.cut = .ac call M ems ∧
      ∃ em ∈ ems, e = em.interp ∧ voteD ctl r M em = true := by
  obtain ⟨r, hr, hn, call, M, ems, hc, em, hem, rfl⟩ := DataRun.voteAt_row (runD ctl) h
  exact ⟨r, hr, hn, call, M, ems, hc, em, hem, rfl,
    (acRow_chk (List.mem_of_getElem? hr) hc).2 em hem⟩

/-! ## The honest blocks -/

/-- Every root of the table, and genesis, is an honest block: all are in `a`'s final tree. -/
theorem valid_honest (ctl : Bool) : ∀ r, X.Valid r → X.blk r ∈ (tr ctl).HonestBlocks H := by
  intro r hr
  have h := List.all_eq_true.1 (checks_true ctl).2.2.2.2.2.2.1 r (DataRun.mem_allR.2 hr)
  exact DataRun.blk_honest (runD ctl) frag_rows (show va ≠ vf by decide) (of_decide_eq_true h)

theorem gBlk_anc_Bk (ctl : Bool) : Anc ((tr ctl).HonestBlocks H) X.gBlk Bk :=
  blk_g hX ▸ DataRun.anc_of_chain hX (valid_honest ctl) (Or.inr (by decide)) (by decide)

/-! ## The source -/

/-- **The source**: `a` writes the fast lock of slot `6` on `B` with the counted votes `CV` at
its tick of `30` (`i₀ = i0 ctl`), joined, and `ac_to_fg` returns `B` at the next cut, in slot
`7`. -/
theorem source (ctl : Bool) :
    StoredFastLockAt (tr ctl) va (i0 ctl) 6 Bk CV ∧
      SA.joined X.sp ((tr ctl).state va (i0 ctl)).ac ((tr ctl).time (i0 ctl)) ∧
      ∃ ℓ, SA.ToFGAt (tr ctl).projAC va (i0 ctl + 1) ℓ Bk ∧
        X.sp.slot ((tr ctl).time (i0 ctl + 1)) = 7 := by
  obtain ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12⟩ := (checks_true ctl).1
  have h₀ : (rowsD ctl)[i0 ctl]? = some (rowI ctl (i0 ctl)) :=
    DataRun.rowI_eq (Nat.lt_of_succ_lt hlt)
  have h₁ : (rowsD ctl)[i0 ctl + 1]? = some (rowI ctl (i0 ctl + 1)) := DataRun.rowI_eq hlt
  generalize rowI ctl (i0 ctl) = r₀ at h₀ h1 h2 h3 h4 h5 h6 h7
  generalize rowI ctl (i0 ctl + 1) = r₁ at h₁ h9 h10 h11 h12
  obtain ⟨ems₀, he₀⟩ := DataRun.tickM_some h3
  obtain ⟨ems₁, he₁⟩ := DataRun.toFGM_some h11
  obtain ⟨hf, hj, ⟨ℓ, htf⟩, hT⟩ := DataRun.source_mk (runD ctl) (run_goldilocksRun ctl) hX
    (show va ≠ vf by decide) closedMa (t := 30) (s := 6) (c := 3) (b := 1) rfl h₀ h₁ h1 h2 he₀
    (by decide) (by decide) h4 h5 h6 h7 h9 h10 he₁ h12 rfl
  refine ⟨hf, hj, ℓ, htf, ?_⟩
  change X.sp.slot ((runD ctl).tr.time (i0 ctl + 1)) = 7
  rw [hT, Fix.slot_eq]; rfl

/-! ## The vote checks -/

theorem voteD_slot7 {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true) (hs : em.vote.slot = 7) :
    em.rp.joinedB r.time = true ∧
      (∀ v ∈ cvL, DataRun.heldD em.rp v 27 = true ∧
        DataRun.chainAcc (dataD ctl) r.node v.head 27 = true) ∧ 1 ∈ em.rp.vbt M 7 := by
  simp only [voteD, hs, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem voteD_slot8 {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true) (hs : em.vote.slot = 8) : em.rp.joinedB r.time = true ∧
      (∀ v ∈ DataRun.votesD (dataD ctl) 7, X.Valid v.head ∧ DataRun.heldD em.rp v 31 = true ∧
        (ctl = true → DataRun.chainAcc (dataD ctl) r.node v.head 31 = true)) ∧
      1 ∈ em.rp.vbt M 8 := by
  have h87 : ((8 : Nat) = 7) = False := by decide
  simp only [voteD, hs, h87, ↓reduceIte, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1.1, fun v hv => ⟨(h.1.2 v hv).1.1, (h.1.2 v hv).1.2, fun hc => ?_⟩, h.2⟩
  rcases (h.1.2 v hv).2 with h' | h'
  · rw [hc] at h'; cases h'
  · exact h'

theorem voteD_slot9 {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true) (hs : em.vote.slot = 9) : em.rp.joinedB r.time = true ∧
      (∀ v ∈ DataRun.votesD (dataD ctl) 8, X.Valid v.head ∧ DataRun.heldD em.rp v 35 = true ∧
        (ctl = true → DataRun.chainAcc (dataD ctl) r.node v.head 35 = true)) := by
  have h97 : ((9 : Nat) = 7) = False := by decide
  have h98 : ((9 : Nat) = 8) = False := by decide
  simp only [voteD, hs, h97, h98, ↓reduceIte, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1, fun v hv => ⟨(h.2 v hv).1.1, (h.2 v hv).1.2, fun hc => ?_⟩⟩
  rcases (h.2 v hv).2 with h' | h'
  · rw [hc] at h'; cases h'
  · exact h'

theorem voteD_slot {ctl : Bool} {r : RowD} {M : List Nat} {em : X.EmD}
    (h : voteD ctl r M em = true) : em.vote.slot ≤ 9 := by
  unfold voteD at h
  split_ifs at h with h7 h8 h9
  · omega
  · omega
  · omega
  · simp only [decide_eq_true_eq] at h; omega

/-- **`Carry(σ, S_σ, B)` from the slot-`(σ+1)` checks** for `σ ∈ {7, 8}` in the control: the
voters hold every honest slot-`σ` vote and accepted its head chain before `t_σ + 3`. -/
theorem carry_of_checks {ctl : Bool} (hc : ctl = true) {σ : Nat} (hσ : σ = 7 ∨ σ = 8) :
    SA.Carry (tr ctl).projAC H ((tr ctl).HonestBlocks H) σ (honestVotes (tr ctl) H σ) := by
  intro y hy i e hv hs
  obtain ⟨r, hr, hn, call, M, ems, hcut, em, hem, rfl, hchk⟩ := voteAt_chk hv
  change em.vote.slot = σ + 1 at hs
  have hS : ∀ T : Nat, X.sp.ts σ + 3 * X.sp.Δ = T →
      (∀ v ∈ DataRun.votesD (dataD ctl) σ, X.Valid v.head ∧ DataRun.heldD em.rp v T = true ∧
        (ctl = true → DataRun.chainAcc (dataD ctl) r.node v.head T = true)) →
      SA.CarryAt (tr ctl).projAC ((tr ctl).HonestBlocks H) y i em.interp σ
        (honestVotes (tr ctl) H σ) := fun T hT hall => by
    have hj : em.rp.joinedB r.time = true := by
      rcases hσ with rfl | rfl
      · exact (voteD_slot8 hchk hs).1
      · exact (voteD_slot9 hchk hs).1
    refine DataRun.carryAt_mk (runD ctl) (run_goldilocksRun ctl) hX frag_rows
      (valid_honest ctl) hy hv hT _ (DataRun.joined_row (runD ctl) hr hj) fun v hvS => ?_
    obtain ⟨hR, hh, hacc⟩ := hall v (DataRun.mem_votesD (runD ctl) hvS)
    exact ⟨hR, hn ▸ hacc hc, DataRun.heldD_spec hh⟩
  rcases hσ with rfl | rfl
  · exact hS 31 rfl (voteD_slot8 hchk hs).2.1
  · exact hS 35 rfl (voteD_slot9 hchk hs).2

/-! ## The premises other than `carryLater` -/

/-- **The initial `Carry(6, CV, B)`**, in both variants: the slot-7 voters `a, b, d` accepted the
head chains `Y → B → G` and `B → G` before `27` and hold `a6, b6, d6` received before `27`. -/
theorem run_carry (ctl : Bool) :
    SA.Carry (tr ctl).projAC H ((tr ctl).HonestBlocks H) 6 CV := by
  intro y hy i e hv hs
  obtain ⟨r, hr, hn, call, M, ems, hc, em, hem, rfl, hchk⟩ := voteAt_chk hv
  obtain ⟨hj, hcv, -⟩ := voteD_slot7 hchk hs
  refine DataRun.carryAt_mk (runD ctl) (run_goldilocksRun ctl) hX frag_rows (valid_honest ctl) hy
    hv rfl CV (DataRun.joined_row (runD ctl) hr hj) fun v hvS => ?_
  have hR : ∀ v ∈ cvL, X.Valid v.head := by decide
  exact ⟨hR v hvS, hn ▸ (hcv v hvS).2, DataRun.heldD_spec (hcv v hvS).1⟩

/-- **`halfCommittee`**, in both variants: the honest voters of slot `7` include `a, b, d`, those
of slot `8` include `a, b, c, d`, and `5 ≤ 2 · 3`. -/
theorem run_halfCommittee (ctl : Bool) : ∀ s', 6 < s' → s' ≤ 8 →
    X.sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt (tr ctl).projAC x' j e' ∧
      e'.msg.slot = s'}.ncard := by
  intro s' h1 h2
  have h8 : [va, vb, vd] ⊆ [va, vb, vc, vd] := by decide
  have hL : [va, vb, vd] ⊆ DataRun.votersD (dataD ctl) s' := by
    rcases (show s' = 7 ∨ s' = 8 by omega) with rfl | rfl
    · exact (checks_true ctl).2.2.2.2.2.2.2.1
    · exact fun y hy => (checks_true ctl).2.2.2.2.2.2.2.2 (h8 hy)
  have : 3 ≤ {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt (tr ctl).projAC x' j e' ∧
      e'.msg.slot = s'}.ncard := DataRun.le_ncard_voters (runD ctl) row_honest hL (by decide)
  change 5 ≤ _
  omega

/-- **Restart-aware `JoinedAt`**: only `c` restarts (at `25`), so `a, b, d` are joined at every
time. -/
theorem joinedAt_abd (ctl : Bool) {y : Fin 5} (hy : y ≠ vc) (t : Time) : (tr ctl).JoinedAt y t :=
  DataRun.joinedAt_of (runD ctl) (List.all_eq_true.2 fun r hr => by
    have h := List.all_eq_true.1 (rows_restart_c ctl) r hr
    by_cases hn : r.node = y
    · subst hn
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at h ⊢
      rcases h with h | h
      · exact Or.inr h
      · exact absurd h.1 hy
    · simp [hn]) t

/-- `f < h_t` on `[0, 39]`: `a, b, d` are awake and joined (`joinedAt_abd`). -/
theorem faultBound_at (ctl : Bool) {t : Int} (h0 : 0 ≤ t) (h39 : t ≤ 39) :
    (tr ctl).FaultBound H t := by
  have hc : Hᶜ = {vf} := by ext y; simp [H]
  have hn : t.toNat ≤ 39 := by omega
  refine DataRun.faultBound_of (runD ctl) (L := [va, vb, vd]) (by decide) (fun y hy => ?_)
    (by rw [hc, Set.ncard_singleton]; decide)
  have hmem : y = va ∨ y = vb ∨ y = vd := by simpa using hy
  have haw : awakeB y t.toNat = true := by
    rcases hmem with rfl | rfl | rfl <;> simp [awakeB, hn]
  refine ⟨?_, ⟨h0, haw⟩, joinedAt_abd ctl ?_ t⟩ <;> rcases hmem with rfl | rfl | rfl <;>
    first | exact (show _ ≠ vf by decide) | decide

/-- **`f < h_t`** at every honest vote time in `(24, 33]`, in both variants. -/
theorem run_faultBound (ctl : Bool) : ∀ y ∈ H, ∀ i e, SA.VoteAt (tr ctl).projAC y i e →
    X.sp.ts 6 < (tr ctl).time i → (tr ctl).time i ≤ X.sp.ts 8 + X.sp.Δ →
    (tr ctl).FaultBound H ((tr ctl).time i) := by
  intro y _ i e _ h1 h2
  have h1' : (24 : Int) < (tr ctl).time i := h1
  have h2' : (tr ctl).time i ≤ (33 : Int) := h2
  exact faultBound_at ctl (le_of_lt (lt_trans (by norm_num) h1')) (le_trans h2' (by norm_num))

/-- **`NoColl` over the four contents**: the blocks of the run are genesis, `B`, `Y` and `W`,
with the distinct digests `2, 1, 3, 4`, in both variants. -/
theorem run_noColl (ctl : Bool) : NoCollRun dg (tr ctl) := by
  have cls : ∀ B ∈ insert (X.sp.toParams.genesisBlock N5.genesisPayload) {B | (tr ctl).Occurs B},
      B = X.sp.toParams.genesisBlock N5.genesisPayload ∨ B = X.blk 1 ∨ B = X.blk 3 ∨
        B = X.blk 4 := by
    rintro B (rfl | ⟨y, k, hB⟩)
    · exact Or.inl rfl
    · obtain ⟨b, hb, rfl⟩ := DataRun.fgBlock_ok (runD ctl) (rowLaws ctl) hB
      rw [roots_eq] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  intro B hB C hC h
  rcases cls B hB with rfl | rfl | rfl | rfl <;>
    rcases cls C hC with rfl | rfl | rfl | rfl <;> revert h <;> decide

/-- **`Clean(6, 8, B)`**, in both variants: (K0) the caches are genesis at every cut, also for
`c` (asleep at `t_6`, in its initial state); (K1) every honest signature names genesis, so the
namers of an excluded entry are `f` only (`1 < 4`); (K2) `B` is in every slot-7 and slot-8 voter
block tree. -/
theorem run_clean (ctl : Bool) : Clean (tr ctl) H 6 8 Bk where
  caches := DataRun.clean_caches (runD ctl) (gBlk_anc_Bk ctl)
  fgAttCut E' hE' := by
    have hsub : Store.namers X.sp.toParams (Payload X.sp.n) H (tr ctl).projFG
        (X.sp.ts (6 + 1 : Nat) + X.sp.Δ) E' ⊆ Hᶜ :=
      DataRun.namers_sub (runD ctl) hX frag_rows sign_G E' hE'
    have hc : Hᶜ = {vf} := by ext y; simp [H]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hc, Set.ncard_singleton] at this
    change _ < 4
    omega
  heightLead := DataRun.heightLead_mk (runD ctl) hX fun i r call M ems em hr hc hem h1 h2 => by
    have hm := List.mem_of_getElem? hr
    obtain ⟨hM, hchk⟩ := acRow_chk hm hc
    refine ⟨hM ▸ (frag_rows r hm).1, ?_⟩
    rcases (show em.vote.slot = 7 ∨ em.vote.slot = 8 by omega) with hs | hs
    · rw [hs]; exact (voteD_slot7 (hchk em hem) hs).2.2
    · rw [hs]; exact (voteD_slot8 (hchk em hem) hs).2.2

/-- **(ii) Every premise of `PersistPremises` but `carryLater`**, for the source of `a` (`i₀`,
slot `6`, `B`, `CV`) and the slot `m + 1 = 8`, in both variants. -/
theorem run_premisesExceptCarryLater (ctl : Bool) :
    PersistPremisesExceptCarryLater (tr ctl) H dg 1 va (i0 ctl) 6 8 Bk CV where
  writer_honest := show va ≠ vf by decide
  fastLock := (source ctl).1
  writer_joined := (source ctl).2.1
  lt := by decide
  sync := run_sync ctl
  carry := run_carry ctl
  halfCommittee := run_halfCommittee ctl
  faultBound := run_faultBound ctl
  noColl := run_noColl ctl
  clean := run_clean ctl
  stock := rfl

end Consensus.Goldilocks.Test.HalfCommittee.Later

end
