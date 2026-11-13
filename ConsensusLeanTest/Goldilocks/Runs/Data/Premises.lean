module
public import ConsensusLeanTest.Goldilocks.Runs.Data.Sync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
@[expose] public section

/-! # A run on data: the premises of `RecentSourceNextVote` from checks on the rows

Fixture-free lemmas over a run on data `R : DataRun.Run X` (`Goldilocks/Runs/Data/Run`) that turn
kernel checks on the rows `rowsD R.D` into the premises of `PersistPremises`
(`Statements/Compose/Persist`) and into the events a premise-necessity witness names:

* **Rows and calls**: an AC call, a vote, an acceptance or a signature of the projections is a
  row of the run (`acRow`, `voteAt_row`, `acceptAt_row`, `signAt_row`), and back (`acRow_of`,
  `voteAt_of`, `voteAny_spec`); the AC state at a row is the row's (`acState`); a node without
  an `ac_on_block` cut of a root never accepts it (`not_accepted`).
* **Honest blocks**: with the fragment at every row (`X.Frag r.post`), the honest blocks are
  table blocks (`honest_sub`), their ancestry is the table's (`anc_chain`, `anc_of_chain`), and
  vote extension follows the head chain (`extends_of_chain`, `not_extends`).
* **The source**: the fast lock written by a tick row and the `ac_to_fg` return of the next row
  (`source_mk`, from `fastSelect_eq` and `fastCounted_eq`).
* **`Carry`**: from accepted head chains (`chainAcc`, `accR_spec`) and held votes (`heldD_spec`),
  `carryAt_mk`; the honest votes and voters of a slot are those of the rows (`mem_votesD`,
  `mem_votersD`, `le_ncard_voters`).
* **The other premises**: `JoinedAt` of a node without restart (`joinedAt_of`), `f < h_t` from a
  list of awake joined honest nodes (`faultBound_of`), and the parts of `Clean`: (K0) the
  mirror's caches are genesis at every cut (`caches_genesis`, `clean_caches`), (K1) the namers
  of an excluded entry when every honest signature names genesis (`namers_sub`), (K2) the
  voter block trees from the rows (`heightLead_mk`).

The lemmas generalize the fixture-bound helpers of `Goldilocks/InitialCarry/Premises` and
`Goldilocks/InitialCarry/Reject` (over head chains, as there) to every run on data, so a further
premise-necessity witness on the core states only its fixture and its kernel checks. -/

namespace Consensus.Goldilocks.Test.HalfCommittee.DataRun

open SA Fix ScheduleRun Compose

variable {X : Fix}

/-! ## Checks on data -/

/-- The roots of the table with genesis. -/
def allR (X : Fix) : List Nat := X.g :: X.roots

theorem allR_closed (hX : X.OK) : X.Closed (allR X) where
  g_mem := List.mem_cons_self
  valid r hr := by
    rcases List.mem_cons.1 hr with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h
  par_mem r hr hg := by
    rcases List.mem_cons.1 hr with rfl | h
    · exact absurd rfl hg
    · rcases valid_par hX h with h' | h'
      · rw [h']; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h'

theorem mem_allR {r : Nat} : r ∈ allR X ↔ X.Valid r := List.mem_cons

/-- The first cut of `y` at `t`. -/
def kAt (D : Data X) (y : Fin X.sp.n) (t : Nat) : Nat :=
  (rowsD D).findIdx fun r => r.node == y && r.time == t

/-- A placeholder row. -/
def row0 (X : Fix) : RowD X :=
  ⟨0, 0, X.f, 0, .fgAtt (attG (X := X) X.f), NodeD.init X, NodeD.init X⟩

/-- Row `i`. -/
def rowI (D : Data X) (i : Nat) : RowD X := (rowsD D).getD i (row0 X)

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

/-- An `ac_on_block` cut of the root `b`. -/
def blockIs (b : Nat) : CutD X → Bool
  | .ac (.block b') _ _ => b' == b
  | _ => false

/-- `y` accepted the root `b` (an `ac_on_block` cut) before `T`, or `b` is genesis. -/
def accR (D : Data X) (y : Fin X.sp.n) (b T : Nat) : Bool :=
  b == X.g || (rowsD D).any fun r => r.node == y && decide (r.time < T) && blockIs b r.cut

/-- `y` accepted the chain of the root `h` (`h` and its ancestors) before `T`. -/
def chainAcc (D : Data X) (y : Fin X.sp.n) (h T : Nat) : Bool :=
  (X.chain h).all fun b => accR D y b T

/-- No `ac_on_block` cut of `y` names a block with root `h`. -/
def noAccD (y : Fin X.sp.n) (h : Nat) (r : RowD X) : Bool :=
  r.node != y || match r.cut with
    | .ac (.block b) _ _ => (X.blk b).root != h
    | _ => true

/-- The honest votes of slot `σ`. -/
def votesD (D : Data X) (σ : Nat) : List X.V :=
  (rowsD D).flatMap fun r => ((emsD r.cut).map EmD.vote).filter (·.slot == σ)

/-- The honest voters of slot `σ`. -/
def votersD (D : Data X) (σ : Nat) : List (Fin X.sp.n) :=
  (rowsD D).filterMap fun r =>
    if (emsD r.cut).any (fun em => em.vote.slot == σ) then some r.node else none

/-- The read point `rp` holds `v`, received before `T`. -/
def heldD (rp : X.ACD) (v : X.V) (T : Int) : Bool :=
  (rp.pool v.slot).contains v && decide (rp.stampV v < ETime.of T)

/-- A row of `y` emits a vote whose emission satisfies `P`. -/
def voteAnyD (D : Data X) (y : Fin X.sp.n) (P : X.EmD → Bool) : Bool :=
  (rowsD D).any fun r => r.node == y && (emsD r.cut).any P

theorem rowI_eq {D : Data X} {i : Nat} (h : i < (rowsD D).length) :
    (rowsD D)[i]? = some (rowI D i) := by
  rw [rowI, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem emsD_mem {c : CutD X} {em : X.EmD} (h : em ∈ emsD c) :
    ∃ call M ems, c = .ac call M ems ∧ em ∈ ems := by
  cases c <;> simp_all [emsD]

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

theorem blockIs_true {c : CutD X} {b : Nat} (h : blockIs b c = true) :
    ∃ M ems, c = .ac (.block b) M ems := by
  cases c with
  | ac call M ems => cases call <;> simp_all [blockIs]
  | _ => simp [blockIs] at h

theorem heldD_spec {rp : X.ACD} {v : X.V} {T : Int} (h : heldD rp v T = true) :
    SA.HeldBefore rp.interp v T := by
  simp only [heldD, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  exact h

/-! ## Rows and calls -/

variable {H : Set (Fin X.sp.n)}

theorem projAC_call (R : Run X) {y : Fin X.sp.n} {i : Nat} {ℓ : ACLabel (X.AC R.ro)}
    (h : R.tr.projAC.CallAt y i ℓ) : R.tr.CallAt y i (.ac ℓ) := by
  obtain ⟨hn, hl⟩ := h
  refine ⟨hn, ?_⟩
  change (R.tr.label i).bind RunTrace.acLabel = some ℓ at hl
  cases hc : R.tr.label i with
  | none => rw [hc] at hl; cases hl
  | some c => rw [hc] at hl; cases c <;> simp [RunTrace.acLabel] at hl; rw [hl]

theorem projAC_call_of (R : Run X) {y : Fin X.sp.n} {i : Nat} {ℓ : ACLabel (X.AC R.ro)}
    (h : R.tr.CallAt y i (.ac ℓ)) : R.tr.projAC.CallAt y i ℓ :=
  ⟨h.1, by change (R.tr.label i).bind RunTrace.acLabel = _; rw [h.2]; rfl⟩

/-- An AC call of the projection is an AC row. -/
theorem acRow (R : Run X) {y : Fin X.sp.n} {i : Nat} {ℓ : ACLabel (X.AC R.ro)}
    (h : R.tr.projAC.CallAt y i ℓ) :
    ∃ r, (rowsD R.D)[i]? = some r ∧ r.node = y ∧ ∃ call M ems, r.cut = .ac call M ems ∧
      ℓ = ⟨call.interp R.ro, X.frameOf M, ems.map EmD.interp⟩ := by
  have hc := projAC_call R h
  obtain ⟨r, hr, hcut⟩ := label_row R hc.2
  exact ⟨r, hr, (trace_row R hr).1 ▸ hc.1, cut_ac hcut⟩

/-- An AC row is an AC call of the projection. -/
theorem acRow_of (R : Run X) {i : Nat} {r : RowD X} (hr : (rowsD R.D)[i]? = some r)
    {call : CallD X} {M : List Nat} {ems : List X.EmD} (hc : r.cut = .ac call M ems) :
    R.tr.projAC.CallAt r.node i ⟨call.interp R.ro, X.frameOf M, ems.map EmD.interp⟩ := by
  have h := callAt_row R hr
  rw [hc] at h
  exact projAC_call_of R h

/-- The AC state of an honest node at its row is the row's. -/
theorem acState (R : Run X) (hrun : GoldilocksRun R.proposer R.dg H R.tr) {i : Nat}
    {r : RowD X} (hr : (rowsD R.D)[i]? = some r) (hy : r.node ∈ H) :
    R.tr.projAC.state r.node i = r.pre.ac.interp := by
  rw [projAC_state hrun.toLocalRun hy, (trace_row R hr).2.2.2.2]; rfl

/-- A vote of the projection is an emission of an AC row. -/
theorem voteAt_row (R : Run X) {y : Fin X.sp.n} {i : Nat}
    {e : SA.Em X.sp (List (FG.Att X.sp.n))} (h : SA.VoteAt R.tr.projAC y i e) :
    ∃ r, (rowsD R.D)[i]? = some r ∧ r.node = y ∧ ∃ call M ems, r.cut = .ac call M ems ∧
      ∃ em ∈ ems, e = em.interp := by
  obtain ⟨ℓ, hc, he⟩ := h
  obtain ⟨r, hr, hn, call, M, ems, hcut, rfl⟩ := acRow R hc
  obtain ⟨em, hem, rfl⟩ := List.mem_map.1 he
  exact ⟨r, hr, hn, call, M, ems, hcut, em, hem, rfl⟩

/-- An emission of an AC row is a vote of the projection. -/
theorem voteAt_of (R : Run X) {i : Nat} {r : RowD X} (hr : (rowsD R.D)[i]? = some r)
    {call : CallD X} {M : List Nat} {ems : List X.EmD} (hc : r.cut = .ac call M ems)
    {em : X.EmD} (hem : em ∈ ems) : SA.VoteAt R.tr.projAC r.node i em.interp :=
  ⟨_, acRow_of R hr hc, List.mem_map_of_mem hem⟩

/-- A vote of `y` on data is a vote of the projection. -/
theorem voteAny_spec (R : Run X) {y : Fin X.sp.n} {P : X.EmD → Bool}
    (h : voteAnyD R.D y P = true) :
    ∃ k em, SA.VoteAt R.tr.projAC y k em.interp ∧ P em = true := by
  obtain ⟨r, hm, hr⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hr
  obtain ⟨rfl, em, hem, hP⟩ := hr
  obtain ⟨call, M, ems, hc, hem'⟩ := emsD_mem hem
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  exact ⟨k, em, voteAt_of R (List.getElem?_eq_getElem hk) hc hem', hP⟩

/-- **An acceptance of the AC projection is an `ac_on_block` row.** -/
theorem acceptAt_row (R : Run X) {y : Fin X.sp.n} {k : Nat} {B : X.Blk}
    (h : R.tr.projAC.AcceptAt y k B) :
    ∃ r, (rowsD R.D)[k]? = some r ∧ r.node = y ∧
      ∃ b M ems, r.cut = .ac (.block b) M ems ∧ B = X.blk b := by
  obtain ⟨ℓ, hc, hcall⟩ := h
  obtain ⟨r, hr, hn, call, M, ems, hcut, rfl⟩ := acRow R hc
  refine ⟨r, hr, hn, ?_⟩
  cases call with
  | block b =>
    exact ⟨b, M, ems, hcut, by simpa [CallD.interp] using hcall.symm⟩
  | _ => simp [CallD.interp] at hcall

/-- A node without an `ac_on_block` cut of a block with the non-genesis root `h` never accepts
the block `h`. -/
theorem not_accepted (R : Run X) {y : Fin X.sp.n} {h : Nat} (hh : X.Valid h) (hg : h ≠ X.g)
    (hno : (rowsD R.D).all (noAccD y h) = true) (T : Time) :
    ¬ AcceptedBefore R.tr.projAC y (X.blk h) T := by
  rintro (hgr | ⟨k, hk, -⟩)
  · exact hg (by rw [← blk_root hh]; exact hgr)
  · obtain ⟨r, hr, hn, b, M, ems, hcut, hb⟩ := acceptAt_row R hk
    have := List.all_eq_true.1 hno r (List.mem_of_getElem? hr)
    simp only [noAccD, hn, bne_self_eq_false, Bool.false_or, hcut, ← hb, blk_root hh,
      bne_self_eq_false] at this
    cases this

/-- An accepted root on data is an `AcceptedBefore` of the projection. -/
theorem accR_spec (R : Run X) {y : Fin X.sp.n} {b T : Nat} (hb : X.Valid b)
    (h : accR R.D y b T = true) : AcceptedBefore R.tr.projAC y (X.blk b) T := by
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact Or.inl (by rw [blk_root hb]; exact beq_iff_eq.1 h)
  obtain ⟨r, hm, hr⟩ := List.any_eq_true.1 h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  have hrk := List.getElem?_eq_getElem hk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
  obtain ⟨⟨hn, ht⟩, hbl⟩ := hr
  obtain ⟨M, ems, hc⟩ := blockIs_true hbl
  refine Or.inr ⟨k, ⟨_, hn ▸ acRow_of R hrk hc, rfl⟩, ?_⟩
  change R.tr.time k < (T : Int)
  rw [rowsD_time R hrk]; exact_mod_cast ht

/-- A signature of the FG projection is an `fg_attest` row. -/
theorem signAt_row (R : Run X) {v : Fin X.sp.n} {j : Nat} {a : FG.Att X.sp.n}
    (h : R.tr.projFG.SignAt v j a) :
    ∃ r, (rowsD R.D)[j]? = some r ∧ ∃ b, r.cut = .fgAttest b (some a) := by
  obtain ⟨src, hn, hl⟩ := h
  have hl' : R.tr.label j = some (.fg (.attest src (some a))) := by
    change (R.tr.label j).bind RunTrace.fgLabel = _ at hl
    cases hc : R.tr.label j with
    | none => rw [hc] at hl; cases hl
    | some c => rw [hc] at hl; cases c <;> simp [RunTrace.fgLabel] at hl; rw [hl]
  obtain ⟨r, hr, hcut⟩ := label_row R hl'
  refine ⟨r, hr, ?_⟩
  cases hc : r.cut <;> rw [hc] at hcut <;> simp_all [CutD.interp]

theorem joined_row (R : Run X) {i : Nat} {r : RowD X} (hr : (rowsD R.D)[i]? = some r)
    {em : X.EmD} (hj : em.rp.joinedB r.time = true) :
    SA.joined X.sp em.interp.readPoint (R.tr.time i) := by
  rw [rowsD_time R hr]; exact (joined_interp _ _).2 hj

/-! ## Honest blocks -/

theorem frag_fold (y : Fin X.sp.n) :
    ∀ (L : List (RowD X)), (∀ r ∈ L, X.Frag r.post) → ∀ d, X.Frag d →
      X.Frag (L.foldl (fun d r => if r.node = y then r.post else d) d)
  | [], _, _, hd => hd
  | r :: L, hL, d, hd => by
    simp only [List.foldl_cons]
    refine frag_fold y L (fun r' h => hL r' (List.mem_cons_of_mem _ h)) _ ?_
    split_ifs
    · exact hL r List.mem_cons_self
    · exact hd

theorem frag_stateD {D : Data X} (hF : ∀ r ∈ rowsD D, X.Frag r.post) (y : Fin X.sp.n)
    (c : Nat) : X.Frag (stateD D y c) :=
  frag_fold y _ (fun r hr => hF r (List.mem_of_mem_take hr)) _ (frag_init X)

theorem trace_tree (R : Run X) (hF : ∀ r ∈ rowsD R.D, X.Frag r.post) (y : Fin X.sp.n)
    (c : Nat) : (R.tr.state y c).fg.tree = X.T (stateD R.D y c).fg.tree := by
  rw [trace_state]; exact tree_interp (frag_stateD hF y c).1

/-- The honest blocks are blocks of the table or genesis. -/
theorem honest_sub (R : Run X) (hF : ∀ r ∈ rowsD R.D, X.Frag r.post) {B : X.Blk}
    (hB : B ∈ R.tr.HonestBlocks H) : ∃ r ∈ allR X, B = X.blk r := by
  obtain ⟨y, -, i, hB⟩ := hB
  rw [trace_tree R hF] at hB
  obtain ⟨r, hr, rfl⟩ := hB
  exact ⟨r, mem_allR.2 ((frag_stateD hF y i).1.valid r hr), rfl⟩

theorem anc_honest (R : Run X) (hF : ∀ r ∈ rowsD R.D, X.Frag r.post) {A C : X.Blk}
    (h : Anc (R.tr.HonestBlocks H) A C) : Anc (X.T (allR X)) A C := by
  induction h with
  | refl => exact .refl
  | tail _ hp ih => exact ih.tail ⟨honest_sub R hF hp.1, honest_sub R hF hp.2.1, hp.2.2⟩

/-- A block in the tree of an honest node is an honest block. -/
theorem blk_honest (R : Run X) (hF : ∀ r ∈ rowsD R.D, X.Frag r.post) {y : Fin X.sp.n}
    (hy : y ∈ H) {c r : Nat} (hr : r ∈ (stateD R.D y c).fg.tree) :
    X.blk r ∈ R.tr.HonestBlocks H :=
  ⟨y, hy, c, by rw [trace_tree R hF]; exact blk_mem_T hr⟩

/-- **Multi-level ancestry**: the ancestors of a valid root inside the honest blocks are blocks
of its chain. -/
theorem anc_chain (R : Run X) (hX : X.OK) (hF : ∀ r ∈ rowsD R.D, X.Frag r.post) {h : Nat}
    (hh : X.Valid h) {A : X.Blk} (hA : Anc (R.tr.HonestBlocks H) A (X.blk h)) :
    ∃ a ∈ X.chain h, A = X.blk a :=
  (anc_T hX (allR_closed hX) (mem_allR.2 hh)).1 (anc_honest R hF hA)

/-- Ancestry inside the table blocks is ancestry inside any set holding every valid root. -/
theorem anc_allR_sub {U : Set X.Blk} (hU : ∀ r, X.Valid r → X.blk r ∈ U) {A C : X.Blk}
    (h : Anc (X.T (allR X)) A C) : Anc U A C := by
  induction h with
  | refl => exact .refl
  | tail _ hp ih =>
    obtain ⟨⟨r, hr, rfl⟩, ⟨r', hr', rfl⟩, hpar⟩ := hp
    exact ih.tail ⟨hU r (mem_allR.1 hr), hU r' (mem_allR.1 hr'), hpar⟩

/-- When every valid root is an honest block, the chain of a root is its ancestry inside the
honest blocks. -/
theorem anc_of_chain (hX : X.OK) {U : Set X.Blk} (hU : ∀ r, X.Valid r → X.blk r ∈ U) {a h : Nat}
    (hh : X.Valid h) (ha : a ∈ X.chain h) : Anc U (X.blk a) (X.blk h) :=
  anc_allR_sub hU
    ((anc_T_blk hX (allR_closed hX) (chain_valid hX hh a ha) (mem_allR.2 hh)).2 ha)

/-- A vote whose head chain holds `b` extends `b`, when every valid root is an honest block. -/
theorem extends_of_chain (hX : X.OK) {U : Set X.Blk} (hU : ∀ r, X.Valid r → X.blk r ∈ U)
    {v : Vote X.sp.n} (hv : X.Valid v.head) {b : Nat} (hb : b ∈ X.chain v.head) :
    SA.VoteExtends U v (X.blk b) :=
  ⟨X.blk v.head, hU _ hv, blk_root hv, anc_of_chain hX hU hv hb⟩

/-- A vote whose head chain misses the valid root `b` does not extend `b` inside the honest
blocks. -/
theorem not_extends (R : Run X) (hX : X.OK) (hF : ∀ r ∈ rowsD R.D, X.Frag r.post)
    {v : Vote X.sp.n} {b : Nat} (hb : X.Valid b) (hn : b ∉ X.chain v.head) :
    ¬ SA.VoteExtends (R.tr.HonestBlocks H) v (X.blk b) := by
  rintro ⟨Hd, hHd, hroot, hanc⟩
  obtain ⟨r, hr, rfl⟩ := honest_sub R hF hHd
  have hrv := mem_allR.1 hr
  rw [blk_root hrv] at hroot
  subst hroot
  exact hn ((anc_T_blk hX (allR_closed hX) hb hr).1 (anc_honest R hF hanc))

/-! ## The source -/

theorem fastSelect_eq (hstock : X.sp.committeeSize = X.sp.n)
    (hX : X.OK) {M : List Nat} (hM : X.Closed M) (a : X.ACD) (t : Int)
    (s : Nat) {c : Nat} (hcM : c ∈ M) :
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
    rw [FastTest, hstock, confirmationScore_eq hX hM a s (hM.valid r (hch r hr.1.1))] at hf
    exact ⟨r, ⟨hr, hf⟩, rfl⟩
  · rintro ⟨r, ⟨hr, hf⟩, rfl⟩
    refine ⟨⟨r, hr, rfl⟩, ?_⟩
    rwa [FastTest, hstock, confirmationScore_eq hX hM a s (hM.valid r (hch r hr.1.1))]

theorem fastCounted_eq (hX : X.OK) {M : List Nat} (hM : X.Closed M) (a : X.ACD) (s : Nat)
    {b : Nat} (hb : X.Valid b) :
    fastCounted X.sp a.interp (X.frameOf M) s (X.blk b) = {v | v ∈ cvD a M s b} := by
  have he : ∀ i, i ∈ equivocators {x | x ∈ a.pool s} ↔ i ∈ eqv (a.pool s) := fun i => by
    rw [equivocators_eq]; rfl
  have hd : X.sp.Δ = 1 := X.hΔ
  ext v
  simp only [fastCounted, interp_pool]
  simp [cvD, he, resolutionTime_interp hM, ancR_frameOf hX hM hb, SAParams.ts, hd, and_assoc]

/-- **The source from two rows**: the tick row `r₀` of `x` at `t = t_s + 6Δ` (cut `i`) writes the
fast lock of slot `s` on `b` (the confirmation `c`, the fast selection `b`, joined, the counted
votes `L`), and the next row `r₁` (`ac_to_fg` of `x` at `t`, same tree) returns `b`. -/
theorem source_mk (R : Run X) (hrun : GoldilocksRun R.proposer R.dg H R.tr) (hX : X.OK)
    {x : Fin X.sp.n} (hx : x ∈ H) {i : Nat} {r₀ r₁ : RowD X} {ems₀ ems₁ : List X.EmD}
    {M : List Nat} (hM : X.Closed M) {t s c b : Nat} (hts : (t : Time) = X.sp.ts s + 6 * X.sp.Δ)
    {L : List X.V}
    (h₀ : (rowsD R.D)[i]? = some r₀) (h₁ : (rowsD R.D)[i + 1]? = some r₁)
    (hn₀ : r₀.node = x) (ht₀ : r₀.time = t) (hc₀ : r₀.cut = .ac .tick M ems₀)
    (hcM : c ∈ M) (hbM : b ∈ M) (hg : r₀.pre.ac.getConf M s = some c)
    (hf : fastSelD r₀.pre.ac M t s c = some b) (hj : r₀.pre.ac.joinedB t = true)
    (hcv : cvD r₀.pre.ac M s b = L) (hn₁ : r₁.node = x) (ht₁ : r₁.time = t)
    (hc₁ : r₁.cut = .ac .toFG M ems₁) (htf : (r₁.pre.ac.toFG M t).2 = some b)
    (hstock : X.sp.committeeSize = X.sp.n) :
    StoredFastLockAt R.tr x i s (X.blk b) {v | v ∈ L} ∧
      SA.joined X.sp (R.tr.state x i).ac (R.tr.time i) ∧
      (∃ ℓ, SA.ToFGAt R.tr.projAC x (i + 1) ℓ (X.blk b)) ∧ R.tr.time (i + 1) = t := by
  have hs₀ := acState R hrun h₀ (hn₀ ▸ hx)
  have hs₁ := acState R hrun h₁ (hn₁ ▸ hx)
  rw [hn₀] at hs₀; rw [hn₁] at hs₁
  have hT₀ : R.tr.time i = t := by rw [rowsD_time R h₀, ht₀]
  have hT₁ : R.tr.time (i + 1) = t := by rw [rowsD_time R h₁, ht₁]
  have hjoin : SA.joined X.sp r₀.pre.ac.interp t := (joined_interp _ _).2 hj
  refine ⟨⟨_, X.blk b, hn₀ ▸ acRow_of R h₀ hc₀, Or.inl ⟨_, X.blk c,
    ⟨hn₀ ▸ acRow_of R h₀ hc₀, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩, ?_,
    ⟨_, hn₁ ▸ acRow_of R h₁ hc₁, rfl, ?_⟩, hT₁⟩
  · change R.tr.time i = _; rw [hT₀, hts]
  · change SA.joined X.sp (R.tr.projAC.state x i) (R.tr.time i)
    rw [hs₀, hT₀]; exact hjoin
  · rw [hs₀]; change getConfirmation X.sp _ (X.frameOf M) s = _
    rw [getConfirmation_eq hX hM, hg]; rfl
  · change deepest _ {X_1 | _ ∧ ¬ conflictsWithLock X.sp (R.tr.projAC.state x i).locks
      _ (R.tr.time i) X_1 ∧ _} = _
    rw [hs₀, hT₀]
    exact (fastSelect_eq hstock hX hM r₀.pre.ac t s hcM).trans (by rw [hf]; rfl)
  · rw [hs₀, fastCounted_eq hX hM _ _ (hM.valid b hbM), hcv]
  · exact (viableAncestor_frameOf hX hM (blk_mem_T hbM)).symm
  · have hst := (trace_row R h₀).2.2.2.2
    rw [hn₀] at hst
    rw [hst, hT₀]; exact hjoin
  · change (acToFG X.sp (R.tr.projAC.state x (i + 1)) (X.frameOf M) (R.tr.time (i + 1))).2 = _
    rw [hs₁, hT₁, acToFG_eq hX hM, resF, htf]; rfl

/-! ## `Carry` from the checks -/

/-- **`Carry_y` from the head chains**: at a vote of the honest `y` whose counted votes `S` have
valid heads, are held before `T` at the read point, and whose head chains `y` accepted before
`T`, when every valid root is an honest block. -/
theorem carryAt_mk (R : Run X) (hrun : GoldilocksRun R.proposer R.dg H R.tr) (hX : X.OK)
    (hF : ∀ r ∈ rowsD R.D, X.Frag r.post) (hU : ∀ r, X.Valid r → X.blk r ∈ R.tr.HonestBlocks H)
    {y : Fin X.sp.n} (hy : y ∈ H) {i : Nat} {e : SA.Em X.sp (List (FG.Att X.sp.n))}
    (hv : SA.VoteAt R.tr.projAC y i e) {s T : Nat} (hT : X.sp.ts s + 3 * X.sp.Δ = T)
    (S : Set (Vote X.sp.n)) (hj : SA.joined X.sp e.readPoint (R.tr.time i))
    (hS : ∀ v ∈ S, X.Valid v.head ∧ chainAcc R.D y v.head T = true ∧
      SA.HeldBefore e.readPoint v T) :
    SA.CarryAt R.tr.projAC (R.tr.HonestBlocks H) y i e s S where
  awake := by
    obtain ⟨ℓ, hc, -⟩ := hv
    exact hrun.toLocalRun.awake_of_call y hy i ⟨_, projAC_call R hc⟩
  joined := hj
  heads v hvS := by
    obtain ⟨hR, hacc, -⟩ := hS v hvS
    refine ⟨X.blk v.head, hU _ hR, blk_root hR, fun A hA => ?_⟩
    obtain ⟨a, ha, rfl⟩ := anc_chain R hX hF hR hA
    rw [hT]
    exact accR_spec R (chain_valid hX hR a ha) (List.all_eq_true.1 hacc a ha)
  holds v hvS := by rw [hT]; exact Or.inl (hS v hvS).2.2

/-- An honest vote of slot `σ` is a vote of the rows. -/
theorem mem_votesD (R : Run X) {σ : Nat} {v : Vote X.sp.n} (h : v ∈ honestVotes R.tr H σ) :
    v ∈ votesD R.D σ := by
  obtain ⟨x, -, j, e', hv, rfl, hs⟩ := h
  obtain ⟨r, hr, -, call, M, ems, hc, em, hem, rfl⟩ := voteAt_row R hv
  exact List.mem_flatMap.2 ⟨r, List.mem_of_getElem? hr, List.mem_filter.2
    ⟨List.mem_map_of_mem (by rw [hc]; exact hem), by simpa using hs⟩⟩

theorem mem_votersD (R : Run X) {σ : Nat} {y : Fin X.sp.n} :
    y ∈ votersD R.D σ ↔ ∃ j e, SA.VoteAt R.tr.projAC y j e ∧ e.msg.slot = σ := by
  constructor
  · intro h
    obtain ⟨r, hm, hr⟩ := List.mem_filterMap.1 h
    split_ifs at hr with hany
    cases hr
    obtain ⟨em, hem, hs⟩ := List.any_eq_true.1 hany
    obtain ⟨call, M, ems, hc, hem'⟩ := emsD_mem hem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    exact ⟨j, _, voteAt_of R (List.getElem?_eq_getElem hj) hc hem', beq_iff_eq.1 hs⟩
  · rintro ⟨j, e, hv, hs⟩
    obtain ⟨r, hr, rfl, call, M, ems, hc, em, hem, rfl⟩ := voteAt_row R hv
    refine List.mem_filterMap.2 ⟨r, List.mem_of_getElem? hr, ?_⟩
    have hany : (emsD r.cut).any (fun em => em.vote.slot == σ) = true :=
      List.any_eq_true.2 ⟨em, by rw [hc]; exact hem, beq_iff_eq.2 hs⟩
    simp only [hany, ↓reduceIte]

/-- **The honest voters of a slot number at least the length of a list of distinct voters on
data** (every node of the rows honest). -/
theorem le_ncard_voters (R : Run X) (hH : ∀ r ∈ rowsD R.D, r.node ∈ H) {σ : Nat}
    {L : List (Fin X.sp.n)} (hL : L ⊆ votersD R.D σ) (hd : L.Nodup) :
    L.length ≤
      {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt R.tr.projAC x' j e' ∧ e'.msg.slot = σ}.ncard := by
  have hsub : (↑L.toFinset : Set (Fin X.sp.n)) ⊆
      {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt R.tr.projAC x' j e' ∧ e'.msg.slot = σ} := by
    intro y hy
    obtain ⟨j, e, hv, hs⟩ := (mem_votersD R).1 (hL (List.mem_toFinset.1 hy))
    obtain ⟨r, hr, rfl, -⟩ := voteAt_row R hv
    exact ⟨hH r (List.mem_of_getElem? hr), j, e, hv, hs⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_coe_finset, List.toFinset_card_of_nodup hd] at this

/-! ## `f < h_t`, `Clean` -/

/-- A node without a restart row is joined at every time. -/
theorem joinedAt_of (R : Run X) {y : Fin X.sp.n}
    (h : (rowsD R.D).all (fun r => r.node != y || !isRestartCut r.cut) = true) (t : Time) :
    R.tr.JoinedAt y t := by
  intro k hk
  obtain ⟨r, hr, rfl, hres⟩ := (restartAt_iff R).1 hk
  have := List.all_eq_true.1 h r (List.mem_of_getElem? hr)
  simp [hres] at this

/-- **`f < h_t`** from a list of distinct honest nodes, awake and joined at `t`, longer than the
number of faulty validators. -/
theorem faultBound_of (R : Run X) {t : Time} {L : List (Fin X.sp.n)} (hd : L.Nodup)
    (hL : ∀ y ∈ L, y ∈ H ∧ R.tr.awake y t ∧ R.tr.JoinedAt y t) (hc : Hᶜ.ncard < L.length) :
    R.tr.FaultBound H t := by
  have hsub : (↑L.toFinset : Set (Fin X.sp.n)) ⊆
      {y | y ∈ H ∧ R.tr.awake y t ∧ R.tr.JoinedAt y t} :=
    fun y hy => hL y (List.mem_toFinset.1 hy)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hd] at this
  exact lt_of_lt_of_le hc this

/-- **(K0) The mirror's caches are genesis** at every cut: its `Σ.F` and `Σ.J` never move. -/
theorem caches_genesis (R : Run X) (y : Fin X.sp.n) (c : Nat) :
    (R.tr.state y c).fg.F = X.gBlk ∧ (R.tr.state y c).fg.J = X.gBlk := by
  rw [trace_state]; exact ⟨rfl, rfl⟩

/-- **(K0) of `Clean`** for a block `B` that genesis precedes inside the honest blocks. -/
theorem clean_caches (R : Run X) {B : X.Blk} (hB : Anc (R.tr.HonestBlocks H) X.gBlk B) {s : Nat} :
    ∀ y ∈ H, ∀ j, R.tr.FirstCutFrom j (X.sp.ts s) →
      Compatible (R.tr.HonestBlocks H) (R.tr.state y j).fg.F B ∧
        Compatible (R.tr.HonestBlocks H) (R.tr.state y j).fg.J B := by
  intro y _ j _
  rw [(caches_genesis R y j).1, (caches_genesis R y j).2]
  exact ⟨Or.inl hB, Or.inl hB⟩

/-- **(K1) The namers of an excluded entry are faulty** when every honest signature names
genesis: an excluded entry strictly extends a cache, which is genesis. -/
theorem namers_sub (R : Run X) (hX : X.OK) (hF : ∀ r ∈ rowsD R.D, X.Frag r.post)
    (hsig : ∀ r ∈ rowsD R.D, ∀ b a, r.cut = .fgAttest b (some a) → a.T = X.g) {B : X.Blk}
    {s : Nat} {T₀ : Time} :
    ∀ E' ∈ excludedEntries R.tr H s B,
      Store.namers X.sp.toParams (Payload X.sp.n) H R.tr.projFG T₀ E' ⊆ Hᶜ := by
  intro E' hE'
  obtain ⟨-, y, -, j, -, hanc, hne⟩ := hE'
  rw [(caches_genesis R y j).1] at hanc hne
  have hE : E' ∈ R.tr.HonestBlocks H := by
    rcases Relation.ReflTransGen.cases_tail hanc with h | ⟨b, -, hp⟩
    · exact absurd h hne
    · exact hp.2.1
  obtain ⟨r, hr, rfl⟩ := honest_sub R hF hE
  have hr2 : r ≠ X.g := fun h => hne (by rw [h]; exact blk_g hX)
  rintro v (hv | ⟨j, a, hs, -, hT⟩)
  · exact hv
  · obtain ⟨r', hr', b, hc⟩ := signAt_row R hs
    have := hsig r' (List.mem_of_getElem? hr') b a hc
    rw [this, blk_root (mem_allR.1 hr)] at hT
    exact absurd hT.symm hr2

/-- **(K2) of `Clean`** from the rows: every vote of a slot in `(s, m]` has the root `b` in its
voter block tree (the frame tree of a closed `M`). -/
theorem heightLead_mk (R : Run X) (hX : X.OK) {s m b : Nat}
    (h : ∀ (i : Nat) (r : RowD X) (call : CallD X) (M : List Nat) (ems : List X.EmD) (em : X.EmD),
      (rowsD R.D)[i]? = some r → r.cut = .ac call M ems → em ∈ ems →
      s < em.vote.slot → em.vote.slot ≤ m → X.Closed M ∧ b ∈ em.rp.vbt M em.vote.slot) :
    ∀ y ∈ H, ∀ i ℓ e, SA.CastAt R.tr.projAC y i ℓ e → s < e.msg.slot → e.msg.slot ≤ m →
      (∃ D ∈ SA.voterBlockTree X.sp e.readPoint ℓ.frame e.msg.slot,
        Anc (R.tr.HonestBlocks H) (X.blk b) D ∧ (R.tr.state y i).fg.IsViable D) ∨
      Anc (R.tr.HonestBlocks H) (X.blk b) ℓ.frame.fcRoot := by
  intro y _ i ℓ e hc h1 h2
  obtain ⟨hca, he⟩ := hc
  obtain ⟨r, hr, -, call, M, ems, hcut, rfl⟩ := acRow R hca
  obtain ⟨em, hem, rfl⟩ := List.mem_map.1 he
  obtain ⟨hcl, hvbt⟩ := h i r call M ems em hr hcut hem h1 h2
  refine Or.inl ⟨X.blk b, ?_, .refl, ?_⟩
  · change X.blk b ∈ voterBlockTree X.sp em.rp.interp (X.frameOf M) em.vote.slot
    rw [voterBlockTree_eq hX hcl]; exact blk_mem_T hvbt
  · rw [trace_state]; exact isViable_interp _ _

end Consensus.Goldilocks.Test.HalfCommittee.DataRun

end
