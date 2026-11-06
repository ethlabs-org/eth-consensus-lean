module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Premises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
@[expose] public section

/-! # A healthy infinite two-validator run: the schedule

Infrastructure for witnesses of the phase-service statements (HS.3, HS.4) and a regression
fixture: an infinite run of the Goldilocks node with two honest validators `v0`, `v1`, no faults,
`Δ = 1`, `t_s = 4s`, `k = c = 2`, `δ_t = 11`, in which the honest frontier stays fixed over long
windows. This file defines the run by execution and proves the cut bookkeeping; the run laws,
the state invariant and the network premises are in the files that import it.

**Why two validators (the one-validator run cannot host HS.3's after-`r` part).** The witness
needs a settled effective phase `(m, c)` at some `w` that is still the phase at the honest
slot-`s` votes of a ready proposal with `t_s ≥ r = t_{a + 2k + 2} ≥ w + 28Δ` (`k = 2`): the
frontier must not rise for about eight slots while every slot has an honest proposal
(`Prop⁺`). With one honest validator and no faults this is impossible. Such a validator's run is
determined: it ticks at every public time, has no other input, and cannot restart after `ḡ`. In
every slot `s ≥ 1` it proposes, accepts its own block, votes for it (its vote is the whole
committee, so the optimistic check writes a fast lock on it), and in the same tick `ac_to_fg`
returns that block and the node signs the row of its entry (a source not yet reported). The next
own proposal carries that row: a target quorum (`q = 1`) for the entry of the parent's height,
with the finality pair of the previous one, so the parent's entry is justified and the chain
enters the next height. So the frontier rises at every slot (the tick run of
`OneValidator.TickRun`, the only such run).

**The two-validator run.** Validator `v0` proposes every slot; `v1` never proposes. At every time
`t ≥ 0`: `v0` ticks, `v1` ticks, then `v1` is delivered (in order) the blocks, votes and
attestations that `v0`'s tick produced, then `v0` is delivered the votes that `v1` emitted at `t`
and the attestations `v1` signed at `t − 35`. With `q = 2` a height is justified only when both
rows of its entry are on chain; `v0`'s own row is in its next proposal, but `v1`'s reaches `v0`
just under `Δ_F = 36` later, so the frontier rises once every ten slots. Every delivery is within
its bound and nothing is suppressed: `v0` includes every row it holds.

**Bookkeeping.** The run is the fold of the node handlers (`Node.exec`) over this schedule, so the
cut law holds by construction. Time `t` has the cuts `1024t … 1024t + 1023`; its `j`-th event
(segment) has the cuts `1024t + 8j …`, labelled by its handler's cuts (at most `7`), the rest
unlabelled. -/

namespace Consensus.Goldilocks.Witness.TwoRun

open Node SA

/-! ## Parameters -/

/-- Two validators, `Δ = 1`, `t_s = 4s`, genesis root `0`, `δ_t = 11`. -/
abbrev P2 : Params where
  n := 2
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 11

/-- The SA parameters: `k = 2`, `c = 2`. -/
abbrev sp : SAParams where
  toParams := P2
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl

/-- A replay order (never used: nobody restarts). -/
noncomputable abbrev ro : ReplayOrder sp (List (FG.Att sp.n)) := ReplayOrder.choice sp

/-- The node. -/
noncomputable abbrev N : NodeAC sp.toParams := goldilocksNode sp ro

/-- The proposer of every slot. -/
abbrev w0 : Fin sp.n := v0

/-- The other validator. -/
abbrev w1 : Fin sp.n := ⟨1, by decide⟩

theorem w1_ne : w1 ≠ w0 := by decide

theorem eq_w0_or_w1 (y : Fin sp.n) : y = w0 ∨ y = w1 := by
  rcases y with ⟨_ | _ | y, hy⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hy (by change ¬ (y + 2 < 2); omega)

/-- The proposer schedule: `w0` at every slot. -/
abbrev prop : Nat → Fin sp.n := fun _ => w0

/-- The content of a block (what its root digests). -/
abbrev Content := Option Nat × Nat × Nat × List (FG.Att sp.n) × Payload sp.n

/-- An injective code of block contents. -/
noncomputable def code : Content → Nat := (Countable.exists_injective_nat Content).choose

theorem code_injective : Function.Injective code :=
  (Countable.exists_injective_nat Content).choose_spec

/-- The genesis content. -/
def genContent : Content := (none, 0, 0, [], ([], []))

open Classical in
/-- A collision-free digest whose value at the genesis content is the genesis root `0`. -/
noncomputable def dg : Digest (List (FG.Att sp.n)) (Payload sp.n) := fun p s x a q =>
  if (p, s, x, a, q) = genContent then 0 else code (p, s, x, a, q) + 1

theorem dg_injective {p s x a q p' s' x' a' q'} (h : dg p s x a q = dg p' s' x' a' q') :
    (p, s, x, a, q) = ((p', s', x', a', q') : Content) := by
  unfold dg at h
  split_ifs at h with h₁ h₂ h₃ <;> first
    | exact h₁.trans h₂.symm
    | exact code_injective (by omega)

theorem dg_genesis : (sp.toParams.genesisBlock N.genesisPayload).RootOk dg := by
  change (0 : Nat) = dg none 0 0 [] ([], [])
  unfold dg; simp [genContent]

theorem dg_noColl (tr : RunTrace N) : Compose.NoCollRun dg tr := by
  intro B _ C _ h
  have := dg_injective h
  simp only [Prod.mk.injEq] at this
  exact this

/-! ## The schedule -/

/-- A node state. -/
abbrev St := NodeState N

/-- The states of both nodes. -/
abbrev Wld := Fin sp.n → St

/-- One event of the run: its node, the event, the states of both nodes before it, and its
cuts. -/
structure Seg where
  node : Fin sp.n
  ev : Node.Event N
  pre : Wld
  cuts : List (Cut N)

/-- The handler of `e` at `y` from the world `w` at time `t`. -/
noncomputable abbrev ex (w : Wld) (y : Fin sp.n) (t : Nat) (e : Node.Event N) :
    St × List (Cut N) :=
  exec prop dg y (w y) (t : Int) e

/-- Run the events `es` at time `t` from the world `w`: the world after them and their segments. -/
noncomputable def runEvs (t : Nat) : Wld → List (Fin sp.n × Node.Event N) → Wld × List Seg
  | w, [] => (w, [])
  | w, (y, e) :: es =>
    let r := ex w y t e
    let rest := runEvs t (Function.update w y r.1) es
    (rest.1, ⟨y, e, w, r.2⟩ :: rest.2)

/-- The events that `v1` is delivered from `v0`'s tick cuts: the own block, the emitted vote,
the signed attestation, in cut order (at most one per cut). -/
def toW1 : Cut N → Option (Node.Event N)
  | .fg (.block B true) => some (.block B)
  | .fg (.attest _ (some a)) => some (.attestation a)
  | .ac ℓ => ℓ.emits.head?.map fun e => .message e.msg
  | _ => none

/-- The vote a cut emits, if any (the first emission), as a delivery. -/
def voteOf : Cut N → Option (Node.Event N)
  | .ac ℓ => ℓ.emits.head?.map fun e => .message e.msg
  | _ => none

/-- The attestation a cut signs, if any. -/
def attOf : Cut N → Option (FG.Att sp.n)
  | .fg (.attest _ (some a)) => some a
  | _ => none

/-- The world at the start of a time: both nodes' states, and the attestations `v1` signed at
each earlier time (delivered to `v0` thirty-five time units later). -/
abbrev World := Wld × (Nat → List (FG.Att sp.n))

/-- The events of time `t` from the world `W`: the two ticks, the deliveries to `v1`, the
deliveries to `v0`; the world at the start of `t + 1` and the segments. -/
noncomputable def stepT (t : Nat) (W : World) : World × List Seg :=
  let e0 := ex W.1 w0 t (.tick 0)
  let w1' := Function.update W.1 w0 e0.1
  let e1 := ex w1' w1 t (.tick 0)
  let w2 := Function.update w1' w1 e1.1
  let r2 := runEvs t w2 ((e0.2.filterMap toW1).map (w1, ·))
  let c3 := r2.2.flatMap Seg.cuts
  let qa := (if 35 ≤ t then W.2 (t - 35) else []).map fun a => (w0, Node.Event.attestation a)
  let r3 := runEvs t r2.1 (((e1.2 ++ c3).filterMap voteOf).map (w0, ·) ++ qa)
  ((r3.1, Function.update W.2 t (e1.2.filterMap attOf)),
    ⟨w0, .tick 0, W.1, e0.2⟩ :: ⟨w1, .tick 0, w1', e1.2⟩ :: (r2.2 ++ r3.2))

/-- The world at the start of time `t`. -/
noncomputable def world : Nat → World
  | 0 => (fun _ => Node.init N, fun _ => [])
  | t + 1 => (stepT t (world t)).1

/-- The segments of time `t`. -/
noncomputable def segs (t : Nat) : List Seg := (stepT t (world t)).2

/-- The segment of cut `i`, if any. -/
noncomputable def segOf (i : Nat) : Option Seg := (segs (i / 1024))[i % 1024 / 8]?

/-- The label of cut `i`. -/
noncomputable def lab (i : Nat) : Option (Cut N) := (segOf i).bind fun sg => sg.cuts[i % 8]?

open Classical in
/-- **The run.** -/
noncomputable def run : RunTrace N where
  init _ := Node.init N
  node i := (segOf i).elim w0 Seg.node
  time i := ((i / 1024 : Nat) : Int)
  event i := if lab i ≠ none then 2 * (i / 8) else 2 * i + 1
  pos i := i % 8
  label i := lab i
  post i := (segOf i).elim (Node.init N) fun sg =>
    (sg.cuts.take (i % 8 + 1)).foldl (cutPost sg.node ((i / 1024 : Nat) : Int)) (sg.pre sg.node)
  awake _ t := 0 ≤ t

/-! ## Bounds -/

/-- Every handler makes at most seven cuts. -/
theorem ex_length (w : Wld) (y : Fin sp.n) (t : Nat) (e : Node.Event N) :
    (ex w y t e).2.length ≤ 7 := by
  cases e with
  | tick x => exact onTick_length N dg y _ _ x
  | block B => exact le_trans (onBlock_length N y _ _ B) (by decide)
  | message m => simp [ex, exec, onMessage]
  | attestation a => simp [ex, exec, onAttestation]
  | restart => simp [ex, exec, Node.restart]

theorem runEvs_length (t : Nat) : ∀ (w : Wld) (es : List (Fin sp.n × Node.Event N)),
    (runEvs t w es).2.length = es.length
  | _, [] => rfl
  | w, (y, e) :: es => by simp only [runEvs, List.length_cons, runEvs_length t _ es]

theorem runEvs_cuts (t : Nat) : ∀ (w : Wld) (es : List (Fin sp.n × Node.Event N)),
    ∀ sg ∈ (runEvs t w es).2, sg.cuts.length ≤ 7
  | _, [] => by simp [runEvs]
  | w, (y, e) :: es => by
    intro sg hsg
    simp only [runEvs, List.mem_cons] at hsg
    rcases hsg with rfl | hsg
    · exact ex_length w y t e
    · exact runEvs_cuts t _ es sg hsg

theorem flatMap_cuts_length {l : List Seg} (h : ∀ sg ∈ l, sg.cuts.length ≤ 7) :
    (l.flatMap Seg.cuts).length ≤ 7 * l.length := by
  induction l with
  | nil => simp
  | cons sg l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := h sg (List.mem_cons_self ..)
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

theorem filterMap_length_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.filterMap_cons]; split <;> simp <;> omega

/-- `v1`'s signed attestations per time: at most seven. -/
theorem world_queue : ∀ t t', ((world t).2 t').length ≤ 7
  | 0, _ => by simp [world]
  | t + 1, t' => by
    change (Function.update (world t).2 t _ t').length ≤ 7
    by_cases h : t' = t
    · subst h; rw [Function.update_self]
      exact le_trans (filterMap_length_le _ _) (ex_length _ _ _ _)
    · rw [Function.update_of_ne h]; exact world_queue t t'

theorem stepT_length (t : Nat) (W : World) (hq : ∀ t', (W.2 t').length ≤ 7) :
    (stepT t W).2.length ≤ 72 := by
  unfold stepT
  dsimp only
  have l0 := ex_length W.1 w0 t (.tick 0)
  generalize ex W.1 w0 t (.tick 0) = e0 at *
  have l1 := ex_length (Function.update W.1 w0 e0.1) w1 t (.tick 0)
  generalize ex (Function.update W.1 w0 e0.1) w1 t (.tick 0) = e1 at *
  generalize Function.update (Function.update W.1 w0 e0.1) w1 e1.1 = w2
  have h0 := le_trans (filterMap_length_le toW1 e0.2) l0
  have hr2 := flatMap_cuts_length (runEvs_cuts t w2 ((e0.2.filterMap toW1).map (w1, ·)))
  rw [runEvs_length, List.length_map] at hr2
  have hl2 := runEvs_length t w2 ((e0.2.filterMap toW1).map (w1, ·))
  rw [List.length_map] at hl2
  generalize (runEvs t w2 ((e0.2.filterMap toW1).map (w1, ·))) = r2 at *
  have hv := filterMap_length_le voteOf (e1.2 ++ r2.2.flatMap Seg.cuts)
  have hqa : (if 35 ≤ t then W.2 (t - 35) else []).length ≤ 7 := by
    split_ifs
    · exact hq _
    · simp
  simp only [List.length_append] at hv
  simp only [List.length_cons, List.length_append, runEvs_length, List.length_map]
  omega

/-- At most `72` events per time. -/
theorem segs_length (t : Nat) : (segs t).length ≤ 72 := stepT_length t _ (world_queue t)

/-- Every event of the run makes at most seven cuts. -/
theorem segs_cuts (t : Nat) : ∀ sg ∈ segs t, sg.cuts.length ≤ 7 := by
  intro sg hsg
  unfold segs stepT at hsg
  dsimp only at hsg
  simp only [List.mem_cons, List.mem_append] at hsg
  rcases hsg with rfl | rfl | hsg | hsg
  · exact ex_length _ _ _ _
  · exact ex_length _ _ _ _
  · exact runEvs_cuts _ _ _ sg hsg
  · exact runEvs_cuts _ _ _ sg hsg

/-! ## The segment chain -/

/-- The segments `l` at time `t` take the world `w` to `w'`, each one the handler of its event. -/
inductive Chain (t : Nat) : Wld → List Seg → Wld → Prop
  | nil (w : Wld) : Chain t w [] w
  | cons {w w' : Wld} {sg : Seg} {l : List Seg} (hpre : sg.pre = w)
      (hcuts : sg.cuts = (ex w sg.node t sg.ev).2)
      (hrest : Chain t (Function.update w sg.node (ex w sg.node t sg.ev).1) l w') :
      Chain t w (sg :: l) w'

theorem chain_runEvs (t : Nat) : ∀ (w : Wld) (es : List (Fin sp.n × Node.Event N)),
    Chain t w (runEvs t w es).2 (runEvs t w es).1
  | w, [] => .nil w
  | _, (_, _) :: es => .cons rfl rfl (chain_runEvs t _ es)

theorem Chain.append {t : Nat} {w w' w'' : Wld} {l l' : List Seg} (h : Chain t w l w')
    (h' : Chain t w' l' w'') : Chain t w (l ++ l') w'' := by
  induction h with
  | nil => exact h'
  | cons hpre hcuts _ ih => exact .cons hpre hcuts (ih h')

/-- The segments of time `t` take the world of `t` to the world of `t + 1`. -/
theorem chain_segs (t : Nat) : Chain t (world t).1 (segs t) (world (t + 1)).1 := by
  unfold segs
  change Chain t (world t).1 (stepT t (world t)).2 (stepT t (world t)).1.1
  unfold stepT
  dsimp only
  exact .cons rfl rfl (.cons rfl rfl ((chain_runEvs _ _ _).append (chain_runEvs _ _ _)))

/-- The world after the segment `sg` at time `t`. -/
noncomputable def nextW (t : Nat) (sg : Seg) : Wld :=
  Function.update sg.pre sg.node (ex sg.pre sg.node t sg.ev).1

theorem Chain.mem_cuts {t : Nat} {w w' : Wld} {l : List Seg} (h : Chain t w l w') :
    ∀ sg ∈ l, sg.cuts = (ex sg.pre sg.node t sg.ev).2 := by
  induction h with
  | nil => simp
  | cons hpre hcuts _ ih =>
    intro sg hsg
    rcases List.mem_cons.1 hsg with rfl | hsg
    · rw [hpre]; exact hcuts
    · exact ih sg hsg

theorem Chain.get_zero {t : Nat} {w w' : Wld} {l : List Seg} (h : Chain t w l w') {sg : Seg}
    (hs : l[0]? = some sg) : sg.pre = w := by
  cases h with
  | nil => simp at hs
  | cons hpre _ _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs; subst hs; exact hpre

theorem Chain.get_succ {t : Nat} {w w' : Wld} {l : List Seg} (h : Chain t w l w') :
    ∀ {j : Nat} {sg : Seg}, l[j]? = some sg →
      (∀ sg', l[j + 1]? = some sg' → sg'.pre = nextW t sg) ∧
        (l[j + 1]? = none → w' = nextW t sg) := by
  induction h with
  | nil => intro j sg hs; simp at hs
  | @cons w w' sg0 l hpre hcuts hrest ih =>
    intro j sg hs
    rcases j with _ | j
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      have hn : nextW t sg0 = Function.update w sg0.node (ex w sg0.node t sg0.ev).1 := by
        rw [nextW, hpre]
      refine ⟨fun sg' hs' => ?_, fun hs' => ?_⟩
      · rw [hn]; exact hrest.get_zero (by simpa using hs')
      · rw [hn]
        have : l = [] := by simpa using hs'
        subst this
        cases hrest; rfl
    · simp only [List.getElem?_cons_succ] at hs ⊢
      exact ih hs

/-- The `0`-th segment of time `t` is `v0`'s tick, from the world of `t`. -/
theorem segs_zero (t : Nat) :
    (segs t)[0]? = some ⟨w0, .tick 0, (world t).1, (ex (world t).1 w0 t (.tick 0)).2⟩ := by
  rfl

/-- The `1`-st segment of time `t` is `v1`'s tick. -/
theorem segs_one (t : Nat) :
    (segs t)[1]? = some ⟨w1, .tick 0, Function.update (world t).1 w0
      (ex (world t).1 w0 t (.tick 0)).1, (ex (Function.update (world t).1 w0
        (ex (world t).1 w0 t (.tick 0)).1) w1 t (.tick 0)).2⟩ := by
  rfl

theorem runEvs_get (t : Nat) : ∀ (w : Wld) (es : List (Fin sp.n × Node.Event N)) {j : Nat}
    {sg : Seg}, (runEvs t w es).2[j]? = some sg → es[j]? = some (sg.node, sg.ev)
  | _, [], _, _, h => by simp [runEvs] at h
  | w, (y, e) :: es, j, sg, h => by
    rcases j with _ | j
    · simp only [runEvs, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
    · simp only [runEvs, List.getElem?_cons_succ] at h ⊢
      exact runEvs_get t _ es h

/-- `v0`'s tick at time `t`. -/
noncomputable abbrev tk0 (t : Nat) : St × List (Cut N) := ex (world t).1 w0 t (.tick 0)

/-- The world after `v0`'s tick. -/
noncomputable abbrev wA (t : Nat) : Wld := Function.update (world t).1 w0 (tk0 t).1

/-- `v1`'s tick at time `t`. -/
noncomputable abbrev tk1 (t : Nat) : St × List (Cut N) := ex (wA t) w1 t (.tick 0)

/-- The world after both ticks. -/
noncomputable abbrev wB (t : Nat) : Wld := Function.update (wA t) w1 (tk1 t).1

/-- The deliveries to `v1` at time `t`. -/
noncomputable abbrev evs1 (t : Nat) : List (Fin sp.n × Node.Event N) :=
  ((tk0 t).2.filterMap toW1).map (w1, ·)

/-- Their run. -/
noncomputable abbrev run1 (t : Nat) : Wld × List Seg := runEvs t (wB t) (evs1 t)

/-- The attestations delivered to `v0` at time `t` (signed by `v1` at `t - 35`). -/
noncomputable abbrev qa (t : Nat) : List (FG.Att sp.n) :=
  if 35 ≤ t then (world t).2 (t - 35) else []

/-- The deliveries to `v0` at time `t`. -/
noncomputable abbrev evs0 (t : Nat) : List (Fin sp.n × Node.Event N) :=
  (((tk1 t).2 ++ (run1 t).2.flatMap Seg.cuts).filterMap voteOf).map (w0, ·) ++
    (qa t).map fun a => (w0, Node.Event.attestation a)

/-- The events of time `t`, unfolded. -/
theorem segs_eq (t : Nat) : segs t =
    ⟨w0, .tick 0, (world t).1, (tk0 t).2⟩ :: ⟨w1, .tick 0, wA t, (tk1 t).2⟩ ::
      ((run1 t).2 ++ (runEvs t (run1 t).1 (evs0 t)).2) := rfl

theorem world_succ (t : Nat) :
    world (t + 1) = ((runEvs t (run1 t).1 (evs0 t)).1,
      Function.update (world t).2 t ((tk1 t).2.filterMap attOf)) := rfl

/-- A delivery segment (index `≥ 2`) of time `t`: to `v1`, an event of `toW1` of a cut of
`v0`'s tick; or to `v0`, a vote of a cut of `v1` at time `t` before it, or an attestation of
`qa t`. -/
theorem segs_delivery {t j : Nat} {sg : Seg} (h : (segs t)[j + 2]? = some sg) :
    (j < (evs1 t).length ∧ sg.node = w1 ∧
      ∃ (k : Nat) (c : Cut N), (tk0 t).2[k]? = some c ∧ toW1 c = some sg.ev) ∨
    ((evs1 t).length ≤ j ∧ sg.node = w0 ∧
      ((∃ c, c ∈ (tk1 t).2 ++ (run1 t).2.flatMap Seg.cuts ∧ voteOf c = some sg.ev) ∨
        ∃ a ∈ qa t, sg.ev = .attestation a)) := by
  rw [segs_eq] at h
  simp only [List.getElem?_cons_succ] at h
  by_cases hj : j < (run1 t).2.length
  · rw [List.getElem?_append_left hj] at h
    have he := runEvs_get t _ _ h
    have hl : (run1 t).2.length = (evs1 t).length := runEvs_length _ _ _
    refine Or.inl ⟨by omega, ?_⟩
    rw [List.getElem?_map] at he
    obtain ⟨e, he1, he2⟩ := Option.map_eq_some_iff.1 he
    simp only [Prod.mk.injEq] at he2
    refine ⟨he2.1.symm, ?_⟩
    obtain ⟨c, hc, hce⟩ := List.mem_filterMap.1 (List.mem_of_getElem? he1)
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hc
    exact ⟨k, c, hk, by rw [hce, he2.2]⟩
  · rw [List.getElem?_append_right (by omega)] at h
    have he := runEvs_get t _ _ h
    have hl : (run1 t).2.length = (evs1 t).length := runEvs_length _ _ _
    refine Or.inr ⟨by omega, ?_⟩
    have hm := List.mem_of_getElem? he
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨e, he1, he2⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at he2
      refine ⟨he2.1.symm, Or.inl ?_⟩
      obtain ⟨c, hc, hce⟩ := List.mem_filterMap.1 he1
      exact ⟨c, hc, by rw [hce, he2.2]⟩
    · obtain ⟨a, ha, he2⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at he2
      exact ⟨he2.1.symm, Or.inr ⟨a, ha, he2.2.symm⟩⟩

/-- The state of `y` before cut `i`, read off the segments. -/
noncomputable def preState (y : Fin sp.n) (i : Nat) : St :=
  match segOf i with
  | some sg =>
    if sg.node = y then (sg.cuts.take (i % 8)).foldl (cutPost y ((i / 1024 : Nat) : Int)) (sg.pre y)
    else sg.pre y
  | none => (world (i / 1024 + 1)).1 y

theorem segOf_eq (t j k : Nat) (hj : j < 128) (hk : k < 8) :
    segOf (1024 * t + 8 * j + k) = (segs t)[j]? := by
  unfold segOf
  rw [show (1024 * t + 8 * j + k) / 1024 = t by omega,
    show (1024 * t + 8 * j + k) % 1024 / 8 = j by omega]

theorem segs_none {t j : Nat} (hj : 72 ≤ j) : (segs t)[j]? = none :=
  List.getElem?_eq_none (le_trans (segs_length t) hj)

theorem mem_segs {t j : Nat} {sg : Seg} (h : (segs t)[j]? = some sg) : sg ∈ segs t :=
  List.mem_of_getElem? h

theorem segs_cuts_eq {t j : Nat} {sg : Seg} (h : (segs t)[j]? = some sg) :
    sg.cuts = (ex sg.pre sg.node t sg.ev).2 := (chain_segs t).mem_cuts sg (mem_segs h)

/-- The fold of all of a segment's cuts is the handler's result. -/
theorem foldl_seg {t j : Nat} {sg : Seg} (h : (segs t)[j]? = some sg) {k : Nat}
    (hk : 7 ≤ k) : (sg.cuts.take k).foldl (cutPost sg.node (t : Int)) (sg.pre sg.node) =
      (ex sg.pre sg.node t sg.ev).1 := by
  rw [List.take_of_length_le (le_trans (segs_cuts t sg (mem_segs h)) hk), segs_cuts_eq h]
  exact foldl_cutPost_exec _ _ _ _ _ _

theorem nextW_apply {t j : Nat} {sg : Seg} (h : (segs t)[j]? = some sg) (y : Fin sp.n) :
    nextW t sg y = if sg.node = y then
      (sg.cuts.take 7).foldl (cutPost y (t : Int)) (sg.pre y) else sg.pre y := by
  unfold nextW
  split_ifs with hy
  · subst hy; rw [Function.update_self, foldl_seg h le_rfl]
  · rw [Function.update_of_ne (Ne.symm hy)]

/-- **The states of the run**: before cut `i`, the state of `y` is `preState y i`. -/
theorem run_state (y : Fin sp.n) : ∀ i, run.state y i = preState y i
  | 0 => by
    unfold preState
    rw [show segOf 0 = (segs 0)[0]? from rfl, segs_zero]
    dsimp only
    split_ifs <;> rfl
  | i + 1 => by
    have ih := run_state y i
    obtain ⟨t, j, k, hj, hk, rfl⟩ : ∃ t j k, j < 128 ∧ k < 8 ∧ i = 1024 * t + 8 * j + k :=
      ⟨i / 1024, i % 1024 / 8, i % 8, by omega, by omega, by omega⟩
    have hti : (1024 * t + 8 * j + k) / 1024 = t := by omega
    have hki : (1024 * t + 8 * j + k) % 8 = k := by omega
    simp only [Trace.state]
    rw [ih]
    unfold preState
    rw [segOf_eq t j k hj hk]
    by_cases hk7 : k < 7
    · -- the same segment
      rw [show 1024 * t + 8 * j + k + 1 = 1024 * t + 8 * j + (k + 1) by omega,
        segOf_eq t j (k + 1) hj (by omega), show (1024 * t + 8 * j + (k + 1)) % 8 = k + 1 by omega,
        show (1024 * t + 8 * j + (k + 1)) / 1024 = t by omega, hki, hti]
      rcases hs : (segs t)[j]? with _ | sg
      · have hlab : run.label (1024 * t + 8 * j + k) = none := by
          change (segOf _).bind _ = _; rw [segOf_eq t j k hj hk, hs]; rfl
        rw [hlab]; simp
      · dsimp only
        have hnode : run.node (1024 * t + 8 * j + k) = sg.node := by
          change (segOf _).elim w0 Seg.node = _; rw [segOf_eq t j k hj hk, hs]; rfl
        have hlab : run.label (1024 * t + 8 * j + k) = sg.cuts[k]? := by
          change (segOf _).bind _ = _; rw [segOf_eq t j k hj hk, hs]; simp [hki]
        have hpost : run.post (1024 * t + 8 * j + k) =
            (sg.cuts.take (k + 1)).foldl (cutPost sg.node (t : Int)) (sg.pre sg.node) := by
          change (segOf _).elim _ _ = _; rw [segOf_eq t j k hj hk, hs]
          simp only [Option.elim, hki, hti]
        rw [hnode, hlab, hpost]
        by_cases hy : sg.node = y
        · subst hy
          simp only [true_and, ite_true]
          split_ifs with hl
          · rfl
          · have hl' : sg.cuts.length ≤ k := by
              by_contra hc; exact hl (by rw [List.getElem?_eq_getElem (by omega)]; simp)
            rw [List.take_of_length_le hl', List.take_of_length_le (by omega)]
        · simp [hy]
    · -- the next segment (or the next time)
      have hk7' : k = 7 := by omega
      subst hk7'
      rcases hs : (segs t)[j]? with _ | sg
      · -- no segment: the world after time `t` stays
        have hlab : run.label (1024 * t + 8 * j + 7) = none := by
          change (segOf _).bind _ = _; rw [segOf_eq t j 7 hj hk, hs]; rfl
        rw [hlab]
        simp only [ne_eq, not_true_eq_false, and_false, ite_false, hti]
        by_cases hj' : j < 127
        · rw [show 1024 * t + 8 * j + 7 + 1 = 1024 * t + 8 * (j + 1) + 0 by omega,
            segOf_eq t (j + 1) 0 (by omega) (by omega),
            List.getElem?_eq_none (le_of_lt (List.getElem?_eq_none_iff.1 hs |> fun h => by
              have := List.getElem?_eq_none_iff.1 hs; omega))]
          dsimp only
          rw [show (1024 * t + 8 * (j + 1) + 0) / 1024 = t by omega]
        · rw [show 1024 * t + 8 * j + 7 + 1 = 1024 * (t + 1) + 8 * 0 + 0 by omega,
            segOf_eq (t + 1) 0 0 (by omega) (by omega), segs_zero]
          dsimp only
          rw [show (1024 * (t + 1) + 8 * 0 + 0) % 8 = 0 by omega]
          split_ifs <;> simp
      · -- the segment ends
        have hlab : run.label (1024 * t + 8 * j + 7) = none := by
          change (segOf _).bind _ = _; rw [segOf_eq t j 7 hj hk, hs]
          simp only [Option.bind_some, hki]
          exact List.getElem?_eq_none (segs_cuts t sg (mem_segs hs))
        rw [hlab]
        simp only [ne_eq, not_true_eq_false, and_false, ite_false, hti, hki]
        have hnw := nextW_apply hs y
        obtain ⟨hsucc, hlast⟩ := (chain_segs t).get_succ hs
        have hj72 : j < 72 := by
          by_contra hc; rw [segs_none (by omega)] at hs; cases hs
        rw [show 1024 * t + 8 * j + 7 + 1 = 1024 * t + 8 * (j + 1) + 0 by omega,
          segOf_eq t (j + 1) 0 (by omega) (by omega)]
        rcases hs' : (segs t)[j + 1]? with _ | sg'
        · dsimp only
          rw [show (1024 * t + 8 * (j + 1) + 0) / 1024 = t by omega, hlast hs', ← hnw]
        · dsimp only
          rw [show (1024 * t + 8 * (j + 1) + 0) % 8 = 0 by omega, hsucc sg' hs', ← hnw]
          split_ifs with h
          · subst h; rfl
          · rfl

/-! ## Cuts and groups -/

/-- A cut, located: time `t`, segment `j`, position `k`. -/
theorem cut_decomp (i : Nat) : ∃ t j k, j < 128 ∧ k < 8 ∧ i = 1024 * t + 8 * j + k :=
  ⟨i / 1024, i % 1024 / 8, i % 8, by omega, by omega, by omega⟩

theorem run_time (t j k : Nat) (hj : j < 128) (hk : k < 8) :
    run.time (1024 * t + 8 * j + k) = (t : Int) := by
  change ((_ / 1024 : Nat) : Int) = _; rw [show (1024 * t + 8 * j + k) / 1024 = t by omega]

theorem run_label (t j k : Nat) (hj : j < 128) (hk : k < 8) :
    run.label (1024 * t + 8 * j + k) = ((segs t)[j]?).bind fun sg => sg.cuts[k]? := by
  change (segOf _).bind _ = _
  rw [segOf_eq t j k hj hk, show (1024 * t + 8 * j + k) % 8 = k by omega]

theorem run_node {t j k : Nat} (hj : j < 128) (hk : k < 8) {sg : Seg}
    (hs : (segs t)[j]? = some sg) : run.node (1024 * t + 8 * j + k) = sg.node := by
  change (segOf _).elim w0 Seg.node = _; rw [segOf_eq t j k hj hk, hs]; rfl

theorem run_post {t j k : Nat} (hj : j < 128) (hk : k < 8) {sg : Seg}
    (hs : (segs t)[j]? = some sg) : run.post (1024 * t + 8 * j + k) =
      (sg.cuts.take (k + 1)).foldl (cutPost sg.node (t : Int)) (sg.pre sg.node) := by
  change (segOf _).elim _ _ = _
  rw [segOf_eq t j k hj hk, hs]
  simp only [Option.elim, show (1024 * t + 8 * j + k) % 8 = k by omega,
    show (1024 * t + 8 * j + k) / 1024 = t by omega]

theorem run_state_seg {t j k : Nat} (hj : j < 128) (hk : k < 8) {sg : Seg}
    (hs : (segs t)[j]? = some sg) :
    run.state sg.node (1024 * t + 8 * j + k) =
      (sg.cuts.take k).foldl (cutPost sg.node (t : Int)) (sg.pre sg.node) := by
  rw [run_state]
  unfold preState
  rw [segOf_eq t j k hj hk, hs]
  simp only [ite_true, show (1024 * t + 8 * j + k) % 8 = k by omega,
    show (1024 * t + 8 * j + k) / 1024 = t by omega]

/-- A labelled cut lies in a segment of its node, at a position below the segment's length. -/
theorem label_some {i : Nat} {c : Cut N} (h : run.label i = some c) :
    ∃ t j k sg, j < 128 ∧ k < 8 ∧ i = 1024 * t + 8 * j + k ∧ (segs t)[j]? = some sg ∧
      sg.cuts[k]? = some c ∧ run.node i = sg.node := by
  obtain ⟨t, j, k, hj, hk, rfl⟩ := cut_decomp i
  rw [run_label t j k hj hk] at h
  rcases hs : (segs t)[j]? with _ | sg
  · rw [hs] at h; cases h
  · rw [hs] at h
    exact ⟨t, j, k, sg, hj, hk, rfl, hs, h, run_node hj hk hs⟩

/-- **The cut law** at every labelled cut. -/
theorem run_cutStep {y : Fin sp.n} {i : Nat} {c : Cut N} (hc : run.CallAt y i c) :
    CutStep y (run.time i) (run.state y i) c (run.post i) := by
  obtain ⟨t, j, k, sg, hj, hk, rfl, hs, hck, hn⟩ := label_some hc.2
  have hy : sg.node = y := hn.symm.trans hc.1
  subst hy
  rw [run_time t j k hj hk, run_state_seg hj hk hs, run_post hj hk hs]
  obtain ⟨hk', he⟩ := List.getElem?_eq_some_iff.1 hck
  have hcuts := segs_cuts_eq hs
  have := chain_step (Compose.exec_is_cut_chain prop dg sg.node (sg.pre sg.node) (t : Int) sg.ev)
    k (by rw [← hcuts]; exact hk')
  simp only [← hcuts, he] at this
  exact this

theorem run_event_lab {i : Nat} (h : run.label i ≠ none) : run.event i = 2 * (i / 8) := by
  change (if lab i ≠ none then _ else _) = _; exact ite_eq_left_of_eq_true _ _ (eq_true h)

theorem run_event_nolab {i : Nat} (h : run.label i = none) : run.event i = 2 * i + 1 := by
  change (if lab i ≠ none then _ else _) = _
  exact ite_eq_right_of_eq_false _ _ (eq_false (not_not.2 h))

theorem run_event_eq {i i' : Nat} (h : run.label i ≠ none) (he : run.event i' = run.event i) :
    run.label i' ≠ none ∧ i' / 8 = i / 8 := by
  rw [run_event_lab h] at he
  by_cases h' : run.label i' = none
  · rw [run_event_nolab h'] at he; omega
  · rw [run_event_lab h'] at he; exact ⟨h', by omega⟩

/-- **Each nonempty segment is a group** of its node at its time. -/
theorem group_seg {t j : Nat} (hj : j < 128) {sg : Seg} (hs : (segs t)[j]? = some sg)
    (hne : sg.cuts ≠ []) : run.GroupAt prop dg sg.node (1024 * t + 8 * j) (t : Int) sg.ev := by
  have hst : run.state sg.node (1024 * t + 8 * j) = sg.pre sg.node := by
    have := run_state_seg hj (by omega : 0 < 8) hs; simpa using this
  have hcs : (exec prop dg sg.node (run.state sg.node (1024 * t + 8 * j)) (t : Int) sg.ev).2 =
      sg.cuts := by rw [hst, segs_cuts_eq hs]
  have hlen := segs_cuts t sg (mem_segs hs)
  have hl0 : run.label (1024 * t + 8 * j) ≠ none := by
    have := run_label t j 0 hj (by omega); rw [Nat.add_zero] at this
    rw [this, hs]; simp only [Option.bind_some, ne_eq, List.getElem?_eq_none_iff, not_le]
    exact List.length_pos_of_ne_nil hne
  refine ⟨by rw [hcs]; exact hne, fun k hk => ?_, fun i hi => ?_⟩
  · have hk' : k < sg.cuts.length := by rw [← hcs]; exact hk
    have hk8 : k < 8 := by omega
    have hlk := run_label t j k hj hk8
    rw [hs] at hlk
    refine ⟨run_node hj hk8 hs, run_time t j k hj hk8, ?_, ?_, ?_⟩
    · have h1 : run.label (1024 * t + 8 * j + k) ≠ none := by
        rw [hlk]; simp [List.getElem?_eq_getElem hk']
      rw [run_event_lab h1, run_event_lab hl0]; congr 1; omega
    · change (1024 * t + 8 * j + k) % 8 = k; omega
    · rw [hlk]; simp only [Option.bind_some, List.getElem?_eq_getElem hk']
      congr 1; exact (List.getElem_of_eq hcs hk).symm
  · obtain ⟨hli, hdiv⟩ := run_event_eq hl0 hi
    obtain ⟨t', j', k', hj', hk', rfl⟩ := cut_decomp i
    have ht : t' = t ∧ j' = j := by omega
    obtain ⟨rfl, rfl⟩ := ht
    rw [run_label t' j' k' hj' hk', hs] at hli
    simp only [Option.bind_some, ne_eq, List.getElem?_eq_none_iff, not_le] at hli
    rw [hcs]; omega

/-- A labelled cut at position `k` of a segment has a labelled cut at position `0` before it. -/
theorem label_start {i : Nat} (h : run.label i ≠ none) : run.label (8 * (i / 8)) ≠ none := by
  obtain ⟨t, j, k, hj, hk, rfl⟩ := cut_decomp i
  rw [run_label t j k hj hk] at h
  rw [show 8 * ((1024 * t + 8 * j + k) / 8) = 1024 * t + 8 * j + 0 by omega, run_label t j 0 hj
    (by omega)]
  rcases hs : (segs t)[j]? with _ | sg
  · rw [hs] at h; exact absurd rfl h
  · rw [hs] at h
    simp only [Option.bind_some, ne_eq, List.getElem?_eq_none_iff, not_le] at h ⊢
    omega

/-- **A group starts at a segment**: at its first cut, of its node and time, with the event of the
segment up to a tick's input. -/
theorem groupAt_inv {y : Fin sp.n} {j0 : Nat} {tt : Time} {e : Node.Event N}
    (h : run.GroupAt prop dg y j0 tt e) :
    ∃ t j sg, j < 128 ∧ j0 = 1024 * t + 8 * j ∧ (segs t)[j]? = some sg ∧ sg.node = y ∧
      tt = (t : Int) ∧ sg.cuts ≠ [] ∧
      (exec prop dg y (sg.pre y) (t : Int) e).2[0]? = sg.cuts[0]? := by
  obtain ⟨hne, hk, hev⟩ := h
  have hlen := List.length_pos_of_ne_nil hne
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  rw [← List.getElem?_eq_getElem hlen] at hl0
  generalize hX : (exec prop dg y (run.state y j0) tt e).2 = X at hl0 hne hev
  rw [Nat.add_zero] at hn0 ht0 hl0
  have hl0' : run.label j0 ≠ none := by
    rw [hl0]; cases X with | nil => exact absurd rfl hne | cons _ _ => simp
  have hstart := label_start hl0'
  have hev0 := hev (8 * (j0 / 8)) (by
    rw [run_event_lab hstart, run_event_lab hl0']; congr 1; omega)
  have hm : j0 % 8 = 0 := by omega
  obtain ⟨t, j, k, hj, hk8, rfl⟩ := cut_decomp j0
  have hk0 : k = 0 := by omega
  subst hk0
  rw [run_label t j 0 hj (by omega)] at hl0
  rcases hs : (segs t)[j]? with _ | sg
  · rw [hs] at hl0; cases X with | nil => exact absurd rfl hne | cons _ _ => simp at hl0
  · rw [hs, Option.bind_some] at hl0
    have hny : sg.node = y := by
      rw [← hn0]; exact (run_node hj (by omega : 0 < 8) hs).symm
    have hst : run.state y (1024 * t + 8 * j + 0) = sg.pre y := by
      have := run_state_seg hj (by omega : 0 < 8) hs; rw [hny] at this; simpa using this
    have htt : tt = (t : Int) := by rw [← ht0]; exact run_time t j 0 hj (by omega)
    subst htt
    rw [hst] at hX
    refine ⟨t, j, sg, hj, rfl, hs, hny, rfl, ?_, ?_⟩
    · intro hc; rw [hc] at hl0; cases X with | nil => exact absurd rfl hne | cons _ _ => simp at hl0
    · rw [hX, hl0]


/-! ## The event of a group -/

/-- The key of a handler's first cut: the event, up to the input of a tick. -/
def headKey : Cut N → Option (Node.Event N)
  | .fg (.block B _) => some (.block B)
  | .fg (.attestation a) => some (.attestation a)
  | .fg (.attest _ _) => none
  | .ac ℓ =>
    match ℓ.call with
    | .tick => some (.tick 0)
    | .message m => some (.message m)
    | .restart => some .restart
    | _ => none

/-- An event up to the input of a tick. -/
def normEv : Node.Event N → Node.Event N
  | .tick _ => .tick 0
  | e => e

/-- A handler's first cut has the key of its event. -/
theorem headKey_exec (self : Fin sp.n) (st : St) (t : Time) (e : Node.Event N) {c : Cut N}
    {cs : List (Cut N)} (h : (exec prop dg self st t e).2 = c :: cs) :
    headKey c = some (normEv e) := by
  cases e with
  | tick x =>
    obtain ⟨ℓ, pc, uc, hℓ, hcs, -, -⟩ := Compose.tick_order prop dg self st t x
    change (onTick prop dg self st t x).2 = _ at h
    rw [hcs] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    simp [headKey, hℓ, normEv]
  | block B =>
    obtain ⟨acc, rfl⟩ := Simulation.exec_block_head prop dg self st t B h
    rfl
  | message m =>
    simp only [exec, onMessage, acCall] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl
  | attestation a =>
    simp only [exec, onAttestation] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl
  | restart =>
    simp only [exec, Node.restart, acCall] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl

/-- **The event of a group** is its segment's, up to a tick's input. -/
theorem groupAt_seg {y : Fin sp.n} {j0 : Nat} {tt : Time} {e : Node.Event N}
    (h : run.GroupAt prop dg y j0 tt e) :
    ∃ t j sg, j < 128 ∧ j0 = 1024 * t + 8 * j ∧ (segs t)[j]? = some sg ∧ sg.node = y ∧
      tt = (t : Int) ∧ normEv e = normEv sg.ev := by
  obtain ⟨t, j, sg, hj, rfl, hs, hny, rfl, hne, h0⟩ := groupAt_inv h
  refine ⟨t, j, sg, hj, rfl, hs, hny, rfl, ?_⟩
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hne
  have hcs := segs_cuts_eq hs
  rw [hc] at h0
  rcases hx : (exec prop dg y (sg.pre y) (t : Int) e).2 with _ | ⟨c', cs'⟩
  · rw [hx] at h0; cases h0
  · rw [hx] at h0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    have h1 := headKey_exec y _ _ e hx
    have h2 := headKey_exec sg.node (sg.pre sg.node) (t : Int) sg.ev (hcs.symm.trans hc)
    exact Option.some.inj (h1.symm.trans h2)

end Consensus.Goldilocks.Witness.TwoRun

end
