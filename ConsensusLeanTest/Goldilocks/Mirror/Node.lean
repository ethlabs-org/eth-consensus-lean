module
public import ConsensusLeanTest.Goldilocks.Mirror.ACStep
@[expose] public section

/-! # A computable mirror of the Goldilocks node: the restart and `Node.exec`

The last module of the mirror (`Goldilocks/Mirror/Setup`). A restart keeps the locks and
`latest_confirmed`, resets the rest, and replays the tree (genesis excluded) through
`ac_on_block`; at a time `t ≥ 0` the node is not joined then, so the replay only stamps every
replayed block with `t`, in any parent order (`acRestart_eq`, with `exists_parentOrder` for
`frameOf M`).

`NodeD` is the node data (FG data, AC data, whether the validator has signed its attestation),
`EvD` the events of the mirror (blocks by root), `CutD` the cuts with their observations, and
`execD` the handler on data. The main theorem `exec_interp`: at a node that never proposes, for
data with a parent-closed tree without repeats (`Frag`), a time `t ≥ 0` and a block event of a
table root, `Node.exec` of the interpretations is the interpretation of `execD`; `frag_execD`:
`execD` keeps `Frag`. The mirror is parametric in the replay order `ro`. -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA

namespace Fix

variable (X : Fix)

/-- The node data: FG data, AC data, and whether the validator has signed (its record). -/
structure NodeD where
  /-- The FG data. -/
  fg : X.FGD
  /-- The AC data. -/
  ac : X.ACD
  /-- Whether the validator has signed its attestation. -/
  signed : Bool

/-- The initial node data. -/
def NodeD.init : X.NodeD := ⟨FGD.init X, ACD.init X, false⟩

/-- An event of the mirror. -/
inductive EvD where
  /-- A tick with the input `x`. -/
  | tick (x : Nat)
  /-- The table block with root `r` is received. -/
  | block (r : Nat)
  /-- A vote is received. -/
  | message (v : X.V)
  /-- An attestation is received. -/
  | attestation (a : FG.Att X.sp.n)
  /-- The node wakes. -/
  | restart

/-- An AC call of the mirror. -/
inductive CallD where
  /-- `ac_on_tick`. -/
  | tick
  /-- `ac_to_fg`. -/
  | toFG
  /-- `ac_on_message`. -/
  | message (v : X.V)
  /-- `ac_on_block` of a root. -/
  | block (r : Nat)
  /-- `ac_restart`. -/
  | restart

/-- A cut of the mirror. -/
inductive CutD where
  /-- `fg_on_block` of a root, accepted or refused. -/
  | fgBlock (r : Nat) (accepted : Bool)
  /-- `fg_on_attestation`. -/
  | fgAtt (a : FG.Att X.sp.n)
  /-- `fg_attest` of a root with what it signed. -/
  | fgAttest (c : Nat) (signed : Option (FG.Att X.sp.n))
  /-- An AC call with the tree of its frame and its emissions. -/
  | ac (call : CallD X) (M : List Nat) (ems : List X.EmD)

/-- The fragment: the accepted tree is parent-closed and without repeats. -/
def Frag (d : X.NodeD) : Prop := X.Closed d.fg.tree ∧ d.fg.tree.Nodup

instance (d : X.NodeD) : Decidable (X.Frag d) := inferInstanceAs (Decidable (_ ∧ _))

/-- The events the mirror covers: a block event names a table root. -/
def EvD.OK : X.EvD → Prop
  | .block r => r ∈ X.roots
  | _ => True

instance (e : X.EvD) : Decidable (EvD.OK X e) := by
  cases e <;> unfold EvD.OK <;> infer_instance

variable {X}

/-- The AC data after a restart at `t` with the tree `M`. -/
def ACD.restart (a : X.ACD) (M : List Nat) (t : Int) : X.ACD :=
  { (ACD.init X) with
    locks := a.locks, lc := a.lc, rst := some t
    bs := (M.filter (fun r => decide (r ≠ X.g))).map (fun r => (r, t)) }

/-- The handler of an event at validator `self` and time `t`, on data. -/
def execD (d : X.NodeD) (self : Fin X.sp.n) (t : Int) : X.EvD → X.NodeD × List (CutD X)
  | .tick _ =>
    let r₁ := d.ac.onTick self d.fg.tree t
    let r₂ := r₁.1.toFG d.fg.tree t
    let d₂ : X.NodeD := ⟨d.fg, r₂.1, d.signed⟩
    let cs : List (CutD X) := [.ac .tick d.fg.tree r₁.2, .ac .toFG d.fg.tree []]
    match r₂.2 with
    | none => (d₂, cs)
    | some c =>
      match X.attestD d.signed self with
      | none => (d₂, cs ++ [.fgAttest c none])
      | some a => (⟨d.fg.onAtt a, r₂.1, true⟩, cs ++ [.fgAttest c (some a), .fgAtt a])
  | .block r =>
    if slotT t < X.slotR r then (d, [])
    else
      match d.fg.onBlock r with
      | none => (d, [.fgBlock r false])
      | some fg' =>
        let r₁ := d.ac.onBlk self fg'.tree t r
        (⟨fg', r₁.1, d.signed⟩, [.fgBlock r true, .ac (.block r) fg'.tree r₁.2])
  | .message v =>
    let r₁ := d.ac.onMsg self d.fg.tree t v
    (⟨d.fg, r₁.1, d.signed⟩, [.ac (.message v) d.fg.tree r₁.2])
  | .attestation a => (⟨d.fg.onAtt a, d.ac, d.signed⟩, [.fgAtt a])
  | .restart => (⟨d.fg, d.ac.restart d.fg.tree t, d.signed⟩, [.ac .restart d.fg.tree []])

/-! ## The restart -/

variable {M : List Nat}

/-- The roots of `M` other than genesis, by depth. -/
def ordD (X : Fix) (M : List Nat) : List Nat :=
  (M.filter (fun r => decide (r ≠ X.g))).mergeSort
    (fun a b => decide ((X.chain a).length ≤ (X.chain b).length))

theorem exists_parentOrder (hX : X.OK) (hM : X.Closed M) (hnd : M.Nodup) :
    ∃ l, ParentOrderAt X.g (X.frameOf M) l := by
  have hperm := List.mergeSort_perm (M.filter (fun r => decide (r ≠ X.g)))
    (fun a b => decide ((X.chain a).length ≤ (X.chain b).length))
  have hmem : ∀ r, r ∈ ordD X M ↔ r ∈ M ∧ r ≠ X.g := by
    intro r; rw [ordD, hperm.mem_iff]; simp
  have hnd' : (ordD X M).Nodup := hperm.nodup_iff.2 (hnd.filter _)
  have hsort := List.pairwise_mergeSort (l := M.filter (fun r => decide (r ≠ X.g)))
    (le := fun a b => decide ((X.chain a).length ≤ (X.chain b).length))
    (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
  have hv : ∀ r ∈ ordD X M, X.Valid r := fun r hr => hM.valid r ((hmem r).1 hr).1
  refine ⟨(ordD X M).map X.blk, hnd'.map_on fun a ha b hb h => blk_inj (hv a ha) (hv b hb) h,
    fun B => ?_, fun i j hi hj h => ?_⟩
  · simp only [List.mem_map, hmem]
    constructor
    · rintro ⟨r, ⟨hr, hg⟩, rfl⟩
      exact ⟨blk_mem_T hr, by rwa [blk_root (hM.valid r hr)]⟩
    · rintro ⟨hB, hg⟩
      obtain ⟨hm, e⟩ := root_mem_of_T hM hB
      exact ⟨B.root, ⟨hm, hg⟩, e.symm⟩
  · simp only [List.length_map] at hi hj
    simp only [List.getElem_map] at h
    set a := (ordD X M)[i]
    set b := (ordD X M)[j]
    have ha : a ∈ ordD X M := List.getElem_mem hi
    have hb : b ∈ ordD X M := List.getElem_mem hj
    have ham := mem_roots_of_valid (hv a ha) ((hmem a).1 ha).2
    rw [blk_parent_of_mem ham, blk_root (hv b hb)] at h
    have hpb : X.par a = b := Option.some_injective _ h
    have hlen : (X.chain b).length < (X.chain a).length := by
      rw [chain_par hX ham, hpb]; simp
    by_contra hji
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hji) with hij | hij
    · have := List.pairwise_iff_getElem.1 hsort i j hi hj hij
      simp only [decide_eq_true_eq] at this
      exact absurd this (Nat.not_le.2 hlen)
    · subst hij
      exact par_ne hX ham hpb

theorem joinedB_restart (a : X.ACD) (t : Int) (ht : 0 ≤ t) :
    (a.restart M t).joinedB t = false := by
  change decide (t ≤ 4 * ((slotT t : Int) - 1)) = false
  have h : ((t / 4).toNat : Int) = t / 4 := Int.toNat_of_nonneg (by omega)
  simp only [decide_eq_false_iff_not, not_le, slotT, h]
  omega

theorem stamp_rst (a : X.ACD) (r : Nat) (t : Int) : (a.stamp r t).rst = a.rst := rfl

/-- A stamp list whose times are all `t` gives `t` to its roots. -/
theorem stampB_const {a : X.ACD} {t : Int} (h : ∀ p ∈ a.bs, p.2 = t) (r : Nat) :
    a.stampB r = if r ∈ a.bs.map Prod.fst then ETime.of t else if r = X.g then ⊥ else ⊤ := by
  unfold ACD.stampB
  cases hf : a.bs.find? (fun p => decide (p.1 = r)) with
  | none =>
    have : r ∉ a.bs.map Prod.fst := by
      rw [List.find?_eq_none] at hf
      intro hmem
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hmem
      exact hf p hp (by simp)
    simp [this]
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hr : p.1 = r := by simpa using List.find?_some hf
    have : r ∈ a.bs.map Prod.fst := List.mem_map.2 ⟨p, hp, hr⟩
    simp [this, h p hp]

theorem replay_fold (hX : X.OK) (hM : X.Closed M) (hnd : M.Nodup) (self : Fin X.sp.n) (t : Int)
    (l : List X.Blk) (hl : ∀ B ∈ l, B ∈ X.T M) :
    ∀ (b : X.ACD), b.joinedB t = false →
      l.foldl (fun acc B => let r := acOnBlock X.sp self acc.1 (X.frameOf M) t B;
        (r.1, acc.2 ++ r.2)) (b.interp, []) =
        ((l.foldl (fun b B => b.stamp B.root t) b).interp, []) := by
  induction l with
  | nil => intro b _; rfl
  | cons B l ih =>
    intro b hb
    obtain ⟨hm, e⟩ := root_mem_of_T hM (hl B List.mem_cons_self)
    simp only [List.foldl_cons]
    rw [e, acOnBlock_eq hX hM hnd b self t (hM.valid _ hm), onBlk_unjoined hb, ← e]
    exact ih (fun B hB => hl B (List.mem_cons_of_mem _ hB)) _ hb

theorem foldl_stamp_bs (l : List X.Blk) (b : X.ACD) (t : Int) :
    (l.foldl (fun b B => b.stamp B.root t) b).bs =
      (l.map (fun B => (B.root, t))).reverse ++ b.bs := by
  induction l generalizing b with
  | nil => rfl
  | cons B l ih => rw [List.foldl_cons, ih]; simp [ACD.stamp]

theorem foldl_stamp_other (l : List X.Blk) (b : X.ACD) (t : Int) :
    l.foldl (fun b B => b.stamp B.root t) b =
      { b with bs := (l.foldl (fun b B => b.stamp B.root t) b).bs } := by
  induction l generalizing b with
  | nil => rfl
  | cons B l ih => rw [List.foldl_cons, ih]; rfl

theorem acRestart_eq (hX : X.OK) (hM : X.Closed M) (hnd : M.Nodup)
    (ro : ReplayOrder X.sp (List (FG.Att X.sp.n))) (self : Fin X.sp.n) (a : X.ACD) {t : Int}
    (ht : 0 ≤ t) :
    acRestart X.sp ro self a.interp (X.frameOf M) t = ((a.restart M t).interp, []) := by
  have hpo := ro.parentOrder t (X.frameOf M) (exists_parentOrder hX hM hnd)
  set l := ro.order t (X.frameOf M)
  have hlmem : ∀ B, B ∈ l ↔ B ∈ X.T M ∧ B.root ≠ X.g := hpo.2.1
  set b₀ : X.ACD := { (ACD.init X) with locks := a.locks, lc := a.lc, rst := some t }
  have hA' : ({ (SAState.initial X.sp.genesisRoot) with
      locks := a.interp.locks, latestConfirmed := a.interp.latestConfirmed
      restartTime := (t : WithBot Time) } : SAState X.sp.n) = b₀.interp := by
    rw [← ACD.interp_init]; rfl
  have hb₀ : b₀.joinedB t = false := joinedB_restart (M := []) a t ht
  unfold acRestart
  dsimp only
  rw [hA', replay_fold hX hM hnd self t l (fun B hB => ((hlmem B).1 hB).1) b₀ hb₀]
  congr 1
  rw [foldl_stamp_other]
  refine sastate_ext rfl rfl ?_ rfl rfl rfl rfl rfl rfl
  funext r
  simp only [interp_blockStamp]
  rw [stampB_const (t := t), stampB_const (t := t)]
  · congr 1
    simp only [foldl_stamp_bs, ACD.restart, ACD.init, List.append_nil, List.map_reverse,
      List.map_map, List.mem_reverse, List.mem_map, List.mem_filter, decide_eq_true_eq, b₀,
      Function.comp_def]
    refine propext ⟨?_, ?_⟩
    · rintro ⟨B, hB, rfl⟩
      obtain ⟨hBT, hg⟩ := (hlmem B).1 hB
      exact ⟨B.root, ⟨(root_mem_of_T hM hBT).1, hg⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hg⟩, rfl⟩
      refine ⟨X.blk r, (hlmem _).2 ⟨blk_mem_T hr, ?_⟩, ?_⟩ <;>
        simp [blk_root (hM.valid r hr), hg]
  · intro p hp; simp only [ACD.restart, List.mem_map] at hp; obtain ⟨_, -, rfl⟩ := hp; rfl
  · intro p hp
    simp only [foldl_stamp_bs, b₀, ACD.init, List.append_nil, List.mem_reverse,
      List.mem_map] at hp
    obtain ⟨_, -, rfl⟩ := hp; rfl

/-! ## `Node.exec` -/

variable (X) in
/-- The node's AC: the Goldilocks SA with the replay order `ro`. -/
noncomputable abbrev AC (ro : ReplayOrder X.sp (List (FG.Att X.sp.n))) : NodeAC X.sp.toParams :=
  goldilocksSA X.sp (List (FG.Att X.sp.n)) ro

variable (ro : ReplayOrder X.sp (List (FG.Att X.sp.n)))

/-- The node state of the data. -/
def NodeD.interp (d : X.NodeD) : NodeState (X.AC ro) := ⟨d.fg.interp, d.ac.interp, X.recI d.signed⟩

/-- The event of the mirror's event. -/
def EvD.interp : X.EvD → Node.Event (X.AC ro)
  | .tick x => .tick x
  | .block r => .block (X.blk r)
  | .message v => .message v
  | .attestation a => .attestation a
  | .restart => .restart

/-- The AC call of the mirror's call. -/
def CallD.interp : CallD X → (X.AC ro).Call
  | .tick => .tick
  | .toFG => .toFG
  | .message v => .message v
  | .block r => .block (X.blk r)
  | .restart => .restart

/-- The cut of the mirror's cut. -/
def CutD.interp : CutD X → Cut (X.AC ro)
  | .fgBlock r b => .fg (.block (X.blk r) b)
  | .fgAtt a => .fg (.attestation a)
  | .fgAttest c s => .fg (.attest (X.blk c) s)
  | .ac call M ems => .ac ⟨call.interp ro, X.frameOf M, ems.map EmD.interp⟩

/-- The interpretation of a handler's result. -/
def resN (r : X.NodeD × List (CutD X)) : NodeState (X.AC ro) × List (Cut (X.AC ro)) :=
  (r.1.interp ro, r.2.map (CutD.interp ro))

theorem NodeD.interp_init (hX : X.OK) : (NodeD.init X).interp ro = Node.init (X.AC ro) := by
  simp only [NodeD.interp, NodeD.init, Node.init, ACD.interp_init, recI_false]
  congr 1
  exact Fix.interp_init hX

@[simp] theorem NodeD.interp_fg (d : X.NodeD) : (d.interp ro).fg = d.fg.interp := rfl
@[simp] theorem NodeD.interp_ac (d : X.NodeD) : (d.interp ro).ac = d.ac.interp := rfl
@[simp] theorem NodeD.interp_record (d : X.NodeD) : (d.interp ro).record = X.recI d.signed := rfl

theorem frame_interp (hX : X.OK) {d : X.NodeD} (hF : X.Frag d) :
    Node.frame (d.interp ro) = X.frameOf d.fg.tree := toFrame_interp hX hF.1

theorem exec_interp (hX : X.OK) (proposer : Nat → Fin X.sp.n)
    (dg : Digest (List (FG.Att X.sp.n)) (Payload X.sp.n)) (self : Fin X.sp.n)
    (hprop : ∀ s, proposer s ≠ self) {d : X.NodeD} (hF : X.Frag d) {t : Int} (ht : 0 ≤ t)
    {e : X.EvD} (he : e.OK) :
    Node.exec proposer dg self (d.interp ro) t (e.interp ro) = resN ro (execD d self t e) := by
  cases e with
  | attestation a =>
    simp only [EvD.interp, Node.exec, Node.onAttestation, execD, resN, NodeD.interp,
      onAtt_interp, List.map_cons, List.map_nil, CutD.interp]
  | message v =>
    simp only [EvD.interp, Node.exec, Node.onMessage, Node.acCall, frame_interp ro hX hF, execD,
      resN, List.map_cons, List.map_nil, CutD.interp, CallD.interp, ACInterface.step]
    rw [show (d.interp ro).ac = d.ac.interp from rfl, acOnMessage_eq hX hF.1 hF.2]
    rfl
  | restart =>
    simp only [EvD.interp, Node.exec, Node.restart, Node.acCall, frame_interp ro hX hF, execD,
      resN, List.map_cons, List.map_nil, CutD.interp, CallD.interp, ACInterface.step]
    rw [show (d.interp ro).ac = d.ac.interp from rfl, acRestart_eq hX hF.1 hF.2 ro self _ ht]
    rfl
  | block r =>
    have hr : r ∈ X.roots := he
    have hs : X.sp.toParams.slotOf t = slotT t := slot_eq t
    simp only [EvD.interp, Node.exec, Node.onBlock, execD, hs, blk_slot]
    by_cases h1 : slotT t < X.slotR r
    · simp only [h1, ↓reduceIte, resN, List.map_nil]
    simp only [h1, ↓reduceIte, NodeD.interp_fg, onBlock_interp hX hF.1 hr]
    cases h : d.fg.onBlock r with
    | none => simp only [Option.map_none, resN, List.map_cons, List.map_nil, CutD.interp]
    | some fg' =>
      have hr1 : r ∉ d.fg.tree ∧ X.par r ∈ d.fg.tree := by
        unfold FGD.onBlock at h; split_ifs at h with hc
        · exact not_or.1 hc |>.imp id not_not.1
      have hfg : fg' = ⟨r :: d.fg.tree, d.fg.atts⟩ := by
        unfold FGD.onBlock at h
        rw [ite_eq_right (by tauto)] at h
        exact (Option.some_injective _ h).symm
      have hM' : X.Closed fg'.tree := hfg ▸ closed_cons hF.1 hr hr1.2
      have hnd' : fg'.tree.Nodup := hfg ▸ List.nodup_cons.2 ⟨hr1.1, hF.2⟩
      simp only [Option.map_some, Node.acCall, Node.frame, toFrame_interp hX hM', ACInterface.step]
      rw [NodeD.interp_ac, acOnBlock_eq hX hM' hnd' _ self t (Or.inr hr)]
      rfl
  | tick x =>
    have hP : ¬ Node.Proposes proposer self t := fun h => hprop _ h.2.2
    simp only [EvD.interp, Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, List.foldl_cons,
      List.foldl_nil, Node.tickStep, Node.acCall, Node.acToFG, Node.frame, ACInterface.step,
      hP, ↓reduceIte, NodeD.interp_fg, NodeD.interp_ac, toFrame_interp hX hF.1, execD]
    rw [acOnTick_eq hX hF.1 hF.2]
    simp only [resI, acToFG_eq hX hF.1, resF, NodeD.interp_record]
    cases h : ((d.ac.onTick self d.fg.tree t).1.toFG d.fg.tree t).2 with
    | none =>
      simp only [Option.map_none, resN, List.nil_append, List.append_nil, List.cons_append,
        List.map_cons, List.map_nil, CutD.interp, CallD.interp]
      rfl
    | some c =>
      simp only [Option.map_some, Node.attest, attest_interp hX]
      cases ha : X.attestD d.signed self with
      | none =>
        simp only [Option.map_none, resN, List.nil_append, List.append_nil, List.cons_append,
          List.map_cons, List.map_nil, CutD.interp, CallD.interp]
        rfl
      | some a =>
        simp only [Option.map_some, Node.onAttestation, resN, List.nil_append, List.append_nil,
          List.cons_append, List.map_cons, List.map_nil, CutD.interp, CallD.interp, onAtt_interp]
        rfl

theorem onAtt_tree (f : X.FGD) (a : FG.Att X.sp.n) : (f.onAtt a).tree = f.tree := by
  unfold FGD.onAtt; split_ifs <;> rfl

/-- `execD` keeps the fragment. -/
theorem frag_execD {d : X.NodeD} (hF : X.Frag d) (self : Fin X.sp.n) (t : Int) {e : X.EvD}
    (he : e.OK) : X.Frag (execD d self t e).1 := by
  cases e with
  | tick x =>
    simp only [execD]
    split
    · exact hF
    · split
      · exact hF
      · simpa [Frag, onAtt_tree] using hF
  | block r =>
    have hr : r ∈ X.roots := he
    simp only [execD]
    split_ifs
    · exact hF
    · cases h : d.fg.onBlock r with
      | none => exact hF
      | some fg' =>
        unfold FGD.onBlock at h
        split_ifs at h with hc
        cases h
        obtain ⟨h1, h2⟩ := not_or.1 hc
        exact ⟨closed_cons hF.1 hr (not_not.1 h2), List.nodup_cons.2 ⟨h1, hF.2⟩⟩
  | message v => exact hF
  | attestation a => simpa [execD, Frag, onAtt_tree] using hF
  | restart => exact hF

end Fix

end Consensus.Goldilocks.Test.HalfCommittee

end
