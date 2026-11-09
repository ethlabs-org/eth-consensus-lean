module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WriteModes.Writes

@[expose] public section

/-! # SA traces with the unlock given per call and the writes of a mode (definitions)

The vocabulary of the lock-rule interface's traces, which the H.1 settings with the unlock given
(`Milestones/Statements/Healing/ACU`) read; its laws are in `Lemmas/AC/RelTrace`.

* the SA's handlers with the locks after the unlock given as an argument (`tryVoteWith`,
  `acProposalWith`, `acOnTickWith`, `acOnMessageWith`, `acOnBlockWith`, the call `stepWith`), and
  the same with the writes of a write mode (`tryVoteWithM` … `stepWithM`);
* the **unlock input** of a call (`callInput`, `callView`, at a mode `callInputM`, `callViewM`)
  and the parent's locks after its unlock (`parentUnlock`);
* **the unlock relation** (`UnlockRel`) and the parent's unlock oracle of a trace
  (`parentOracle`);
* the same handlers with the head walk from a given **start** in place of `get_anchor`
  (`StartFn`, `parentStartFn`, `getHeadFrom`, `tryVoteWithMS` … `stepWithMS`);
* **the trace law over a step family** (`ACLocalRunStep m u step`): the AC trace contract with
  each honest call `i` executing `step i` at the locks `u i`, related to the call's unlock input by
  `UnlockRel`; its parent instance (`ACLocalRunU m u`, each call executing `stepWithM m`) and its
  instance from the starts `st` (`ACLocalRunUS m u st`, each call `i` walking from `st i`); the
  reachable states (`ReachableAtU`) and the runs with the honest-object facts (`ACRunU`,
  `ACRunUS`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

variable (sp) in
open Classical in
/-- The parent's `try_vote` at `self`, with `L₁` as the locks after its unlock (for `s > 0`). -/
noncomputable abbrev tryVoteWith (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (A, [])
  else
    let V := mergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := L₁ } else A
    let dom := voteDomain sp A₁ Φ s
    let H := getHead sp A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let A₃ := optimisticConfirmation sp (admitVote sp A₂ t vote) Φ t
    (A₃, [{ msg := vote, readPoint := A₂,
            head := some { head := H, start := getAnchor sp A₁ Φ t, dom := dom } }])

variable (sp) in
open Classical in
/-- The parent's `ac_proposal`, with `L₁` as the locks after its unlock. -/
noncomputable abbrev acProposalWith (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : SAState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp A t then (A, none)
  else
    let s : Int := sp.slot t
    let p := voteViewList A Φ (s - 1) ⊤
    let V := View.ofLists p
    let A₁ := { A with locks := L₁ }
    let H := getHead sp A₁ Φ t (Φ.viableTree Φ.tree) V (s - 1)
    (A₁, some (⟨H, getAnchor sp A₁ Φ t, Φ.tree⟩, p))

variable (sp) in
open Classical in
/-- The parent's `ac_on_tick` at `self`, with `L₁` as the locks after the unlock of its vote. -/
noncomputable abbrev acOnTickWith (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVoteWith sp self L₁ A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmation sp r.1 Φ t (s - 1)
      else r.1
    (A₂, r.2)

variable (sp) in
/-- The parent's `ac_on_message` at `self`, with `L₁` as the locks after the unlock. -/
noncomputable abbrev acOnMessageWith (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) : SAState sp.n × List (Em sp FGP) :=
  tryVoteWith sp self L₁ (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ t

variable (sp) in
/-- The parent's `ac_on_block` at `self`, with `L₁` as the locks after the unlock. -/
noncomputable abbrev acOnBlockWith (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) : SAState sp.n × List (Em sp FGP) :=
  tryVoteWith sp self L₁ (optimisticConfirmation sp (blockReceipt sp A t B) Φ t) Φ t

variable (sp) in
/-- A call of the SA at `self` with `L₁` as the locks after its unlock (`ac_to_fg` and the
restart are the parent's: neither unlocks). -/
noncomputable abbrev stepWith (ro : ReplayOrder sp FGP) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → SAState sp.n × List (Em sp FGP)
  | .tick => acOnTickWith sp self L₁ A Φ t
  | .proposal => ((acProposalWith sp L₁ A Φ t).1, [])
  | .toFG => ((acToFG sp A Φ t).1, [])
  | .message m => acOnMessageWith sp self L₁ A Φ t m
  | .block B => acOnBlockWith sp self L₁ A Φ t B
  | .restart => acRestart sp ro self A Φ t

variable (sp) in
/-- The state whose locks the unlock of the call `c` reads: the state `try_vote` receives (after
the receipt and the optimistic confirmation of a message or a block), else the state itself. -/
noncomputable abbrev callInput {ro : ReplayOrder sp FGP} (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (goldilocksSA sp FGP ro).Call → SAState sp.n
  | .message v => optimisticConfirmation sp (admitVote sp A t v) Φ t
  | .block C => optimisticConfirmation sp (blockReceipt sp A t C) Φ t
  | _ => A

variable (sp) in
/-- The view the unlock of the call `c` reads (the pool view in `ac_proposal`, else the merged
vote view of the call's input). -/
noncomputable abbrev callView {ro : ReplayOrder sp FGP} (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksSA sp FGP ro).Call) : View sp.n :=
  match c with
  | .proposal => View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤)
  | _ => mergedVoteView sp (callInput sp A Φ t c) Φ (sp.slot t)

variable (sp) in
/-- The parent's locks after the unlock of the call `c`. -/
noncomputable abbrev parentUnlock {ro : ReplayOrder sp FGP} (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksSA sp FGP ro).Call) : Set Lock :=
  unlock sp (callInput sp A Φ t c).locks Φ t ((sp.slot t : Int) - 1) (callView sp A Φ t c)

variable (sp) in
open Classical in
/-- `tryVoteWith` with the optimistic confirmation of mode `m`. -/
noncomputable abbrev tryVoteWithM (m : WriteMode) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (A, [])
  else
    let V := mergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := L₁ } else A
    let dom := voteDomain sp A₁ Φ s
    let H := getHead sp A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let A₃ := optimisticConfirmationM sp m (admitVote sp A₂ t vote) Φ t
    (A₃, [{ msg := vote, readPoint := A₂,
            head := some { head := H, start := getAnchor sp A₁ Φ t, dom := dom } }])

variable (sp) in
open Classical in
/-- `acOnTickWith` with the writes of mode `m`. -/
noncomputable abbrev acOnTickWithM (m : WriteMode) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVoteWithM sp m self L₁ A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmationM sp m r.1 Φ t (s - 1)
      else r.1
    (A₂, r.2)

variable (sp) in
/-- `acOnMessageWith` with the writes of mode `m`. -/
noncomputable abbrev acOnMessageWithM (m : WriteMode) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) :
    SAState sp.n × List (Em sp FGP) :=
  tryVoteWithM sp m self L₁ (optimisticConfirmationM sp m (admitVote sp A t v) Φ t) Φ t

variable (sp) in
/-- `acOnBlockWith` with the writes of mode `m`. -/
noncomputable abbrev acOnBlockWithM (m : WriteMode) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) :
    SAState sp.n × List (Em sp FGP) :=
  tryVoteWithM sp m self L₁ (optimisticConfirmationM sp m (blockReceipt sp A t B) Φ t) Φ t

variable (sp) in
/-- A call of the SA at `self` with `L₁` as the locks after its unlock and the writes of mode `m`
(`ac_to_fg` and the restart are the parent's). -/
noncomputable abbrev stepWithM (ro : ReplayOrder sp FGP) (m : WriteMode) (self : Fin sp.n)
    (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → SAState sp.n × List (Em sp FGP)
  | .tick => acOnTickWithM sp m self L₁ A Φ t
  | .proposal => ((acProposalWith sp L₁ A Φ t).1, [])
  | .toFG => ((acToFG sp A Φ t).1, [])
  | .message v => acOnMessageWithM sp m self L₁ A Φ t v
  | .block B => acOnBlockWithM sp m self L₁ A Φ t B
  | .restart => acRestart sp ro self A Φ t

variable (sp) in
/-- The state whose locks the unlock of the call `c` reads at mode `m` (`callInput`). -/
noncomputable abbrev callInputM {ro : ReplayOrder sp FGP} (m : WriteMode) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : (goldilocksSA sp FGP ro).Call → SAState sp.n
  | .message v => optimisticConfirmationM sp m (admitVote sp A t v) Φ t
  | .block C => optimisticConfirmationM sp m (blockReceipt sp A t C) Φ t
  | _ => A

variable (sp) in
/-- The view the unlock of the call `c` reads at mode `m` (`callView`). -/
noncomputable abbrev callViewM {ro : ReplayOrder sp FGP} (m : WriteMode) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call) : View sp.n :=
  match c with
  | .proposal => View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤)
  | _ => mergedVoteView sp (callInputM sp m A Φ t c) Φ (sp.slot t)

variable (sp) in
/-- **The unlock relation**: every lock of `L'` is a live lock of `L` on a block `B` of the tree,
with its slot, fast bit and expiry, on an ancestor (in the tree) of the unlock target of
`B`'s viable ancestor when its slot is below `s`, and on that viable ancestor otherwise. -/
abbrev UnlockRel (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Int) (V : View sp.n)
    (L' : Set Lock) : Prop :=
  ∀ l' ∈ L', ∃ l ∈ L, ∃ B ∈ Φ.tree, B.root = l.block ∧ l.LiveAt sp t ∧ l'.slot = l.slot ∧
    l'.fast = l.fast ∧ l'.expiry = l.expiry ∧
    ((l.slot : Int) < s → ∃ Y ∈ Φ.tree, Y.root = l'.block ∧
      Φ.Anc Y (unlockTarget sp Φ V s (Φ.viableAncestor B))) ∧
    (s ≤ (l.slot : Int) → l'.block = (Φ.viableAncestor B).root)

variable (sp) in
/-- The parent's unlock oracle of a trace: at each labelled cut, the parent's locks after the
unlock of the call at the pre-state. -/
noncomputable abbrev parentOracle {ro : ReplayOrder sp FGP} (tr : SATrace sp FGP ro) (i : Nat) :
    Set Lock :=
  match tr.label i with
  | some ℓ => parentUnlock sp (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call
  | none => ∅

variable (sp) (FGP) in
/-- A **start function**: the block a head walk starts from, given the state after the unlock, the
frame, the time, the walk's view and its label. Generic: it carries no rule of its own, and the
parent's start (`parentStartFn`, `get_anchor`) is one instance. -/
abbrev StartFn := SAState sp.n → Frm sp.n FGP → Time → View sp.n → Int → Blk sp.n FGP

variable (sp) in
/-- The parent's start: `get_anchor`, for every view and label. -/
noncomputable abbrev parentStartFn : StartFn sp FGP := fun A Φ t _ _ => getAnchor sp A Φ t

variable (sp) in
/-- The head walk of `getHead` from the start `a` in place of `get_anchor`. -/
noncomputable abbrev getHeadFrom (a : Blk sp.n FGP) (Φ : Frm sp.n FGP) (t : Time)
    (tree : Set (Blk sp.n FGP)) (V : View sp.n) (s : Int) : Blk sp.n FGP :=
  ghost sp tree (goldfishScore sp Φ V s) (goldfishEligible sp Φ t V s) Φ.tree.ncard a

variable (sp) in
open Classical in
/-- `tryVoteWithM` with the head walk from the start `st`. -/
noncomputable abbrev tryVoteWithMS (m : WriteMode) (st : StartFn sp FGP) (self : Fin sp.n)
    (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (A, [])
  else
    let V := mergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := L₁ } else A
    let dom := voteDomain sp A₁ Φ s
    let a := st A₁ Φ t V ((s : Int) - 1)
    let H := getHeadFrom sp a Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let A₃ := optimisticConfirmationM sp m (admitVote sp A₂ t vote) Φ t
    (A₃, [{ msg := vote, readPoint := A₂,
            head := some { head := H, start := a, dom := dom } }])

variable (sp) in
open Classical in
/-- `acProposalWith` with the head walk from the start `st`. -/
noncomputable abbrev acProposalWithS (st : StartFn sp FGP) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp A t then (A, none)
  else
    let s : Int := sp.slot t
    let p := voteViewList A Φ (s - 1) ⊤
    let V := View.ofLists p
    let A₁ := { A with locks := L₁ }
    let a := st A₁ Φ t V (s - 1)
    let H := getHeadFrom sp a Φ t (Φ.viableTree Φ.tree) V (s - 1)
    (A₁, some (⟨H, a, Φ.tree⟩, p))

variable (sp) in
open Classical in
/-- `acOnTickWithM` with the head walk from the start `st`. -/
noncomputable abbrev acOnTickWithMS (m : WriteMode) (st : StartFn sp FGP) (self : Fin sp.n)
    (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVoteWithMS sp m st self L₁ A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmationM sp m r.1 Φ t (s - 1)
      else r.1
    (A₂, r.2)

variable (sp) in
/-- `acOnMessageWithM` with the head walk from the start `st`. -/
noncomputable abbrev acOnMessageWithMS (m : WriteMode) (st : StartFn sp FGP) (self : Fin sp.n)
    (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) :
    SAState sp.n × List (Em sp FGP) :=
  tryVoteWithMS sp m st self L₁ (optimisticConfirmationM sp m (admitVote sp A t v) Φ t) Φ t

variable (sp) in
/-- `acOnBlockWithM` with the head walk from the start `st`. -/
noncomputable abbrev acOnBlockWithMS (m : WriteMode) (st : StartFn sp FGP) (self : Fin sp.n)
    (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) :
    SAState sp.n × List (Em sp FGP) :=
  tryVoteWithMS sp m st self L₁ (optimisticConfirmationM sp m (blockReceipt sp A t B) Φ t) Φ t

variable (sp) in
/-- `stepWithM` with the head walk from the start `st`; at `parentStartFn` it is `stepWithM`
(`stepWithMS_parentStartFn`). -/
noncomputable abbrev stepWithMS (ro : ReplayOrder sp FGP) (m : WriteMode) (st : StartFn sp FGP)
    (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → SAState sp.n × List (Em sp FGP)
  | .tick => acOnTickWithMS sp m st self L₁ A Φ t
  | .proposal => ((acProposalWithS sp st L₁ A Φ t).1, [])
  | .toFG => ((acToFG sp A Φ t).1, [])
  | .message v => acOnMessageWithMS sp m st self L₁ A Φ t v
  | .block B => acOnBlockWithMS sp m st self L₁ A Φ t B
  | .restart => acRestart sp ro self A Φ t

/-- **The AC trace contract with the unlock given by `u`, the writes of mode `m` and the step
family `step`**: `ACLocalRun` of the SA, except that each honest call `i` executes `step i` at the
locks `u i`, which the unlock relation ties to the call's unlock input. Its instances are the
parent's (`ACLocalRunU`) and the one from the starts `st` (`ACLocalRunUS`). -/
structure ACLocalRunStep {ro : ReplayOrder sp FGP} (m : WriteMode) (u : Nat → Set Lock)
    (step : Nat → Fin sp.n → Set Lock → SAState sp.n → Frm sp.n FGP → Time →
      (goldilocksSA sp FGP ro).Call → SAState sp.n × List (Em sp FGP))
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) : Prop where
  /-- `U` is coherent: roots injective, slots increasing along parent edges. -/
  coherent : Coherent U
  /-- Each honest node starts from the initial AC state. -/
  init : ∀ y ∈ H, tr.init y = (goldilocksSA sp FGP ro).initial
  /-- Each call `i` of an honest node executes `step i` at the locks `u i`. -/
  exec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H →
    step i (tr.node i) (u i) (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call =
      (tr.post i, ℓ.emits)
  /-- The locks `u i` are related to the call's unlock input. -/
  lawful : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H → FrameOK ℓ.frame →
    UnlockRel sp (callInputM sp m (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call).locks
      ℓ.frame (tr.time i) ((sp.slot (tr.time i) : Int) - 1)
      (callViewM sp m (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call) (u i)
  /-- The frame law and the input contract (`ACLocalRun.frameLaw`). -/
  frameLaw : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ →
    (tr.NoCallBetween y 0 i ∧ ∃ Φ₀, (goldilocksSA sp FGP ro).InitialFrame Φ₀ ∧
      (goldilocksSA sp FGP ro).FrameIn U Φ₀ ∧
      (goldilocksSA sp FGP ro).CallOK U Φ₀ (tr.time i) ℓ.call ℓ.frame) ∨
    (∃ j ℓ', j < i ∧ tr.CallAt y j ℓ' ∧ tr.NoCallBetween y (j + 1) i ∧
      (goldilocksSA sp FGP ro).CallOK U ℓ'.frame (tr.time i) ℓ.call ℓ.frame)
  /-- Cuts are at times from `0` on. -/
  time_nonneg : ∀ i, 0 ≤ tr.time i
  /-- The cut order is by time. -/
  time_mono : Monotone tr.time
  /-- An honest node is called only while awake. -/
  awake_of_call : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → tr.awake y (tr.time i)
  /-- The first call of an honest node after it was asleep is a restart. -/
  restart_of_sleep : ∀ y ∈ H, ∀ i ℓ (u : Time), tr.CallAt y i ℓ → 0 ≤ u → u < tr.time i →
    ¬ tr.awake y u → (∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u) → ℓ.call = .restart
  /-- A wake is a restart. -/
  restart_at_wake : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v → ¬ tr.awake y u → tr.awake y v →
    ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  /-- A restart is a wake. -/
  sleep_of_restart : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ℓ.call = .restart →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧
      ∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u

/-- **The AC trace contract with the unlock given by `u` and the writes of mode `m`**: each honest
call executes `stepWithM m` at the locks `u i` (`ACLocalRunStep` at the parent's call). -/
abbrev ACLocalRunU {ro : ReplayOrder sp FGP} (m : WriteMode) (u : Nat → Set Lock)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) : Prop :=
  ACLocalRunStep m u (fun _ => stepWithM sp ro m) H U tr

/-- **The AC trace contract from the starts `st`**: each honest call `i` executes `stepWithMS m`
with its head walks from `st i`; at `parentStartFn` it is `ACLocalRunU`
(`acLocalRunUS_parentStartFn`). -/
abbrev ACLocalRunUS {ro : ReplayOrder sp FGP} (m : WriteMode) (u : Nat → Set Lock)
    (st : Nat → StartFn sp FGP) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (tr : SATrace sp FGP ro) : Prop :=
  ACLocalRunStep m u (fun i => stepWithMS sp ro m (st i)) H U tr

/-- The states reached at validator `self` inside `U` by calls under the call law, each executing
`stepWith` at locks related to its unlock input (`ACInterface.ReachableAt`, with the unlock
given). -/
inductive ReachableAtU {ro : ReplayOrder sp FGP} (m : WriteMode) (self : Fin sp.n)
    (U : Set (Blk sp.n FGP)) :
    SAState sp.n → Frm sp.n FGP → Time → Prop
  /-- The initial state, with the initial frame, at time `0`. -/
  | init (Φ : Frm sp.n FGP) : (goldilocksSA sp FGP ro).InitialFrame Φ →
      (goldilocksSA sp FGP ro).FrameIn U Φ →
      ReachableAtU m self U (SAState.initial sp.genesisRoot) Φ 0
  /-- One more call at locks `L₁` related to its unlock input. -/
  | step {A : SAState sp.n} {Φ Φ' : Frm sp.n FGP} {t t' : Time}
      (c : (goldilocksSA sp FGP ro).Call) (L₁ : Set Lock) : ReachableAtU m self U A Φ t → t ≤ t' →
      (goldilocksSA sp FGP ro).CallOK U Φ t' c Φ' →
      UnlockRel sp (callInputM sp m A Φ' t' c).locks Φ' t' ((sp.slot t' : Int) - 1)
        (callViewM sp m A Φ' t' c) L₁ →
      ReachableAtU m self U (stepWithM sp ro m self L₁ A Φ' t' c).1 Φ' t'

/-- An AC trace of the SA with the unlock given, its contract and the honest-object facts
(`ACRun` with the unlock given). -/
structure ACRunU (m : WriteMode) (u : Nat → Set Lock) {ro : ReplayOrder sp FGP}
    (selectedProposer : Nat → Fin sp.n) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) : Prop where
  /-- The AC trace contract with the unlock given. -/
  localRun : ACLocalRunU m u H U tr
  /-- The honest-object facts. -/
  honest : HonestObjects selectedProposer tr H

/-- `ACRunU` from the starts `st`: an AC trace with the contract `ACLocalRunUS` and the
honest-object facts. -/
structure ACRunUS (m : WriteMode) (u : Nat → Set Lock) (st : Nat → StartFn sp FGP)
    {ro : ReplayOrder sp FGP} (selectedProposer : Nat → Fin sp.n) (tr : SATrace sp FGP ro)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) : Prop where
  /-- The AC trace contract from the starts `st`. -/
  localRun : ACLocalRunUS m u st H U tr
  /-- The honest-object facts. -/
  honest : HonestObjects selectedProposer tr H

end Consensus.Goldilocks.SA

end
