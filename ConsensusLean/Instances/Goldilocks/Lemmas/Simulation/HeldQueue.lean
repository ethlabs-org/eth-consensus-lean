module
public import ConsensusLean.Instances.Goldilocks.AsChainShape

public section

/-! # Goldilocks Simulation: the held attestation queue

The laws of the shape's queue of held attestations (`State.held`) under every step of the
shape, at an arbitrary release schedule `release`. No run is involved; the engine-level
invariants follow from these by induction over the duties of a run.

* **Only own signings, in signing order.** No step except the FG update adds to `held`, and the
  FG update appends exactly the attestation it signs (`fgSigned`), at the end, and only when the
  schedule refuses release at the node's time (`fgUpdate_held`); otherwise that attestation is
  queued in `outbox` (`fgUpdate_outbox`). A delivery, a recorded own object, the node's tick, a
  proposal and a restart leave `held` unchanged (`process_held`, `recordOwn_held`,
  `nodeTick_held`, `propose_held`, `restore_held`); the batch poll empties it or keeps it, then
  runs the FG update when due (`pollBatch_held`).
* **After the first poll after the tick step, `held ≠ []` implies `release self now = false`.**
  A batch poll after the tick step of the node's time (`ticked`) establishes `HeldRefused release`
  (`heldRefused_pollBatch`), the FG update keeps it (`heldRefused_fgUpdate`), and so does every
  step that keeps the key and the clock and does not grow `held` (`heldRefused_of_held`); only the
  clock and a restart set the time.
* **The flush.** A batch poll after the tick step at a time the schedule allows processes every
  held attestation by the own `on_attestation`, oldest first, before its FG update
  (`heldDrain`), releases them at the end of its batch, and empties `held` (`pollBatch_snd`,
  `pollBatch_flush`). Processing an attestation changes only the pool, which neither `ac_to_fg`
  nor `fg_attest` reads, so the flush leaves what the FG update signs and queues unchanged
  (`fgSigned_heldDrain`, `fgUpdate_outbox_heldDrain`).
* **The stock schedule.** With `release ≡ true` no step makes `held` non-empty (`init_held`,
  `fgUpdate_held_stock`, `pollBatch_held_stock` and the laws that keep `held`), and with
  `held = []` the batch poll is the one of the stock node, releasing nothing more
  (`pollBatch_of_held_nil`, `pollBatch_stock`), so every stock lemma about `poll` applies
  unchanged.

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape
open AC (ACParams Vote Payload)

variable {binding : VoteBinding} {sp : ACParams}
  {release : Fin sp.n → Time → Bool}

/-- The attestation the FG update signs at `st`, if any: `fg_attest` at the source that
`ac_to_fg` returns. -/
noncomputable def fgSigned (st : State sp binding) : Option (FG.Att sp.n) :=
  (Node.acToFG st.node st.now).2.2.bind fun C =>
    ((Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record st.self
      C).map Prod.fst

/-- The signed attestation is `fg_attest`'s at the source of `ac_to_fg`. -/
theorem fgSigned_eq (st : State sp binding) : fgSigned st =
    (Node.acToFG st.node st.now).2.2.bind fun C =>
      ((Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record st.self
        C).map Prod.fst := by rfl

/-! ## The steps that keep `held` -/

/-- Applying handler cuts keeps the held queue. -/
theorem apply_held (st : State sp binding) origin r : (apply st origin r).held = st.held := by
  rfl

/-- Relaying keeps the held queue. -/
theorem relayIf_held (st : State sp binding) (c : Prop) [Decidable c] o :
    (relayIf st c o).held = st.held := by
  unfold relayIf; split <;> rfl

/-- Processing one received object keeps the held queue. -/
theorem processOne_held io hs (st : State sp binding) o :
    (processOne io hs st o).held = st.held := by
  rw [processOne_eq]
  split <;> (try dsimp only) <;> simp only [relayIf_held, apply_held]

/-- A delivery keeps the held queue. -/
theorem process_held (st : State sp binding) o hs : (process st o hs).held = st.held := by
  rw [process_eq]
  generalize delivered st.voteIO hs st o = os
  suffices ∀ st', st'.held = st.held → (os.foldl (processOne st.voteIO hs) st').held = st.held from
    this st rfl
  induction os with
  | nil => exact fun _ h => h
  | cons o os ih => exact fun st' h => ih _ ((processOne_held _ _ _ _).trans h)

/-- Recording an own object keeps the held queue. -/
theorem recordOwn_held (st : State sp binding) o hs : (recordOwn st o hs).held = st.held := by
  rw [recordOwn_eq]; split <;> (try split) <;> rfl

/-- The node's tick keeps the held queue. -/
theorem nodeTick_held {sign : Fin sp.n → Time → Bool} (st : State sp binding) :
    (nodeTick st sign).held = st.held := by
  rw [nodeTick_eq (sign := _)]; split <;> rfl

/-- The slot proposal keeps the held queue. -/
theorem propose_held (st : State sp binding) s : (propose st s).1.held = st.held := by
  rw [propose_eq]; dsimp only; split <;> rfl

/-- Recording an own object keeps the tick flag. -/
theorem recordOwn_ticked (st : State sp binding) o hs :
    (recordOwn st o hs).ticked = st.ticked := by
  rw [recordOwn_eq]; split <;> (try split) <;> rfl

/-- The slot proposal keeps the tick flag. -/
theorem propose_ticked (st : State sp binding) s : (propose st s).1.ticked = st.ticked := by
  rw [propose_eq]; dsimp only; split <;> rfl

/-- A restart keeps the held queue: held attestations survive a sleep. -/
theorem restore_held (k : Fin sp.n) (d : State sp binding) (t : Time) :
    (restore k d t).held = d.held := by
  rw [restore_eq]; rfl

/-! ## The FG update and the batch poll -/

/-- The FG update keeps the key. -/
theorem fgUpdate_self (st : State sp binding) : (fgUpdate st release).self = st.self := by
  rw [fgUpdate_eq st release]; simp only; split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- The FG update keeps the clock. -/
theorem fgUpdate_now (st : State sp binding) : (fgUpdate st release).now = st.now := by
  rw [fgUpdate_eq st release]; simp only; split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- The FG update keeps the tick flag. -/
theorem fgUpdate_ticked (st : State sp binding) :
    (fgUpdate st release).ticked = st.ticked := by
  rw [fgUpdate_eq st release]; simp only; split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- The FG update clears the FG-due flag. -/
theorem fgUpdate_fgDue (st : State sp binding) : (fgUpdate st release).fgDue = false := by
  rw [fgUpdate_eq st release]; simp only; split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- The FG update appends the attestation it signs to the held queue exactly when the schedule
refuses release at the node's time. -/
theorem fgUpdate_held (st : State sp binding) : (fgUpdate st release).held =
    st.held ++ if release st.self st.now then [] else (fgSigned st).toList := by
  rw [fgUpdate_eq st release, fgSigned_eq]; dsimp only
  cases (Node.acToFG st.node st.now).2.2 with
  | none => simp
  | some C =>
    simp only [Option.bind_some]
    cases (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with
    | none => simp
    | some ar => cases hr : release st.self st.now <;> simp

/-- The FG update queues the attestation it signs in `outbox` exactly when the schedule allows
release at the node's time. -/
theorem fgUpdate_outbox (st : State sp binding) : (fgUpdate st release).outbox =
    st.outbox ++ if release st.self st.now then
      (fgSigned st).toList.map fun a => Body.att (encodeAtt a) else [] := by
  rw [fgUpdate_eq st release, fgSigned_eq]; dsimp only
  cases (Node.acToFG st.node st.now).2.2 with
  | none => simp
  | some C =>
    simp only [Option.bind_some]
    cases (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with
    | none => simp
    | some ar => cases hr : release st.self st.now <;> simp

/-- A poll step's state is the FG update's when due, with its outbox head taken and its forwards
cleared; its held queue is the FG update's. -/
theorem poll_held (st : State sp binding) t :
    (poll st t release).1.held = (if st.fgDue then fgUpdate st release else st).held := by
  unfold poll; dsimp only; split <;> rfl

/-- A poll step's body: the head of the outbox after the FG update when due. -/
theorem poll_snd (st : State sp binding) t : (poll st t release).2 =
    (if st.fgDue then fgUpdate st release else st).outbox.head?.map fun b => (b, []) := by
  unfold poll; dsimp only
  split <;> simp_all

/-- A poll step keeps the key. -/
theorem poll_self (st : State sp binding) t : (poll st t release).1.self = st.self := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_self]

/-- A poll step keeps the clock. -/
theorem poll_now (st : State sp binding) t : (poll st t release).1.now = st.now := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_now]

/-- After a poll step the FG update is not due: the step ran it if it was. -/
theorem poll_fgDue (st : State sp binding) t : (poll st t release).1.fgDue = false := by
  unfold poll; simp only; split <;> split <;> simp_all [fgUpdate_fgDue]

/-- A poll step keeps the tick flag. -/
theorem poll_ticked (st : State sp binding) t : (poll st t release).1.ticked = st.ticked := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_ticked]

/-- Processing attestations by the own `on_attestation` changes only the pool of the FG store. -/
private theorem foldl_onAttestation (l : List (FG.Att sp.n))
    (n : NodeState (goldilocksNode sp)) :
    ∃ atts, l.foldl (fun n a => (Node.onAttestation n a).1) n =
      { n with fg := { n.fg with atts := atts } } := by
  induction l generalizing n with
  | nil => exact ⟨n.fg.atts, rfl⟩
  | cons a l ih =>
    obtain ⟨atts, h⟩ := ih (Node.onAttestation n a).1
    refine ⟨atts, ?_⟩
    rw [List.foldl_cons, h]
    simp only [Node.onAttestation, Store.onAttestation]
    split <;> rfl

/-- The flush of a batch poll: every held attestation processed by the own `on_attestation`,
oldest first, and `held` emptied. -/
noncomputable def heldDrain (st : State sp binding) : State sp binding :=
  { st with held := [], node := st.held.foldl (fun n a => (Node.onAttestation n a).1) st.node }

/-- The flush changes only `held` and the pool. -/
theorem heldDrain_eq (st : State sp binding) : ∃ atts, heldDrain st =
    { st with held := [], node := { st.node with fg := { st.node.fg with atts := atts } } } := by
  obtain ⟨atts, h⟩ := foldl_onAttestation st.held st.node
  exact ⟨atts, by rw [← h]; rfl⟩

/-- The signed attestation does not read the pool. -/
theorem fgSigned_atts (st : State sp binding) (atts : List (FG.Att sp.n)) (l) :
    fgSigned { st with held := l, node := { st.node with fg := { st.node.fg with atts := atts } } }
      = fgSigned st := by rfl

/-- The flush leaves the attestation the FG update signs unchanged. -/
theorem fgSigned_heldDrain (st : State sp binding) : fgSigned (heldDrain st) = fgSigned st := by
  obtain ⟨atts, h⟩ := heldDrain_eq st
  rw [h, fgSigned_atts]

/-- The flush keeps the key, the clock, the FG-due flag and the queues. -/
theorem heldDrain_self (st : State sp binding) : (heldDrain st).self = st.self := by rfl
theorem heldDrain_now (st : State sp binding) : (heldDrain st).now = st.now := by rfl
theorem heldDrain_fgDue (st : State sp binding) : (heldDrain st).fgDue = st.fgDue := by rfl
theorem heldDrain_outbox (st : State sp binding) : (heldDrain st).outbox = st.outbox := by rfl
theorem heldDrain_relayBuf (st : State sp binding) : (heldDrain st).relayBuf = st.relayBuf := by
  rfl
theorem heldDrain_held (st : State sp binding) : (heldDrain st).held = [] := by rfl
theorem heldDrain_node (st : State sp binding) :
    (heldDrain st).node = st.held.foldl (fun n a => (Node.onAttestation n a).1) st.node := by rfl

/-- With nothing held the flush changes nothing. -/
theorem heldDrain_of_held_nil (st : State sp binding) (hh : st.held = []) :
    heldDrain st = st := by
  cases st; simp only at hh; subst hh; rfl

/-- After the flush the FG update queues what it queues from the state before it. -/
theorem fgUpdate_outbox_heldDrain (st : State sp binding) :
    (fgUpdate (heldDrain st) release).outbox = (fgUpdate st release).outbox := by
  rw [fgUpdate_outbox, fgUpdate_outbox, fgSigned_heldDrain]; rfl

/-- The batch poll's state is the poll step's, from the flushed state when the batch flushes. -/
theorem pollBatch_fst (st : State sp binding) t : (pollBatch st t release).1 =
    (poll (if (release st.self st.now && st.ticked) = true then heldDrain st else st) t
      release).1 := by rfl

/-- The batch: the poll step's body, the block wrappers, the vote envelopes, then, when the batch
flushes, every held attestation, oldest first. -/
theorem pollBatch_snd (st : State sp binding) t : (pollBatch st t release).2 =
    (poll (if (release st.self st.now && st.ticked) = true then heldDrain st else st) t
      release).2.toList ++
      (st.forwards.map fun p => (.forward p.1, p.2)) ++
      (st.voteForwards.map fun p => (.voteForward p.1 (encodeVote p.2.1), [p.2.2])) ++
      (if (release st.self st.now && st.ticked) = true then
        st.held.map fun a => (.att (encodeAtt a), []) else []) := by
  rfl

/-- The held attestations a batch poll at `st` releases, oldest first: every held one when it
runs after the tick step at a time the schedule allows, none otherwise. -/
def pollFlush (st : State sp binding) (release : Fin sp.n → Time → Bool) :
    List (FG.Att sp.n) :=
  if (release st.self st.now && st.ticked) = true then st.held else []

/-- `pollFlush` unfolded. -/
theorem pollFlush_eq (st : State sp binding) (release : Fin sp.n → Time → Bool) :
    pollFlush st release =
      if (release st.self st.now && st.ticked) = true then st.held else [] := by rfl

/-- Before the tick step of the node's time a batch poll flushes nothing. -/
theorem pollFlush_of_unticked (st : State sp binding) (hk : st.ticked = false) :
    pollFlush st release = [] := by
  rw [pollFlush_eq]; simp [hk]

/-- The poll step's body after the flush is the one without it. -/
theorem poll_snd_heldDrain (st : State sp binding) t :
    (poll (heldDrain st) t release).2 = (poll st t release).2 := by
  rw [poll_snd, poll_snd, heldDrain_fgDue]
  split
  · rw [fgUpdate_outbox_heldDrain]
  · rfl

/-- The batch with its flush written as `pollFlush`. -/
theorem pollBatch_snd_flush (st : State sp binding) t : (pollBatch st t release).2 =
    (poll st t release).2.toList ++
      (st.forwards.map fun p => (.forward p.1, p.2)) ++
      (st.voteForwards.map fun p => (.voteForward p.1 (encodeVote p.2.1), [p.2.2])) ++
      (pollFlush st release).map fun a => (.att (encodeAtt a), []) := by
  rw [pollBatch_snd, pollFlush_eq]
  split
  · rw [poll_snd_heldDrain]
  · rfl

/-- The batch poll keeps the key. -/
theorem pollBatch_self (st : State sp binding) t :
    (pollBatch st t release).1.self = st.self := by
  rw [pollBatch_fst, poll_self]; split <;> rfl

/-- The batch poll keeps the clock. -/
theorem pollBatch_now (st : State sp binding) t : (pollBatch st t release).1.now = st.now := by
  rw [pollBatch_fst, poll_now]; split <;> rfl

/-- The batch poll keeps the tick flag. -/
theorem pollBatch_ticked (st : State sp binding) t :
    (pollBatch st t release).1.ticked = st.ticked := by
  rw [pollBatch_fst, poll_ticked]; split <;> rfl

/-- After a batch poll the FG update is not due. -/
theorem pollBatch_fgDue (st : State sp binding) t :
    (pollBatch st t release).1.fgDue = false := by
  rw [pollBatch_fst, poll_fgDue]

/-- The held queue after a batch poll: emptied when the schedule allows release at the node's
time, kept otherwise; then the attestation the FG update signs, when it is due and the schedule
refuses release. -/
theorem pollBatch_held (st : State sp binding) t : (pollBatch st t release).1.held =
    (if (release st.self st.now && st.ticked) = true then [] else st.held) ++
      if st.fgDue ∧ release st.self st.now = false then (fgSigned st).toList else [] := by
  rw [pollBatch_fst, poll_held]
  cases hr : release st.self st.now <;> cases hk : st.ticked <;> cases hd : st.fgDue <;>
    simp [hr, hd, fgUpdate_held, heldDrain_fgDue, heldDrain_held, heldDrain_self,
      heldDrain_now]

/-- **The flush.** At a time the schedule allows, the batch poll empties the held queue and
releases every held attestation, oldest first, at the end of its batch. -/
theorem pollBatch_flush (st : State sp binding) t (hr : release st.self st.now = true)
    (hk : st.ticked = true) :
    (pollBatch st t release).1.held = [] ∧
      ∃ pre, (pollBatch st t release).2 = pre ++ st.held.map fun a => (.att (encodeAtt a), []) :=
  ⟨by simp [pollBatch_held, hr, hk],
    ⟨_, by rw [pollBatch_snd]; simp only [hr, hk, Bool.and_self, ↓reduceIte]; rfl⟩⟩

/-- A property kept by the poll step and by emptying the held queue is kept by the batch poll. -/
theorem pollBatch_pres {Q : State sp binding → Prop} {st : State sp binding} {t : Time}
    (hpoll : ∀ st, Q st → Q (poll st t release).1) (hclear : ∀ st, Q st → Q (heldDrain st))
    (h : Q st) : Q (pollBatch st t release).1 := by
  rw [pollBatch_fst]
  split
  · exact hpoll _ (hclear _ h)
  · exact hpoll _ h

/-! ## After the first poll of a tick -/

/-- The held queue is empty, or the schedule refuses release at the node's own time. -/
def HeldRefused (release : Fin sp.n → Time → Bool) (st : State sp binding) : Prop :=
  st.held ≠ [] → release st.self st.now = false

/-- `HeldRefused` is a non-empty queue's refusal at the node's time. -/
theorem heldRefused_iff (st : State sp binding) :
    HeldRefused release st ↔ (st.held ≠ [] → release st.self st.now = false) := Iff.rfl

/-- A step that keeps the key and the clock and does not grow `held` keeps `HeldRefused`. -/
theorem heldRefused_of_held {st st' : State sp binding} (hs : st'.self = st.self)
    (hn : st'.now = st.now) (hh : st'.held = st.held) (h : HeldRefused release st) :
    HeldRefused release st' := by
  intro hne; rw [hs, hn]; exact h (hh ▸ hne)

/-- **A batch poll after the tick step establishes `HeldRefused`**: at a time the schedule
allows, it empties the queue and holds nothing new. -/
theorem heldRefused_pollBatch (st : State sp binding) t (hk : st.ticked = true) :
    HeldRefused release (pollBatch st t release).1 := by
  intro hne
  rw [pollBatch_self, pollBatch_now]
  cases hr : release st.self st.now
  · rfl
  · simp [pollBatch_held, hr, hk] at hne

/-- A batch poll keeps `HeldRefused`, whether or not it runs after the tick step. -/
theorem heldRefused_pollBatch_of_refused {st : State sp binding} (h : HeldRefused release st)
    t : HeldRefused release (pollBatch st t release).1 := by
  intro hne
  rw [pollBatch_self, pollBatch_now]
  cases hr : release st.self st.now
  · rfl
  · have hh : st.held = [] := by
      by_contra hc; exact absurd (h hc) (by simp [hr])
    simp [pollBatch_held, hr, hh] at hne

/-- The FG update keeps `HeldRefused`: it holds its attestation only when the schedule refuses
release at the node's time. -/
private theorem heldRefused_fgUpdate {st : State sp binding} (h : HeldRefused release st) :
    HeldRefused release (fgUpdate st release) := by
  intro hne
  rw [fgUpdate_self, fgUpdate_now]
  cases hr : release st.self st.now
  · rfl
  · simp only [fgUpdate_held, hr, ↓reduceIte, List.append_nil] at hne
    exact hr ▸ h hne

/-- Under `HeldRefused`, a batch poll flushes nothing. -/
theorem pollFlush_eq_nil {st : State sp binding} (h : HeldRefused release st) :
    pollFlush st release = [] := by
  rw [pollFlush_eq]
  by_cases hh : st.held = []
  · simp [hh]
  · simp [h hh]

/-! ## The stock schedule -/

/-- The initial state holds nothing. -/
theorem init_held (sign release : Fin sp.n → Time → Bool) k p io :
    ((nodeOps sp binding sign release).init k p io).held = [] := by rfl

/-- The stock FG update (`release ≡ true`) holds nothing new. -/
theorem fgUpdate_held_stock (st : State sp binding) : (fgUpdate st).held = st.held := by
  simp [fgUpdate_held]

/-- The stock batch poll leaves the held queue empty. -/
theorem pollBatch_held_stock (st : State sp binding) t (hh : st.held = []) :
    (pollBatch st t).1.held = [] := by
  rw [pollBatch_held]; simp [hh]

/-- **The R = 0 identity.** With nothing held (at the stock
schedule `release ≡ true`, every reachable state: `init_held`, `pollBatch_held_stock`,
`fgUpdate_held_stock` and the `*_held` laws), the batch poll is the stock node's: the poll step's
state and body, the block wrappers and the vote envelopes, releasing nothing more. -/
theorem pollBatch_of_held_nil (st : State sp binding) t (hh : st.held = []) :
    pollBatch st t release =
      ((poll st t release).1, (poll st t release).2.toList ++
        (st.forwards.map fun p => (.forward p.1, p.2)) ++
        (st.voteForwards.map fun p => (.voteForward p.1 (encodeVote p.2.1), [p.2.2]))) := by
  have hst : heldDrain st = st := heldDrain_of_held_nil st hh
  refine Prod.ext ?_ ?_
  · rw [pollBatch_fst, hst, ite_self]
  · rw [pollBatch_snd_flush, pollFlush_eq, hh, ite_self, List.map_nil, List.append_nil]

/-- At the stock schedule a state with nothing held polls as the stock node. -/
private theorem pollBatch_stock (st : State sp binding) t (hh : st.held = []) : pollBatch st t =
    ((poll st t).1, (poll st t).2.toList ++ (st.forwards.map fun p => (.forward p.1, p.2)) ++
      (st.voteForwards.map fun p => (.voteForward p.1 (encodeVote p.2.1), [p.2.2]))) :=
  pollBatch_of_held_nil st t hh

end Consensus.Goldilocks.Simulation

end
