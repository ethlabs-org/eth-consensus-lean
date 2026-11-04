module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Interface

@[expose] public section

/-! # Goldilocks milestone vocabulary: AC traces

The part of `Spec/AC/Trace` that no Challenge statement reaches (docs/decisions.md, 2026-11-04): the
milestone statements use it; it is not on the trusted surface. Names and bodies are unchanged.

The AC component trace (decomposition §2 D, `AC.LocalRun`): a `Trace` over the AC state alone,
whose labelled cuts are AC calls (`ACLabel`, `Spec/AC/Trace`). FG cuts and the other nodes' cuts
are stutters (no label).

`ACLocalRun A H U tr` is the contract a node run's projection satisfies (claims C0.5 (a), (b)),
for the honest validators `H`, inside the coherent set `U`: each honest node starts from the
initial AC state and each call executes the AC on its pre-state, under the frame law at call
boundaries (`CallOK`), in the run's time order from `0`, with the run's sleep and wake laws; its
fields state each. `SyncAC A H U a b tr` is the
network premise `Sync[a, b]` (claims §"Premises") as the AC trace observes it: a deadline is
read at every call of `y` at or after it, and "extends `y`'s finalized tip" at that call's
frame. -/

namespace Consensus.Goldilocks

variable {P : Params} {FGP : Type}

/-- An AC trace: per validator, the AC state; labelled cuts are AC calls. -/
abbrev ACTrace (A : ACInterface P FGP) := Trace (Fin P.n) A.State (ACLabel A)

namespace ACTrace

variable {A : ACInterface P FGP} (tr : ACTrace A)

/-- `y` makes no AC call at a cut in `[j, i)`. -/
def NoCallBetween (y : Fin P.n) (j i : Nat) : Prop :=
  ∀ k, j ≤ k → k < i → ∀ ℓ, ¬ tr.CallAt y k ℓ

/-- `y` restarts at cut `k`. -/
def RestartAt (y : Fin P.n) (k : Nat) : Prop := ∃ ℓ, tr.CallAt y k ℓ ∧ ℓ.call = .restart

/-- `y` accepts `B` at cut `k` (an `on_block(B)` call). -/
def AcceptAt (y : Fin P.n) (k : Nat) (B : A.Blk) : Prop := ∃ ℓ, tr.CallAt y k ℓ ∧ ℓ.call = .block B

/-- `y` processes the message `m` at cut `k`: an `on_message(m)` call, or `m` is an emission of
its call there (an own message is processed at once). -/
def ProcessAt (y : Fin P.n) (k : Nat) (m : A.Msg) : Prop :=
  ∃ ℓ, tr.CallAt y k ℓ ∧ (ℓ.call = .message m ∨ ∃ e ∈ ℓ.emits, e.msg = m)

/-- `x` sends `m` at cut `i` (an emission), or admits it there: a call other than a restart
after which its AC holds `m` and before which it did not, whether `m` came as a message or from
the payload of a block the call accepts (`on_block`). An honest node forwards an AC message when
its AC admits it, also from the payload of an accepted block; a refused receipt is not
forwarded, and the restart's replay re-processes blocks already accepted and sends nothing
(composition.tex §"Model"; claims §"How to read the DAG", A0.7; goldilocks#28, #32). -/
def SendOrAdmit (x : Fin P.n) (i : Nat) (m : A.Msg) : Prop :=
  ∃ ℓ, tr.CallAt x i ℓ ∧ ((∃ e ∈ ℓ.emits, e.msg = m) ∨
    (ℓ.call ≠ .restart ∧ ¬ A.holdsMsg (tr.state x i) m ∧ A.holdsMsg (tr.post i) m))

open Classical in
/-- The latest wake of `y` at or before cut `k`: the time of its latest restart at a cut `≤ k`
(`⊥` if none). -/
noncomputable def lastWake (y : Fin P.n) : Nat → WithBot Time
  | 0 => if tr.RestartAt y 0 then (tr.time 0 : WithBot Time) else ⊥
  | k + 1 => if tr.RestartAt y (k + 1) then (tr.time (k + 1) : WithBot Time) else lastWake y k

/-- The delivery deadline at `y` for an object of time `τ`, as of cut `k`: `max(τ, w_y) + Δ`. -/
noncomputable def deadline (y : Fin P.n) (k : Nat) (τ : Time) : Time :=
  Option.elim (tr.lastWake y k) τ (fun w => max τ w) + P.Δ

end ACTrace

/-- The AC trace contract (claims C0.5 (a), (b)) for the honest validators `H` inside `U`. -/
structure ACLocalRun (A : ACInterface P FGP) (H : Set (Fin P.n)) (U : Set A.Blk)
    (tr : ACTrace A) : Prop where
  /-- `U` is coherent: roots injective, slots increasing along parent edges. -/
  coherent : Coherent U
  /-- Each honest node starts from the initial AC state. -/
  init : ∀ y ∈ H, tr.init y = A.initial
  /-- Each call of an honest node executes the AC on the pre-state, the label's frame and the
  cut's time: the post-state and the emissions are the call's. -/
  exec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H →
    A.step (tr.node i) (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call = (tr.post i, ℓ.emits)
  /-- The frame law and the input contract: the first call of an honest node follows an initial
  frame, each later call follows the previous call's frame, by the call law. -/
  frameLaw : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ →
    (tr.NoCallBetween y 0 i ∧ ∃ Φ₀, A.InitialFrame Φ₀ ∧ A.FrameIn U Φ₀ ∧
      A.CallOK U Φ₀ (tr.time i) ℓ.call ℓ.frame) ∨
    (∃ j ℓ', j < i ∧ tr.CallAt y j ℓ' ∧ tr.NoCallBetween y (j + 1) i ∧
      A.CallOK U ℓ'.frame (tr.time i) ℓ.call ℓ.frame)
  /-- Cuts are at times from `0` on. -/
  time_nonneg : ∀ i, 0 ≤ tr.time i
  /-- The cut order is by time. -/
  time_mono : Monotone tr.time
  /-- An honest node is called only while awake. -/
  awake_of_call : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → tr.awake y (tr.time i)
  /-- The first call of an honest node after it was asleep is a restart. -/
  restart_of_sleep : ∀ y ∈ H, ∀ i ℓ (u : Time), tr.CallAt y i ℓ → 0 ≤ u → u < tr.time i →
    ¬ tr.awake y u → (∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u) → ℓ.call = .restart
  /-- A wake is a restart: when an honest node is asleep at `u` and awake at a later `v`, it
  restarts at a cut in `(u, v]`. -/
  restart_at_wake : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v → ¬ tr.awake y u → tr.awake y v →
    ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  /-- A restart is a wake: the node was asleep after its previous call. -/
  sleep_of_restart : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ℓ.call = .restart →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧
      ∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u

/-- **`Sync[a, b]` over an AC trace** (claims §"Premises" at goldilocks `a470648c`). Messages:
every AC message that an honest `x` sends or admits at `τ ∈ [a, b]`, also from a block's
payload (an honest node forwards an AC message when it admits it) is processed by every honest
`y` at a time in `[τ, max(τ, w_y) + Δ)`: the delivery of that send or forward, not an earlier
processing; a refused receipt triggers nothing. Blocks (acceptance relay): every block that an
honest `x` accepts at `τ ∈ [a, b]` is accepted by every honest `y` whose finalized tip it extends
(inside `U`) before its deadline. Both read at every call of `y` at or after its deadline. -/
def SyncAC (A : ACInterface P FGP) (H : Set (Fin P.n)) (U : Set A.Blk) (a b : Time)
    (tr : ACTrace A) : Prop :=
  (∀ x ∈ H, ∀ i m, tr.SendOrAdmit x i m → a ≤ tr.time i → tr.time i ≤ b →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.ProcessAt y k m ∧
        tr.time k < tr.deadline y k (tr.time i)) ∧
  (∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → a ≤ tr.time i → tr.time i ≤ b →
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → tr.deadline y j (tr.time i) ≤ tr.time j →
      Anc U ℓ.frame.F B →
      ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k (tr.time i))

end Consensus.Goldilocks

end
