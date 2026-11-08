module
public import ConsensusLean.Spec.Shape.Run

@[expose] public section

/-! # Adversary activity and the content-origin hold over model runs (L1, statements)

The canonical signature readings of the model's systems, fixed from the objects' authentications
(`Obj.auth`) and parts (`Obj.parts`); a generic communication log is opaque in its messages. Both
read only the run's releases and receipts and the protocol's public roles, never protocol state,
admission or outputs.

* **Honest release.** Key `k`'s validator releases content `d` honestly at `t` when it is honest at
  `t` and releases at `t` an object that has `d` among its parts (`d` itself or carried at any
  depth). Own signatures nested in a container count as the validator's own.
* `activeFaulty rho fl a b`: the validators whose key has a signed content that its validator never
  released honestly, **charged** to `[a, b)`. A content is charged once, at `max t₀ t_s`: `t₀` its
  first receipt by an honest node by any route (directly or carried in another object, read from the
  receipts, not from protocol admission), `t_s` the time floor of its signing role (`fl`; for chain
  shapes the start of the role's slot, `shapeFloor`). Later honest forwarding of a content is not
  new activity; what a validator released while honest is never activity (under growing faults
  included); a forgery by an extracted key is, also when it claims an earlier slot. The floor
  charges a content for a future slot, received early, to the window of its own slot.
* `ContentOriginHold rho G b₀ b₁`: no node of one group of `G`, honest at the receipt, receives
  before `b₁`, by any route, a content signed by a validator of the other group whose **first**
  honest release by its signer is at `t₀ < b₁` with delivery deadline `t₀ + ΔAC − 1` past `b₀`
  (`HeldOrigin`: a release that `SyncUntil b₀` does not owe). The first release fixes the class of
  a content: later honest re-releases never make prefix stock held. FG attestations are out of
  scope. Holding honest sends alone would not suffice: the adversary may relay or nest authentic
  honest content.
* `RoleFloor`, `shapeFloor`, `shapeRoleFloor`: role time floors, read from the protocol's public
  roles only; `activity` and `contentHold` lift the readings to runs of `sysOf`. -/

namespace Consensus.Comparison

open Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
  {E : Env V}

section Run

variable (rho : Model.Run F E)

/-- The validator of key `k` releases `d` honestly at `t`: it is honest at `t` and releases at `t`
an object that has `d` among its parts (`d` itself or carried at any depth). -/
def HonestReleaseAt (k : Fin (Fintype.card V)) (d : (protoOf F E).Object) (t : Time) : Prop :=
  rho.point.HonestAt (rho.key k) t ∧ ∃ o, rho.releases (rho.key k) o t ∧ Obj.Contains o d

/-- `d` is an honest content of key `k`: its validator released it honestly at some time. -/
def HonestMade (k : Fin (Fintype.card V)) (d : (protoOf F E).Object) : Prop :=
  ∃ t, HonestReleaseAt rho k d t

/-- `t₀` is the first honest release of `d` by key `k`'s validator: one at `t₀`, none earlier. -/
def FirstHonestRelease (k : Fin (Fintype.card V)) (d : (protoOf F E).Object) (t₀ : Time) :
    Prop :=
  HonestReleaseAt rho k d t₀ ∧ ∀ t, HonestReleaseAt rho k d t → t₀ ≤ t

/-- A node honest at `t` received, at `t`, an object containing `d` at any depth (`d` itself, or
carried in it, by any route). -/
def HonestReceipt (d : (protoOf F E).Object) (t : Time) : Prop :=
  ∃ v o, rho.receives v o t ∧ rho.point.HonestAt v t ∧ Obj.Contains o d

/-- `t₀` is the first honest receipt of `d`: an honest receipt at `t₀`, and none earlier. -/
def FirstHonestReceipt (d : (protoOf F E).Object) (t₀ : Time) : Prop :=
  HonestReceipt rho d t₀ ∧ ∀ t, HonestReceipt rho d t → t₀ ≤ t

end Run

/-- The charging time of a content signed in role `r` and first received by an honest node at
`t₀`: `max t₀ t_s`, with `t_s` the time floor of the role (`fl r`); a role without a floor is
charged at `t₀`. -/
def chargeTime {Role : Type} (fl : Role → Option Time) (r : Role) (t₀ : Time) : Time :=
  max t₀ ((fl r).getD t₀)

/-- Key `k` is **active on `[a, b)`** in run `rho` with role floors `fl`: some content signed by
`k` (in some role `r`), never released honestly by `k`'s validator (at any nesting depth), has its
charging time `max t₀ t_s` (first honest receipt `t₀`, role floor `t_s`) in `[a, b)`. -/
def ActiveIn (rho : Model.Run F E) (fl : (protoOf F E).Role → Option Time)
    (k : Fin (Fintype.card V)) (a b : Time) : Prop :=
  ∃ (d : (protoOf F E).Object) (r : (protoOf F E).Role) (t₀ : Time),
    d.auth = .signed k r ∧ ¬ HonestMade rho k d ∧ FirstHonestReceipt rho d t₀ ∧
      a ≤ chargeTime fl r t₀ ∧ chargeTime fl r t₀ < b

/-- **The adversary's active set on `[a, b)`**: the validators whose own key is active on `[a, b)`
(`ActiveIn`). Each signed content is charged once, to the window of `max` (its first honest
receipt by any route, the floor of its signing role); later honest forwarding of the same content
is propagation, not activity; a validator's honest releases are never activity. -/
noncomputable def activeFaulty (rho : Model.Run F E) (fl : (protoOf F E).Role → Option Time)
    (a b : Time) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ActiveIn rho fl (rho.ownKey v) a b

/-- **A held origin** for the incident `[b₀, b₁)`: `d` is not an FG attestation, and its first
honest release by key `k`'s validator is at `t₀ < b₁` with delivery deadline `t₀ + ΔAC − 1` past
`b₀`, so `SyncUntil b₀` does not owe its delivery. A content first released earlier (prefix stock)
or from `b₁` on is never held, whatever its later releases. -/
def HeldOrigin (rho : Model.Run F E) (b₀ b₁ : Time) (k : Fin (Fintype.card V))
    (d : (protoOf F E).Object) : Prop :=
  ¬ (protoOf F E).isFGAtt d ∧
    ∃ t₀, FirstHonestRelease rho k d t₀ ∧ t₀ < b₁ ∧ b₀ < t₀ + E.ΔAC - 1

/-- **The content-origin hold** of the split `G` for the incident `[b₀, b₁)`: no node honest at a
receipt before `b₁` receives, at any depth (directly, relayed by a faulty node, or carried in a
payload), a content signed by a key of the other group with a held origin (`HeldOrigin`). -/
def ContentOriginHold (rho : Model.Run F E) (G : V → Bool) (b₀ b₁ : Time) : Prop :=
  ∀ w o t, rho.receives w o t → rho.point.HonestAt w t → t < b₁ → ∀ d, Obj.Contains o d →
    ∀ k r, d.auth = .signed k r → G (rho.key k) ≠ G w → ¬ HeldOrigin rho b₀ b₁ k d

/-- Role time floors of family `F`: in each environment, a time floor (or none) per signing role.
A function of the protocol's public roles only, not of a run. -/
abbrev RoleFloor {O : OutputSchema} (F : ProtocolFamily O) (V : Type) [Fintype V]
    [DecidableEq V] :=
  (E : Env V) → (protoOf F E).Role → Option Time

/-- The time floors of chain-shape roles on grid `G`: the start of the slot for a slot proposal
and for a committee duty (`t_s`); none for the poll role, which carries no slot. -/
def shapeFloor {Kind : Type} (G : Blocks.TimeGrid) : Shape.ShapeRole Kind → Option Time
  | .proposer s => some (G.slotTime s)
  | .duty s _ => some (G.slotTime s)
  | .poll => none

/-- The role floors of a compiled chain-shape family: `shapeFloor` of each environment's grid. -/
def shapeRoleFloor {Info : Type} [DecidableEq Info] [Countable Info]
    (F : Shape.ChainShapeFamily O Info) (V : Type) [Fintype V] [DecidableEq V] :
    RoleFloor (Shape.compiled F) V :=
  fun E => shapeFloor (F (pubOf E)).skel.grid

variable (F) in
/-- **The canonical activity measure** of a run of `sysOf O F V` with role floors `fl`: the number
of validators active on `[a, b)` (`activeFaulty`). -/
noncomputable def activity (fl : RoleFloor F V) (r : (sysOf O F V).Run) (a b : Time) : ℕ :=
  (activeFaulty r.2 (fl r.1) a b).card

variable (F) in
/-- **The canonical content-origin hold** of a run of `sysOf O F V` (`ContentOriginHold`). -/
def contentHold (r : (sysOf O F V).Run) (G : V → Bool) (b₀ b₁ : Time) : Prop :=
  ContentOriginHold r.2 G b₀ b₁

end Consensus.Comparison

end
