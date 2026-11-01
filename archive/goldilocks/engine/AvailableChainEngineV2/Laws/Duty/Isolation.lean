module
public import AvailableChainEngineV2.Engine.Duty.Run -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Committees

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {In : Type} {P : ProtocolSpecD In}

def LabelFamilies.APObject (F : LabelFamilies P) (o : P.Object) : Prop :=
  match o.auth with
  | .seat ℓ _ => F.ap ℓ
  | .none => True

@[simp] theorem LabelFamilies.apObject_seat (F : LabelFamilies P) (ℓ : P.Label)
    (i : Fin (P.seats ℓ)) (p : P.Payload) : F.APObject ⟨.seat ℓ i, p⟩ ↔ F.ap ℓ :=
  Iff.rfl

@[simp] theorem LabelFamilies.apObject_none (F : LabelFamilies P) (p : P.Payload) :
    F.APObject ⟨.none, p⟩ :=
  trivial

structure Isolation (P : ProtocolSpecD In) (F : LabelFamilies P) where
  Base : Type
  base : P.State → Base
  clockB : Base → Time → Base
  clock_base : ∀ st t, base (P.clock st t) = clockB (base st) t
  processB : Base → P.Object → Base
  process_base : ∀ st o, base (P.process st o) = processB (base st) o
  recordOwn_base : ∀ st o, base (P.recordOwn st o) = base st
  actB : Base → P.Duty → In → Option P.Payload
  act_base : ∀ st d x, F.ap (P.signLabel d) → P.act st d x = actB (base st) d x
  gossipB : Base → Time → List P.Payload
  gossip_base : ∀ st t, P.gossip st t = gossipB (base st) t

  depsB : Base → P.Object → Bool

  processedB : Base → P.Object → Bool

  excludesB : Base → P.Object → Bool

  handlesB : Base → P.Object → P.Object → Prop

  hooks_base : ∀ st o, F.APObject o →
    P.depsPresent st o = depsB (base st) o ∧ P.processed st o = processedB (base st) o ∧
      P.excludes st o = excludesB (base st) o ∧
      ∀ o', F.APObject o' → (P.handles st o o' ↔ handlesB (base st) o o')

  separation : ∀ ℓ, F.ap ℓ ∨ F.fresh ℓ → P.selfVisible ℓ = false

namespace Isolation

variable {F : LabelFamilies P}

theorem foldl_recordOwn_base (iso : Isolation P F) :
    ∀ (l : List P.Object) (s : P.State), iso.base (l.foldl P.recordOwn s) = iso.base s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      simp only [List.foldl_cons]
      rw [ih]
      exact iso.recordOwn_base s o

theorem base_tick {V : Type} [DecidableEq V] (iso : Isolation P F) (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    iso.base (tick E rho st v t).1 = iso.clockB (iso.base st) t := by
  rw [tick_decomp, iso.foldl_recordOwn_base, iso.clock_base]

theorem hooks_congr (iso : Isolation P F) {st st' : P.State}
    (h : iso.base st = iso.base st') {o : P.Object} (ho : F.APObject o) :
    P.depsPresent st o = P.depsPresent st' o ∧ P.processed st o = P.processed st' o ∧
      P.excludes st o = P.excludes st' o ∧
      ∀ o', F.APObject o' → (P.handles st o o' ↔ P.handles st' o o') := by
  obtain ⟨hd, hp, hx, hh⟩ := iso.hooks_base st o ho
  obtain ⟨hd', hp', hx', hh'⟩ := iso.hooks_base st' o ho
  refine ⟨by rw [hd, hd', h], by rw [hp, hp', h], by rw [hx, hx', h], fun o' ho' => ?_⟩
  rw [hh o' ho', hh' o' ho', h]

theorem not_ap_of_selfVisible (iso : Isolation P F) {ℓ : P.Label}
    (h : P.selfVisible ℓ = true) : ¬ F.ap ℓ ∧ ¬ F.fresh ℓ := by
  refine ⟨fun ha => ?_, fun hf => ?_⟩
  · rw [iso.separation ℓ (Or.inl ha)] at h; exact Bool.false_ne_true h
  · rw [iso.separation ℓ (Or.inr hf)] at h; exact Bool.false_ne_true h

end Isolation

end AvailableChain.V2.D

end
