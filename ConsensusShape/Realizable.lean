module
public import ConsensusShape.Refinement
public import Mathlib.Tactic

@[expose] public section

/-! # Coverage and the extremal selection (L2)

* `coverage` (fixed selection): any well-formed environment point, with any
  PKI, any admissible selection and any GST `g`, is exactly the point, PKI and
  selection of a valid, collision-free, conviction-free compiled run whose log
  is eager from `g`. Progress requirements read only the point, the PKI and
  the selection, so whatever progress holds there holds on that run.
* The extremal selection (`extremalSel`) gives every `.sized m` role (`m`
  below the population) the keys `1, …, m`, all honest under the extremal PKI
  (`extremalKey`) when only validator `0` is faulty
  (`extremalSel_proposers`). Generic realizability (stage 4) builds its
  witnesses from these. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-! ## Fixed-selection coverage -/

/-- Fixed-selection coverage. Inputs are fixed, outputs preserve them: the
point `p`, the PKI `key`, an admissible selection `sel`, and a GST `g`. Some
valid, collision-free, conviction-free compiled run has exactly that point,
PKI and selection, and its log is eager from `g`. -/
theorem coverage (F : ShapeFamily O Info) {V : Type} [Fintype V] [DecidableEq V]
    (p : EnvPoint V) (hp : p.WellFormed) (key : Fin (Fintype.card V) ≃ V)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ r, ((protoOf (compiled F) p.env).selSpec r).Admits (sel r)) (g : Time) :
    ∃ rho : Model.Run (compiled F) p.env, rho.point = p ∧ rho.key = key ∧ rho.sel = sel ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧
      (sysOf O (compiled F) V).convicted ⟨p.env, rho⟩
        ((sysOf O (compiled F) V).honestEvidence ⟨p.env, rho⟩) = ∅ ∧
      CommLog.EagerFrom rho.point rho.log g := by
  let hash : (protoOf (compiled F) p.env).Item → Nat := fun x => Encodable.encode x + 1
  obtain ⟨relay, events, hv, he, hc⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.honest p.horizon hp key sel hsel
      p.submit hash g
  let rho := Model.mkRun (F := compiled F) (E := p.env) p.honest p.horizon key sel p.submit
    relay hash events
  refine ⟨rho, rfl, rfl, rfl, hv, ?_, ?_, he⟩
  · apply Model.Run.not_hashCollision_of_injective
    intro a b hab
    exact Encodable.encode_injective (Nat.add_right_cancel hab)
  · exact Model.convicted_honestEvidence_eq_empty rho (rho.not_slashable_of_causal hv hc)

/-! ## The extremal selection -/

/-- An admissible key set for each selection specification on `Fin N`:
everybody, the fixed set, or the keys `1, …, m` for `.sized m` with `m < N`
(everybody otherwise). Key `0` is selected only when a specification forces
it. -/
def extremalKeys {N : Nat} : SelSpec N → Finset (Fin N)
  | .all => Finset.univ
  | .fixed T => T
  | .sized m => if m < N then Finset.univ.filter fun k => 1 ≤ k.val ∧ k.val ≤ m else Finset.univ

theorem extremalKeys_admits {N : Nat} (s : SelSpec N) : s.Admits (extremalKeys s) := by
  cases s with
  | all => rfl
  | fixed T => rfl
  | sized m =>
    change (if m < N then Finset.univ.filter (fun k : Fin N => 1 ≤ k.val ∧ k.val ≤ m)
      else Finset.univ).card = min m N
    split_ifs with hm
    · rw [min_eq_left hm.le]
      have : (Finset.univ.filter fun k : Fin N => 1 ≤ k.val ∧ k.val ≤ m).map Fin.valEmbedding =
          Finset.Icc 1 m := by
        ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply, Finset.mem_Icc]
        constructor
        · rintro ⟨k, hk, rfl⟩; exact hk
        · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
      rw [← Finset.card_map, this, Nat.card_Icc]; omega
    · rw [Finset.card_univ, Fintype.card_fin, min_eq_right (by omega)]

/-- The extremal PKI on `Fin (n + 1)`: key `k` is validator `k`. -/
def extremalKey (n : Nat) : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
  finCongr (Fintype.card_fin _)

/-- The extremal selection: `extremalKeys` of every role's specification. -/
def extremalSel (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) :=
  fun r => extremalKeys ((protoOf (compiled F) E).selSpec r)

theorem extremalSel_admits (F : ShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    ∀ r, ((protoOf (compiled F) E).selSpec r).Admits (extremalSel F E r) :=
  fun _ => extremalKeys_admits _

/-- Under the extremal selection, a proposer selection `.sized m` with
`1 ≤ m ≤ n` selects the keys `1, …, m`; at a point where validators
`1, …, m` are honest and always awake, these are honest and ready, and at least
one is selected. -/
theorem extremalSel_proposers (F : ShapeFamily O Info) {n m : Nat}
    (p : EnvPoint (Fin (n + 1))) (hm1 : 1 ≤ m) (hm : m ≤ n)
    (hF : (F (pubOf p.env)).skel.proposerSel = .sized m)
    (hp : ∀ v : Fin (n + 1), 1 ≤ v.val → v.val ≤ m → v ∈ p.honest ∧ ∀ t, p.env.awake v t = true) :
    ∀ s c t, HonestReadyIn p (extremalKey n) (extremalSel F p.env)
      (ShapeRole.proposer s : ShapeRole (F (pubOf p.env)).skel.Kind) c t := by
  intro s c t
  have hN : m < Fintype.card (Fin (n + 1)) := by rw [Fintype.card_fin]; omega
  have hsel : extremalSel F p.env (ShapeRole.proposer s) =
      Finset.univ.filter fun k => 1 ≤ k.val ∧ k.val ≤ m := by
    change extremalKeys (F (pubOf p.env)).skel.proposerSel = _
    rw [hF]
    simp only [extremalKeys, hN, ↓reduceIte]
  unfold HonestReadyIn
  rw [hsel]
  refine ⟨⟨⟨1, by omega⟩, by simp [hm1]⟩, ?_⟩
  intro k hk
  have hk' := (Finset.mem_filter.mp hk).2
  have hv : (extremalKey n k).val = k.val := rfl
  obtain ⟨hh, ha⟩ := hp (extremalKey n k) (by rw [hv]; exact hk'.1) (by rw [hv]; exact hk'.2)
  exact ⟨hh, hh, fun u _ _ => ha u⟩

/-- The relay is exercised: in a run partially synchronous with a GST at or
before `start` where every validator is always awake, an active liveness
witness (`TxLiveActive`) has an honest reader that receives the submitted
transaction by relay, never by its own submission. -/
theorem active_relay {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (rho : Model.Run (compiled F) E) {gst c start D : Time}
    (hs : CommLog.PSync rho.point rho.log gst) (hgs : gst ≤ start) (hD : 0 ≤ D)
    (hawake : ∀ v t, E.awake v t = true)
    (ha : ((sysOf O (compiled F) V).trace ⟨E, rho⟩).TxLiveActive c start D) :
    ∃ x, ∃ w ∈ rho.honest, (∀ τ, x ∉ rho.submit w τ) ∧ ∃ τ, 0 ≤ τ ∧ x ∈ rho.relay w τ := by
  obtain ⟨x, t, t', u, w, ht0, hu, hua, hx, hw, -, hnw, hdl, hth, -⟩ := ha
  change u ∈ rho.honest at hu
  change w ∈ rho.honest at hw
  change x ∈ rho.submit u t at hx
  change ∀ τ, x ∉ rho.submit w τ at hnw
  change max t start + E.Δ + D ≤ t' at hdl
  change t' ≤ rho.horizon at hth
  have hm : max t gst ≤ max t start := max_le_max le_rfl hgs
  have hd : max t gst + E.Δ ≤ rho.horizon := by linarith
  obtain ⟨τ, hτ, -, hxτ⟩ := hs.txs u hu x t ht0 hua hx w hw t le_rfl hd hd (hawake w _)
  refine ⟨x, w, hw, hnw, τ, hτ, ?_⟩
  rcases List.mem_append.mp hxτ with h | h
  · exact absurd h (hnw τ)
  · exact h

end Consensus.Shape

end
