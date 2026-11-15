module
public import ConsensusLean.Spec.Shape.Active
public import ConsensusLean.Lemmas.Shape.Payload
public import ConsensusLean.Spec.Shape.ProgressFit
import ConsensusLean.Lemmas.Problem.Constant
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Coverage, the extremal selection and generic realizability (L2)

* `coverage` (fixed selection): any environment point with `0 ≤ horizon`, with any
  PKI, any admissible selection and any GST `g`, is exactly the point, PKI and
  selection of a valid, collision-free, conviction-free compiled run whose log
  is eager from `g`. Progress requirements read only the point, the PKI and
  the selection, so whatever progress holds there holds on that run.
* The extremal selection (`extremalSel`) gives every `.sized m` role (`m`
  below the population) the keys `1, …, m`; a `.sized 1` proposer role selects
  exactly key `1` (`extremalSel_proposer_mem`), honest when only key `0` is
  faulty.
* Generic realizability (`regimes_realizable`): L0
  `Realizable` for every family whose progress fits its skeleton and every
  progress-tolerant admissible contract with `Params.Room`, with active progress
  windows (`ProgressActive`). Witnesses: `sleepy_witness`,
  `healthy_witness`, `outage_witness` and `sleepyStress_witness` (a bounded
  awake profile), and the L2-only bad-proposer witness (`healthy_witness_sel`
  under the bad-slot selection `badSel`, `bad_selection`): a faulty proposer
  slot in every progress window. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

section Activity

variable (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem progLen_nonneg (cap : Capability) (i : K.Idx) (E : Env V) : 0 ≤ progLen F K cap i E := by
  unfold progLen
  split
  · exact mul_nonneg (by positivity) (F (pubOf E)).skel.grid.slotLen_pos.le
  · exact le_rfl

/-- Active realizability gives L0 realizability (the four L0 witness
families, dropping `ProgressActive`; `badProposer` has no L0 counterpart). -/
theorem RealizableActive.toRealizable {V : Type} [Fintype V] [DecidableEq V]
    (h : RealizableActive F K V) : Realizable (Sys F V) (shapeProgress F V) K where
  sleepy cap i Δ ΔF hΔ hΔF :=
    (h.sleepy cap i Δ ΔF hΔ hΔF).imp fun _ h => ⟨h.1, h.2.1⟩
  healthy cap i Δ ΔF g hΔ hΔF hr hg :=
    (h.healthy cap i Δ ΔF g hΔ hΔF hr hg).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  sleepyStress cap hc ho k hk hθ :=
    (h.sleepyStress cap hc ho k hk hθ).imp fun _ h Δ ΔF hΔ hΔF =>
    (h Δ ΔF hΔ hΔF).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  outage := h.outage
  sleepyGrowth cap i Δ ΔF hΔ hΔF :=
    (h.sleepyGrowth cap i Δ ΔF hΔ hΔF).imp fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  healthyGrowth cap i Δ ΔF g hΔ hΔF hr hg :=
    (h.healthyGrowth cap i Δ ΔF g hΔ hΔF hr hg).imp fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  outageGrowth := h.outageGrowth

end Activity

/-! ## Fixed-selection coverage -/

/-- Fixed-selection coverage. Inputs are fixed, outputs preserve them: the
point `p`, the PKI `key`, an admissible selection `sel`, and a GST `g`. Some
valid, collision-free, conviction-free compiled run has exactly that point,
PKI and selection, and its log is eager from `g`. -/
theorem coverage (F : ChainShapeFamily O Info) {V : Type} [Fintype V] [DecidableEq V]
    (p : EnvPoint V) (hp : 0 ≤ p.horizon) (key : Fin (Fintype.card V) ≃ V)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : (protoOf (compiled F) p.env).SelAdmits sel) (g : Time) :
    ∃ rho : Model.Run (compiled F) p.env, rho.point = p ∧ rho.key = key ∧ rho.sel = sel ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧
      Consensus.convicted ((Sys F V).convicts ⟨p.env, rho⟩)
        ((Sys F V).honestEvidenceBy ⟨p.env, rho⟩ p.horizon) = ∅ ∧
      CommLog.EagerFrom rho.point rho.log g := by
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) p.env).Item
  obtain ⟨relay, events, hv, he, hc⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.faultyAt p.faultyAt_mono
      p.horizon hp key sel hsel p.submit hash g
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt p.faultyAt_mono
      p.horizon events key sel p.submit relay hash
  refine ⟨rho, rfl, rfl, rfl, hv, ?_, ?_, he⟩
  · exact Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj)
  · exact Model.convicted_honestEvidence_eq_empty rho hv (rho.not_slashable_of_causal hc)

/-! ## The extremal selection -/

/-- An admissible key set for each selection specification on `Fin N`:
the fixed set, or the keys `1, …, m` for `.sized m` with `m < N`
(everybody otherwise). Key `0` is selected only when a specification forces
it. -/
def extremalKeys {N : Nat} : SelSpec N → Finset (Fin N)
  | .fixed T => T
  | .sized m => if m < N then Finset.univ.filter fun k => 1 ≤ k.val ∧ k.val ≤ m else Finset.univ

theorem extremalKeys_fixed {N : Nat} (T : Finset (Fin N)) :
    extremalKeys (.fixed T) = T := by rfl

theorem extremalKeys_sized {N : Nat} (m : Nat) :
    extremalKeys (N := N) (.sized m) =
      if m < N then Finset.univ.filter (fun k : Fin N => 1 ≤ k.val ∧ k.val ≤ m)
      else Finset.univ := by rfl

theorem extremalKeys_admits {N : Nat} (s : SelSpec N) : s.Admits (extremalKeys s) := by
  cases s with
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

/-- The extremal selection: `extremalKeys` of every role's specification. -/
def extremalSel (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) :=
  fun r => extremalKeys ((protoOf (compiled F) E).selSpec r)

theorem extremalSel_apply (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V)
    (r : (protoOf (compiled F) E).Role) :
    extremalSel F E r = extremalKeys ((protoOf (compiled F) E).selSpec r) := by rfl

theorem extremalSel_admits (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    (protoOf (compiled F) E).SelAdmits (extremalSel F E) :=
  fun _ => extremalKeys_admits _

/-- Fix one admitted committee for the participation kind at every slot.
All other roles, including the proposer, retain the extremal selection. -/
def outageSel (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V)
    (C : Finset (Fin (Fintype.card V))) :
    (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) :=
  fun r => match r with
    | .duty _ k => if (F (pubOf E)).skel.participationKind = some k then C else extremalSel F E r
    | _ => extremalSel F E r

theorem outageSel_admits (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V)
    (C : Finset (Fin (Fintype.card V)))
    (hC : ∀ k, (F (pubOf E)).skel.participationKind = some k →
      ((F (pubOf E)).skel.kindSel k).Admits C) :
    (protoOf (compiled F) E).SelAdmits (outageSel F E C) := by
  intro r
  cases r with
  | proposer s => exact extremalSel_admits F E (.proposer s)
  | poll => exact extremalSel_admits F E .poll
  | duty s k =>
    change ((F (pubOf E)).skel.kindSel k).Admits
      (if (F (pubOf E)).skel.participationKind = some k then C else extremalSel F E (.duty s k))
    split_ifs with hk
    · exact hC k hk
    · exact extremalSel_admits F E (.duty s k)

/-- The chosen participation set is constant; admitted selections in general
need not be constant for a sized specification. -/
theorem outageSel_selected (F : ChainShapeFamily O Info) {V : Type}
    [Fintype V] [DecidableEq V] (E : Env V) (key : Fin (Fintype.card V) ≃ V)
    (C : Finset (Fin (Fintype.card V))) (t : Time) :
    (shapeProgress F V).selected E (key, outageSel F E C) t =
      if (F (pubOf E)).skel.participationKind.isSome then C.map key.toEmbedding
      else Finset.univ := by
  cases hk : (F (pubOf E)).skel.participationKind with
  | none => simp [shapeProgress, Model.sysExternal, protoOf, compiled, compile, hk]
  | some k => simp [shapeProgress, Model.sysExternal, protoOf, compiled, compile,
      outageSel, hk]

/-- Put both exceptional identities outside a small committee, and the sleeper
outside a committee missing exactly one identity. -/
theorem exists_outage_pair {N : Nat} (hn : 3 ≤ N) (C : Finset (Fin N)) :
    ∃ f s : Fin N, f ≠ s ∧
      (f ∉ C ∧ s ∉ C ∨ N - 1 ≤ C.card ∧ (C.card < N → s ∉ C)) := by
  classical
  by_cases hc : N - 1 ≤ C.card
  · by_cases hfull : C.card < N
    · obtain ⟨s, hs⟩ : ∃ s, s ∉ C := by
        by_contra h
        push Not at h
        have he := Finset.eq_univ_of_forall h
        simp only [he, Finset.card_univ, Fintype.card_fin, lt_self_iff_false] at hfull
      obtain ⟨f, hf⟩ : ∃ f : Fin N, f ≠ s := by
        by_cases h0 : (⟨0, by omega⟩ : Fin N) = s
        · exact ⟨⟨1, by omega⟩, by rw [← h0]; simp⟩
        · exact ⟨⟨0, by omega⟩, h0⟩
      exact ⟨f, s, hf, Or.inr ⟨hc, fun _ => hs⟩⟩
    · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, by simp, Or.inr ⟨hc, fun h => (hfull h).elim⟩⟩
  · have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    have htwo : 1 < (Finset.univ \ C).card := by
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      omega
    obtain ⟨f, hf, s, hs, hfs⟩ := Finset.one_lt_card.mp htwo
    exact ⟨f, s, hfs, Or.inl ⟨(Finset.mem_sdiff.mp hf).2, (Finset.mem_sdiff.mp hs).2⟩⟩

/-- Send two distinct indices to two distinct targets. -/
theorem exists_perm_pair {N : Nat} {a b : Fin N} (hab : a ≠ b) (f s : Fin N) (hfs : f ≠ s) :
    ∃ e : Equiv.Perm (Fin N), e a = f ∧ e b = s := by
  let e := Equiv.swap a f
  have hne : e b ≠ f := by
    rw [← Equiv.swap_apply_left a f]
    exact e.injective.ne hab.symm
  refine ⟨e.trans (Equiv.swap (e b) s), ?_, ?_⟩
  · change Equiv.swap (e b) s (e a) = f
    rw [show e a = f from Equiv.swap_apply_left a f]
    exact Equiv.swap_apply_of_ne_of_ne hne.symm hfs
  · exact Equiv.swap_apply_left (e b) s

/-- Reindex the PKI so a fixed committee avoids the witness's two exceptional
validators, unless its cardinality already supplies the required margin. -/
theorem exists_outage_key {V : Type} [Fintype V]
    (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V)
    (C : Finset (Fin (Fintype.card V))) :
    ∃ key' : Fin (Fintype.card V) ≃ V,
      (key ⟨0, by omega⟩ ∉ C.map key'.toEmbedding ∧
        key ⟨2, by omega⟩ ∉ C.map key'.toEmbedding) ∨
      Fintype.card V - 1 ≤ (C.map key'.toEmbedding).card ∧
        ((C.map key'.toEmbedding).card < Fintype.card V →
          key ⟨2, by omega⟩ ∉ C.map key'.toEmbedding) := by
  obtain ⟨f, s, hfs, hgood⟩ := exists_outage_pair hn C
  obtain ⟨e, he0, he2⟩ := exists_perm_pair (a := ⟨0, by omega⟩) (b := ⟨2, by omega⟩)
    (by simp) f s hfs
  refine ⟨e.symm.trans key, ?_⟩
  rcases hgood with ⟨hf, hs⟩ | hlarge
  · left
    constructor
    · intro hv
      obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hv
      have hj0 : e.symm j = ⟨0, by omega⟩ := key.injective he
      have hjf : j = f := by simpa only [Equiv.apply_symm_apply, he0] using congrArg e hj0
      exact hf (hjf ▸ hj)
    · intro hv
      obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hv
      have hj2 : e.symm j = ⟨2, by omega⟩ := key.injective he
      have hjs : j = s := by simpa only [Equiv.apply_symm_apply, he2] using congrArg e hj2
      exact hs (hjs ▸ hj)
  · refine Or.inr ⟨by simpa only [Finset.card_map] using hlarge.1, ?_⟩
    intro hc hv
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hv
    have hj2 : e.symm j = ⟨2, by omega⟩ := key.injective he
    have hjs : j = s := by simpa only [Equiv.apply_symm_apply, he2] using congrArg e hj2
    exact hlarge.2 (by simpa only [Finset.card_map] using hc) (hjs ▸ hj)

/-- Choose one constant admitted participation set and a compatible PKI.
The environment and its exceptional validators remain unchanged. -/
theorem exists_outage_selection (F : ChainShapeFamily O Info) {V : Type}
    [Fintype V] [DecidableEq V] (E : Env V) (key : Fin (Fintype.card V) ≃ V)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (key' : Fin (Fintype.card V) ≃ V)
      (sel : (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V))) (C : Finset V),
      (protoOf (compiled F) E).SelAdmits sel ∧
      (∀ t, (shapeProgress F V).selected E (key', sel) t = C) ∧
      ((key ⟨0, by omega⟩ ∉ C ∧ key ⟨2, by omega⟩ ∉ C) ∨
        Fintype.card V - 1 ≤ C.card ∧
          (C.card < Fintype.card V → key ⟨2, by omega⟩ ∉ C)) := by
  classical
  cases hk : (F (pubOf E)).skel.participationKind with
  | none =>
    refine ⟨key, outageSel F E Finset.univ, Finset.univ, ?_, ?_, Or.inr (by simp)⟩
    · exact outageSel_admits F E _ (by intro k h; simp [hk] at h)
    · intro t
      rw [outageSel_selected]
      simp only [hk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  | some k =>
    let D := extremalKeys ((F (pubOf E)).skel.kindSel k)
    obtain ⟨key', hgood⟩ := exists_outage_key key hn D
    refine ⟨key', outageSel F E D, D.map key'.toEmbedding, ?_, ?_, hgood⟩
    · apply outageSel_admits
      intro k' hk'
      have he : k' = k := Option.some.inj (hk'.symm.trans hk)
      subst k'
      exact extremalKeys_admits _
    · intro t
      rw [outageSel_selected]
      simp only [hk, Option.isSome_some, ↓reduceIte]

/-- The refined placement supplies the weighted participation margin. -/
theorem outage_committee_margin {V : Type} [Fintype V] [DecidableEq V]
    {θ : ℚ} (hθ : 0 ≤ θ ∧ θ < 1)
    (hroom : θ * (Fintype.card V : ℚ) < (Fintype.card V : ℚ) - 2) (C : Finset V)
    (f s : V) (hC : C.Nonempty)
    (hgood : f ∉ C ∧ s ∉ C ∨ Fintype.card V - 1 ≤ C.card ∧
      (C.card < Fintype.card V → s ∉ C)) :
    θ * ((((C.erase f).erase s).card : ℚ) + ({f} ∩ C).card) <
      ((C.erase f).erase s).card := by
  classical
  have hsum : ((C.erase f).erase s).card + ({f} ∩ C).card ≤ C.card := by
    have he : (C.erase f).card + ({f} ∩ C).card = C.card := by
      by_cases hf : f ∈ C
      · have := Finset.card_pos.mpr ⟨f, hf⟩
        rw [Finset.card_erase_of_mem hf, Finset.singleton_inter_of_mem hf,
          Finset.card_singleton]; omega
      · rw [Finset.erase_eq_of_notMem hf, Finset.singleton_inter_of_notMem hf,
          Finset.card_empty, Nat.add_zero]
    exact (Nat.add_le_add_right (Finset.card_le_card (Finset.erase_subset _ _)) _).trans he.le
  rcases hgood with ⟨hf, hs⟩ | hlarge
  · simp only [Finset.erase_eq_of_notMem hf, Finset.erase_eq_of_notMem hs,
      Finset.singleton_inter_of_notMem hf, Finset.card_empty, Nat.cast_zero, add_zero]
    exact mul_lt_of_lt_one_left (by exact_mod_cast hC.card_pos) hθ.2
  · have hlow₁ : C.card ≤ (C.erase f).card + 1 := by
      by_cases hf : f ∈ C
      · rw [Finset.card_erase_of_mem hf]; omega
      · rw [Finset.erase_eq_of_notMem hf]; omega
    have hlow₂ : (C.erase f).card ≤ ((C.erase f).erase s).card + 1 := by
      by_cases hs : s ∈ C.erase f
      · rw [Finset.card_erase_of_mem hs]; omega
      · rw [Finset.erase_eq_of_notMem hs]; omega
    have hsupport : Fintype.card V ≤ ((C.erase f).erase s).card + 2 := by
      by_cases hc : C.card < Fintype.card V
      · have hs := hlarge.2 hc
        have hs' : s ∉ C.erase f := fun h => hs (Finset.mem_of_mem_erase h)
        rw [Finset.erase_eq_of_notMem hs']
        omega
      · omega
    have hbound : (((C.erase f).erase s).card : ℚ) + ({f} ∩ C).card ≤
        (Fintype.card V : ℚ) := by
      exact_mod_cast hsum.trans (Finset.card_le_univ C)
    have hs : (Fintype.card V : ℚ) ≤ ((C.erase f).erase s).card + 2 := by
      exact_mod_cast hsupport
    exact (mul_le_mul_of_nonneg_left hbound hθ.1).trans_lt (by linarith only [hroom, hs])

/-- The committee index set the extremal selection reads at every time: every key without a
participation kind, else the extremal keys of the participation kind's specification. -/
def extremalCommittee (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) :
    Finset (Fin (Fintype.card V)) :=
  match (F (pubOf E)).skel.participationKind with
  | none => Finset.univ
  | some k => extremalKeys ((F (pubOf E)).skel.kindSel k)

/-- A selection that is extremal on every duty role selects the extremal committee at every
time. -/
theorem selected_of_duty (F : ChainShapeFamily O Info) {V : Type} [Fintype V] [DecidableEq V]
    (E : Env V) (key : Fin (Fintype.card V) ≃ V)
    (sel : (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ s k, sel (ShapeRole.duty s k : ShapeRole (F (pubOf E)).skel.Kind) =
      extremalSel F E (ShapeRole.duty s k : ShapeRole (F (pubOf E)).skel.Kind)) (t : Time) :
    (shapeProgress F V).selected E (key, sel) t = (extremalCommittee F E).map key.toEmbedding := by
  unfold extremalCommittee
  cases hk : (F (pubOf E)).skel.participationKind with
  | none => simp [shapeProgress, Model.sysExternal, protoOf, compiled, compile, hk]
  | some k =>
    simp only [shapeProgress, Model.sysExternal, protoOf, compiled, compile, hk, Option.map_some]
    rw [hsel]
    rfl

/-- A run PKI that keeps key `1` and moves the faulty `key 0` out of the committee `D` (to index
`z`), unless `D` misses at most one key. Of the two indices outside a small `D`
(`exists_outage_pair`) one is not `1`. -/
theorem exists_witness_key {V : Type} [Fintype V]
    (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V)
    (D : Finset (Fin (Fintype.card V))) :
    ∃ (key' : Fin (Fintype.card V) ≃ V) (z : Fin (Fintype.card V)),
      key' z = key ⟨0, by omega⟩ ∧ key' ⟨1, by omega⟩ = key ⟨1, by omega⟩ ∧
      (key ⟨0, by omega⟩ ∉ D.map key'.toEmbedding ∨
        Fintype.card V - 1 ≤ (D.map key'.toEmbedding).card) := by
  obtain ⟨f, s, hfs, hgood⟩ := exists_outage_pair (by omega) D
  rcases hgood with ⟨hf, hs⟩ | hlarge
  · obtain ⟨j, hjD, hj1⟩ : ∃ j, j ∉ D ∧ j ≠ ⟨1, by omega⟩ := by
      by_cases h : f = ⟨1, by omega⟩
      · exact ⟨s, hs, fun hs1 => hfs (h.trans hs1.symm)⟩
      · exact ⟨f, hf, h⟩
    refine ⟨(Equiv.swap ⟨0, by omega⟩ j).trans key, j, ?_, ?_, Or.inl ?_⟩
    · simp only [Equiv.trans_apply, Equiv.swap_apply_right]
    · simp only [Equiv.trans_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) hj1.symm]
    · intro hm
      obtain ⟨x, hx, he⟩ := Finset.mem_map.mp hm
      have hx0 : Equiv.swap ⟨0, by omega⟩ j x = ⟨0, by omega⟩ := key.injective he
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at hx0
      exact hjD (hx0 ▸ hx)
  · exact ⟨key, ⟨0, by omega⟩, rfl, rfl,
      Or.inr (by simpa only [Finset.card_map] using hlarge.1)⟩

/-- A run PKI and an index `q ∈ D` of key `1` that move the faulty `key 0` out of a nonempty
committee `D` other than the whole population. -/
theorem exists_stress_key {V : Type} [Fintype V]
    (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V)
    (D : Finset (Fin (Fintype.card V))) :
    ∃ (key' : Fin (Fintype.card V) ≃ V) (q : Fin (Fintype.card V)),
      key' q = key ⟨1, by omega⟩ ∧ (D.Nonempty →
        D = Finset.univ ∨ key ⟨0, by omega⟩ ∉ D.map key'.toEmbedding ∧ q ∈ D) := by
  classical
  by_cases h : D.Nonempty ∧ D ≠ Finset.univ
  · obtain ⟨⟨i, hi⟩, hD⟩ := h
    obtain ⟨j, hj⟩ : ∃ j, j ∉ D := by
      by_contra hall
      push Not at hall
      exact hD (Finset.eq_univ_of_forall hall)
    obtain ⟨e, he0, he1⟩ := exists_perm_pair (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩)
      (by simp) j i (fun hji => hj (hji ▸ hi))
    refine ⟨e.symm.trans key, i, ?_, fun _ => Or.inr ⟨?_, hi⟩⟩
    · simp only [Equiv.trans_apply, ← he1, Equiv.symm_apply_apply]
    · intro hm
      obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp hm
      have hx0 : e.symm x = ⟨0, by omega⟩ := key.injective hxe
      rw [Equiv.symm_apply_eq, he0] at hx0
      exact hj (hx0 ▸ hx)
  · refine ⟨key, ⟨1, by omega⟩, rfl, fun hne => Or.inl ?_⟩
    by_contra hD
    exact h ⟨hne, hD⟩

/-- A constant awake profile with weighted selected support meets the committee clause, for
every look-back and catch-up. This applies to every retained view used by the witnesses. -/
theorem committee_of_constant_awake {V : Type} [Fintype V] [DecidableEq V]
    (p : EnvPoint V) (C : Finset V) (θ : ℚ) (η c W : Time)
    (hθ : 0 ≤ θ) (hc : 0 ≤ c)
    (haw : ∀ v t u, p.env.awake v t = p.env.awake v u)
    (hmargin : ∀ d, C.Nonempty →
      θ * (((p.retain d).awakeAt 0 ∩ C).card + (p.faultyAt d ∩ C).card : ℚ) <
        ((p.retain d).awakeAt 0 ∩ C).card) :
    p.CommitteeSleepyOn (fun _ => C) θ η c W 0 p.horizon := by
  classical
  have hready (d t : Time) (ht : 0 ≤ t) :
      (p.retain d).readyAt c t = (p.retain d).awakeAt 0 := by
    ext v
    constructor
    · intro hv
      obtain ⟨_, hh, hr⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩,
        (haw v 0 t).trans (hr t (max_le ht (by linarith)) le_rfl)⟩
    · intro hv
      obtain ⟨hh, hr⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hh).2,
        fun u _ _ => (haw v u 0).trans hr⟩
  intro t ht _ hC
  let d := p.lookAhead W t
  have hcount := hmargin d hC
  dsimp only
  split_ifs
  · rw [hready d t ht]
    exact_mod_cast hcount
  · have hsub : (p.retain d).awakeIn (max 0 (t - η)) t ⊆ (p.retain d).awakeAt 0 := by
      intro v hv
      obtain ⟨_, u, -, -, hh, hu⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩,
        (haw v 0 u).trans hu⟩
    rw [hready d t ht, Finset.union_eq_left.mpr hsub]
    have hn := Finset.card_union_le ((p.retain d).awakeAt 0 ∩ C) (p.faultyAt d ∩ C)
    rw [← Finset.union_inter_distrib_right] at hn
    have hnq : ((((p.retain d).awakeAt 0 ∪ p.faultyAt d) ∩ C).card : ℚ) ≤
        ((p.retain d).awakeAt 0 ∩ C).card + (p.faultyAt d ∩ C).card := by
      exact_mod_cast hn
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hnq hθ) hcount

/-- The room bound controls a selected committee with at most one fault. -/
theorem committeeHealthy_of_one_fault {V : Type} [Fintype V] [DecidableEq V]
    (hn : 3 ≤ Fintype.card V) (p : EnvPoint V) (C : Finset V) (f : V) {βK : ℚ}
    (hβK : 0 < βK) (hroom : 1 < βK * ((Fintype.card V : ℚ) - 1))
    (a b : Time) (hf : p.faultyAt b ⊆ {f})
    (hgood : f ∉ C ∨ Fintype.card V - 1 ≤ C.card) :
    p.CommitteeHealthyOn (fun _ => C) βK a b := by
  intro _ _ _ hC
  change ((p.faultyAt b ∩ C).card : ℚ) < βK * C.card
  have hle := Finset.card_le_card (Finset.inter_subset_inter hf (Finset.Subset.refl C))
  rcases hgood with hfC | hlarge
  · rw [Finset.singleton_inter_of_notMem hfC, Finset.card_empty] at hle
    rw [Nat.eq_zero_of_le_zero hle, Nat.cast_zero]
    exact mul_pos hβK (by exact_mod_cast hC.card_pos)
  · have h1 : ({f} ∩ C).card ≤ 1 := (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    have hn1 : Fintype.card V - 1 + 1 = Fintype.card V := by omega
    have hsize : (Fintype.card V : ℚ) - 1 ≤ C.card := by
      have hq : ((Fintype.card V - 1 : Nat) : ℚ) + 1 = Fintype.card V := by
        exact_mod_cast hn1
      have hq' : ((Fintype.card V - 1 : Nat) : ℚ) ≤ C.card := by exact_mod_cast hlarge
      linarith only [hq, hq']
    have hF : ((p.faultyAt b ∩ C).card : ℚ) ≤ 1 := by exact_mod_cast hle.trans h1
    exact hF.trans_lt (hroom.trans_le (mul_le_mul_of_nonneg_left hsize hβK.le))

/-! ## The bad-slot selection -/

/-- A proposer role at a periodic bad slot: slot `s` with `s % P = P − 1`. -/
def badSlotRole {Kind : Type} (P : Nat) : ShapeRole Kind → Bool
  | .proposer s => decide (s % P = P - 1)
  | _ => false

theorem badSlotRole_proposer {Kind : Type} (P : Nat) (s : Slot) :
    badSlotRole (Kind := Kind) P (.proposer s) = decide (s % P = P - 1) := by rfl

theorem badSlotRole_duty {Kind : Type} (P : Nat) (k : Kind) (s : Slot) :
    badSlotRole P (.duty s k) = false := by rfl

theorem badSlotRole_poll {Kind : Type} (P : Nat) :
    badSlotRole (Kind := Kind) P .poll = false := by rfl

/-- The bad-slot selection with period `P` and bad key `z` (faulty at the witness points):
key `z` proposes at every slot `s` with `s % P = P − 1` (at every slot when `P = 1`); every other
role is selected as by `extremalSel`. -/
def badSel (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) (P : Nat)
    (z : Fin (Fintype.card V)) :
    (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) :=
  fun r => if badSlotRole (Kind := (F (pubOf E)).skel.Kind) P r then {z}
    else extremalSel F E r

theorem badSel_apply (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) (P : Nat)
    (z : Fin (Fintype.card V)) (r : (protoOf (compiled F) E).Role) :
    badSel F E P z r =
      if badSlotRole (Kind := (F (pubOf E)).skel.Kind) P r then {z}
      else extremalSel F E r := by rfl

/-- With one proposer per slot, the bad-slot selection is admissible. -/
theorem badSel_admits (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) (P : Nat)
    (z : Fin (Fintype.card V)) (hF : ∀ s, (F (pubOf E)).skel.proposerSel s = .sized 1) :
    (protoOf (compiled F) E).SelAdmits (badSel F E P z) := by
  intro r
  rw [badSel_apply]
  split_ifs with hb
  · change ShapeRole (F (pubOf E)).skel.Kind at r
    cases r with
    | proposer s =>
      change SelSpec.Admits ((F (pubOf E)).skel.proposerSel s) _
      rw [hF]
      change ({z} : Finset (Fin (Fintype.card V))).card = min 1 (Fintype.card V)
      have := z.pos
      rw [Finset.card_singleton]; omega
    | duty _ _ => simp [badSlotRole_duty] at hb
    | poll => simp [badSlotRole_poll] at hb
  · exact extremalSel_admits F E r

/-- Under the bad-slot selection, the proposer of a bad slot is exactly key `z`. -/
theorem badSel_bad (F : ChainShapeFamily O Info) {V : Type} [Fintype V] {E : Env V} {P : Nat}
    (z : Fin (Fintype.card V)) {s : Slot} (hs : s % P = P - 1) :
    badSel F E P z (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) = {z} := by
  simp only [badSel_apply F E P z (.proposer s), badSlotRole_proposer, hs, decide_true, ↓reduceIte]

/-- The bad-slot selection is extremal on every duty role. -/
theorem badSel_duty (F : ChainShapeFamily O Info) {V : Type} [Fintype V] (E : Env V) (P : Nat)
    (z : Fin (Fintype.card V)) (s : Slot) (k : (F (pubOf E)).skel.Kind) :
    badSel F E P z (ShapeRole.duty s k : ShapeRole (F (pubOf E)).skel.Kind) =
      extremalSel F E (ShapeRole.duty s k : ShapeRole (F (pubOf E)).skel.Kind) := by
  simp only [badSel_apply F E P z (.duty s k), badSlotRole_duty, Bool.false_eq_true, ↓reduceIte]

/-! ## Generic realizability

`regimes_realizable`: for every family whose progress fits its skeleton and
every admissible, progress-tolerant contract, with `Params.Room`,
every regime of the
L0 table is met by a clean witness with active claims, at every `Δ`, every
GST and arbitrarily late outages; in addition, every progress window of the
sleepy and healthy witnesses lies inside the horizon (`ProgressActive`).

The witnesses: validator `key 0` faulty, every other validator honest, at the
point PKI `Fintype.equivFin`; the extremal selection (`.sized 1` proposer roles
select key `1`, honest and always awake); transaction `42` submitted to
`key 1` at time `0`, read by `key 2`. The selected committees are constant
(`selected_of_duty`), but a `.fixed` participation specification may name the
faulty key's index, so the run PKI is reindexed as for the outage witness: it
keeps key `1` and moves the faulty key out of the committee unless the committee
misses at most one key (`exists_witness_key`); then the committee is sleepy and
its faulty fraction is below `βK` by `Room` (`committeeHealthy_of_one_fault`).

* stress: `m = min k (n − 1)` honest keys awake, with `θ·(m + 1) < m`; the run PKI
  puts key `1` inside a committee that is not every key and the faulty key outside it
  (`exists_stress_key`), and key `1` proposes every slot (`stress_selection`);
* bad proposer: the healthy witness (everyone awake) under the bad-slot
  selection, where the faulty key (index `z` of the run PKI) proposes every slot `s` with
  `s % (span + 2) = span + 1` (so every window of a recurrence with
  `span + 2 ≤ gap` holds a faulty proposer slot and a whole good pattern);
* sleepy and healthy: everyone awake (healthy is full participation, and the
  one faulty validator is below `β·n` by `Room`); the healthy witness is the canonical
  run from the GST `g`, whose log has no message receipt before `g` (protocol
  messages sent before `g` are received at `g` by the recipients awake then;
  transaction relay is part of the log too). The witness exercises delayed
  delivery only as far as the family sends messages before `g`;
* outage: honest `key 2` always asleep, so at most two validators are not
  ready at any time, for every catch-up; η-sleepy participation holds for every
  look-back `η` (the look-back set has at most `n` members), and inside every
  committee of the time-constant selection. `Room` supplies `θ·n < n − 2`, and the
  selection keeps the sleeper outside a committee missing exactly one identity.
  The log is eager from `0`: the outage witness exercises
  participation (one honest sleeper in the window, a ready reader from the
  recovery point), not asynchrony.

Thresholds use the contract's fractions and `Params.Room`, not fixed optimal fractions. -/

section Realize

variable (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The witness points -/

variable {F K}

/-- The witness point: `Δ`, awake profile `awake`, horizon `H`; validator
`key 0` faulty, every other validator honest; transaction `42` submitted to
`key 1` at time `0`. -/
def realPoint (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V) (Δ : Time)
    (hΔ : 0 < Δ) (ΔF : Time) (hΔF : 0 < ΔF) (awake : V → Time → Bool) (H : Time) : EnvPoint V :=
  ⟨⟨Δ, hΔ, ΔF, hΔF, awake⟩, fun _ => {key ⟨0, by omega⟩}, monotone_const, H,
    fun v t => if v = key ⟨1, by omega⟩ ∧ t = 0 then [42] else []⟩

theorem realPoint_eq (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V) (Δ : Time)
    (hΔ : 0 < Δ) (ΔF : Time) (hΔF : 0 < ΔF) (awake : V → Time → Bool) (H : Time) :
    realPoint key hn Δ hΔ ΔF hΔF awake H =
      ⟨⟨Δ, hΔ, ΔF, hΔF, awake⟩, fun _ => {key ⟨0, by omega⟩}, monotone_const, H,
        fun v t => if v = key ⟨1, by omega⟩ ∧ t = 0 then [42] else []⟩ := by rfl

/-- Everyone awake at every time. -/
def allAwake : V → Time → Bool := fun _ _ => true

/-- `s` always asleep; everyone else always awake. -/
def asleepAlways (s : V) : V → Time → Bool := fun v _ => !decide (v = s)

omit [Fintype V] [DecidableEq V] in
theorem allAwake_apply (v : V) (t : Time) : allAwake v t = true := by rfl

omit [Fintype V] in
theorem asleepAlways_apply (s : V) (v : V) (t : Time) :
    asleepAlways s v t = !decide (v = s) := by rfl

section Point

variable (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V) {Δ : Time} (hΔ : 0 < Δ)
  {ΔF : Time} (hΔF : 0 < ΔF)
  (awake : V → Time → Bool) (H : Time)

/-- The validator of key `j`. -/
abbrev kv (j : Nat) (hj : j < 3) : V := key ⟨j, by omega⟩

omit [DecidableEq V] in
theorem kv_eq (j : Nat) (hj : j < 3) : kv key hn j hj = key ⟨j, by omega⟩ := by rfl

omit [DecidableEq V] in
theorem kv_ne {j j' : Nat} {hj : j < 3} {hj' : j' < 3} (h : j ≠ j') :
    kv key hn j hj ≠ kv key hn j' hj' := by
  intro he
  have := congrArg Fin.val (key.injective he)
  exact h this

theorem realPoint_env :
    (realPoint key hn Δ hΔ ΔF hΔF awake H).env = ⟨Δ, hΔ, ΔF, hΔF, awake⟩ := by rfl

theorem realPoint_constant : (realPoint key hn Δ hΔ ΔF hΔF awake H).ConstantFaults :=
  fun _ => rfl

theorem realPoint_faulty (t : Time) :
    (realPoint key hn Δ hΔ ΔF hΔF awake H).faultyAt t = {kv key hn 0 (by decide)} := by rfl

theorem realPoint_honest {j : Nat} (hj : j < 3) (h0 : j ≠ 0) {t : Time} :
    (realPoint key hn Δ hΔ ΔF hΔF awake H).HonestAt (kv key hn j hj) t := by
  simpa only [EnvPoint.HonestAt, realPoint_faulty, Finset.mem_singleton] using
    (kv_ne key hn (hj' := by decide) h0)

theorem realPoint_card_honest (t : Time) :
    ((realPoint key hn Δ hΔ ΔF hΔF awake H).honestAt t).card + 1 = Fintype.card V := by
  simp only [EnvPoint.honestAt, realPoint_faulty, Finset.sdiff_singleton_eq_erase]
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  omega

/-- A set of honest, always-awake validators is ready at every time. -/
theorem card_le_readyAt (A : Finset V)
    (hA : ∀ v ∈ A, (realPoint key hn Δ hΔ ΔF hΔF awake H).HonestAt v 0 ∧
      ∀ t, awake v t = true)
    (c t : Time) : A.card ≤ ((realPoint key hn Δ hΔ ΔF hΔF awake H).readyAt c t).card := by
  classical
  apply Finset.card_le_card
  intro v hv
  unfold EnvPoint.readyAt
  obtain ⟨hh, ha⟩ := hA v hv
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, fun u _ _ => ha u⟩
  exact ((realPoint key hn Δ hΔ ΔF hΔF awake H).honestAt_iff_zero
    (realPoint_constant key hn hΔ hΔF awake H) v t).mpr hh

/-- Everyone awake: all honest validators are ready at every time. -/
theorem allAwake_readyAt (c t : Time) :
    Fintype.card V ≤ ((realPoint key hn Δ hΔ ΔF hΔF allAwake H).readyAt c t).card + 1 := by
  have := card_le_readyAt key hn hΔ hΔF allAwake H
    ((realPoint key hn Δ hΔ ΔF hΔF allAwake H).honestAt 0)
    (fun v hv => ⟨(Finset.mem_sdiff.mp hv).2, fun _ => rfl⟩) c t
  have := realPoint_card_honest key hn hΔ hΔF allAwake H 0
  omega

/-- One sleeper `key 2`: all honest validators but one are ready at every
time. -/
theorem asleepAlways_readyAt (c t : Time) :
    Fintype.card V ≤
      ((realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H).readyAt
        c t).card + 2 := by
  have h2 : kv key hn 2 (by decide) ∈
      (realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H).honestAt 0 := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      realPoint_honest key hn hΔ hΔF _ H (by decide) (by decide)⟩
  have h := card_le_readyAt key hn hΔ hΔF (asleepAlways (kv key hn 2 (by decide))) H
    (((realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H).honestAt 0).erase
      (kv key hn 2 (by decide))) (fun v hv => by
      obtain ⟨hne, hv⟩ := Finset.mem_erase.mp hv
      exact ⟨(Finset.mem_sdiff.mp hv).2, fun t => by simp [asleepAlways_apply, hne]⟩) c t
  rw [Finset.card_erase_of_mem h2] at h
  have := realPoint_card_honest key hn hΔ hΔF (asleepAlways (kv key hn 2 (by decide))) H 0
  omega

/-- Selected support at the one-fault, one-sleeper point. -/
theorem asleepAlways_committee_margin {θ : ℚ} (hθ : 0 ≤ θ ∧ θ < 1)
    (hroom : θ * (Fintype.card V : ℚ) < (Fintype.card V : ℚ) - 2) (C : Finset V)
    (hgood : kv key hn 0 (by decide) ∉ C ∧ kv key hn 2 (by decide) ∉ C ∨
      Fintype.card V - 1 ≤ C.card ∧
        (C.card < Fintype.card V → kv key hn 2 (by decide) ∉ C))
    (d : Time) (hC : C.Nonempty) :
    let p := realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H
    θ * (((p.retain d).awakeAt 0 ∩ C).card + (p.faultyAt d ∩ C).card : ℚ) <
      ((p.retain d).awakeAt 0 ∩ C).card := by
  classical
  dsimp only
  have hset :
      ((realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H).retain d).awakeAt
        0 ∩ C = (C.erase (kv key hn 0 (by decide))).erase (kv key hn 2 (by decide)) := by
    ext v
    change (v ∈ (Finset.univ \ {kv key hn 0 (by decide)}).filter
      (fun w => asleepAlways (kv key hn 2 (by decide)) w 0 = true) ∩ C) ↔ _
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_singleton, true_and, asleepAlways_apply, Bool.not_eq_true',
      decide_eq_false_iff_not, Finset.mem_erase]
    tauto
  rw [hset, realPoint_faulty]
  exact outage_committee_margin hθ hroom C _ _ hC hgood

/-- Selected support at the one-fault, everyone-awake point. -/
theorem allAwake_committee_margin {θ : ℚ} (hθ : 0 ≤ θ ∧ θ < 1)
    (hroom : θ * (Fintype.card V : ℚ) < (Fintype.card V : ℚ) - 2) (C : Finset V)
    (hgood : kv key hn 0 (by decide) ∉ C ∨ Fintype.card V - 1 ≤ C.card) (d : Time)
    (hC : C.Nonempty) :
    let p := realPoint key hn Δ hΔ ΔF hΔF allAwake H
    θ * (((p.retain d).awakeAt 0 ∩ C).card + (p.faultyAt d ∩ C).card : ℚ) <
      ((p.retain d).awakeAt 0 ∩ C).card := by
  classical
  dsimp only
  have hset : ((realPoint key hn Δ hΔ ΔF hΔF allAwake H).retain d).awakeAt 0 ∩ C =
      C.erase (kv key hn 0 (by decide)) := by
    ext v
    change (v ∈ (Finset.univ \ {kv key hn 0 (by decide)}).filter
      (fun w => allAwake w 0 = true) ∩ C) ↔ _
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_singleton, true_and, allAwake_apply, and_true, Finset.mem_erase]
  rw [hset, realPoint_faulty]
  rcases hgood with hf | hlarge
  · simp only [Finset.erase_eq_of_notMem hf, Finset.singleton_inter_of_notMem hf,
      Finset.card_empty, Nat.cast_zero, add_zero]
    exact mul_lt_of_lt_one_left (by exact_mod_cast hC.card_pos) hθ.2
  · have hc : C.card ≤ (C.erase (kv key hn 0 (by decide))).card + 1 := by
      by_cases hf : kv key hn 0 (by decide) ∈ C
      · rw [Finset.card_erase_of_mem hf]; omega
      · rw [Finset.erase_eq_of_notMem hf]; omega
    have hs : (Fintype.card V : ℚ) ≤ (C.erase (kv key hn 0 (by decide))).card + 2 := by
      exact_mod_cast (by omega : Fintype.card V ≤ (C.erase (kv key hn 0 (by decide))).card + 2)
    have hsum : (C.erase (kv key hn 0 (by decide))).card +
        ({kv key hn 0 (by decide)} ∩ C).card ≤ Fintype.card V := by
      by_cases hf : kv key hn 0 (by decide) ∈ C
      · have := Finset.card_pos.mpr ⟨_, hf⟩
        rw [Finset.card_erase_of_mem hf, Finset.singleton_inter_of_mem hf,
          Finset.card_singleton]
        have := Finset.card_le_univ C
        omega
      · simpa only [Finset.erase_eq_of_notMem hf, Finset.singleton_inter_of_notMem hf,
          Finset.card_empty, Nat.add_zero] using Finset.card_le_univ C
    have hsumq : ((C.erase (kv key hn 0 (by decide))).card : ℚ) +
        ({kv key hn 0 (by decide)} ∩ C).card ≤ Fintype.card V := by exact_mod_cast hsum
    exact (mul_le_mul_of_nonneg_left hsumq hθ.1).trans_lt (by linarith only [hroom, hs])

omit [DecidableEq V] in
/-- The room margin covers at most two unavailable validators. -/
theorem readyAbove_of_card {p : EnvPoint V} {θ : ℚ} (hθ : 0 ≤ θ)
    (hroom : θ * (Fintype.card V : ℚ) < (Fintype.card V : ℚ) - 2) (c t : Time)
    (hr : Fintype.card V ≤ (p.readyAt c t).card + 2) :
    p.ReadyAbove θ c t := by
  classical
  rw [p.readyAbove_iff_union]
  have hbound : ((p.readyAt c t ∪ p.faultyAt t).card : ℚ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ _
  have hr' : ((Fintype.card V : Nat) : ℚ) ≤ ((p.readyAt c t).card : ℚ) + 2 := by exact_mod_cast hr
  exact (mul_le_mul_of_nonneg_left hbound hθ).trans_lt (by linarith only [hroom, hr'])

/-- The room margin covers every look-back, whose union has at most `n` members. -/
theorem etaReadyAbove_of_card {p : EnvPoint V} {θ : ℚ} (hθ : 0 ≤ θ)
    (hroom : θ * (Fintype.card V : ℚ) < (Fintype.card V : ℚ) - 2) (η c t : Time)
    (hr : Fintype.card V ≤ (p.readyAt c t).card + 2) : p.EtaReadyAbove θ η c t := by
  have hr' : ((Fintype.card V : Nat) : ℚ) ≤ ((p.readyAt c t).card : ℚ) + 2 := by exact_mod_cast hr
  have key : ∀ A : Finset V, θ * (A.card : ℚ) < (p.readyAt c t).card := fun A => by
    have hs : (A.card : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast Finset.card_le_univ _
    exact (mul_le_mul_of_nonneg_left hs hθ).trans_lt (by linarith only [hroom, hr'])
  unfold EnvPoint.EtaReadyAbove
  split_ifs
  · exact (p.readyAbove_iff_union θ c t).mpr (key _)
  · exact key _

omit [DecidableEq V] in
/-- Room for a fault in `n − 1` implies room in the population. -/
theorem one_lt_beta_mul_card {β : ℚ} (hβ : 0 < β)
    (hroom : 1 < β * ((Fintype.card V : ℚ) - 1)) :
    ((1 : Nat) : ℚ) < β * Fintype.card V := by
  norm_num only [Nat.cast_one]
  linarith only [hroom, hβ]

end Point

/-! ### Progress at the witness points -/

omit [DecidableEq V] in
/-- Under the extremal selection, a `.sized 1` proposer role selects exactly
key `1`. -/
theorem extremalSel_proposer_mem (F : ChainShapeFamily O Info) {E : Env V}
    (hF : ∀ s, (F (pubOf E)).skel.proposerSel s = .sized 1) (h2 : 2 ≤ Fintype.card V)
    (s : Slot) (k : Fin (Fintype.card V)) :
    k ∈ extremalSel F E (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) ↔
      k.val = 1 := by
  rw [extremalSel_apply F E (.proposer s)]
  change k ∈ extremalKeys ((F (pubOf E)).skel.proposerSel s) ↔ _
  rw [hF]
  have h1 : 1 < Fintype.card V := by omega
  simp only [extremalKeys_sized, h1, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

omit [DecidableEq V] in
/-- Under the bad-slot selection with one proposer per slot, the proposer of
a good slot is exactly key `1`. -/
theorem badSel_good_mem (F : ChainShapeFamily O Info) {E : Env V} {P : Nat}
    (z : Fin (Fintype.card V)) (hF : ∀ s, (F (pubOf E)).skel.proposerSel s = .sized 1)
    (h2 : 2 ≤ Fintype.card V) {s : Slot} (hs : s % P ≠ P - 1) (k : Fin (Fintype.card V)) :
    k ∈ badSel F E P z (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) ↔
      k.val = 1 := by
  have he : badSel F E P z (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) =
      extremalSel F E (ShapeRole.proposer s : ShapeRole (F (pubOf E)).skel.Kind) := by
    simp only [badSel_apply F E P z (.proposer s), badSlotRole_proposer, hs, decide_false,
      Bool.false_eq_true, ↓reduceIte]
  rw [he]
  exact extremalSel_proposer_mem F hF h2 s k

/-- Keys up to `k` stay awake; all larger keys stay asleep. -/
def awakeUpTo (key : Fin (Fintype.card V) ≃ V) (k : Nat) : V → Time → Bool :=
  fun v _ => decide ((key.symm v).val ≤ k)

omit [DecidableEq V] in
theorem awakeUpTo_apply (key : Fin (Fintype.card V) ≃ V) (k : Nat) (v : V) (t : Time) :
    awakeUpTo key k v t = decide ((key.symm v).val ≤ k) := by rfl

/-- The honest awake set contains exactly keys `1` through `k`. -/
theorem awakeUpTo_card (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V)
    {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF) (H : Time) (k : Nat)
    (hk : k < Fintype.card V) (t : Time) :
    ((realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key k) H).awakeAt t).card = k := by
  classical
  have he : ((realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key k) H).awakeAt t).map
      key.symm.toEmbedding = Finset.univ.filter (fun j => 1 ≤ j.val ∧ j.val ≤ k) := by
    ext j
    simp only [EnvPoint.awakeAt, EnvPoint.honestAt, realPoint_eq, awakeUpTo_apply,
      decide_eq_true_eq, Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, Finset.mem_univ,
      Equiv.symm_apply_apply, true_and, and_congr_left_iff, Finset.mem_sdiff,
      Finset.mem_singleton]
    omega
  have hi : (Finset.univ.filter (fun j : Fin (Fintype.card V) =>
      1 ≤ j.val ∧ j.val ≤ k)).map Fin.valEmbedding = Finset.Icc 1 k := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hj; exact ⟨⟨j, by omega⟩, hj, rfl⟩
  rw [← Finset.card_map, he, ← Finset.card_map, hi, Nat.card_Icc]
  omega

/-- Always-awake honest validators are ready, so the bounded profile has at
least `k` ready validators. -/
theorem awakeUpTo_ready (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V)
    {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF) (H : Time) (k : Nat)
    (hk : k < Fintype.card V) (c t : Time) :
    k ≤ ((realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key k) H).readyAt c t).card := by
  conv_lhs => rw [← awakeUpTo_card key hn hΔ hΔF H k hk t]
  apply card_le_readyAt key hn hΔ hΔF (awakeUpTo key k) H
  intro v hv
  obtain ⟨hh, ha⟩ := Finset.mem_filter.mp hv
  exact ⟨(Finset.mem_sdiff.mp hh).2, fun _ => ha⟩

/-- Selected support at the stress point: every validator, or a committee holding key `1` but
not the faulty key `0`. -/
theorem awakeUpTo_committee_margin (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V)
    {Δ : Time} (hΔ : 0 < Δ) {ΔF : Time} (hΔF : 0 < ΔF) (H : Time) (C : Finset V)
    (m : Nat) (hm : 2 ≤ m) (hmn : m < Fintype.card V) {θ : ℚ}
    (hθ : θ < 1) (hmargin : θ * ((m : ℚ) + 1) < m)
    (hgood : C = Finset.univ ∨ kv key hn 0 (by decide) ∉ C ∧ kv key hn 1 (by decide) ∈ C)
    (d : Time) :
    let p := realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key m) H
    θ * (((p.retain d).awakeAt 0 ∩ C).card + (p.faultyAt d ∩ C).card : ℚ) <
      ((p.retain d).awakeAt 0 ∩ C).card := by
  classical
  dsimp only
  have hmem (j : Nat) (hj : j < 3) (h0 : j ≠ 0) (h2 : j ≤ m) : kv key hn j hj ∈
      ((realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key m) H).retain d).awakeAt 0 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      realPoint_honest key hn hΔ hΔF (awakeUpTo key m) H hj h0 (t := d)⟩, ?_⟩
    change awakeUpTo key m (kv key hn j hj) 0 = true
    simp only [awakeUpTo_apply, kv_eq, Equiv.symm_apply_apply, decide_eq_true_eq]
    exact h2
  rw [realPoint_faulty]
  rcases hgood with rfl | ⟨h0, h1⟩
  · rw [Finset.inter_univ, Finset.inter_univ, Finset.card_singleton]
    have he : (realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key m) H).retain d =
        realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key m) H :=
      EnvPoint.retain_eq (realPoint_constant key hn hΔ hΔF _ H) d
    rw [he, awakeUpTo_card key hn hΔ hΔF H m hmn]
    exact hmargin
  · simp only [Finset.singleton_inter_of_notMem h0, Finset.card_empty, Nat.cast_zero, add_zero]
    apply mul_lt_of_lt_one_left _ hθ
    exact_mod_cast (Finset.card_pos.mpr
      ⟨_, Finset.mem_inter.mpr ⟨hmem 1 (by decide) (by decide) (by omega), h1⟩⟩)

section Witnesses

variable (key : Fin (Fintype.card V) ≃ V) (hn : 3 ≤ Fintype.card V) {Δ : Time} (hΔ : 0 < Δ)
  {ΔF : Time} (hΔF : 0 < ΔF)
  (H : Time)

/-- Everyone awake, a fitting progress requirement holds on every window under
the extremal selection with any run PKI `key'` keeping key `1`: key `1` (honest, always awake) is
the proposer of every slot, and every honest validator is ready at every time. -/
theorem allAwake_holds (key' : Fin (Fintype.card V) ≃ V)
    (hk1 : key' ⟨1, by omega⟩ = key ⟨1, by omega⟩) (hf : ProgressFits K F) (cap : Capability)
    (i : K.Idx) (c s e : Time) :
    shapeHolds F (K.progress cap i) c s e (realPoint key hn Δ hΔ ΔF hΔF allAwake H)
      (key', extremalSel F (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env) := by
  have hfit := hf cap i (pubOf (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env)
  revert hfit
  cases K.progress cap i with
  | recur ρ =>
    intro hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    apply patternRecurrence_of_all
    intro sl j _
    have hmem := extremalSel_proposer_mem F hfit (by omega) (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1' : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1'
    change (realPoint key hn Δ hΔ ΔF hΔF allAwake H).Ready _ (key' ⟨1, by omega⟩) _ ∧
      (realPoint key hn Δ hΔ ΔF hΔF allAwake H).HonestAt (key' ⟨1, by omega⟩) _
    rw [hk1]
    exact ⟨⟨realPoint_honest key hn hΔ hΔF allAwake H (by decide) (by decide),
      fun _ _ _ => rfl⟩, realPoint_honest key hn hΔ hΔF allAwake H (by decide) (by decide)⟩
  | notReadyAtMost m =>
    intro _ t _ _ _
    exact le_trans (allAwake_readyAt key hn hΔ hΔF H c t) (Nat.add_le_add_left m.pos _)

/-- Everyone awake: liveness is active from `start`, with transaction `42`
submitted to `key 1` at `0` and read by `key 2` at the horizon. -/
theorem allAwake_txLiveActive (p : EnvPoint V)
    (hp : p = realPoint key hn Δ hΔ ΔF hΔF allAwake H) (c start D : Time)
    (hH : max 0 start + Δ + D ≤ H) : p.TxLiveActive c start D := by
  unfold EnvPoint.TxLiveActive
  rw [hp]
  refine ⟨42, 0, H, kv key hn 1 (by decide), kv key hn 2 (by decide), le_rfl,
    realPoint_honest key hn hΔ hΔF allAwake H (by decide) (by decide), rfl, ?_,
    kv_ne key hn (by decide), ?_, hH, le_rfl,
    realPoint_honest key hn hΔ hΔF allAwake H (by decide) (by decide), fun _ _ _ => rfl⟩
  · simp only [realPoint_eq, and_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
  · intro τ
    have : kv key hn 2 (by decide) ≠ kv key hn 1 (by decide) := kv_ne key hn (by decide)
    simp only [realPoint_eq, this, false_and, ↓reduceIte, List.not_mem_nil, not_false_eq_true]

/-- Everyone awake: safety is active after `t₀` (keys `1` and `2` ready at
`t₀ + 1`, key `1` again at `t₀ + 2`). -/
theorem allAwake_safeActive (c t₀ : Time) (hH : t₀ + 2 ≤ H) :
    SafeActive c t₀ (realPoint key hn Δ hΔ ΔF hΔF allAwake H) := by
  have h1 := fun t => realPoint_honest key hn hΔ hΔF allAwake H
    (j := 1) (t := t) (by decide) (by decide)
  have h2 := fun t => realPoint_honest key hn hΔ hΔF allAwake H
    (j := 2) (t := t) (by decide) (by decide)
  exact ⟨kv key hn 1 (by decide), kv key hn 2 (by decide), t₀ + 1, t₀ + 2,
    kv_ne key hn (by decide), lt_add_one t₀, add_lt_add_right one_lt_two t₀, hH,
    ⟨h1 _, fun _ _ _ => rfl⟩, ⟨h2 _, fun _ _ _ => rfl⟩, ⟨h1 _, fun _ _ _ => rfl⟩⟩

/-- A selection for the stress witness at index `i` (tolerant of `n` validators not ready), on a
profile where key `1` stays awake, with key `1` at run index `q` of the run PKI `key'`: for a
recurrence, `q` proposes every slot (the bad-slot selection of period `1`); for a bound on the
validators not ready, the extremal selection (the tolerant bound holds on every point). Both are
extremal on every duty role. -/
theorem stress_selection (awake : V → Time → Bool)
    (ha1 : ∀ t, awake (kv key hn 1 (by decide)) t = true) (key' : Fin (Fintype.card V) ≃ V)
    (q : Fin (Fintype.card V)) (hq : key' q = key ⟨1, by omega⟩)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (ht : ProgressReq.Tolerates (Fintype.card V) (K.progress cap i)) :
    ∃ sel : (protoOf (compiled F) (realPoint key hn Δ hΔ ΔF hΔF awake H).env).Role →
        Finset (Fin (Fintype.card V)),
      (protoOf (compiled F) (realPoint key hn Δ hΔ ΔF hΔF awake H).env).SelAdmits sel ∧
      (∀ s k, sel (ShapeRole.duty s k :
          ShapeRole (F (pubOf (realPoint key hn Δ hΔ ΔF hΔF awake H).env)).skel.Kind) =
        extremalSel F (realPoint key hn Δ hΔ ΔF hΔF awake H).env (ShapeRole.duty s k)) ∧
      ∀ c s e, shapeHolds F (K.progress cap i) c s e (realPoint key hn Δ hΔ ΔF hΔF awake H)
        (key', sel) := by
  have hfit := hf cap i (pubOf (realPoint key hn Δ hΔ ΔF hΔF awake H).env)
  cases hreq : K.progress cap i with
  | recur ρ =>
    rw [hreq] at hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    refine ⟨badSel F _ 1 q, badSel_admits F _ 1 q hfit, badSel_duty F _ 1 q, fun c s e => ?_⟩
    apply patternRecurrence_of_all
    intro sl j _
    have hb := badSel_bad F (E := (realPoint key hn Δ hΔ ΔF hΔF awake H).env) (P := 1) q
      (s := sl + j) (Nat.mod_one _)
    refine ⟨⟨q, by dsimp only; rw [hb]; exact Finset.mem_singleton_self q⟩, fun k hk => ?_⟩
    dsimp only at hk
    rw [hb, Finset.mem_singleton] at hk
    subst hk
    change (realPoint key hn Δ hΔ ΔF hΔF awake H).Ready _ (key' k) _ ∧
      (realPoint key hn Δ hΔ ΔF hΔF awake H).HonestAt (key' k) _
    rw [hq]
    exact ⟨⟨realPoint_honest key hn hΔ hΔF awake H (by decide) (by decide),
      fun t _ _ => ha1 t⟩, realPoint_honest key hn hΔ hΔF awake H (by decide) (by decide)⟩
  | notReadyAtMost m =>
    rw [hreq] at ht
    exact ⟨extremalSel F _, extremalSel_admits F _, fun _ _ => rfl,
      fun _ _ _ => NotReadyOn.of_card_le ht⟩

/-- With keys `1` and `2` always awake, liveness is active: key `1` submits
transaction `42` at `0`, and key `2` reads at the horizon. -/
theorem profile_txLiveActive (awake : V → Time → Bool)
    (ha1 : ∀ t, awake (kv key hn 1 (by decide)) t = true)
    (ha2 : ∀ t, awake (kv key hn 2 (by decide)) t = true) (p : EnvPoint V)
    (hp : p = realPoint key hn Δ hΔ ΔF hΔF awake H) (c start D : Time)
    (hH : max 0 start + Δ + D ≤ H) : p.TxLiveActive c start D := by
  unfold EnvPoint.TxLiveActive
  rw [hp]
  refine ⟨42, 0, H, kv key hn 1 (by decide), kv key hn 2 (by decide), le_rfl,
    realPoint_honest key hn hΔ hΔF awake H (by decide) (by decide), ha1 0, ?_,
    kv_ne key hn (by decide), ?_, hH, le_rfl,
    realPoint_honest key hn hΔ hΔF awake H (by decide) (by decide), fun t _ _ => ha2 t⟩
  · simp only [realPoint_eq, and_self, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
  · intro τ
    have : kv key hn 2 (by decide) ≠ kv key hn 1 (by decide) := kv_ne key hn (by decide)
    simp only [realPoint_eq, this, false_and, ↓reduceIte, List.not_mem_nil, not_false_eq_true]

/-- With keys `1` and `2` always awake, safety is active after `t₀`. -/
theorem profile_safeActive (awake : V → Time → Bool)
    (ha1 : ∀ t, awake (kv key hn 1 (by decide)) t = true)
    (ha2 : ∀ t, awake (kv key hn 2 (by decide)) t = true) (c t₀ : Time) (hH : t₀ + 2 ≤ H) :
    SafeActive c t₀ (realPoint key hn Δ hΔ ΔF hΔF awake H) := by
  have h1 := fun t => realPoint_honest key hn hΔ hΔF awake H
    (j := 1) (t := t) (by decide) (by decide)
  have h2 := fun t => realPoint_honest key hn hΔ hΔF awake H
    (j := 2) (t := t) (by decide) (by decide)
  exact ⟨kv key hn 1 (by decide), kv key hn 2 (by decide), t₀ + 1, t₀ + 2,
    kv_ne key hn (by decide), lt_add_one t₀, add_lt_add_right one_lt_two t₀, hH,
    ⟨h1 _, fun t _ _ => ha1 t⟩, ⟨h2 _, fun t _ _ => ha2 t⟩,
    ⟨h1 _, fun t _ _ => ha1 t⟩⟩

/-- The canonical run at a witness point, from GST `g`, with some injective
hash and an admissible selection `sel`: valid, no collision, and eager from
`g`; its point, PKI and selection are the given ones definitionally
(a `Run` literal). -/
theorem real_run_sel (F : ChainShapeFamily O Info) (p : EnvPoint V) (hp : 0 ≤ p.horizon) (g : Time)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : (protoOf (compiled F) p.env).SelAdmits sel) :
    ∃ hash relay events,
      let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt p.faultyAt_mono
          p.horizon events key sel p.submit relay hash
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧ CommLog.EagerFrom rho.point rho.log g := by
  obtain ⟨hash, hinj⟩ := Countable.exists_injective_nat (protoOf (compiled F) p.env).Item
  obtain ⟨relay, events, hv, he, -⟩ :=
    Model.canonical_run_from_causal O (compiled F) V p.env p.faultyAt p.faultyAt_mono
      p.horizon hp key sel hsel p.submit hash g
  exact ⟨hash, relay, events, hv,
    Model.Run.not_hashCollision_of_injective (Model.Run.injectiveHash_iff.mpr hinj), he⟩

/-- The canonical run at a witness point under the extremal selection. -/
theorem real_run (F : ChainShapeFamily O Info) (p : EnvPoint V) (hp : 0 ≤ p.horizon) (g : Time) :
    ∃ hash relay events,
      let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt p.faultyAt_mono
          p.horizon events key (extremalSel F p.env) p.submit relay hash
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧ CommLog.EagerFrom rho.point rho.log g :=
  real_run_sel key F p hp g _ (extremalSel_admits F p.env)

/-- The sleepy witness: everyone awake, the synchronous canonical run, horizon
`H` long enough for one liveness deadline and one progress window. The run PKI keeps key `1` and
moves the faulty key `0` out of the extremal committee unless that committee misses at most one
key (`exists_witness_key`), so every selected committee is sleepy too. -/
theorem sleepy_witness (ha : K.params.Admissible) (hroom : K.params.Room (Fintype.card V))
    (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF)
    (hf : ProgressFits K F) (cap : Capability)
    (i : K.Idx)
    (hH : Δ + (K.params.latency cap i : Time) * Δ +
      progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env,
      rho.point = realPoint key hn Δ hΔ ΔF hΔF allAwake H ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧ (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨_, rho⟩ ∧
      (Sys F V).prog (shapeProgress F V) K cap i 0 rho.horizon ⟨_, rho⟩ ∧
      ProgressActive F K cap i 0 rho ∧
      rho.point.TxLiveActive ((Sys F V).cDur K ⟨_, rho⟩) 0
        ((Sys F V).lat K cap i ⟨_, rho⟩) := by
  have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V)
  have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hH0 : 0 ≤ H := by linarith only [hH, hL, hlat, hΔ]
  let p := realPoint key hn Δ hΔ ΔF hΔF allAwake H
  obtain ⟨key', _, -, hk1, hgood⟩ := exists_witness_key key hn (extremalCommittee F p.env)
  obtain ⟨hash, relay, events, hv, hnc, he⟩ := real_run key' F p hH0 0
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt monotone_const H events key'
    (extremalSel F p.env) p.submit relay hash
  have hcomm := committee_of_constant_awake p ((extremalCommittee F p.env).map key'.toEmbedding)
    K.params.θ 0 ((Sys F V).cDur K ⟨_, rho⟩) ((Sys F V).committeeAheadDur K ⟨_, rho⟩)
    ha.θ_range.1 (mul_nonneg (by positivity) hΔ.le) (fun _ _ _ => rfl)
    (allAwake_committee_margin key hn hΔ hΔF H ha.θ_range hroom.1 _ hgood)
  refine ⟨rho, rfl, ⟨hv, hnc, fun _ => rfl, ?_, ?_⟩,
    ⟨(Model.sysOf_eagerFrom _ he).psync le_rfl hΔ1 hΔF1, ?_, ?_⟩,
    allAwake_holds key hn hΔ hΔF H key' hk1 hf cap i _ _ _, ?_, ?_⟩
  · change (p.faultyAt 0).Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      realPoint_honest key hn hΔ hΔF allAwake H (j := 1) (by decide) (by decide)⟩⟩
  · intro t _ _
    exact readyAbove_of_card ha.θ_range.1 hroom.1 _ t
      ((allAwake_readyAt key hn hΔ hΔF H _ t).trans (Nat.le_succ _))
  · change p.CommitteeSleepyOn ((shapeProgress F V).selected p.env (key', extremalSel F p.env))
      K.params.θ 0 ((Sys F V).cDur K ⟨_, rho⟩) ((Sys F V).committeeAheadDur K ⟨_, rho⟩) 0 H
    rw [funext (selected_of_duty F p.env key' _ fun _ _ => rfl)]
    exact hcomm
  · change max 0 0 + progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) ≤ H
    simp only [max_self, zero_add]; linarith only [hH, hΔ, hlat]
  · refine allAwake_txLiveActive key hn hΔ hΔF H _ rfl _ _ _ ?_
    change max 0 0 + Δ + (K.params.latency cap i : Time) * Δ ≤ H
    simp only [max_self, zero_add]; linarith only [hH, hL]

/-- The healthy witness at GST `g` under a run PKI `key'` and an admissible selection `sel`,
extremal on duty roles, at which the progress requirement holds: everyone awake (full
participation, one faulty validator, outside the extremal committee unless that committee misses
at most one key), the canonical run from `g` (no receipt before `g`), horizon `H` long enough for
one liveness deadline after the heal point, two cuts after it, and one progress window from
`ready`. -/
theorem healthy_witness_sel (ha : K.params.Admissible) (hroom : K.params.Room (Fintype.card V))
    (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF)
    (cap : Capability) (i : K.Idx) (g : Time) (key' : Fin (Fintype.card V) ≃ V)
    (sel : (protoOf (compiled F) (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env).Role →
      Finset (Fin (Fintype.card V)))
    (hsel : (protoOf (compiled F) (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env).SelAdmits sel)
    (hduty : ∀ s k, sel (ShapeRole.duty s k :
        ShapeRole (F (pubOf (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env)).skel.Kind) =
      extremalSel F (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env (ShapeRole.duty s k))
    (hgood : kv key hn 0 (by decide) ∉ (extremalCommittee F
        (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env).map key'.toEmbedding ∨
      Fintype.card V - 1 ≤ ((extremalCommittee F
        (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env).map key'.toEmbedding).card)
    (hprog : ∀ c s e, shapeHolds F (K.progress cap i) c s e
      (realPoint key hn Δ hΔ ΔF hΔF allAwake H) (key', sel))
    (hr : ΔF ≤ (K.params.fgDelay : Time) * Δ)
    (h1 : max g 0 + (K.params.heal cap i : Time) * Δ + Δ + (K.params.latency cap i : Time) * Δ ≤ H)
    (h2 : max g 0 + (K.params.heal cap i : Time) * Δ + 2 ≤ H)
    (h3 : max g 0 + (K.params.catchUp : Time) * Δ + 1 +
      progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env,
      rho.point = realPoint key hn Δ hΔ ΔF hΔF allAwake H ∧ rho.key = key' ∧ rho.sel = sel ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧
      CommLog.EagerFrom ((Sys F V).pt ⟨_, rho⟩)
        ((Sys F V).log ⟨_, rho⟩) g ∧ (Sys F V).Healthy (shapeProgress F V).toExternal K g ⟨_, rho⟩ ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K g ⟨_, rho⟩) rho.horizon
        ⟨_, rho⟩ ∧
      ProgressActive F K cap i ((Sys F V).ready K g ⟨_, rho⟩) rho ∧
      rho.point.TxLiveActive ((Sys F V).cDur K ⟨_, rho⟩)
        ((Sys F V).heal K cap i g ⟨_, rho⟩) ((Sys F V).lat K cap i ⟨_, rho⟩) ∧
      SafeActive ((Sys F V).cDur K ⟨_, rho⟩) ((Sys F V).heal K cap i g ⟨_, rho⟩) rho.point := by
  have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V)
  have hc : 0 ≤ ((K.params.catchUp : Time) * Δ) := mul_nonneg (by positivity) hΔ.le
  have hheal : 0 ≤ (max g 0 + (K.params.heal cap i : Time) * Δ) :=
    add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
  have hrdy : 0 ≤ (max g 0 + (K.params.catchUp : Time) * Δ + 1) := by
    have hg := le_max_right g 0; linarith only [hg, hc]
  have hH0 : 0 ≤ H := by linarith only [h2, hheal]
  let p := realPoint key hn Δ hΔ ΔF hΔF allAwake H
  obtain ⟨hash, relay, events, hv, hnc, he⟩ := real_run_sel key' F p hH0 g sel hsel
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt monotone_const H events key'
    sel p.submit relay hash
  have hse := Model.sysOf_eagerFrom (O := O) rho he
  refine ⟨rho, rfl, rfl, rfl, ⟨hv, hnc, fun _ => rfl, ?_, ?_⟩, hse,
    ⟨hse.psync le_rfl hΔ1 hΔF1, ?_, hr, ?_⟩,
    hprog _ _ _, ?_, ?_,
    allAwake_safeActive key hn hΔ hΔF H _ _ h2⟩
  · change (p.faultyAt 0).Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      realPoint_honest key hn hΔ hΔF allAwake H (j := 1) (by decide) (by decide)⟩⟩
  · refine ⟨?_, fun _ _ _ _ _ => rfl⟩
    change ((p.faultyAt H).card : ℚ) < K.params.β * Fintype.card V
    rw [realPoint_faulty, Finset.card_singleton]
    exact one_lt_beta_mul_card ha.β_range.1 hroom.2.1
  · change p.CommitteeHealthyOn ((shapeProgress F V).selected p.env (key', sel))
      K.params.βK (max g 0) H
    rw [funext (selected_of_duty F p.env key' sel hduty)]
    exact committeeHealthy_of_one_fault hn p _ _ ha.β_range.2 hroom.2.2 _ _
      (subset_of_eq (realPoint_faulty key hn hΔ hΔF allAwake H H)) hgood
  · change max ((max g 0 + (K.params.catchUp : Time) * Δ + 1)) 0 +
      progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) ≤ H
    rw [max_eq_left hrdy]; exact h3
  · refine allAwake_txLiveActive key hn hΔ hΔF H _ rfl _ _ _ ?_
    change max 0 (max g 0 + (K.params.heal cap i : Time) * Δ) + Δ +
      (K.params.latency cap i : Time) * Δ ≤ H
    rw [max_eq_right hheal]; exact h1

/-- The healthy witness at GST `g` under the extremal selection (key `1`
proposes every slot) and the run PKI of `exists_witness_key`. -/
theorem healthy_witness (ha : K.params.Admissible) (hroom : K.params.Room (Fintype.card V))
    (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF)
    (hf : ProgressFits K F) (cap : Capability)
    (i : K.Idx) (g : Time) (hr : ΔF ≤ (K.params.fgDelay : Time) * Δ)
    (h1 : max g 0 + (K.params.heal cap i : Time) * Δ + Δ + (K.params.latency cap i : Time) * Δ ≤ H)
    (h2 : max g 0 + (K.params.heal cap i : Time) * Δ + 2 ≤ H)
    (h3 : max g 0 + (K.params.catchUp : Time) * Δ + 1 +
      progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, allAwake⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env,
      rho.point = realPoint key hn Δ hΔ ΔF hΔF allAwake H ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧
      CommLog.EagerFrom ((Sys F V).pt ⟨_, rho⟩)
        ((Sys F V).log ⟨_, rho⟩) g ∧ (Sys F V).Healthy (shapeProgress F V).toExternal K g ⟨_, rho⟩ ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K g ⟨_, rho⟩) rho.horizon
        ⟨_, rho⟩ ∧
      ProgressActive F K cap i ((Sys F V).ready K g ⟨_, rho⟩) rho ∧
      rho.point.TxLiveActive ((Sys F V).cDur K ⟨_, rho⟩)
        ((Sys F V).heal K cap i g ⟨_, rho⟩) ((Sys F V).lat K cap i ⟨_, rho⟩) ∧
      SafeActive ((Sys F V).cDur K ⟨_, rho⟩) ((Sys F V).heal K cap i g ⟨_, rho⟩) rho.point := by
  obtain ⟨key', _, -, hk1, hgood⟩ :=
    exists_witness_key key hn (extremalCommittee F (realPoint key hn Δ hΔ ΔF hΔF allAwake H).env)
  obtain ⟨rho, hp, -, -, h⟩ := healthy_witness_sel key hn hΔ hΔF H ha hroom hΔ1 hΔF1 cap i g key' _
    (extremalSel_admits F _) (fun _ _ => rfl) hgood
    (allAwake_holds key hn hΔ hΔF H key' hk1 hf cap i) hr h1 h2 h3
  exact ⟨rho, hp, h⟩

/-- A selection for the bad-proposer witness at index `i` (tolerant of
`n` validators not ready and of bad slots), on a profile where key `1`
stays awake, under a run PKI `key'` keeping key `1` and placing the faulty key `0` at index `z`:
for a recurrence, the bad-slot selection with period `span + 2` and bad key `z` (faulty, proposes
one slot in every `span + 2`), under which the recurrence still holds and every window holds a
faulty proposer slot; for a bound on the validators not ready, the extremal selection (the
tolerant bound holds on every point). Both are extremal on every duty role. -/
theorem bad_selection (awake : V → Time → Bool)
    (ha1 : ∀ t, awake (kv key hn 1 (by decide)) t = true) (key' : Fin (Fintype.card V) ≃ V)
    (z : Fin (Fintype.card V)) (hz : key' z = key ⟨0, by omega⟩)
    (hk1 : key' ⟨1, by omega⟩ = key ⟨1, by omega⟩)
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (ht : ProgressReq.Tolerates (Fintype.card V) (K.progress cap i)) :
    ∃ sel : (protoOf (compiled F) (realPoint key hn Δ hΔ ΔF hΔF awake H).env).Role →
        Finset (Fin (Fintype.card V)),
      (protoOf (compiled F) (realPoint key hn Δ hΔ ΔF hΔF awake H).env).SelAdmits sel ∧
      (∀ s k, sel (ShapeRole.duty s k :
          ShapeRole (F (pubOf (realPoint key hn Δ hΔ ΔF hΔF awake H).env)).skel.Kind) =
        extremalSel F (realPoint key hn Δ hΔ ΔF hΔF awake H).env (ShapeRole.duty s k)) ∧
      (∀ c s e, shapeHolds F (K.progress cap i) c s e (realPoint key hn Δ hΔ ΔF hΔF awake H)
        (key', sel)) ∧
      ∀ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ ΔF hΔF awake H).env, rho.sel = sel →
        rho.key = key' → rho.faultyAt = (realPoint key hn Δ hΔ ΔF hΔF awake H).faultyAt →
        BadProposerEvery F K cap i rho := by
  have hfit := hf cap i (pubOf (realPoint key hn Δ hΔ ΔF hΔF awake H).env)
  cases hreq : K.progress cap i with
  | recur ρ =>
    rw [hreq] at hfit ht
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    change ρ.BadSlotSlack at ht
    have hP : ρ.pattern.span + 2 - 1 = ρ.pattern.span + 1 := by omega
    refine ⟨badSel F (realPoint key hn Δ hΔ ΔF hΔF awake H).env (ρ.pattern.span + 2) z,
      badSel_admits F _ _ z hfit, badSel_duty F _ _ z, fun c s e => ?_, fun rho hs hk hh => ?_⟩
    · apply patternRecurrence_of_periodic ht
      intro sl j hsl hj
      have hg := Recurrence.pattern_good hsl hj
      have hmem := badSel_good_mem F z hfit (by omega) (s := sl + j)
        (P := ρ.pattern.span + 2) (by rw [hP]; exact hg)
      refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
      have hk1' : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
      subst hk1'
      change (realPoint key hn Δ hΔ ΔF hΔF awake H).Ready _ (key' ⟨1, by omega⟩) _ ∧
        (realPoint key hn Δ hΔ ΔF hΔF awake H).HonestAt (key' ⟨1, by omega⟩) _
      rw [hk1]
      exact ⟨⟨realPoint_honest key hn hΔ hΔF awake H (by decide) (by decide),
        fun t _ _ => ha1 t⟩, realPoint_honest key hn hΔ hΔF awake H (by decide) (by decide)⟩
    · unfold BadProposerEvery
      rw [hreq]
      intro a
      obtain ⟨s, h1, h2, h3⟩ := Recurrence.exists_bad_slot ht a
      have hb := badSel_bad F (E := (realPoint key hn Δ hΔ ΔF hΔF awake H).env) z (s := s)
        (P := ρ.pattern.span + 2) (by rw [hP]; exact h3)
      refine ⟨s, h1, h2, ?_, ?_⟩
      · rw [hs]; rw [hb]; exact Finset.singleton_nonempty _
      · rw [hs]; rw [hb]
        intro k hk'
        rw [Finset.mem_singleton.mp hk', hk, hh, hz]
        rw [realPoint_faulty]
        exact Finset.mem_singleton_self _
  | notReadyAtMost m =>
    rw [hreq] at ht
    refine ⟨extremalSel F _, extremalSel_admits F _, fun _ _ => rfl, fun c s e => ?_,
      fun rho _ _ _ => ?_⟩
    · exact NotReadyOn.of_card_le ht
    · unfold BadProposerEvery; rw [hreq]; trivial

/-- Sleepy stress: honest keys `1` through `m` stay awake, with active
liveness and progress on the synchronous canonical run. The strict margin
`θ·(m + 1) < m` covers the single faulty validator.
The run PKI puts key `1` at an index of the extremal committee and the faulty key `0`
outside it, unless the committee is every key (`exists_stress_key`); key `1` proposes every slot
(`stress_selection`), so every selected committee is sleepy too. -/
theorem sleepyStress_witness (ha : K.params.Admissible) (m : Nat) (hm : 2 ≤ m)
    (hmn : m < Fintype.card V) (hmargin : K.params.θ * ((m : ℚ) + 1) < m)
    (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF)
    (hf : ProgressFits K F) (cap : Capability)
    (i : K.Idx) (ht : ProgressReq.Tolerates (Fintype.card V) (K.progress cap i))
    (hH : Δ + (K.params.latency cap i : Time) * Δ +
      progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, (awakeUpTo key m)⟩ : Env V) ≤ H) :
    ∃ rho : Model.Run (compiled F) (realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key m) H).env,
      rho.point = realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key m) H ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧ (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨_, rho⟩ ∧
      (Sys F V).prog (shapeProgress F V) K cap i 0 rho.horizon ⟨_, rho⟩ ∧
      ProgressActive F K cap i 0 rho ∧
      rho.point.TxLiveActive ((Sys F V).cDur K ⟨_, rho⟩) 0
        ((Sys F V).lat K cap i ⟨_, rho⟩) ∧
      rho.point.AwakeAtMost m := by
  have hL := progLen_nonneg F K cap i (⟨Δ, hΔ, ΔF, hΔF, (awakeUpTo key m)⟩ : Env V)
  have hlat : 0 ≤ (K.params.latency cap i : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hH0 : 0 ≤ H := by linarith only [hH, hL, hlat, hΔ]
  let p := realPoint key hn Δ hΔ ΔF hΔF (awakeUpTo key m) H
  have ha1 : ∀ t, awakeUpTo key m (kv key hn 1 (by decide)) t = true := by
    intro t; simp only [awakeUpTo_apply, kv_eq, Equiv.symm_apply_apply, decide_eq_true_eq]
    omega
  obtain ⟨key', q, hq, hgood⟩ := exists_stress_key key hn (extremalCommittee F p.env)
  obtain ⟨sel, hsel, hduty, hprog⟩ :=
    stress_selection key hn hΔ hΔF H (awakeUpTo key m) ha1 key' q hq hf cap i ht
  obtain ⟨hash, relay, events, hv, hnc, he⟩ := real_run_sel key' F p hH0 0 sel hsel
  let rho := Model.Run.mk (F := compiled F) (E := p.env) p.faultyAt monotone_const H events key'
    sel p.submit relay hash
  have hcomm := committee_of_constant_awake p ((extremalCommittee F p.env).map key'.toEmbedding)
    K.params.θ 0 ((Sys F V).cDur K ⟨_, rho⟩) ((Sys F V).committeeAheadDur K ⟨_, rho⟩)
    ha.θ_range.1 (mul_nonneg (by positivity) hΔ.le) (fun _ _ _ => rfl) fun d hC => by
      refine awakeUpTo_committee_margin key hn hΔ hΔF H _ m hm hmn ha.θ_range.2 hmargin ?_ d
      rcases hgood (Finset.map_nonempty.mp hC) with hD | ⟨h0, hqD⟩
      · left; rw [hD]; exact Finset.map_univ_equiv key'
      · right
        refine ⟨h0, ?_⟩
        rw [kv_eq, ← hq]
        exact Finset.mem_map_of_mem key'.toEmbedding hqD
  refine ⟨rho, rfl, ⟨hv, hnc, fun _ => rfl, ?_, ?_⟩,
    ⟨(Model.sysOf_eagerFrom _ he).psync le_rfl hΔ1 hΔF1, ?_, ?_⟩, hprog _ _ _, ?_, ?_, ?_⟩
  · change (p.faultyAt 0).Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      realPoint_honest key hn hΔ hΔF (awakeUpTo key m) H (j := 1) (by decide) (by decide)⟩⟩
  · intro t _ _
    change p.ReadyAbove K.params.θ ((K.params.catchUp : Time) * Δ) t
    unfold EnvPoint.ReadyAbove EnvPoint.faultCount
    rw [realPoint_faulty, Finset.card_singleton]
    have hr := awakeUpTo_ready key hn hΔ hΔF H m hmn (((K.params.catchUp : Time) * Δ)) t
    have hr' : (m : ℚ) ≤ (p.readyAt (((K.params.catchUp : Time) * Δ)) t).card := by
      exact_mod_cast hr
    have hmono := mul_nonneg (sub_nonneg.mpr ha.θ_range.2.le) (sub_nonneg.mpr hr')
    push_cast
    linarith only [hmargin, hmono]
  · change p.CommitteeSleepyOn ((shapeProgress F V).selected p.env (key', sel))
      K.params.θ 0 ((Sys F V).cDur K ⟨_, rho⟩) ((Sys F V).committeeAheadDur K ⟨_, rho⟩) 0 H
    rw [funext (selected_of_duty F p.env key' sel hduty)]
    exact hcomm
  · change max 0 0 + progLen F K cap i (⟨Δ, hΔ, ΔF, hΔF, (awakeUpTo key m)⟩ : Env V) ≤ H
    simp only [max_self, zero_add]; linarith only [hH, hΔ, hlat]
  · refine profile_txLiveActive key hn hΔ hΔF H _ ha1
      (by intro t; simp only [awakeUpTo_apply, kv_eq, Equiv.symm_apply_apply,
        decide_eq_true_eq]; omega) _ rfl _ _ _ ?_
    change max 0 0 + Δ + (K.params.latency cap i : Time) * Δ ≤ H
    simp only [max_self, zero_add]; linarith only [hH, hL]
  · intro t _ _
    change (p.awakeAt t).card ≤ _
    rw [awakeUpTo_card key hn hΔ hΔF H m hmn]

/-- The outage witness `(T, [b₀, b₁))`: honest `key 2` always asleep, everyone
else always awake (so readiness does not depend on the catch-up and the
look-back adds no opponent), the synchronous canonical run, horizon
`H ≥ b₁ + recovery·Δ`, at every look-back `η`. -/
theorem outage_witness (ha : K.params.Admissible) (hroom : K.params.Room (Fintype.card V))
    (hΔ1 : 1 < Δ) (hΔF1 : 1 < ΔF)
    {T b₀ b₁ : Time}
    (hT : OutageTimes K.params Δ T b₀ b₁) (hTb : T < b₀) (hb : b₀ + Δ ≤ b₁)
    (hH : b₁ + (K.params.recovery : Time) * Δ ≤ H) :
    ∃ rho : Model.Run (compiled F)
        (realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H).env,
      rho.point = realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H ∧
      (Sys F V).Witness ⟨_, rho⟩ ∧
      (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨_, rho⟩ ∧
      OutageActive ((Sys F V).cDur K ⟨_, rho⟩) ((K.params.recovery : Time) * Δ) T b₀ b₁
        rho.point := by
  have hT0 : 0 ≤ T := hT.1
  have hD : (0 : Time) ≤ (K.params.recovery : Time) * Δ := mul_nonneg (by positivity) hΔ.le
  have hH0 : 0 ≤ H := by linarith only [hH, hD, hb, hTb, hT0, hΔ]
  have h12 : kv key hn 1 (by decide) ≠ kv key hn 2 (by decide) := kv_ne key hn (by decide)
  let p := realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H
  obtain ⟨key', sel, C, hsel, hselected, hgood⟩ := exists_outage_selection F p.env key hn
  obtain ⟨hash, relay, events, hv, hnc, he⟩ :=
    real_run_sel key' F p hH0 0 sel hsel
  let rho := Model.Run.mk (F := compiled F)
      (E := (realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H).env)
      (realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H).faultyAt
      monotone_const H events key' sel
      (realPoint key hn Δ hΔ ΔF hΔF (asleepAlways (kv key hn 2 (by decide))) H).submit relay hash
  have hse := Model.sysOf_eagerFrom (O := O) rho he
  have hawake1 :
      ∀ t, asleepAlways (kv key hn 2 (by decide)) (kv key hn 1 (by decide)) t = true := by
    intro t; simp [asleepAlways_apply, h12]
  have hh1 := fun t => realPoint_honest key hn hΔ hΔF
    (asleepAlways (kv key hn 2 (by decide))) H (j := 1) (t := t) (by decide) (by decide)
  have hh2 := fun t => realPoint_honest key hn hΔ hΔF
    (asleepAlways (kv key hn 2 (by decide))) H (j := 2) (t := t) (by decide) (by decide)
  have hcomm := committee_of_constant_awake p C K.params.θ
    ((K.params.η : Time) * Δ)
    (max ((Sys F V).cDur K ⟨_, rho⟩) ((K.params.η : Time) * Δ - 1))
    ((Sys F V).committeeAheadDur K ⟨_, rho⟩)
    ha.θ_range.1 (le_max_of_le_left (mul_nonneg (by positivity) hΔ.le)) (fun _ _ _ => rfl)
    (asleepAlways_committee_margin key hn hΔ hΔF H ha.θ_range hroom.1 C hgood)
  have hselEq : (shapeProgress F V).selected p.env (key', sel) = fun _ => C := funext hselected
  refine ⟨rho, rfl, ⟨hv, hnc, fun _ => rfl, ?_,
      ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh1 _⟩⟩⟩,
    ⟨hT, ⟨?_, hse.psync (by linarith only [hb, hTb, hT0, hΔ]) hΔ1 hΔF1⟩,
      ?_, fun δ _ _ => ?_⟩,
    ⟨hT0, hTb, hb, ⟨_, hh1 _, fun u _ _ => hawake1 u⟩,
      ⟨_, b₀, le_rfl, by linarith only [hb, hΔ], hh2 _,
        show asleepAlways (kv key hn 2 (by decide)) (kv key hn 2 (by decide)) b₀ = false by
          simp [asleepAlways_apply]⟩,
      ⟨_, H, hH, le_rfl, hh1 _, fun u _ _ => hawake1 u⟩⟩⟩
  · change ((realPoint key hn Δ hΔ ΔF hΔF
      (asleepAlways (kv key hn 2 (by decide))) H).faultyAt 0).Nonempty
    rw [realPoint_faulty]; exact Finset.singleton_nonempty _
  · exact (Model.sysOf_delivers_iff (O := O) rho _ _ _).mpr
      (he.syncUntil (Model.Run.log_sendsFromZero rho hv) le_rfl hΔ1 hΔF1 b₀)
  · intro t _ _
    exact etaReadyAbove_of_card ha.θ_range.1 hroom.1 _ _ t
      (asleepAlways_readyAt key hn hΔ hΔF H _ t)
  · change p.CommitteeSleepyOn
      (fun t => (shapeProgress F V).selected p.env (key', sel) (max 0 (t - δ))) K.params.θ
      ((K.params.η : Time) * Δ)
      (max ((Sys F V).cDur K ⟨_, rho⟩) ((K.params.η : Time) * Δ - 1))
      ((Sys F V).committeeAheadDur K ⟨_, rho⟩) 0 H
    rw [hselEq]
    exact hcomm

end Witnesses

end Realize

end Consensus.Shape

end
