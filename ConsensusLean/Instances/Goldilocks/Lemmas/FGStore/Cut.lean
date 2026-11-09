module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutBase
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutSteps

public section

/-! # Goldilocks FG store: G1.10 at the scope of C1.1

The excluded entries of C1.1's scope are the blocks that conflict with `B` and strictly extend
the `Σ.F` of some honest node at `Ts` (`excludedEntries`). Under (K0) (at `Ts` the `Σ.F` and
`Σ.J` of every honest node are compatible with `B`), every entry that conflicts with `B` on the
chain of a block that an honest `y` accepts from `Ts` on strictly extends `y`'s `Σ.F` at `Ts`,
so it is excluded, and the core (`quorum_free_entries`) keeps it unjustified there: (a) no
justification on such a chain conflicts with `B`; (b) a block that conflicts with `B` is at most
one height above its deepest common ancestor with `B`; (c) `y`'s `Σ.F` and `Σ.J`, which move
only when a block is accepted (to its justification and below), stay compatible with `B`
(`cut_scope`; claims G1.10, "The scope of C1.1"). The vocabulary is in `FGStore/CutBase`,
the steps, which the growing-fault sibling shares, in `FGStore/CutSteps`. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- **G1.10 at the scope of C1.1.** (a), (b) at every block that the honest `y` accepts in
`[Ts, T + Δ)`, or its own proposal at `T + Δ`; (c) `y`'s `Σ.F` and `Σ.J` after every cut in
`[Ts, T + Δ]` up to which `y` accepted only such blocks. -/
theorem cut_scope {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
    {tr : FGTrace P ACP} (hr : FGLocalRun acp₀ H U tr) {B : NodeBlock P ACP} {Ts T₀ T : Time}
    (hT₀ : P.IsPublic T₀) (hT : P.IsPublic T)
    (hK0 : ∀ z ∈ H, ∀ j, Ts ≤ tr.time j → (∀ k < j, tr.time k < Ts) →
      Compatible U (tr.store z j).F B ∧ Compatible U (tr.store z j).J B)
    (hK1 : ∀ E ∈ excludedEntries H U tr Ts B, (namers P ACP H tr T₀ E).ncard < P.fg.q)
    (hrows : ∀ v ∈ H, ∀ j a, tr.SignAt v j a → T₀ < tr.time j → tr.time j ≤ T →
      ∀ E ∈ excludedEntries H U tr Ts B, a.T ≠ E.root)
    {y : Fin P.n} (hy : y ∈ H) :
    (∀ i X, tr.AcceptAt y i X → Ts ≤ tr.time i →
      (tr.time i < T + P.Δ ∨ (tr.time i = T + P.Δ ∧ X.proposer = y ∧ P.slotTime X.slot = T + P.Δ)) →
      let S := tr.store y (i + 1)
      (∀ A' ∈ S.tree, S.Anc A' X → ∀ Jb, S.blocks (S.σ A'.root).J = some Jb → Compatible U Jb B) ∧
      (¬ Compatible U X B → ∀ Pc, Goldilocks.Anc U Pc X → Goldilocks.Anc U Pc B →
        (∀ Q, Goldilocks.Anc U Q X → Goldilocks.Anc U Q B → Goldilocks.Anc U Q Pc) →
        (S.σ X.root).h ≤ (S.σ Pc.root).h + 1)) ∧
    (∀ i, Ts ≤ tr.time i → tr.time i ≤ T + P.Δ →
      (∀ j ≤ i, ∀ X, tr.AcceptAt y j X → Ts ≤ tr.time j → tr.time j < T + P.Δ ∨
        (tr.time j = T + P.Δ ∧ X.proposer = y ∧ P.slotTime X.slot = T + P.Δ)) →
      Compatible U (tr.store y (i + 1)).F B ∧ Compatible U (tr.store y (i + 1)).J B) := by
  classical
  have first : ∀ i, Ts ≤ tr.time i →
      ∃ j₀ ≤ i, Ts ≤ tr.time j₀ ∧ ∀ k < j₀, tr.time k < Ts := fun i hi =>
    have hex : ∃ k, Ts ≤ tr.time k := ⟨i, hi⟩
    ⟨Nat.find hex, Nat.find_min' hex hi, Nat.find_spec hex,
      fun k hk => not_le.1 (Nat.find_min hex hk)⟩
  refine ⟨fun i X hX hTi htime => ?_, fun i hTi _ hsc => ?_⟩
  · obtain ⟨j₀, hji, hj₀, hmin⟩ := first i hTi
    exact scope_block_of hr hy hj₀ hmin (hK0 y hy j₀ hj₀ hmin).1 hji hX
      (quorum_free_entries P ACP acp₀ H U tr _ T₀ T y hr hT₀ hT hy hK1 hrows i X hX htime)
  obtain ⟨j₀, hji, hj₀, hmin⟩ := first i hTi
  suffices h : ∀ m, j₀ ≤ m → m ≤ i + 1 →
      Compatible U (tr.store y m).F B ∧ Compatible U (tr.store y m).J B from
    h (i + 1) (by omega) le_rfl
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact fun _ => hK0 y hy j₀ hj₀ hmin
  | succ m hjm ih =>
    intro hmi
    have ih := ih (by omega)
    rcases store_step hr hy m with he | ⟨X, hX, hXo⟩ | ⟨a, -, he⟩
    · rw [he]
      exact ih
    · obtain ⟨hJ, hF⟩ := onBlock_FJ hXo
      have hTm : Ts ≤ tr.time m := hj₀.trans (hr.time_mono hjm)
      have hJc : Compatible U (tr.store y (m + 1)).J B := by
        rcases hJ with hJ | hJ
        · rw [hJ]
          exact ih.2
        · exact (scope_block_of hr hy hj₀ hmin (hK0 y hy j₀ hj₀ hmin).1 hjm hX
            (quorum_free_entries P ACP acp₀ H U tr _ T₀ T y hr hT₀ hT hy hK1 hrows m X hX
              (hsc m (by omega) X hX hTm))).1 X (accept_mem hr hy hX) .refl _ hJ
      refine ⟨?_, hJc⟩
      rcases hF with hF | hF
      · rw [hF]
        exact ih.1
      · exact compatible_of_anc hr.coherent (hF.mono (hr.tree_subset y hy _)) hJc
    · obtain ⟨atts, he'⟩ := (tr.store y m).onAttestation_eq a
      rw [he, he']
      exact ih

end Consensus.Goldilocks.Store

end
