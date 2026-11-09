module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PhaseMono

public section

/-! # Goldilocks Healing: HR.2, phase count

HR.2, an FG store node over FG traces (`FGLocalRun`) with `f < 2q − n`. Proved on paper (claims
HR.2, status S): (a) two honest accepted states with the same `h_j` have the same `J`
(G1.1, G0.5: two justifications at one height have intersecting quorums, and an honest validator
signs one target per height); (b) while the frontier `m` is fixed the effective phase moves only
forward through gap, top `J`, contest — a justification at `m − 1`, once held by an honest node,
stays held (durable stores), (a) makes its `J` unique, and a contest's witness block stays held —
so at most two changes per value of `m`.

The proof: a chain whose state has `h_j ≥ 1` carries a target quorum of non-timeout attestations
with height pair `(h_j, J)`; two such quorums at one height with different `J` cross in `2q − n`
validators with E2 pairs (`Store.justified_crossing`), one of them honest, whose two
attestations client safety (G0.5) excludes (`Store.J_eq_of_hj_eq_of_safe` with
`held_atts_safe`; `J_eq_of_hj_eq`, part (a)). Honest stores keep their blocks and their states
(`held_mono`), and ancestry of a held block does not change as the store grows
(`Store.anc_transfer`), so justifications and contests stay (part (b)); with (a) the phase at a
cut is unique, so a change raises the rank, which lies in `{0, 1, 2}` (part (c)). -/

namespace Consensus.Goldilocks.Healing

open Store

/-! ## Part (a): one justified entry per height -/

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- **HR.2 (a).** Two honest accepted states with the same `h_j` have the same `J`. -/
theorem J_eq_of_hj_eq (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y z : Fin P.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat} {B B' : NodeBlock P ACP}
    (hB : B ∈ (tr.store y i).tree) (hB' : B' ∈ (tr.store z j).tree)
    (he : ((tr.store y i).σ B.root).hj = ((tr.store z j).σ B'.root).hj) :
    ((tr.store y i).σ B.root).J = ((tr.store z j).σ B'.root).J :=
  J_eq_of_hj_eq_of_safe (store_reachable hr hy i) (store_reachable hr hz j) hH
    (held_atts_safe hr hy hz i j) hB hB' he

/-- With (a), a justified block at a height is unique across cuts (roots are injective on
`U`). -/
theorem justifiedAt_unique (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {i i' h : Nat} {J J' : NodeBlock P ACP} (h₁ : JustifiedAt tr H i h J)
    (h₂ : JustifiedAt tr H i' h J') : J = J' := by
  obtain ⟨y, hy, hJ, B, hB, hBh, hBJ⟩ := h₁
  obtain ⟨z, hz, hJ', B', hB', hBh', hBJ'⟩ := h₂
  exact hr.coherent.1 (hr.tree_subset y hy i hJ) (hr.tree_subset z hz i' hJ')
    (hBJ.symm.trans ((J_eq_of_hj_eq hr hH hy hz hB hB' (hBh.trans hBh'.symm)).trans hBJ'))

/-! ## Part (b): justifications and contests stay -/

/-- **HR.2 (b).** While the frontier stays, the phase moves only forward, with one `J`. -/
theorem phaseAt_mono (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {m i j : Nat} {c c' : PhaseCase (NodeBlock P ACP)} (hij : i ≤ j)
    (hc : PhaseAt tr H i m c) (hc' : PhaseAt tr H j m c') :
    c.rank ≤ c'.rank ∧ ∀ J, c.topJ = some J → c'.topJ = some J := by
  cases c with
  | gap => exact ⟨Nat.zero_le _, fun _ h => by cases h⟩
  | top J =>
    have hJ := justifiedAt_mono hr hij hc.2.1
    cases c' with
    | gap => exact absurd hJ (hc'.2 J)
    | top J' =>
      obtain rfl := justifiedAt_unique hr hH hJ hc'.2.1
      exact ⟨le_rfl, fun _ h => h⟩
    | contest J' =>
      obtain rfl := justifiedAt_unique hr hH hJ hc'.2.1
      exact ⟨Nat.le_succ 1, fun _ h => h⟩
  | contest J =>
    have hJ := justifiedAt_mono hr hij hc.2.1
    cases c' with
    | gap => exact absurd hJ (hc'.2 J)
    | top J' =>
      obtain rfl := justifiedAt_unique hr hH hJ hc'.2.1
      exact absurd (contestAt_mono hr hij hc.2.2) hc'.2.2
    | contest J' =>
      obtain rfl := justifiedAt_unique hr hH hJ hc'.2.1
      exact ⟨le_rfl, fun _ h => h⟩

/-- Two cases with the same rank and the first's top `J` kept are equal. -/
theorem PhaseCase.eq_of_rank {β : Type} {c c' : PhaseCase β} (hr : c.rank = c'.rank)
    (ht : ∀ J, c.topJ = some J → c'.topJ = some J) : c = c' := by
  cases c <;> cases c' <;> simp only [PhaseCase.rank, PhaseCase.topJ] at hr ht
  all_goals first
    | rfl
    | omega
    | rw [Option.some.inj (ht _ rfl)]

/-- With (a), the phase at a cut is unique. -/
theorem phaseAt_unique (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {m i : Nat} {c c' : PhaseCase (NodeBlock P ACP)} (hc : PhaseAt tr H i m c)
    (hc' : PhaseAt tr H i m c') : c = c' :=
  let ⟨h₁, ht⟩ := phaseAt_mono hr hH le_rfl hc hc'
  PhaseCase.eq_of_rank (le_antisymm h₁ (phaseAt_mono hr hH le_rfl hc' hc).1) ht

/-- A phase change at a fixed frontier raises the rank. -/
private theorem rank_lt_of_ne (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {m i j : Nat} {c c' : PhaseCase (NodeBlock P ACP)} (hij : i ≤ j)
    (hc : PhaseAt tr H i m c) (hc' : PhaseAt tr H j m c') (hne : c ≠ c') : c.rank < c'.rank :=
  let ⟨h₁, ht⟩ := phaseAt_mono hr hH hij hc hc'
  lt_of_le_of_ne h₁ fun he => hne (PhaseCase.eq_of_rank he ht)

/-- **HR.2 (c).** At most two phase changes per value of the frontier. -/
theorem phase_changes_le_two (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    (m : Nat) :
    {i | ∃ c c', PhaseAt tr H i m c ∧ PhaseAt tr H (i + 1) m c' ∧ c ≠ c'}.encard ≤ 2 := by
  classical
  set S := {i | ∃ c c', PhaseAt tr H i m c ∧ PhaseAt tr H (i + 1) m c' ∧ c ≠ c'}
  let f : Nat → Nat := fun i =>
    if h : ∃ c, PhaseAt tr H i m c then (Classical.choose h).rank else 0
  have hf : ∀ {i c}, PhaseAt tr H i m c → f i = c.rank := fun {i c} hc => by
    have h : ∃ c, PhaseAt tr H i m c := ⟨c, hc⟩
    simp only [f, h, ↓reduceDIte]
    rw [phaseAt_unique hr hH (Classical.choose_spec h) hc]
  have hlt : ∀ i ∈ S, ∀ i' ∈ S, i < i' → f i < f i' := by
    rintro i ⟨c, c', hc, hc', hne⟩ i' ⟨d, -, hd, -⟩ hii'
    rw [hf hc, hf hd]
    exact (rank_lt_of_ne hr hH (Nat.le_succ i) hc hc' hne).trans_le
      (phaseAt_mono hr hH hii' hc' hd).1
  have hinj : Set.InjOn f S := fun i hi i' hi' he => by
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd he (hlt i hi i' hi' h).ne
    · exact h
    · exact absurd he (hlt i' hi' i hi h).ne'
  have hmaps : f '' S ⊆ {0, 1} := by
    rintro _ ⟨i, ⟨c, c', hc, hc', hne⟩, rfl⟩
    have h1 := rank_lt_of_ne hr hH (Nat.le_succ i) hc hc' hne
    have h2 : c'.rank ≤ 2 := by cases c' <;> simp [PhaseCase.rank]
    rw [hf hc]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [← hinj.encard_image]
  exact (Set.encard_le_encard hmaps).trans (Set.encard_pair (by decide)).le

/-- **HR.2, phase count.** -/
theorem phase_count (P : Params) (ACP : Type) : PhaseCount P ACP := by
  intro acp₀ H U tr hr hH
  exact ⟨fun y hy z hz i j B hB B' hB' he => J_eq_of_hj_eq hr hH hy hz hB hB' he,
    fun m i j c c' hij hc hc' => phaseAt_mono hr hH hij hc hc',
    fun m => phase_changes_le_two hr hH m⟩

end Consensus.Goldilocks.Healing

end
