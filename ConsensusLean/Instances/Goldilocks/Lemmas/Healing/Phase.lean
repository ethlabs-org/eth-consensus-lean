module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service

public section

/-! # Goldilocks Healing: HR.2, phase count

HR.2, an FG store node over FG traces (`FGLocalRun`) with `f < 2q − n`. Proved on paper (claims
HR.2, status S; healing-simple `t1-proof.md` §8 (F2, first part), `producer-reset-continuation.md`
§14, slides 25, 26, 30): (a) two honest accepted states with the same `h_j` have the same `J`
(G1.1, G0.5: two justifications at one height have intersecting quorums, and an honest validator
signs one target per height); (b) while the frontier `m` is fixed the effective phase moves only
forward through gap, top `J`, contest — a justification at `m − 1`, once held by an honest node,
stays held (durable stores), (a) makes its `J` unique, and a contest's witness block stays held —
so at most two changes per value of `m`.

The proof: a chain whose state has `h_j ≥ 1` carries a target quorum of non-timeout attestations
with height pair `(h_j, J)` (`justification_quorum`, by induction over the chain, from the target
bits); two such quorums at one height with different `J` meet in an honest validator, whose two
attestations are an E2 pair, which client safety (G0.5) excludes (`J_eq_of_hj_eq`, part (a)). Honest
stores keep their blocks and their states (`held_mono`), and ancestry of a held block does not
change as the store grows (`Store.anc_transfer`), so justifications and contests stay (part
(b)); with (a) the phase at a cut is unique, so a change raises the rank, which lies in
`{0, 1, 2}` (part (c)). -/

namespace Consensus.Goldilocks.Healing

open Store

/-! ## The target quorum of a justification, chain level -/

/-- A target bit after counting is old or set by a counted non-timeout attestation on the
entry. -/
private theorem mem_foldl_target {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ (atts.foldl FG.ChainState.processAtt σ).target) :
    v ∈ σ.target ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.target ∨ (a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) := by
        unfold FG.ChainState.processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals aesop
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · rw [hh, hT] at hb'
      exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

/-- **The target quorum of a justification.** Each target bit of a chain's state has its
non-timeout attestation on the chain, and a justification `(h_j, J)` with `h_j ≥ 1` has a
quorum of non-timeout attestations on the chain with height pair `(h_j, J)`. -/
private theorem justification_quorum (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)}
    {σ : FG.ChainState gp.n} (h : gp.chainState c = some σ) :
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false) := by
  refine gp.chainState_induction (P := fun c σ =>
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false))
    ⟨by simp [FG.ChainState.init], by simp [FG.ChainState.init]⟩ ?_ h
  intro c σ B σ' _ ⟨ht, hq⟩ hB
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append] at h ⊢
    exact Or.inl h
  have liftB : ∀ {a}, a ∈ B.atts → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append]
    exact Or.inr (by simpa using h)
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 hB
  have hT := fun v => @mem_foldl_target _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hT ⊢
  dsimp only at hT
  have ht₀ : ∀ v ∈ t, ∃ a ∈ gp.chainAtts (c ++ [B]),
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
    intro v hv
    rcases hT v hv with hv | ⟨a, ha, h'⟩
    · obtain ⟨a, ha, h'⟩ := ht v hv
      exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, liftB ha, h'⟩
  have hq₀ : 1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
      ∀ v ∈ Q, ∃ a ∈ gp.chainAtts (c ++ [B]),
        a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false := fun h1 =>
    let ⟨Q, hQ, hv⟩ := hq h1
    ⟨Q, hQ, fun v h => let ⟨a, ha, h'⟩ := hv v h; ⟨a, liftA ha, h'⟩⟩
  obtain ⟨F, hF', σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨⟨hq', -⟩, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨by simp [FG.ChainState.advance], fun _ => ⟨t, hq', ht₀⟩⟩
  · exact ⟨by simp [FG.ChainState.advance], hq₀⟩
  · exact ⟨ht₀, hq₀⟩

/-! ## Part (a): one justified entry per height -/

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- A held block of an honest store has a chain whose fold is its state, and every attestation
of that chain with an honest signer was signed before the cut. -/
private theorem held_chain (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) :
    ∃ c : List (NodeBlock P ACP),
      P.fg.chainState (c.map Block.fgView) = some ((tr.store y i).σ B.root) ∧
      ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), a.val ∈ H → ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨c, hc, -, -, hσ⟩ := chain_state_of_chain P ACP acp₀ _ (store_reachable hr hy i) B hB
  refine ⟨c, hσ, fun a ha hav => ?_⟩
  obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
  obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
  rcases tree_accepted hr hy (hc X hXc) with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · obtain ⟨k', hk', hs⟩ := hr.unforgeable y hy k a ⟨_, hacc, haX⟩ hav
    exact ⟨k', by omega, hs⟩

/-- **HR.2 (a).** Two honest accepted states with the same `h_j` have the same `J`. -/
theorem J_eq_of_hj_eq (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y z : Fin P.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat} {B B' : NodeBlock P ACP}
    (hB : B ∈ (tr.store y i).tree) (hB' : B' ∈ (tr.store z j).tree)
    (he : ((tr.store y i).σ B.root).hj = ((tr.store z j).σ B'.root).hj) :
    ((tr.store y i).σ B.root).J = ((tr.store z j).σ B'.root).J := by
  obtain ⟨c₁, h₁, ha₁⟩ := held_chain hr hy hB
  obtain ⟨c₂, h₂, ha₂⟩ := held_chain hr hz hB'
  rcases Nat.eq_zero_or_pos ((tr.store y i).σ B.root).hj with h0 | h0
  · rw [(FG.chain_invariants P.fg _ _ h₁).2.2.2.1 h0,
      (FG.chain_invariants P.fg _ _ h₂).2.2.2.1 (he ▸ h0)]
  by_contra hne
  obtain ⟨Q₁, hQ₁, hv₁⟩ := (justification_quorum P.fg h₁).2 h0
  obtain ⟨Q₂, hQ₂, hv₂⟩ := (justification_quorum P.fg h₂).2 (he ▸ h0)
  obtain ⟨v, hvQ, hv⟩ : ∃ v ∈ Q₁ ∩ Q₂, v ∈ H := by
    by_contra! hS
    have h1 := (FG.quorum_intersection P.fg Q₁ Q₂ hQ₁ hQ₂).1
    have := Set.ncard_le_ncard (s := ((Q₁ ∩ Q₂ : Finset _) : Set (Fin P.fg.n))) (t := Hᶜ) hS
    rw [Set.ncard_coe_finset] at this
    have : (Hᶜ : Set (Fin P.fg.n)).ncard = (Hᶜ : Set (Fin P.n)).ncard := rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, rfl, hah, haT, hat⟩ := hv₁ v (Finset.mem_inter.1 hvQ).1
  obtain ⟨b, hb, hvb, hbh, hbT, hbt⟩ := hv₂ a.val (Finset.mem_inter.1 hvQ).2
  obtain ⟨inputs, hin, hrun⟩ := signed_run hr hv (i + j)
  obtain ⟨k, hk, hka⟩ := ha₁ a ha hv
  obtain ⟨k', hk', hkb⟩ := ha₂ b hb (hvb ▸ hv)
  rw [hvb] at hkb
  exact FG.client_safety P.fg a.val inputs hin a (hrun k (by omega) a hka) b
    (hrun k' (by omega) b hkb)
    ⟨hvb.symm, Or.inr (Or.inr ⟨by rw [hah, hbh, he], hat, hbt, by rw [haT, hbT]; exact hne⟩)⟩

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

/-- A justification held at an honest node stays held. -/
private theorem justifiedAt_mono (hr : FGLocalRun acp₀ H U tr) {i j : Nat} (hij : i ≤ j)
    {h : Nat} {J : NodeBlock P ACP} (hJ : JustifiedAt tr H i h J) : JustifiedAt tr H j h J := by
  obtain ⟨y, hy, hJ, B, hB, hh, hJr⟩ := hJ
  obtain ⟨hB', hσ⟩ := held_mono hr hy hij hB
  exact ⟨y, hy, (held_mono hr hy hij hJ).1, B, hB', by rw [hσ]; exact hh, by rw [hσ]; exact hJr⟩

/-- A contest held at an honest node stays held. -/
private theorem contestAt_mono (hr : FGLocalRun acp₀ H U tr) {i j : Nat} (hij : i ≤ j)
    {m : Nat} {J : NodeBlock P ACP} (hc : ContestAt tr H i m J) : ContestAt tr H j m J := by
  obtain ⟨y, hy, B, hB, hh, hn⟩ := hc
  obtain ⟨hB', hσ⟩ := held_mono hr hy hij hB
  exact ⟨y, hy, B, hB', by rw [hσ]; exact hh, fun ha => hn (Store.anc_transfer hr hy hy ha hB)⟩

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
