module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Same-slot writers under windowed service, across a compromise

The growing forms of the static `result_result_compatible_window_before` and
`result_optimistic_compatible_window_before` (`Healing/AC/Compat`). Each writer is honest at its
write, and each counted vote is released by a writer while that writer is honest (`Relayed`).
Service is the growing `ServiceWindowBefore` from `a ≤ t_s`, used only through the update at
`t_s + 6Δ ≤ b`. The releases end before `t_s + 2Δ`, so the only deadlines consumed are by
`t_s + 3Δ`. -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- A release in `[t_s, t_s + 2Δ)`, at or after the start `a` of the service window, reaches an
update of slot `s` at `t_s + 6Δ ≤ b` of a node honest at it whose restarts are by `t_s`. -/
private theorem relayed_held_window
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {a b : Time} {s : Nat} (hsvc : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {X Y : Fin sp.n} {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hY : Y ∈ H (tr.time c)) (hc : tr.CallAt Y c ℓ)
    (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hb : tr.time c ≤ b)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D : Blk sp.n FGP} {u : Fin sp.n} (hu : u ∈ Relayed tr H U X s D) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hX, hsend, h1, h2⟩ := relayed_iff.mp hu
  refine ⟨v, rfl, hR, ?_⟩
  have h := sync_window_before_forward hr hsvc hX hsend (ha.trans h1)
    (by linarith) hY hc (fun j hj hjr => (hrs j hj hjr).trans h1)
    (by rw [ht]; linarith) fun t ht₁ ht₂ => by
      rw [CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]
      omega
  rwa [hvs] at h

/-- Votes for an incompatible block released by a writer while honest occupy seats of an update
disjoint from its result's supporters, under windowed service. -/
private theorem relayed_against_window
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {a b : Time} {s : Nat} (hsvc : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {X Y : Fin sp.n} {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hY : Y ∈ H (tr.time c)) (hc : tr.CallAt Y c ℓ)
    (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hb : tr.time c ≤ b)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D DY : Blk sp.n FGP} {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Relayed tr H U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard := by
  have held := fun {u} (hu : u ∈ Relayed tr H U X s D) =>
    relayed_held_window hr hsvc ha hY hc ht hb hrs hu
  have hU := hr.coherent
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro u hu hu'
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS u hu'
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := held (hT hu)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hnc (anc_total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, _, hv | ⟨a, ha, _, _, _, hav, _⟩⟩ := held (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨_, v, hv, rfl, _⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

/-- Same-slot results of writers honest at their writes are compatible, using only service
through their observation cutoff. -/
theorem result_result_compatible_window_before_at (hrun : ACRun proposer tr H U)
    {a b : Time} {s : Nat} (hsync : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {x x' : Fin sp.n} {i i' : Nat} (hx : x ∈ H (tr.time i)) (hx' : x' ∈ H (tr.time i'))
    {C C' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)}
    (hR : ResultAt tr x i s C CV) (hR' : ResultAt tr x' i' s C' CV')
    (hi : tr.time i ≤ b) (hi' : tr.time i' ≤ b)
    (hreset : ∀ q ≤ i, tr.RestartAt x q → tr.time q ≤ sp.ts s)
    (hreset' : ∀ q ≤ i', tr.RestartAt x' q → tr.time q ≤ sp.ts s) :
    Compatible U C C' := by
  by_contra hnc
  obtain ⟨ℓ, S, hc, ht, -, hmaj, hSF, hSs⟩ := result_side hrun hx hR
  obtain ⟨ℓ', S', hc', ht', -, hmaj', hSF', hSs'⟩ := result_side hrun hx' hR'
  have h1 := relayed_against_window hrun.localRun hsync ha hx hc ht hi hreset hSs hSF'
    fun h => hnc (Or.symm h)
  have h2 := relayed_against_window hrun.localRun hsync ha hx' hc' ht' hi' hreset' hSs' hSF hnc
  omega

/-- A result and an optimistic lock of one slot, by writers honest at their writes, agree with
windowed message service. -/
theorem result_optimistic_compatible_window_before_at
    (hrun : ACRun proposer tr H U)
    {a b : Time} {s : Nat} (hsync : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {x x' : Fin sp.n} {i i' : Nat} (hx : x ∈ H (tr.time i)) (hx' : x' ∈ H (tr.time i'))
    {C O : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)}
    (hR : ResultAt tr x i s C CV) (hO : OptimisticLockAt tr x' i' s O CV')
    (hi : tr.time i ≤ b) (_hi' : tr.time i' ≤ b)
    (hreset : ∀ q ≤ i, tr.RestartAt x q → tr.time q ≤ sp.ts s) : Compatible U C O := by
  by_contra hnc
  obtain ⟨ℓ, S, hc, ht, -, hmaj, -, hSs⟩ := result_side hrun hx hR
  obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := optimistic_seats hrun hx' hO
  rw [hrun.stock] at h34
  have h1 := relayed_against_window hrun.localRun hsync ha hx hc ht hi hreset hSs hT
    fun h => hnc (Or.symm h)
  have hle := Set.ncard_le_ncard (Set.subset_univ (voters {v | v ∈ (tr.state x i).pool s}))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

end Consensus.Goldilocks.SA.Growing

end
