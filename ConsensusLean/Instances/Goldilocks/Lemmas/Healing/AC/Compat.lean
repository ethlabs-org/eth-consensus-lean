module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: results of one slot `≥ r` are compatible (T1 §2)

Over a `StandaloneRun` (H.1's premises), for a slot `s` with `t_s ≥ ḡ + 4Δ` (`s ≥ r_AC(ḡ)`):

* two fast origins (fast test or optimistic, any combination) are compatible
  (`fastLock_fastLock_compatible`: A1.9's `fastLock_same_slot`);
* two results of `get_confirmation` (fast, slow, vetoed or not) at honest nodes are compatible
  (`result_result_compatible`): their supporter sets are disjoint, since a common supporter's two
  votes both reach both readers before their updates (`Sync`), and each reader counts both sets
  as participants, against the two strict majorities;
* a result and an optimistic confirmation are compatible (`result_optimistic_compatible`): the
  `≥ 3n/4` optimistic voters reach the reader and none supports a conflicting result without
  equivocating there, so the result's strict majority would need more than the remaining
  `n/4` seats.

The forwarding helpers are those of `Lemmas/AC/Steps/CompatibleSides`, with the
update's side taken for any result. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- **The result side.** At an honest update of slot `s` with result `C`: its supporters `S`
of `C` are more than half of its voters; each has a vote in its pool, extending `C`, and does
not equivocate there, and that vote was admitted in `[t_s, t_s + 2Δ)`. -/
private theorem result_side (hrun : ACRun proposer tr H U) {Y : Fin sp.n} (hY : Y ∈ H) {c s : Nat}
    {C : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr Y c s C CV) :
    ∃ (ℓ : ACLabel (goldilocksSA sp FGP ro)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Fwd tr U Y s C ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U C R := by
  have hr := hrun.localRun
  obtain ⟨ℓ, ⟨hc, -, ht, -⟩, hC, -⟩ := hR
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hY hc
  refine ⟨ℓ, supporters ℓ.frame ⟨{v | v ∈ (tr.state Y c).pool s}, {v | v ∈ (tr.state Y c).pool s ∧
    resolutionTime (tr.state Y c) ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s C, hc, ht,
    ?_, ?_, ?_⟩
  · have hmaj := (deepest_mem hC).1.2.2
    unfold confirmationScore at hmaj
    exact hmaj
  · rintro u ⟨-, v, ⟨hvp, hres⟩, rfl, -, R, hR, hRr, hDR⟩
    have hvs := state_pool_slot sp hr hY c s v hvp
    rw [fwd_iff]
    refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, admitted_of_held hr hY hvs hvp le_rfl
      fun k _ hst => ?_⟩
    have hst' : (tr.state Y c).voteStamp v < ETime.of (sp.ts s + 2 * sp.Δ) := by
      unfold resolutionTime at hres
      split at hres
      · exact absurd hres (by simp [ETime.of])
      · split_ifs at hres
        · exact absurd hres (by simp [ETime.of])
        · exact lt_of_le_of_lt (le_max_left _ _) hres
    rw [hst] at hst'
    exact WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst')
  · rintro u ⟨hneq, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hDR⟩
    exact ⟨hneq, v, hvp, rfl, R, hΦU hR, hRr, Anc.mono hΦU hDR⟩

/-- A forwardable slot-`s` vote (`Fwd`: sent or admitted by an honest `X` in `[t_s, t_s + 2Δ)`)
reaches an honest node's update of slot `s` (its restarts at or before `t_s`) under `Sync`: the
node holds it, or two other votes of its validator. -/
theorem fwd_reaches_update (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D : Blk sp.n FGP} {u : Fin sp.n}
    (hu : ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  exact fwd_held hr hsync hX hY hc ht hrs (fwd_iff.2 hu)

/-- **T1 §2, two fast origins of one slot** (fast test or optimistic, in any combination; the
optimistic/optimistic case of T1 §2): A1.9's same-slot lemma under `Sync[t_s, t_{s+1} + Δ]` and
`f < n/2`. -/
theorem fastLock_fastLock_compatible (hS : HealthyBase tr H U proposer g)
    {s : Nat} {x x' : Fin sp.n}
    {i i' : Nat} {B B' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)} (hx : x ∈ H)
    (hfl : FastLockAt tr x i s B CV) (hx' : x' ∈ H) (hfl' : FastLockAt tr x' i' s B' CV')
    (hs : gbar g ≤ sp.ts s) : Compatible U B B' :=
  fastLock_same_slot hS.run hx hfl hx' hfl' (hS.syncAC hs _) hS.two_faulty_lt

/-- **T1 §2, regular/regular**: two results (`get_confirmation`, vetoed or not) of one slot
`s ≥ r` at honest nodes are compatible. -/
theorem result_result_compatible (hS : HealthyBase tr H U proposer g) {s : Nat} {x x' : Fin sp.n}
    {i i' : Nat} {C C' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)} (hx : x ∈ H)
    (hR : ResultAt tr x i s C CV) (hx' : x' ∈ H) (hR' : ResultAt tr x' i' s C' CV')
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) : Compatible U C C' := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hsync := hS.syncAC (a := sp.ts s) (by linarith) (sp.ts (s + 1 : Nat) + sp.Δ)
  have hrs : ∀ y ∈ H, ∀ k, tr.RestartAt y k → tr.time k ≤ sp.ts s := fun y hy k hk =>
    (hS.restart_le hy hk).trans (by linarith)
  by_contra hnc
  obtain ⟨ℓ, S, hc, ht, hmaj, hSF, hSs⟩ := result_side hS.run hx hR
  obtain ⟨ℓ', S', hc', ht', hmaj', hSF', hSs'⟩ := result_side hS.run hx' hR'
  have h1 := against_update hr hsync hx' hx hc ht (fun k _ => hrs x hx k) hSs hSF'
    fun h => hnc (Or.symm h)
  have h2 := against_update hr hsync hx hx' hc' ht' (fun k _ => hrs x' hx' k) hSs' hSF hnc
  omega

/-- **T1 §2, regular/optimistic**: a result of slot `s ≥ r` at an honest node is compatible
with an honest optimistic confirmation of slot `s`. -/
theorem result_optimistic_compatible (hS : HealthyBase tr H U proposer g)
    {s : Nat} {x x' : Fin sp.n}
    {i i' : Nat} {C B : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)} (hx : x ∈ H)
    (hR : ResultAt tr x i s C CV) (hx' : x' ∈ H) (hO : OptimisticLockAt tr x' i' s B CV')
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) : Compatible U C B := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hsync := hS.syncAC (a := sp.ts s) (by linarith) (sp.ts (s + 1 : Nat) + sp.Δ)
  by_contra hnc
  obtain ⟨ℓ, S, hc, ht, hmaj, -, hSs⟩ := result_side hS.run hx hR
  obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := optimistic_side hS.run hx' hO
  have h1 := against_update hr hsync hx' hx hc ht
    (fun k _ hk => (hS.restart_le hx hk).trans (by linarith)) hSs hT fun h => hnc (Or.symm h)
  have hle := Set.ncard_le_ncard (Set.subset_univ (voters {v | v ∈ (tr.state x i).pool s}))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

private theorem fwd_reaches_update_window_before
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {a b : Time} {s : Nat}
    (hsync : SyncACWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt Y c ℓ)
    (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hb : tr.time c ≤ b)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D : Blk sp.n FGP} {u : Fin sp.n} (hu : u ∈ Fwd tr U X s D) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  rw [fwd_iff] at hu
  obtain ⟨v, rfl, hvs, hR, k, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have h := sync_window_before_forward hr (serviceWindowBefore_of_sync hsync) hX hsend (ha.trans h1)
    (by linarith) hY hc (fun k' hk' hr' => (hrs k' hk' hr').trans h1)
    (by linarith) fun t ht₁ ht₂ => by
      rw [CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]
      omega
  rwa [hvs] at h

private theorem against_update_window_before
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {a b : Time} {s : Nat}
    (hsync : SyncACWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt Y c ℓ)
    (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hb : tr.time c ≤ b)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D DY : Blk sp.n FGP} {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Fwd tr U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard := by
  have hU := hr.coherent
  have hf := fun {u} (hu : u ∈ Fwd tr U X s D) =>
    fwd_reaches_update_window_before hr hsync ha hX hY hc ht hb hrs hu
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro u hu hu'
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS u hu'
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := hf (hT hu)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hnc (anc_total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, -, hv | ⟨a, ha, -, -, -, hav, -⟩⟩ := hf (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨-, v, hv, rfl, -⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

/-- Same-slot results are compatible using only service through their observation cutoff. -/
theorem result_result_compatible_window_before (hrun : ACRun proposer tr H U)
    {a b : Time} {s : Nat} (hsync : SyncACWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {x x' : Fin sp.n} (hx : x ∈ H) (hx' : x' ∈ H)
    {i i' : Nat} {C C' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)}
    (hR : ResultAt tr x i s C CV) (hR' : ResultAt tr x' i' s C' CV')
    (hi : tr.time i ≤ b) (hi' : tr.time i' ≤ b)
    (hreset : ∀ y ∈ H, ∀ q ≤ max i i', tr.RestartAt y q → tr.time q ≤ sp.ts s) :
    Compatible U C C' := by
  by_contra hnc
  obtain ⟨ℓ, S, hc, ht, hmaj, hSF, hSs⟩ := result_side hrun hx hR
  obtain ⟨ℓ', S', hc', ht', hmaj', hSF', hSs'⟩ := result_side hrun hx' hR'
  have h1 := against_update_window_before hrun.localRun hsync ha hx' hx hc ht hi
    (fun q hq => hreset x hx q (hq.trans (le_max_left _ _))) hSs hSF'
    fun h => hnc (Or.symm h)
  have h2 := against_update_window_before hrun.localRun hsync ha hx hx' hc' ht' hi'
    (fun q hq => hreset x' hx' q (hq.trans (le_max_right _ _))) hSs' hSF hnc
  omega

/-- A result and optimistic lock of one slot agree with windowed message service. -/
theorem result_optimistic_compatible_window_before (hrun : ACRun proposer tr H U)
    {a b : Time} {s : Nat} (hsync : SyncACWindowBefore H U a b tr) (ha : a ≤ sp.ts s)
    {x x' : Fin sp.n} (hx : x ∈ H) (hx' : x' ∈ H)
    {i i' : Nat} {C O : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)}
    (hR : ResultAt tr x i s C CV) (hO : OptimisticLockAt tr x' i' s O CV')
    (hi : tr.time i ≤ b) (_hi' : tr.time i' ≤ b)
    (hreset : ∀ q ≤ i, tr.RestartAt x q → tr.time q ≤ sp.ts s) : Compatible U C O := by
  by_contra hnc
  obtain ⟨ℓ, S, hc, ht, hmaj, -, hSs⟩ := result_side hrun hx hR
  obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := optimistic_side hrun hx' hO
  have h1 := against_update_window_before hrun.localRun hsync ha hx' hx hc ht hi hreset
    hSs hT fun h => hnc (Or.symm h)
  have hle := Set.ncard_le_ncard (Set.subset_univ (voters {v | v ∈ (tr.state x i).pool s}))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

end Consensus.Goldilocks.SA

end
