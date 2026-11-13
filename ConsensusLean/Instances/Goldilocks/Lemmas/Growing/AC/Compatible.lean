module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Locks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents

public section

/-! # Compatibility of historical fast locks with later honest votes -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- The fault bound is read at the later call, not at the historical lock writer. -/
theorem fastLock_compatible_of_votes
    (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n)
    (hP : ∀ t, CommitteeP K (tr.upTo t) (H t))
    {x : Fin sp.n} {j i s : Nat} (hx : x ∈ H (tr.time j)) (hji : j < i)
    {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr x j s D CV)
    (hf : 2 * (K.committee s ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hvotes : ∀ z k, k < i → z ∈ H (tr.time k) → ∀ e,
      VoteAt tr z k e → e.msg.slot = s → VoteExtends U e.msg B) :
    Compatible U D B := by
  have hr := hrun.localRun
  have hjt := hr.time_mono hji.le
  have hf' : 2 * (K.committee s ∩ (H (tr.time j))ᶜ).ncard < sp.committeeSize := by
    have hsub : K.committee s ∩ (H (tr.time j))ᶜ ⊆ K.committee s ∩ (H (tr.time i))ᶜ :=
      Set.inter_subset_inter_right _ (Set.compl_subset_compl.mpr (hr.antitone hjt))
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard hsub)) hf
  refine SA.fastLock_compatible_of_votes (hrun.upTo (hr.time_nonneg j)) K (hP (tr.time j)) hx
    hji ((upTo_fastLockAt hr.time_mono).mpr ⟨le_rfl, hfl⟩) hf' ?_
  intro z hz k hki e hv hs
  obtain ⟨hkt, hv⟩ := upTo_voteAt.mp hv
  exact hvotes z k hki (hr.antitone hkt hz) e hv hs

private theorem update_side
    (hrun : ACRun proposer tr H U) {Y : Fin sp.n} {c s : Nat}
    (hY : Y ∈ H (tr.time c)) {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hfl : FastUpdateAt tr Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksSA sp FGP ro)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      sp.committeeSize ≤ 2 * S.ncard ∧
        (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Relayed tr H U Y s D ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U D R := by
  obtain ⟨ℓ, C, hu, hC, hD, rfl⟩ := hfl
  obtain ⟨ℓ', S, hc, ht, hrs, hmaj, hrel, hS⟩ := result_side hrun hY
    (show ResultAt tr Y c s C _ from ⟨ℓ, hu, hC, rfl⟩)
  -- Unlike the result side, the fast side counts supporters of the selected ancestor `D`.
  set V : View sp.n := ⟨{v | v ∈ (tr.state Y c).pool s},
    {v | v ∈ (tr.state Y c).pool s ∧
      resolutionTime (tr.state Y c) ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  set T := supporters ℓ.frame V s D
  have hCD := (deepest_mem hD).1.1.2.2
  have hfast : sp.committeeSize ≤ 2 * T.ncard := by
    simpa only [FastTest, confirmationScore] using (deepest_mem hD).1.2.2
  have hmaj' : (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * T.ncard := by
    have hmajC := (deepest_mem hC).1.2.2
    unfold confirmationScore at hmajC
    exact lt_of_lt_of_le hmajC (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard
      ((supporters_antitone sp) FGP ℓ.frame V s D C hCD)))
  have hr := hrun.upTo (hrun.localRun.time_nonneg c)
  have hm := hrun.localRun.time_mono
  have hstate : (tr.upTo (tr.time c)).state Y c = tr.state Y c :=
    Trace.upTo_state tr Y fun _ hk => hm hk.le
  have hΦU := (frameIn_of_call hr.localRun hY
    ((upTo_updateAt hm).mpr ⟨le_rfl, hu⟩).1).2
  refine ⟨ℓ', T, hc, ht, hrs, hfast, hmaj', ?_, ?_⟩
  · rintro u ⟨_, v, ⟨hvp, hres⟩, rfl, _, R, hR, hRr, hDR⟩
    have hvp' : v ∈ ((tr.upTo (tr.time c)).state Y c).pool s := hstate.symm ▸ hvp
    have hvs := state_pool_slot sp hr.localRun hY c s v hvp'
    rw [relayed_iff]
    refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, ?_⟩
    obtain ⟨k, hsend, h1, h2⟩ := admitted_of_held hr.localRun hY hvs hvp' le_rfl
      (fun k _ hst => by
        rw [hstate] at hst
        have hst' : (tr.state Y c).voteStamp v < ETime.of (sp.ts s + 2 * sp.Δ) := by
          unfold resolutionTime at hres
          split at hres
          · exact absurd hres (by simp [ETime.of])
          · split_ifs at hres
            · exact absurd hres (by simp [ETime.of])
            · exact lt_of_le_of_lt (le_max_left _ _) hres
        rw [hst] at hst'
        exact WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst'))
    obtain ⟨hkc, hsend⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hsend
    exact ⟨k, hrun.localRun.antitone hkc hY, hsend, h1, h2⟩
  · rintro u ⟨hne, v, ⟨hvp, _⟩, rfl, _, R, hR, hRr, hDR⟩
    exact ⟨hne, v, hvp, rfl, R, hΦU hR, hRr, Anc.mono hΦU hDR⟩

private theorem against_update
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U
      (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hY : Y ∈ H (tr.time c)) (hc : tr.CallAt Y c ℓ)
    (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D DY : Blk sp.n FGP} {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Relayed tr H U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard := by
  have held := fun {u} (hu : u ∈ Relayed tr H U X s D) =>
    relayed_held hr hsync hY hc ht hrs hu
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

/-- Two historical locks are compatible even if their writers do not survive each other.
The shared honest validator in the optimistic case is chosen at the later write cut. -/
theorem fastLock_same_slot
    (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n)
    (hP : ∀ t, CommitteeP K (tr.upTo t) (H t))
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    {w x : Fin sp.n} {i₀ j : Nat} {B D : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)}
    (hw : w ∈ H (tr.time i₀)) (hfl : FastLockAt tr w i₀ s B CV)
    (hx : x ∈ H (tr.time j)) (hfl' : FastLockAt tr x j s D CV')
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U
      (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {d : Time} (hi₀ : OptimisticLockAt tr w i₀ s B CV → tr.time i₀ ≤ d)
    (hj : tr.time j ≤ d)
    (hf : 2 * (K.committee s ∩ (H d)ᶜ).ncard < sp.committeeSize) : Compatible U B D := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hf2 : 2 * (K.committee s ∩ (H d)ᶜ).ncard < (K.committee s).ncard := by
    rw [hsize s]; exact hf
  have hW : ∀ z c, z ∈ H (tr.time c) →
      voters {v | v ∈ (tr.state z c).pool s} ⊆ K.committee s := by
    rintro z c hz u ⟨v, hv, rfl⟩
    have hst : (tr.upTo (tr.time c)).state z c = tr.state z c :=
      Trace.upTo_state tr z fun _ hk => hr.time_mono hk.le
    exact (hP (tr.time c)).1 z hz c s v (by rw [hst]; exact hv)
  have hO : ∀ z c ℓ A, z ∈ H (tr.time c) → OptimisticPoint tr z c ℓ A →
      ∀ D', optimisticVoters sp A ℓ.frame s D' ⊆ K.committee s := by
    rintro z c ℓ A hz hpt D' u ⟨v, hv, rfl, -⟩
    exact (hP (tr.time c)).2 z hz c ℓ A ((upTo_optimisticPoint hr.time_mono).mpr ⟨le_rfl, hpt⟩)
      s v hv
  by_contra hnc
  rcases hfl with hw' | hw' <;> rcases hfl' with hx' | hx'
  · obtain ⟨ℓ, S, hc, ht, hrs, _, hmaj, _, hS⟩ := update_side hrun hw hw'
    obtain ⟨_, S', _, _, _, hn', _, hS'F, _⟩ := update_side hrun hx hx'
    have := against_update hr hsync hw hc ht hrs hS hS'F fun h => hnc h.symm
    exact not_update_update (K.committee s) (hsize s) (hW w i₀ hw) hn' hmaj this
  · obtain ⟨ℓ, S, hc, ht, hrs, hn, _, _, hS⟩ := update_side hrun hw hw'
    obtain ⟨_, _, _, _, h34, hT⟩ := optimistic_seats hrun hx hx'
    have := against_update hr hsync hw hc ht hrs hS hT fun h => hnc h.symm
    exact not_update_optimistic (K.committee s) (hsize s) (hW w i₀ hw) hf2 hn h34 this
  · obtain ⟨ℓ, S, hc, ht, hrs, hn, _, _, hS⟩ := update_side hrun hx hx'
    obtain ⟨_, _, _, _, h34, hT⟩ := optimistic_seats hrun hw hw'
    have := against_update hr hsync hx hc ht hrs hS hT hnc
    exact not_update_optimistic (K.committee s) (hsize s) (hW x j hx) hf2 hn h34 this
  · have hi₀ := hi₀ hw'
    obtain ⟨ℓ, A, hpt, hΦU, h34, _⟩ := optimistic_seats hrun hw hw'
    obtain ⟨ℓ', A', hpt', hΦU', h34', _⟩ := optimistic_seats hrun hx hx'
    obtain ⟨u, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, v', hv', hv'u, R', hR', hR'r, hDR'⟩, huH⟩ :=
      quorums_meet (K.committee s) (hsize s) (hO w i₀ ℓ A hw hpt B) (hO x j ℓ' A' hx hpt' D)
        h34 h34' hf2
    have huH := not_not.1 huH
    have hrw := hrun.upTo (hr.time_nonneg i₀)
    have hrx := hrun.upTo (hr.time_nonneg j)
    obtain ⟨hvs, k₁, _, e₁, he₁, rfl⟩ := optimisticPoint_pool_vote hrw hw
      ((upTo_optimisticPoint hr.time_mono).mpr ⟨le_rfl, hpt⟩) hv (hr.antitone hi₀ huH)
    obtain ⟨hvs', k₂, _, e₂, he₂, rfl⟩ := optimisticPoint_pool_vote hrx hx
      ((upTo_optimisticPoint hr.time_mono).mpr ⟨le_rfl, hpt'⟩) hv' (hv'u ▸ hr.antitone hj huH)
    obtain ⟨ht₁, he₁⟩ := upTo_voteAt.mp he₁
    obtain ⟨ht₂, he₂⟩ := upTo_voteAt.mp he₂
    have hrd := hrun.upTo ((hr.time_nonneg i₀).trans hi₀)
    have he₁' := upTo_voteAt.mpr ⟨ht₁.trans hi₀, he₁⟩
    have he₂' := upTo_voteAt.mpr ⟨ht₂.trans hj, he₂⟩
    rw [hv'u] at he₂'
    obtain ⟨_, rfl⟩ := SA.one_vote_per_slot sp FGP ro (H d) U (tr.upTo d)
      hrd.localRun _ huH k₁ k₂ e₁ e₂ he₁' he₂' (hvs.trans hvs'.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hnc (anc_total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hDR'))

end Consensus.Goldilocks.SA.Growing

end
