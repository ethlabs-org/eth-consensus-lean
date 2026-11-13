module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: two fast locks of one slot are compatible (A1.9, source slot `s`)

Two honest fast locks of slot `s` (by the fast test of an update at `t_s + 6Δ`, or by an
optimistic confirmation before `t_s + 2Δ`) are on compatible blocks, under
`Sync[t_s, t_{s+1} + Δ]` and `f < n/2`:
* two optimistic origins have three quarters of the committee each, so an honest validator in
  common, whose one slot-`s` vote (A0.8) extends both blocks;
* otherwise the votes of one origin (its early supporters, or its optimistic voters), admitted
  before `t_s + 2Δ`, reach the updating node before its update (`sync_forward`): each of their
  validators is a voter there, and none supports a conflicting block without equivocating; the
  counts (three quarters and a half, or the update result's strict majority) then exceed the
  committee. -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

theorem rt_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

/-- `update_side` with the unlock given. -/
private theorem update_sideU
    {uL : Nat → Set Lock} (hrun : ACRunU wm uL proposer tr H U) {Y : Fin sp.n} (hY : Y ∈ H)
    {c s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastUpdateAt tr Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksSA sp FGP ro)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      sp.n ≤ 2 * S.ncard ∧ (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Fwd tr U Y s D ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U D R := by
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨ℓ, C, ⟨hc, hcall, ht, hj⟩, hC, hD, -⟩ := hfl
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callU hr hY hc
  refine ⟨ℓ, supporters ℓ.frame ⟨{v | v ∈ (tr.state Y c).pool s}, {v | v ∈ (tr.state Y c).pool s ∧
    resolutionTime (tr.state Y c) ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s D, hc, ht,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- joined at the update: the restarts were at or before `t_s`
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hY)
    rw [hc.1, hcall] at he
    have hpost : joined sp (tr.post c) (tr.time c) := by
      have : tr.post c = (acOnTickWithM sp wm Y (uL c) (tr.state Y c) ℓ.frame (tr.time c)).1 :=
        (congrArg Prod.fst he).symm
      unfold joined at hj ⊢
      rw [this, SA.onTick_restartTimeWith]
      exact hj
    have hsl : sp.slot (tr.time c) = s + 1 :=
      CompatibleSides.slot_of_lt (s := s + 1)
        (by rw [ht, ← add_zero (sp.ts (s + 1 : Nat)), ts_add]; linarith)
        (by rw [ht, ts_add]; linarith)
    intro k hk hrk
    have := ((joined_awakeU sp) FGP ro H U tr hr Y hY c ℓ hc hpost).2 k hk hrk
    rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this
  · have hfast := (deepest_mem hD).1.2.2
    unfold FastTest confirmationScore at hfast
    simpa only [hrun.stock] using hfast
  · have hmaj := (deepest_mem hC).1.2.2
    unfold confirmationScore at hmaj
    exact lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard
      ((supporters_antitone sp) FGP ℓ.frame _ s D C (deepest_mem hD).1.1.2.2)))
  · rintro u ⟨-, v, ⟨hvp, hres⟩, rfl, -, R, hR, hRr, hDR⟩
    have hvs := state_pool_slotU sp hr hY c s v hvp
    rw [fwd_iff]
    refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, admitted_of_heldU hr hY hvs hvp le_rfl
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

/-- **The update side.** At an honest update of slot `s` whose fast test selects `D`: the
node's restarts were at or before `t_s`; its supporters `S` of `D` are at least half of the
committee and more than half of its voters; each has a vote in its pool, extending `D`, and
does not equivocate there, and that vote was admitted in `[t_s, t_s + 2Δ)`. -/
private theorem update_side
    (hrun : ACRun proposer tr H U) {Y : Fin sp.n} (hY : Y ∈ H) {c s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastUpdateAt tr Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksSA sp FGP ro)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      sp.n ≤ 2 * S.ncard ∧ (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Fwd tr U Y s D ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U D R :=
  update_sideU (hrun := hrun.toU) (Y := Y) (hY := hY) (c := c) (s := s) (D := D) (CV := CV)
      (hfl := hfl)

/-- `fastLock_same_slot` with the unlock given. -/
theorem fastLock_same_slotU
    {uL : Nat → Set Lock} (hrun : ACRunU wm uL proposer tr H U) {s : Nat} {w x : Fin sp.n}
    {i₀ j : Nat}
    {B B' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)} (hw : w ∈ H) (hfl : FastLockAt tr w i₀ s B CV)
    (hx : x ∈ H) (hfl' : FastLockAt tr x j s B' CV')
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    (hf : 2 * Hᶜ.ncard < sp.n) : Compatible U B B' := by
  have hstock := hrun.stock
  have hr := hrun.localRun
  have hU := hr.coherent
  have hpos : 0 < sp.n := Fin.pos w
  have hle : ∀ T : Set (Fin sp.n), T.ncard ≤ sp.n := fun T =>
    (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])
  by_contra hnc
  rcases hfl with hw' | hw' <;> rcases hfl' with hx' | hx'
  · -- two updates: `x`'s supporters reach `w`, against `w`'s result majority
    obtain ⟨ℓ, S, hc, ht, hrs, -, hmaj, -, hS⟩ := update_sideU hrun hw hw'
    obtain ⟨-, S', -, -, -, hn', -, hS'F, -⟩ := update_sideU hrun hx hx'
    have := against_updateU hr hsync hx hw hc ht hrs hS hS'F fun h => hnc h.symm
    have := hle (voters {v | v ∈ (tr.state w i₀).pool s})
    omega
  · -- `x`'s optimistic voters reach `w`'s update
    obtain ⟨ℓ, S, hc, ht, hrs, hn, -, -, hS⟩ := update_sideU hrun hw hw'
    obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := optimistic_sideU hrun hx hx'
    have := against_updateU hr hsync hx hw hc ht hrs hS hT fun h => hnc h.symm
    have := hle (voters {v | v ∈ (tr.state w i₀).pool s})
    omega
  · -- `w`'s optimistic voters reach `x`'s update
    obtain ⟨ℓ, S, hc, ht, hrs, hn, -, -, hS⟩ := update_sideU hrun hx hx'
    obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := optimistic_sideU hrun hw hw'
    have := against_updateU hr hsync hw hx hc ht hrs hS hT hnc
    have := hle (voters {v | v ∈ (tr.state x j).pool s})
    omega
  · -- two optimistic confirmations: an honest validator in common, with one slot-`s` vote
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := optimistic_sideU hrun hw hw'
    obtain ⟨ℓ', A', hpt', hΦU', h34', -⟩ := optimistic_sideU hrun hx hx'
    have hI := Set.ncard_inter_add_ncard_union (optimisticVoters sp A ℓ.frame s B)
      (optimisticVoters sp A' ℓ'.frame s B')
    have := hle (optimisticVoters sp A ℓ.frame s B ∪ optimisticVoters sp A' ℓ'.frame s B')
    obtain ⟨u, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, ⟨v', hv', hv'u, R', hR', hR'r, hBR'⟩⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := optimisticVoters sp A ℓ.frame s B ∩ optimisticVoters sp A' ℓ'.frame s B')
        (by omega)
    have huH := not_not.1 huH
    obtain ⟨hvs, j₁, -, e₁, he₁, rfl⟩ := optimisticPoint_pool_voteU hrun hw hpt hv huH
    obtain ⟨hv's, j₂, -, e₂, he₂, rfl⟩ :=
      optimisticPoint_pool_voteU hrun hx hpt' hv' (hv'u ▸ huH)
    rw [hv'u] at he₂
    obtain ⟨-, rfl⟩ := (one_vote_per_slotU sp) FGP ro H U tr hr _ huH j₁ j₂ e₁ e₂ he₁ he₂
      (hvs.trans hv's.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hnc (anc_total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hBR'))

/-- **Fast locks of one slot are compatible.** -/
theorem fastLock_same_slot
    (hrun : ACRun proposer tr H U) {s : Nat} {w x : Fin sp.n} {i₀ j : Nat}
    {B B' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)} (hw : w ∈ H) (hfl : FastLockAt tr w i₀ s B CV)
    (hx : x ∈ H) (hfl' : FastLockAt tr x j s B' CV')
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    (hf : 2 * Hᶜ.ncard < sp.n) : Compatible U B B' :=
  fastLock_same_slotU (hrun := hrun.toU) (s := s) (w := w) (x := x) (i₀ := i₀) (j := j) (B := B)
      (B' := B') (CV := CV) (CV' := CV') (hw := hw) (hfl := hfl) (hx := hx) (hfl' := hfl')
          (hsync := hsync) (hf := hf)

end Consensus.Goldilocks.SA

end
