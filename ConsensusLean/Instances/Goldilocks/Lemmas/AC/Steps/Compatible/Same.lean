module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock

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

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- `u` has a slot-`s` vote whose head extends `D` inside `U`, which `X` sent or admitted at a
time in `[t_s, t_s + 2Δ)`. -/
private def Fwd (tr : SATrace sp FGP ro) (U : Set (Blk sp.n FGP)) (X : Fin sp.n) (s : Nat)
    (D : Blk sp.n FGP) (u : Fin sp.n) : Prop :=
  ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ

private theorem frameIn_of_call (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

private theorem ts_add (s : Nat) (a : Time) :
    sp.ts (s + 1 : Nat) + a = sp.ts s + 4 * sp.Δ + a := by
  simp only [SAParams.ts]; push_cast; ring

/-- The slot of a time in `[t_s, t_s + 4Δ)` is `s`. -/
private theorem slot_of_lt {s : Nat} {t : Time} (h₁ : sp.ts s ≤ t) (h₂ : t < sp.ts s + 4 * sp.Δ) :
    sp.slot t = s :=
  slot_of_mem sp s h₁ (by rw [← add_zero (sp.ts (s + 1 : Nat)), ts_add]; linarith)

/-- A vote that an honest node holds before cut `c`, of slot `s`, admitted before a time of slot
`s`, was admitted by the node at a time in `[t_s, T)` (a restart puts in the pools only votes of
frame blocks, whose slots are at most the restart's). -/
private theorem admitted_of_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {X : Fin sp.n}
    (hX : X ∈ H) {c s : Nat} {v : Vote sp.n} (hvs : v.slot = s) (hv : v ∈ (tr.state X c).pool s)
    {T : Time} (hT : T ≤ sp.ts s + 2 * sp.Δ)
    (hlt : ∀ k < c, (tr.state X c).voteStamp v = ETime.of (tr.time k) → tr.time k < T) :
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < T := by
  have hΔ := sp.toParams.hΔ
  rcases pool_origin hr hX c v (hvs ▸ hv) with ⟨k, hk, hsend, hst, hsl⟩ |
    ⟨k, hk, ℓ, hck, -, hst, B, hB, hvB⟩
  · refine ⟨k, hsend, ?_, hlt k hk hst⟩
    exact ((ts_le_iff_le_slot sp (hr.time_nonneg k)) _).2 (by rw [← hvs]; exact_mod_cast hsl)
  · exfalso
    have h1 := (frame_validPayload sp hr hX hck B hB).1 v hvB
    have h2 := frame_slot_le sp hr hX hck B hB
    have h3 := hlt k hk hst
    have h4 : sp.slot (tr.time k) ≤ s := by
      by_contra h
      have := ((ts_le_iff_le_slot sp (hr.time_nonneg k)) (s + 1 : Nat)).2 (by push_cast; omega)
      rw [← add_zero (sp.ts (s + 1 : Nat)), ts_add] at this
      linarith
    omega

private theorem rt_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote; split_ifs <;> rfl

theorem rt_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

private theorem rt_tryVote (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (tryVote sp x A Φ t).1.restartTime = A.restartTime := by
  unfold tryVote; dsimp only
  split_ifs <;> simp only [rt_optimistic, rt_admitVote]

private theorem rt_update (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (updateConfirmation sp A Φ t s).restartTime = A.restartTime := by
  unfold updateConfirmation updateLatestConfirmed; dsimp only
  split
  · rfl
  · split_ifs <;> rfl

private theorem rt_onTick (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acOnTick sp x A Φ t).1.restartTime = A.restartTime := by
  unfold acOnTick; dsimp only
  split_ifs <;> simp only [rt_update, rt_tryVote]

/-- **The update side.** At an honest update of slot `s` whose fast test selects `D`: the
node's restarts were at or before `t_s`; its supporters `S` of `D` are at least half of the
committee and more than half of its voters; each has a vote in its pool, extending `D`, and
does not equivocate there, and that vote was admitted in `[t_s, t_s + 2Δ)`. -/
private theorem update_side (hrun : ACRun proposer tr H U) {Y : Fin sp.n} (hY : Y ∈ H) {c s : Nat}
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
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hr hY hc
  refine ⟨ℓ, supporters ℓ.frame ⟨{v | v ∈ (tr.state Y c).pool s}, {v | v ∈ (tr.state Y c).pool s ∧
    resolutionTime (tr.state Y c) ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s D, hc, ht,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- joined at the update: the restarts were at or before `t_s`
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hY)
    rw [hc.1, hcall] at he
    have hpost : joined sp (tr.post c) (tr.time c) := by
      have : tr.post c = (acOnTick sp Y (tr.state Y c) ℓ.frame (tr.time c)).1 :=
        (congrArg Prod.fst he).symm
      unfold joined at hj ⊢
      rw [this, rt_onTick]
      exact hj
    have hsl : sp.slot (tr.time c) = s + 1 :=
      slot_of_lt (s := s + 1) (by rw [ht, ← add_zero (sp.ts (s + 1 : Nat)), ts_add]; linarith)
        (by rw [ht, ts_add]; linarith)
    intro k hk hrk
    have := ((joined_awake sp) FGP ro H U tr hr Y hY c ℓ hc hpost).2 k hk hrk
    rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this
  · have hfast := (deepest_mem hD).1.2.2
    unfold FastTest confirmationScore at hfast
    exact hfast
  · have hmaj := (deepest_mem hC).1.2.2
    unfold confirmationScore at hmaj
    exact lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard
      ((supporters_antitone sp) FGP ℓ.frame _ s D C (deepest_mem hD).1.1.2.2)))
  · rintro u ⟨-, v, ⟨hvp, hres⟩, rfl, -, R, hR, hRr, hDR⟩
    have hvs := state_pool_slot sp hr hY c s v hvp
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

/-- **The optimistic side.** At an honest optimistic confirmation of slot `s` on `D`, three
quarters of the committee are optimistic voters of `D`, each with a vote extending `D` that the
node admitted (or cast) in `[t_s, t_s + 2Δ)`. -/
private theorem optimistic_side (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {k s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : OptimisticLockAt tr X k s D CV) :
    ∃ ℓ A, OptimisticPoint tr X k ℓ A ∧ ℓ.frame.tree ⊆ U ∧
      3 * sp.n ≤ 4 * (optimisticVoters sp A ℓ.frame s D).ncard ∧
      optimisticVoters sp A ℓ.frame s D ⊆ Fwd tr U X s D := by
  have hr := hrun.localRun
  obtain ⟨ℓ, A, hpt, hsl, hsel, -⟩ := hfl
  obtain ⟨-, hΦU⟩ := frameIn_of_call hr hX hpt.1
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel with hcond
  have h34 := (deepest_mem hsel).1.2.1
  rw [hsl] at h34 hcond
  refine ⟨ℓ, A, hpt, hΦU, h34, ?_⟩
  rintro u ⟨v, hv, rfl, R, hR, hRr, hDR⟩
  have hvs := optimisticPoint_pool_slot hr hX hpt hv
  have htk : tr.time k < sp.ts s + 2 * sp.Δ := by
    exact not_le.1 (not_or.1 (not_or.1 hcond).2).2
  refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, ?_⟩
  exact admitted_of_held hr hX hvs (optimisticPoint_pool_post hr hX hpt s hv) le_rfl
    fun k' hk' _ => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk')) htk

/-- A vote of `Fwd` reaches an honest node's update of slot `s` (its restarts at or before
`t_s`) under `Sync`: the node holds it, or two other votes of its validator. -/
private theorem fwd_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D : Blk sp.n FGP} {u : Fin sp.n}
    (hu : Fwd tr U X s D u) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have := sync_forward hr hsync hX hsend h1 (by rw [ts_add]; linarith) hY hc
    (fun k' hk' hr' => (hrs k' hk' hr').trans h1) (by rw [ht]; linarith)
    fun t ht₁ ht₂ => by rw [slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]; omega
  rwa [hvs] at this

/-- **Against an update.** At an honest update of slot `s` on `DY`, the validators `T` with
forwardable votes for a block `D` that conflicts with `DY` are voters there and none is a
supporter `S` of `DY`. -/
private theorem against_update (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D DY : Blk sp.n FGP}
    {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Fwd tr U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard := by
  have hU := hr.coherent
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro u hu hu'
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS u hu'
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := fwd_held hr hsync hX hY hc ht hrs (hT hu)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hnc (anc_total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, -, hv | ⟨a, ha, -, -, -, hav, -⟩⟩ := fwd_held hr hsync hX hY hc ht hrs (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨-, v, hv, rfl, -⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

/-- **Fast locks of one slot are compatible.** -/
theorem fastLock_same_slot (hrun : ACRun proposer tr H U) {s : Nat} {w x : Fin sp.n} {i₀ j : Nat}
    {B B' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)} (hw : w ∈ H) (hfl : FastLockAt tr w i₀ s B CV)
    (hx : x ∈ H) (hfl' : FastLockAt tr x j s B' CV')
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    (hf : 2 * Hᶜ.ncard < sp.n) : Compatible U B B' := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hpos : 0 < sp.n := Fin.pos w
  have hle : ∀ T : Set (Fin sp.n), T.ncard ≤ sp.n := fun T =>
    (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])
  by_contra hnc
  rcases hfl with hw' | hw' <;> rcases hfl' with hx' | hx'
  · -- two updates: `x`'s supporters reach `w`, against `w`'s result majority
    obtain ⟨ℓ, S, hc, ht, hrs, -, hmaj, -, hS⟩ := update_side hrun hw hw'
    obtain ⟨-, S', -, -, -, hn', -, hS'F, -⟩ := update_side hrun hx hx'
    have := against_update hr hsync hx hw hc ht hrs hS hS'F fun h => hnc h.symm
    have := hle (voters {v | v ∈ (tr.state w i₀).pool s})
    omega
  · -- `x`'s optimistic voters reach `w`'s update
    obtain ⟨ℓ, S, hc, ht, hrs, hn, -, -, hS⟩ := update_side hrun hw hw'
    obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := optimistic_side hrun hx hx'
    have := against_update hr hsync hx hw hc ht hrs hS hT fun h => hnc h.symm
    have := hle (voters {v | v ∈ (tr.state w i₀).pool s})
    omega
  · -- `w`'s optimistic voters reach `x`'s update
    obtain ⟨ℓ, S, hc, ht, hrs, hn, -, -, hS⟩ := update_side hrun hx hx'
    obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := optimistic_side hrun hw hw'
    have := against_update hr hsync hw hx hc ht hrs hS hT hnc
    have := hle (voters {v | v ∈ (tr.state x j).pool s})
    omega
  · -- two optimistic confirmations: an honest validator in common, with one slot-`s` vote
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := optimistic_side hrun hw hw'
    obtain ⟨ℓ', A', hpt', hΦU', h34', -⟩ := optimistic_side hrun hx hx'
    have hI := Set.ncard_inter_add_ncard_union (optimisticVoters sp A ℓ.frame s B)
      (optimisticVoters sp A' ℓ'.frame s B')
    have := hle (optimisticVoters sp A ℓ.frame s B ∪ optimisticVoters sp A' ℓ'.frame s B')
    obtain ⟨u, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, ⟨v', hv', hv'u, R', hR', hR'r, hBR'⟩⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := optimisticVoters sp A ℓ.frame s B ∩ optimisticVoters sp A' ℓ'.frame s B')
        (by omega)
    have huH := not_not.1 huH
    obtain ⟨hvs, j₁, -, e₁, he₁, rfl⟩ := optimisticPoint_pool_vote hrun hw hpt hv huH
    obtain ⟨hv's, j₂, -, e₂, he₂, rfl⟩ :=
      optimisticPoint_pool_vote hrun hx hpt' hv' (hv'u ▸ huH)
    rw [hv'u] at he₂
    obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr _ huH j₁ j₂ e₁ e₂ he₁ he₂
      (hvs.trans hv's.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hnc (anc_total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hBR'))

end Consensus.Goldilocks.SA

end
