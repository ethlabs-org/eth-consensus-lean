module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: forwarding sides of same-slot compatibility

Early votes from an optimistic origin reach an honest update under synchrony. Validators of
forwarded votes for a conflicting block are voters there, disjoint from its supporters.
These facts are shared by fast-lock compatibility and Healing's result compatibility. -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- `u` has a slot-`s` vote whose head extends `D` inside `U`, which `X` sent or admitted at a
time in `[t_s, t_s + 2Δ)`. -/
def Fwd (tr : SATrace sp FGP ro) (U : Set (Blk sp.n FGP)) (X : Fin sp.n) (s : Nat)
    (D : Blk sp.n FGP) : Set (Fin sp.n) :=
  {u | ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ}

theorem fwd_iff {X : Fin sp.n} {s : Nat} {D : Blk sp.n FGP} {u : Fin sp.n} :
    u ∈ Fwd tr U X s D ↔
      ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
        ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ :=
  Iff.rfl

theorem ts_add (s : Nat) (a : Time) :
    sp.ts (s + 1 : Nat) + a = sp.ts s + 4 * sp.Δ + a := by
  simp only [SAParams.ts]; push_cast; ring

/-- The slot of a time in `[t_s, t_s + 4Δ)` is `s`. -/
theorem CompatibleSides.slot_of_lt {s : Nat} {t : Time}
    (h₁ : sp.ts s ≤ t) (h₂ : t < sp.ts s + 4 * sp.Δ) :
    sp.slot t = s :=
  slot_of_mem sp s h₁ (by rw [← add_zero (sp.ts (s + 1 : Nat)), ts_add]; linarith)

/-- `admitted_of_held` with the unlock given. -/
theorem admitted_of_heldU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {X : Fin sp.n}
    (hX : X ∈ H) {c s : Nat} {v : Vote sp.n} (hvs : v.slot = s) (hv : v ∈ (tr.state X c).pool s)
    {T : Time} (hT : T ≤ sp.ts s + 2 * sp.Δ)
    (hlt : ∀ k < c, (tr.state X c).voteStamp v = ETime.of (tr.time k) → tr.time k < T) :
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < T := by
  have hΔ := sp.toParams.hΔ
  rcases pool_originU hr hX c v (hvs ▸ hv) with ⟨k, hk, hsend, hst, hsl⟩ |
    ⟨k, hk, ℓ, hck, -, hst, B, hB, hvB⟩
  · refine ⟨k, hsend, ?_, hlt k hk hst⟩
    exact ((ts_le_iff_le_slot sp (hr.time_nonneg k)) _).2 (by rw [← hvs]; exact_mod_cast hsl)
  · exfalso
    have h1 := (frame_validPayloadU sp hr hX hck B hB).1 v hvB
    have h2 := frame_slot_leU sp hr hX hck B hB
    have h3 := hlt k hk hst
    have h4 : sp.slot (tr.time k) ≤ s := by
      by_contra h
      have := ((ts_le_iff_le_slot sp (hr.time_nonneg k)) (s + 1 : Nat)).2 (by push_cast; omega)
      rw [← add_zero (sp.ts (s + 1 : Nat)), ts_add] at this
      linarith
    omega

/-- A vote that an honest node holds before cut `c`, of slot `s`, admitted before a time of slot
`s`, was admitted by the node at a time in `[t_s, T)` (a restart puts in the pools only votes of
frame blocks, whose slots are at most the restart's). -/
theorem admitted_of_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {X : Fin sp.n}
    (hX : X ∈ H) {c s : Nat} {v : Vote sp.n} (hvs : v.slot = s) (hv : v ∈ (tr.state X c).pool s)
    {T : Time} (hT : T ≤ sp.ts s + 2 * sp.Δ)
    (hlt : ∀ k < c, (tr.state X c).voteStamp v = ETime.of (tr.time k) → tr.time k < T) :
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < T :=
  admitted_of_heldU (hr := hr.toU) (X := X) (hX := hX) (c := c) (s := s) (v := v) (hvs := hvs)
      (hv := hv) (T := T) (hT := hT) (hlt := hlt)

/-- `optimistic_side` with the unlock given. -/
theorem optimistic_sideU
    {uL : Nat → Set Lock} (hrun : ACRunU wm uL proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {k s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : OptimisticLockAt tr X k s D CV) :
    ∃ ℓ A, OptimisticPoint tr X k ℓ A ∧ ℓ.frame.tree ⊆ U ∧
      3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A ℓ.frame s D).ncard ∧
      optimisticVoters sp A ℓ.frame s D ⊆ Fwd tr U X s D := by
  have hr := hrun.localRun
  obtain ⟨ℓ, A, hpt, hsl, hsel, -⟩ := hfl
  obtain ⟨-, hΦU⟩ := frameIn_of_callU hr hX hpt.1
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel with hcond
  have h34 := (deepest_mem hsel).1.2.1
  rw [hsl] at h34 hcond
  refine ⟨ℓ, A, hpt, hΦU, h34, ?_⟩
  rintro u ⟨v, hv, rfl, R, hR, hRr, hDR⟩
  have hvs := optimisticPoint_pool_slotU hr hX hpt hv
  have htk : tr.time k < sp.ts s + 2 * sp.Δ := by
    exact not_le.1 (not_or.1 (not_or.1 hcond).2).2
  rw [fwd_iff]
  refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, ?_⟩
  exact admitted_of_heldU hr hX hvs (optimisticPoint_pool_postU hr hX hpt s hv) le_rfl
    fun k' hk' _ => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk')) htk

/-- **The optimistic side.** At an honest optimistic confirmation of slot `s` on `D`, three
quarters of the committee are optimistic voters of `D`, each with a vote extending `D` that the
node admitted (or cast) in `[t_s, t_s + 2Δ)`. -/
theorem optimistic_side (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {k s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : OptimisticLockAt tr X k s D CV) :
    ∃ ℓ A, OptimisticPoint tr X k ℓ A ∧ ℓ.frame.tree ⊆ U ∧
      3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A ℓ.frame s D).ncard ∧
      optimisticVoters sp A ℓ.frame s D ⊆ Fwd tr U X s D :=
  optimistic_sideU (hrun := hrun.toU) (X := X) (hX := hX) (k := k) (s := s) (D := D) (CV := CV)
      (hfl := hfl)

/-- `fwd_held` with the unlock given. -/
theorem fwd_heldU
    {uL : Nat → Set Lock} (hr : ACLocalRunU wm uL H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D : Blk sp.n FGP} {u : Fin sp.n}
    (hu : u ∈ Fwd tr U X s D) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  rw [fwd_iff] at hu
  obtain ⟨v, rfl, hvs, hR, k, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have := sync_forwardU hr hsync hX hsend h1 (by rw [ts_add]; linarith) hY hc
    (fun k' hk' hr' => (hrs k' hk' hr').trans h1) (by rw [ht]; linarith)
    fun t ht₁ ht₂ => by
      rw [CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]; omega
  rwa [hvs] at this

/-- A vote of `Fwd` reaches an honest node's update of slot `s` (its restarts at or before
`t_s`) under `Sync`: the node holds it, or two other votes of its validator. -/
theorem fwd_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D : Blk sp.n FGP} {u : Fin sp.n}
    (hu : u ∈ Fwd tr U X s D) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) :=
  fwd_heldU (hr := hr.toU) (s := s) (hsync := hsync) (X := X) (Y := Y) (hX := hX) (hY := hY)
      (c := c) (ℓ := ℓ) (hc := hc) (ht := ht) (hrs := hrs) (D := D) (u := u) (hu := hu)

/-- `against_update` with the unlock given. -/
theorem against_updateU
    {uL : Nat → Set Lock} (hr : ACLocalRunU wm uL H U tr) {s : Nat}
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
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := fwd_heldU hr hsync hX hY hc ht hrs (hT hu)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hnc (anc_total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, -, hv | ⟨a, ha, -, -, -, hav, -⟩⟩ := fwd_heldU hr hsync hX hY hc ht hrs (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨-, v, hv, rfl, -⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

/-- **Against an update.** At an honest update of slot `s` on `DY`, the validators `T` with
forwardable votes for a block `D` that conflicts with `DY` are voters there and none is a
supporter `S` of `DY`. -/
theorem against_update (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D DY : Blk sp.n FGP}
    {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Fwd tr U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard :=
  against_updateU (hr := hr.toU) (s := s) (hsync := hsync) (X := X) (Y := Y) (hX := hX) (hY := hY)
      (c := c) (ℓ := ℓ) (hc := hc) (ht := ht) (hrs := hrs) (D := D) (DY := DY) (S := S) (T := T)
          (hS := hS) (hT := hT) (hnc := hnc)

end Consensus.Goldilocks.SA

end
