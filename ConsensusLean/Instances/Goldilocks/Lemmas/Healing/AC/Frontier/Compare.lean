module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CompatibleSides
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The pre-`b` frontier over AC traces: comparing origins (`P_s` to `P_{s+1}`)

The AC content of `Compose/Sleepy/Compare`'s finite-deadline origin step, over an AC trace with
the unlock given at a write mode. No step reads the locks, so the unlock oracle is free:

* the honest validators awake and joined at `t_s + Δ` are voters of an honest update of slot `s`
  within `b` (`awake_participantAC`): the tick duty makes them vote by `t_s + Δ`, and the service
  before `b` delivers the votes to the updater, whose restarts are at or before `t_s`;
* an origin within `b` has an honest supporter (`honest_supporterAC`): an honest slot-`s` vote at
  a time `≤ b` extending it;
* two origins of one label within `b` are compatible (`same_label_compatibleAC`): the counted
  votes of a result and the optimistic seats reach the other writer before `t_s + 3Δ ≤ b`
  (`fwd_held_service`, `against_update_service`), and two optimistic selections share an honest
  seat;
* `origins_below_succAC`: `P_s` and `V_s` give `P_{s+1}`. -/

namespace Consensus.Goldilocks.SA


variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {b : Time}

/-- **The awake joined validators participate in a result within `b`**: their slot-`s` votes,
cast by `t_s + Δ`, reach the updater (restarted at or before `t_s`) before `t_s + 2Δ ≤ b`. -/
theorem awake_participantAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H)
    (hsv : ServiceWindowBefore H U 0 b tr) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr X i₀ s ℓX) (hib : tr.time i₀ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) (hw : tr.awake y (sp.ts s + sp.Δ))
    (hj : JoinedAt tr y (sp.ts s + sp.Δ)) :
    y ∈ voters {v | v ∈ (tr.state X i₀).pool s} := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joinedAC hr htick hy hw hj
  obtain ⟨hval, hsl', -, -⟩ := castAt_specU hr hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.time k :=
    (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have := sync_window_before_forwardU hr hsv hy ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩
    (hr.time_nonneg k) (by linarith) hX hu.1
    (fun k' hk' hr' => (update_restartsAC hr hX hu k' hk' hr').trans hsk) (by linarith)
    fun t h₁ h₂ => by
      have : sp.slot t = s := slot_of_mem sp s (hsk.trans h₁) (by rw [ts_succ]; linarith)
      omega
  rw [hes] at this
  rcases this with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact ⟨e.msg, h, hval⟩
  · exact ⟨a, ha, hav.trans hval⟩

/-- **A result's side.** At an honest update of slot `s` with result `D`: the node's restarts were
at or before `t_s`; its counted validators `S` are more than half of its voters; each has a vote
in its pool, extending `D`, and does not equivocate there, and that vote was admitted in
`[t_s, t_s + 2Δ)` (so `S ⊆ Fwd`). -/
theorem result_sideAC (hrun : ACRunU wm u proposer tr H U) {Y : Fin sp.n} (hY : Y ∈ H)
    {c s : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksSA sp FGP ro)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Fwd tr U Y s D ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U D R := by
  have hr := hrun.localRun
  have hmaj := result_majority hR
  obtain ⟨ℓ, hu, -, rfl⟩ := hR
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hY hu.1
  refine ⟨ℓ, _, hu.1, hu.2.2.1, update_restartsAC hr hY hu, hmaj, ?_, ?_⟩
  · rintro w ⟨v, ⟨hvp, -, hres, R, hR, hRr, hDR⟩, rfl⟩
    have hvs := state_pool_slotU sp hr hY c s v hvp
    refine fwd_iff.2 ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩,
      admitted_of_heldU hr hY hvs hvp le_rfl
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
  · rintro w ⟨v, ⟨hvp, hne, -, R, hR, hRr, hDR⟩, rfl⟩
    exact ⟨hne, v, hvp, rfl, R, hΦU hR, hRr, Anc.mono hΦU hDR⟩

/-- **A vote of `Fwd` reaches an honest update of slot `s`** whose restarts are at or before
`t_s`, under the service before `b ≥ t_s + 3Δ`: the update holds it, or two other votes of its
validator. -/
theorem fwd_held_service (hr : ACLocalRunU wm u H U tr) (hsv : ServiceWindowBefore H U 0 b tr)
    {s : Nat} (hb : sp.ts s + 3 * sp.Δ ≤ b) {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt Y c ℓ)
    (ht : tr.time c = sp.ts s + 6 * sp.Δ) (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s)
    {D : Blk sp.n FGP} {w : Fin sp.n} (hu : w ∈ Fwd tr U X s D) :
    ∃ v : Vote sp.n, v.val = w ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ w ∈ equivocators {w' | w' ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  rw [fwd_iff] at hu
  obtain ⟨v, rfl, hvs, hR, k, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have := sync_window_before_forwardU hr hsv hX hsend (hr.time_nonneg k) (by linarith) hY hc
    (fun k' hk' hr' => (hrs k' hk' hr').trans h1) (by rw [ht]; linarith)
    fun t ht₁ ht₂ => by
      rw [CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁) (by linarith), hvs]; omega
  rwa [hvs] at this

/-- **Against an update**, under the service before `b ≥ t_s + 3Δ`: at an honest update of slot
`s` whose validators `S` support `DY` without equivocating, the validators `T` with forwarded
votes for a block `D` that conflicts with `DY` are voters there, and none is in `S`. -/
theorem against_update_service (hr : ACLocalRunU wm u H U tr)
    (hsv : ServiceWindowBefore H U 0 b tr) {s : Nat} (hb : sp.ts s + 3 * sp.Δ ≤ b)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D DY : Blk sp.n FGP}
    {S T : Set (Fin sp.n)}
    (hS : ∀ w ∈ S, w ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = w ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Fwd tr U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard := by
  have hU := hr.coherent
  have held := fun {w} (h : w ∈ Fwd tr U X s D) =>
    fwd_held_service hr hsv hb hX hY hc ht hrs h
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro w hw hw'
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS w hw'
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := held (hT hw)
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hnc (anc_total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro w (hw | hw)
  · obtain ⟨v, rfl, -, hv | ⟨a, ha, -, -, -, hav, -⟩⟩ := held (hT hw)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨-, v, hv, rfl, -⟩ := hS w hw
    exact ⟨v, hv, rfl⟩

private theorem ncard_le_n (T : Set (Fin sp.n)) : T.ncard ≤ sp.n :=
  (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])

/-- **An origin within `b` has an honest supporter**: an honest slot-`s` vote at a time `≤ b`
whose head extends it. A result's counted validators include an honest one, since the more than
`f` honest validators awake and joined at `t_s + Δ ≤ b` are voters of the update; an optimistic
selection has `3n/4 > f` seats. -/
theorem honest_supporterAC
    (hrun : ACRunU wm u proposer tr H U) (htick : TickDuty tr H)
    (hsv : ServiceWindowBefore H U 0 b tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hJ : ∀ s : Nat, sp.ts s + sp.Δ ≤ b → FaultBound tr H (sp.ts s + sp.Δ))
    {C : Blk sp.n FGP} {s : Nat} (hC : OriginWithinAC tr H C s b) :
    ∃ x ∈ H, ∃ j e, VoteAt tr x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧ VoteExtends U e.msg C := by
  have hr := hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨X, hX, i₀, CV, hi₀, hR | hO⟩ := originWithinAC_iff.1 hC
  · have hmaj := result_majority hR
    obtain ⟨ℓX, hu, -, hCV⟩ := hR
    have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hJs := hJ s (by linarith)
    change Hᶜ.ncard <
      {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ JoinedAt tr y (sp.ts s + sp.Δ)}.ncard at hJs
    have hJV : {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ JoinedAt tr y (sp.ts s + sp.Δ)} ⊆
        voters {v | v ∈ (tr.state X i₀).pool s} := fun y hy =>
      awake_participantAC hr htick hsv hX hu hi₀ hy.1 hy.2.1 hy.2.2
    have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ voters {v | v ∈ (tr.state X i₀).pool s} := by
      rintro w ⟨v, hv, rfl⟩
      rw [hCV] at hv
      exact ⟨v, hv.1, rfl⟩
    obtain ⟨w, ⟨v, hv, rfl⟩, hwH⟩ : ∃ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∈ H := by
      by_contra hno'
      have hno : ∀ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∉ H := fun w hw hwH => hno' ⟨w, hw, hwH⟩
      have hdisj : Disjoint
          {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ JoinedAt tr y (sp.ts s + sp.Δ)}
          {w | ∃ v ∈ CV, v.val = w} :=
        Set.disjoint_left.2 fun y hyJ hyS => hno y hyS hyJ.1
      have h1 := Set.ncard_union_eq hdisj
      have h2 := Set.ncard_le_ncard (Set.union_subset hJV hSV)
      have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Hᶜ.ncard :=
        Set.ncard_le_ncard fun y hy => hno y hy
      omega
    rw [hCV] at hv
    obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
    obtain ⟨j, hj, e, hve, rfl⟩ := hrun.honest.pool_vote X hX i₀ s _ hvp hwH
    obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hX hu.1
    exact ⟨_, hwH, j, e, hve, (hr.time_mono hj.le).trans hi₀,
      state_pool_slotU sp hr hX i₀ s _ hvp, R, hΦU hR, hRr, Anc.mono hΦU hCR⟩
  · obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := optimistic_sideU hrun hX hO
    rw [hrun.stock] at h34
    obtain ⟨w, ⟨v, hv, rfl, R, hR, hRr, hCR⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := optimisticVoters sp A ℓ.frame s C) (by omega)
    have huH : v.val ∈ H := not_not.1 huH
    obtain ⟨hvs, j, hj, e, hve, rfl⟩ := optimisticPoint_pool_voteU hrun hX hpt hv huH
    exact ⟨_, huH, j, e, hve, (hr.time_mono hj).trans hi₀, hvs, R, hΦU hR, hRr,
      Anc.mono hΦU hCR⟩

/-- A result within `b` and an optimistic selection of one label are compatible (RO): the
`≥ 3n/4` optimistic seats reach the result's writer before `t_s + 3Δ ≤ b`, where none supports a
conflicting result without equivocating. -/
theorem result_optimistic_compatibleAC
    (hrun : ACRunU wm u proposer tr H U)
    (hsv : ServiceWindowBefore H U 0 b tr) {s : Nat} {X x : Fin sp.n} (hX : X ∈ H) (hx : x ∈ H)
    {i i' : Nat} {C C' : Blk sp.n FGP} {CV CV' : Set (Vote sp.n)} (hi : tr.time i ≤ b)
    (hR : ResultAt tr X i s C CV) (hO : OptimisticLockAt tr x i' s C' CV') :
    Compatible U C C' := by
  by_contra hnc'
  obtain ⟨ℓ, S, hc, ht, hrs, hmaj, -, hS⟩ := result_sideAC hrun hX hR
  obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := optimistic_sideU hrun hx hO
  rw [hrun.stock] at h34
  have hb : sp.ts s + 3 * sp.Δ ≤ b := by
    have := sp.toParams.hΔ; rw [ht] at hi; linarith
  have := against_update_service hrun.localRun hsv hb hx hX hc ht hrs hS hT
    fun h => hnc' (Or.symm h)
  have := ncard_le_n (sp := sp) (voters {v | v ∈ (tr.state X i).pool s})
  omega

/-- **Origins within `b` of one label are compatible** (RR, RO, OO). -/
theorem same_label_compatibleAC
    (hrun : ACRunU wm u proposer tr H U)
    (hsv : ServiceWindowBefore H U 0 b tr) (hf : 2 * Hᶜ.ncard < sp.n)
    {C C' : Blk sp.n FGP} {s : Nat} (hC : OriginWithinAC tr H C s b)
    (hC' : OriginWithinAC tr H C' s b) : Compatible U C C' := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨X, hX, i, CV, hi, hR | hO⟩ := originWithinAC_iff.1 hC <;>
    obtain ⟨X', hX', i', CV', hi', hR' | hO'⟩ := originWithinAC_iff.1 hC'
  · by_contra hnc'
    obtain ⟨ℓ, S, hc, ht, hrs, hmaj, hSF, hS⟩ := result_sideAC hrun hX hR
    obtain ⟨ℓ', S', hc', ht', hrs', hmaj', hSF', hS'⟩ := result_sideAC hrun hX' hR'
    have hb : sp.ts s + 3 * sp.Δ ≤ b := by rw [ht] at hi; linarith
    have h1 := against_update_service hr hsv hb hX' hX hc ht hrs hS hSF'
      fun h => hnc' (Or.symm h)
    have h2 := against_update_service hr hsv hb hX hX' hc' ht' hrs' hS' hSF hnc'
    omega
  · exact result_optimistic_compatibleAC hrun hsv hX hX' hi hR hO'
  · exact Or.symm (result_optimistic_compatibleAC hrun hsv hX' hX hi' hR' hO)
  · by_contra hnc'
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := optimistic_sideU hrun hX hO
    obtain ⟨ℓ', A', hpt', hΦU', h34', -⟩ := optimistic_sideU hrun hX' hO'
    rw [hrun.stock] at h34 h34'
    have hI := Set.ncard_inter_add_ncard_union (optimisticVoters sp A ℓ.frame s C)
      (optimisticVoters sp A' ℓ'.frame s C')
    have := ncard_le_n (sp := sp)
      (optimisticVoters sp A ℓ.frame s C ∪ optimisticVoters sp A' ℓ'.frame s C')
    obtain ⟨w, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, ⟨v', hv', hv'u, R', hR', hR'r, hBR'⟩⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := optimisticVoters sp A ℓ.frame s C ∩ optimisticVoters sp A' ℓ'.frame s C')
        (by omega)
    have huH := not_not.1 huH
    obtain ⟨hvs, j₁, -, e₁, he₁, rfl⟩ := optimisticPoint_pool_voteU hrun hX hpt hv huH
    obtain ⟨hv's, j₂, -, e₂, he₂, rfl⟩ :=
      optimisticPoint_pool_voteU hrun hX' hpt' hv' (hv'u ▸ huH)
    rw [hv'u] at he₂
    obtain ⟨-, rfl⟩ := one_vote_per_slotU sp FGP ro H U tr hr _ huH j₁ j₂ e₁ e₂ he₁ he₂
      (hvs.trans hv's.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hnc' (anc_total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hBR'))

/-- Two blocks below the head of one vote are compatible. -/
private theorem compatible_of_voteExtendsAC (hU : Coherent U) {v : Vote sp.n} {C C' : Blk sp.n FGP}
    (h : VoteExtends U v C) (h' : VoteExtends U v C') : Compatible U C C' := by
  obtain ⟨Hd, hHd, hHdr, hC⟩ := h
  obtain ⟨Hd', hHd', hHd'r, hC'⟩ := h'
  obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
  exact Anc.total hU hC hC'

/-- **Extending the origin frontier up to `b`**: `P_s` and `V_s` give `P_{s+1}`. -/
theorem origins_below_succAC
    (hrun : ACRunU wm u proposer tr H U) (htick : TickDuty tr H)
    (hsv : ServiceWindowBefore H U 0 b tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hJ : ∀ s : Nat, sp.ts s + sp.Δ ≤ b → FaultBound tr H (sp.ts s + sp.Δ)) {s : Nat}
    (hP : OriginsBelowAC tr H U s b) (hV : VotesBelowAC tr H U s b) :
    OriginsBelowAC tr H U (s + 1) b := by
  have hU := hrun.localRun.coherent
  have hnew : ∀ C C' j, j < s → OriginWithinAC tr H C s b → OriginWithinAC tr H C' j b →
      Compatible U C C' := by
    intro C C' j hj hC hC'
    obtain ⟨x, hx, i, e, hv, hib, hs, hext⟩ := honest_supporterAC hrun htick hsv hf hJ hC
    exact compatible_of_voteExtendsAC hU hext
      (votesBelowAC_iff.1 hV C' j hC' x hx i e hv hib (by omega) (by omega))
  refine originsBelowAC_iff.2 fun C j C' j' hj hj' hC hC' => ?_
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact originsBelowAC_iff.1 hP C j C' j' hj hj' hC hC'
  · exact Or.symm (hnew C' C j hj hC' hC)
  · exact hnew C C' j' hj' hC hC'
  · exact same_label_compatibleAC hrun hsv hf hC hC'

end Consensus.Goldilocks.SA

end
