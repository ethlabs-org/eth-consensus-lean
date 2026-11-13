module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: comparing origins (extending `P_s` to `P_{s+1}`)

* **An honest supporter** (`honest_supporter`): an origin of label `s` has an honest slot-`s`
  vote whose head extends it. For a result: the honest validators awake and joined at `t_s + Δ`
  (more than `f`, by `Sleepy`) vote in slot `s` and reach the joined writer before `t_s + 2Δ`, so
  they are among its participants; if every counted supporter were faulty, the participants would
  hold those seats and more than `f` disjoint honest ones, against the strict majority. For an
  optimistic selection: `3n/4 > f` voters.
* **Same-label origins compare** (`same_label_compatible`): two results by the disjointness
  of conflicting supporter sets and the relay of counted votes to both writers (RR); a result and
  an optimistic selection by the relay of the `≥ 3n/4` optimistic seats (RO); two selections share
  `n/2 > f` seats (OO).
* `origins_below_succ`: an origin of label `s` and one of label `j < s` are both below the head of
  the honest supporter's vote, which extends the older one by `V_s`. -/

/-! ## Over SA traces: `voted_slot`, and the relay of one slot's votes to a writer -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- At the tick at `t_s + Δ` of a joined node, `try_vote` runs: the node votes in slot `s`, or
`voted_slot = s` already. -/
private theorem acOnTick_votes (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) {t : Time}
    (hj : joined sp A t) (ht : t = sp.ts (sp.slot t) + sp.Δ)
    (hm : A.mayVote (sp.slot t) = true) :
    A.votedSlot = sp.slot t ∨ ∃ e ∈ (acOnTick sp self A Φ t).2, e.msg.slot = sp.slot t := by
  unfold acOnTick
  simp only [hj, not_true_eq_false, ↓reduceIte, ← ht]
  unfold tryVote
  simp only [hm, ↓reduceIte]
  split_ifs with h₁ h₂
  · rcases h₁ with h | h | h
    · exact absurd hj h
    · exact Or.inl h
    · exact absurd ht h.ne'
  · exact absurd ht h₂.1.ne
  all_goals exact Or.inr ⟨_, List.mem_singleton_self _, rfl⟩

private theorem add_mul_delta_le {x a b : Time} (h : a ≤ b) : x + a * sp.Δ ≤ x + b * sp.Δ :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_right h sp.toParams.hΔ.le)

private theorem add_mul_delta_lt {x a b : Time} (h : a < b) : x + a * sp.Δ < x + b * sp.Δ :=
  add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_right h sp.toParams.hΔ)

private theorem add_delta_add_delta (x : Time) : x + sp.Δ + sp.Δ = x + 2 * sp.Δ := by
  rw [add_assoc, ← two_mul]

private theorem add_mul_delta_add_delta (x a : Time) :
    x + a * sp.Δ + sp.Δ = x + (a + 1) * sp.Δ := by
  rw [add_assoc, add_one_mul]

/-- The restarts of an honest node up to its update of slot `s` (joined) are at or before
`t_s`. -/
private theorem update_restarts {ini} (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    {Y : Fin sp.n}
    (hY : Y ∈ H) {c s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr Y c s ℓ) :
    ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have he := hr.exec c ℓ hc.2 (hc.1 ▸ hY)
  rw [hc.1, hcall] at he
  have hpost : joined sp (tr.post c) (tr.time c) := by
    have : tr.post c = (acOnTick sp Y (tr.state Y c) ℓ.frame (tr.time c)).1 :=
      (congrArg Prod.fst he).symm
    unfold joined at hj ⊢
    rw [this, show (acOnTick sp Y (tr.state Y c) ℓ.frame (tr.time c)).1.restartTime =
      (tr.state Y c).restartTime from step_restartTime (ro := ro) Y _ _ _ .tick nofun]
    exact hj
  have hsl : sp.slot (tr.time c) = s + 1 :=
    CompatibleSides.slot_of_lt (s := s + 1)
      (by
        rw [ht, ← add_zero (sp.ts (s + 1 : Nat)), ts_add, add_zero]
        exact add_mul_delta_le (by norm_num))
      (by rw [ht, ts_add, add_assoc, ← add_mul]; exact add_mul_delta_lt (by norm_num))
  intro k hk hrk
  have := (joined_awakeU sp FGP ro H U tr hr.toU Y hY c ℓ hc hpost).2 k hk hrk
  rwa [hsl, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at this

/-- `u` has a slot-`s` vote whose head extends `D` inside `U`, which `X` sent or admitted at a
time in `[t_s, t_s + 2Δ)`. -/
private def Relayed (tr : SATrace sp FGP ro) (U : Set (Blk sp.n FGP)) (X : Fin sp.n) (s : Nat)
    (D : Blk sp.n FGP) (u : Fin sp.n) : Prop :=
  ∃ v : Vote sp.n, v.val = u ∧ v.slot = s ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
    ∃ k, tr.SendOrAdmit X k v ∧ sp.ts s ≤ tr.time k ∧ tr.time k < sp.ts s + 2 * sp.Δ

/-- **A result's side.** At an honest update of slot `s` with result `D`: the node's restarts were
at or before `t_s`; its counted validators `S` are more than half of its voters; each has a vote
in its pool, extending `D`, and does not equivocate there, and that vote was admitted in
`[t_s, t_s + 2Δ)`. -/
private theorem result_side (hrun : ACRun proposer tr H U) {Y : Fin sp.n} (hY : Y ∈ H) {c s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hR : ResultAt tr Y c s D CV) :
    ∃ (ℓ : ACLabel (goldilocksSA sp FGP ro)) (S : Set (Fin sp.n)),
      tr.CallAt Y c ℓ ∧ tr.time c = sp.ts s + 6 * sp.Δ ∧
      (∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) ∧
      (voters {v | v ∈ (tr.state Y c).pool s}).ncard < 2 * S.ncard ∧
      S ⊆ Relayed tr U Y s D ∧
      ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
        ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U D R := by
  have hr := hrun.localRun
  have hmaj := result_majority hR
  obtain ⟨ℓ, hu, -, rfl⟩ := hR
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hY hu.1
  refine ⟨ℓ, _, hu.1, hu.2.2.1, update_restarts hr hY hu, hmaj, ?_, ?_⟩
  · rintro u ⟨v, ⟨hvp, -, hres, R, hR, hRr, hDR⟩, rfl⟩
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
  · rintro u ⟨v, ⟨hvp, hne, -, R, hR, hRr, hDR⟩, rfl⟩
    exact ⟨hne, v, hvp, rfl, R, hΦU hR, hRr, Anc.mono hΦU hDR⟩

/-- **An optimistic selection's seats.** At an honest optimistic confirmation of slot `s` on `D`,
three quarters of the committee are optimistic voters of `D`, each with a vote extending `D` that
the node admitted (or cast) in `[t_s, t_s + 2Δ)`. -/
private theorem optimistic_seats
    (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} (hX : X ∈ H) {k s : Nat}
    {D : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : OptimisticLockAt tr X k s D CV) :
    ∃ ℓ A, OptimisticPoint tr X k ℓ A ∧ ℓ.frame.tree ⊆ U ∧
      3 * sp.n ≤ 4 * (optimisticVoters sp A ℓ.frame s D).ncard ∧
      optimisticVoters sp A ℓ.frame s D ⊆ Relayed tr U X s D := by
  have hr := hrun.localRun
  obtain ⟨ℓ, A, hpt, hsl, hsel, -⟩ := hfl
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hX hpt.1
  unfold optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel with hcond
  have h34 := (deepest_mem hsel).1.2.1
  rw [hsl] at h34 hcond
  rw [hrun.stock] at h34
  refine ⟨ℓ, A, hpt, hΦU, h34, ?_⟩
  rintro u ⟨v, hv, rfl, R, hR, hRr, hDR⟩
  have hvs := optimisticPoint_pool_slot hr hX hpt hv
  have htk : tr.time k < sp.ts s + 2 * sp.Δ := not_le.1 (not_or.1 (not_or.1 hcond).2).2
  refine ⟨v, rfl, hvs, ⟨R, hΦU hR, hRr, Anc.mono hΦU hDR⟩, ?_⟩
  exact admitted_of_held hr hX hvs (optimisticPoint_pool_post hr hX hpt s hv) le_rfl
    fun k' hk' _ => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk')) htk

/-- A `Relayed` vote reaches an honest node's update of slot `s` (its restarts at or before `t_s`)
under `Sync`: the node holds it, or two other votes of its validator. -/
private theorem relayed_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D : Blk sp.n FGP} {u : Fin sp.n}
    (hu : Relayed tr U X s D u) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have := sync_forward hr hsync hX hsend h1 (by
    rw [ts_add]
    exact h2.le.trans ((add_mul_delta_le (by norm_num)).trans (le_add_of_nonneg_right hΔ.le))) hY hc
    (fun k' hk' hr' => (hrs k' hk' hr').trans h1) (by
      rw [ht]
      exact (add_le_add h2.le le_rfl).trans
        (by rw [add_mul_delta_add_delta]; exact add_mul_delta_le (by norm_num)))
    fun t ht₁ ht₂ => by
      rw [CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁)
        (ht₂.trans ((add_lt_add_of_lt_of_le h2 le_rfl).trans_le
        (by rw [add_mul_delta_add_delta]; exact add_mul_delta_le (by norm_num)))), hvs]
      omega
  rwa [hvs] at this

/-- Relay delivery to an update uses recipient deadlines only through `t_s + 3Δ`,
not through the later update time. -/
private theorem relayed_held_before (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {s : Nat} {b : Time} (hsync : ServiceBefore H U b tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hb : sp.ts s + 3 * sp.Δ ≤ b)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D : Blk sp.n FGP} {u : Fin sp.n}
    (hu : Relayed tr U X s D u) :
    ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}) := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, rfl, hvs, hR, k, hsend, h1, h2⟩ := hu
  refine ⟨v, rfl, hR, ?_⟩
  have := sync_before_forward hr hsync hX hsend ((add_le_add h2.le le_rfl).trans
    (by rw [add_mul_delta_add_delta]; exact (add_mul_delta_le (by norm_num)).trans hb)) hY hc
    (fun k' hk' hr' => (hrs k' hk' hr').trans h1) (by
      rw [ht]
      exact (add_le_add h2.le le_rfl).trans
        (by rw [add_mul_delta_add_delta]; exact add_mul_delta_le (by norm_num)))
    fun t ht₁ ht₂ => by
      rw [CompatibleSides.slot_of_lt (s := s) (h1.trans ht₁)
        (ht₂.trans ((add_lt_add_of_lt_of_le h2 le_rfl).trans_le
        (by rw [add_mul_delta_add_delta]; exact add_mul_delta_le (by norm_num)))), hvs]
      omega
  rwa [hvs] at this

/-- **Against an update.** At an honest update of slot `s` whose validators `S` support `DY`
without equivocating, the validators `T` with relayed votes for a block `D` that conflicts with
`DY` are voters there, and none is in `S`. -/
private theorem relayed_against_of_held (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    {X Y : Fin sp.n} {c : Nat} {D DY : Blk sp.n FGP}
    (held : ∀ {u}, Relayed tr U X s D u →
      ∃ v : Vote sp.n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
        (v ∈ (tr.state Y c).pool s ∨ u ∈ equivocators {w | w ∈ (tr.state Y c).pool s}))
    {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Relayed tr U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard := by
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
  · obtain ⟨v, rfl, -, hv | ⟨a, ha, -, -, -, hav, -⟩⟩ :=
      held (hT hu)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, hav⟩
  · obtain ⟨-, v, hv, rfl, -⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

private theorem relayed_against (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {s : Nat}
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr)
    {X Y : Fin sp.n} (hX : X ∈ H) (hY : Y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt Y c ℓ) (ht : tr.time c = sp.ts s + 6 * sp.Δ)
    (hrs : ∀ k ≤ c, tr.RestartAt Y k → tr.time k ≤ sp.ts s) {D DY : Blk sp.n FGP}
    {S T : Set (Fin sp.n)}
    (hS : ∀ u ∈ S, u ∉ equivocators {v | v ∈ (tr.state Y c).pool s} ∧
      ∃ v ∈ (tr.state Y c).pool s, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : T ⊆ Relayed tr U X s D) (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters {v | v ∈ (tr.state Y c).pool s}).ncard :=
  relayed_against_of_held hr (relayed_held hr hsync hX hY hc ht hrs) hS hT hnc

end Consensus.Goldilocks.SA

/-! ## Over a Goldilocks run -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

private theorem ts_nonneg (s : Nat) : (0 : Time) ≤ sp.ts s := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  simp only [SAParams.ts]
  exact mul_nonneg (mul_nonneg (by norm_num) hΔ.le) (Int.natCast_nonneg s)

/-- Slot starts are monotone in the slot. -/
theorem ts_le_ts {s s' : Nat} (h : s ≤ s') : sp.ts s ≤ sp.ts s' :=
  (SA.ts_le_iff sp).2 (by exact_mod_cast h)

/-- Under `Sleepy`, `f < n/2`. -/
theorem two_faults_lt_of_sleepy (hsl : tr.SleepyRun H ΔF) : 2 * Hᶜ.ncard < sp.n := by
  have h := (hsl.2 0).1
  have hle : tr.honestAwakeJoined H (sp.toParams.slotTime 0) ≤ H.ncard :=
    Set.ncard_le_ncard fun x hx => hx.1
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold RunTrace.FaultBound at h
  omega

/-- Under `Sleepy`, more than `f` honest validators are awake and joined at `t_s + Δ`. -/
theorem faults_lt_awake_joined (hsl : tr.SleepyRun H ΔF) (s : Nat) :
    Hᶜ.ncard <
      {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}.ncard := by
  have h := (hsl.2 s).2.1
  have hT : sp.toParams.slotTime s + sp.toParams.Δ = sp.ts s + sp.Δ := by
    rw [sp.slotTime_eq]; simp only [SAParams.ts]
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined at h
  rwa [hT] at h

/-- Under `Sleepy`, `Sync` from any `a ≥ 0` holds of the AC projection. -/
theorem syncAC_of_sleepy (hrun : GoldilocksRun proposer dg H tr) (hsl : tr.SleepyRun H ΔF)
    {a b : Time} (ha : 0 ≤ a) :
    SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) a b tr.projAC :=
  sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr proposer ΔF a b
    hrun.toLocalRun (show tr.SyncOn H ΔF (fun τ => a ≤ τ ∧ τ ≤ b) (fun τ => a ≤ τ ∧ τ ≤ b) id from
      ⟨hsl.1.deltaF, hsl.1.delta_le,
        fun x hx i m hm hw => hsl.1.message x hx i m hm (ha.trans hw.1),
        fun x hx i B hB hw => hsl.1.block x hx i B hB (ha.trans hw.1),
        fun x hx i B hB hw => hsl.1.relay x hx i B hB (ha.trans hw.1),
        fun x hx i a' h hw => hsl.1.attestation x hx i a' h (ha.trans hw.1)⟩)

variable {b : Time} {s₀ : Nat}

/-- On the window from slot `s₀` to `b`, `f < n/2` (`f < h_{t_{s₀}}`). -/
theorem two_faults_lt_of_window (hwin : SleepyWindow tr H ΔF s₀ b) : 2 * Hᶜ.ncard < sp.n := by
  obtain ⟨hb, -, hfb⟩ := sleepyWindow_iff.1 hwin
  have h := hfb s₀ le_rfl 0 (by simp) (by simpa using hb)
  have hle : tr.honestAwakeJoined H (sp.ts s₀ + 0) ≤ H.ncard :=
    Set.ncard_le_ncard fun x hx => hx.1
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold RunTrace.FaultBound at h
  omega

/-- On the window from slot `s₀` to `b`, more than `f` honest validators are awake and joined at
`t_s + Δ ≤ b` for `s ≥ s₀`. -/
theorem faults_lt_awake_joined_win (hwin : SleepyWindow tr H ΔF s₀ b) {s : Nat} (hs₀ : s₀ ≤ s)
    (hs : sp.ts s + sp.Δ ≤ b) :
    Hᶜ.ncard <
      {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}.ncard := by
  have h := (sleepyWindow_iff.1 hwin).2.2 s hs₀ sp.Δ (by simp) hs
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined at h
  exact h

/-- On the window from slot `s₀` to `b`, `Sync[a, b']` holds of the AC projection for
`t_{s₀} ≤ a` and `b' ≤ b − Δ`. -/
theorem syncAC_of_window (hrun : GoldilocksRun proposer dg H tr) (hwin : SleepyWindow tr H ΔF s₀ b)
    {a b' : Time} (ha : sp.ts s₀ ≤ a) (hb : b' ≤ b - sp.Δ) :
    SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) a b' tr.projAC :=
  have hs := (sleepyWindow_iff.1 hwin).2.1
  sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr proposer ΔF a b'
    hrun.toLocalRun (show tr.SyncOn H ΔF (fun τ => a ≤ τ ∧ τ ≤ b') (fun τ => a ≤ τ ∧ τ ≤ b') id
      from ⟨hs.deltaF, hs.delta_le,
        fun x hx i m hm hw => hs.message x hx i m hm ⟨ha.trans hw.1, hw.2.trans hb⟩,
        fun x hx i B hB hw => hs.block x hx i B hB ⟨ha.trans hw.1, hw.2.trans hb⟩,
        fun x hx i B hB hw => hs.relay x hx i B hB ⟨ha.trans hw.1, hw.2.trans hb⟩,
        fun x hx i a' h hw => hs.attestation x hx i a' h ⟨ha.trans hw.1, hw.2.trans hb⟩⟩)

/-- Under the prefix premises up to `b ≥ 0`, `f < n/2` (`f < h_0`). -/
theorem two_faults_lt_of_prefix (hpre : SleepyPrefix tr H ΔF b) : 2 * Hᶜ.ncard < sp.n :=
  two_faults_lt_of_window hpre.window

/-- The cuts of a tick: the AC's tick, the proposal step, the FG update. -/
private theorem tick_cuts (y : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (x : Nat) :
    (Node.exec proposer dg y st t (.tick x)).2 =
      (Node.tickStep proposer dg y st t x .acTick).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (Node.tickStep proposer dg y
        (Node.tickStep proposer dg y (Node.tickStep proposer dg y st t x .acTick).1 t x
          .proposal).1 t x .fgUpdate).2 := by
  simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps]

/-- **An honest validator awake and joined at `t_s + Δ` votes in slot `s`**, at or before
`t_s + Δ`: its tick there runs `try_vote` unless it voted in slot `s` already. -/
theorem vote_of_awake_joined {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {s : Nat} (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    ∃ k e, SA.VoteAt tr.projAC y k e ∧ e.msg.slot = s ∧ tr.projAC.time k ≤ sp.ts s + sp.Δ := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h0 := ts_nonneg (sp := sp) s
  have hslot : sp.slot (sp.ts s + sp.Δ) = s :=
    SA.slot_of_mem sp s (le_add_of_nonneg_right hΔ.le)
      (by simp only [SAParams.ts]; push_cast; linarith)
  obtain ⟨j, x, hj'⟩ := hrun.tick_of_awake y hy _ (add_nonneg h0 hΔ.le)
    (show sp.toParams.IsPublic _ from Dvd.intro (4 * (s : Int) + 1)
      (by simp only [SAParams.ts]; ring)) hw
  obtain ⟨-, hk, -⟩ := hj'
  have hlen : 0 < (Node.exec proposer dg y (tr.state y j) (sp.ts s + sp.Δ) (.tick x)).2.length := by
    rw [tick_cuts]; simp [Node.tickStep]
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hk 0 hlen
  have hget : (Node.exec proposer dg y (tr.state y j) (sp.ts s + sp.Δ) (.tick x)).2[0]'hlen =
      (Node.acCall y (tr.state y j) (sp.ts s + sp.Δ) .tick).2 := by
    simp only [tick_cuts]; rfl
  rw [hget] at hl0
  simp only [Nat.add_zero] at hn0 ht0 hl0
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.label j = some (.ac ℓ) ∧ ℓ.call = .tick := ⟨_, hl0, rfl⟩
  have hc : tr.projAC.CallAt y j ℓ := ⟨hn0, by simp [RunTrace.projAC, hl, RunTrace.acLabel]⟩
  have htj : tr.projAC.time j = sp.ts s + sp.Δ := ht0
  have he := hr.exec j ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1, hcall] at he
  have hemit : (SA.acOnTick sp y (tr.projAC.state y j) ℓ.frame (tr.projAC.time j)).2 = ℓ.emits :=
    congrArg Prod.snd he
  have hnr : ¬ tr.RestartAt y j := by
    rintro ⟨ℓ', ⟨-, hl'⟩, hr'⟩
    have h := hl'.symm.trans hl
    injection h with h
    injection h with h
    rw [h, hcall] at hr'
    cases hr'
  have hjo : SA.joined sp (tr.projAC.state y j) (tr.projAC.time j) := by
    rw [projAC_state hrun.toLocalRun hy j, htj]
    exact ((joined_projection_from hrun hy _).2.1 j ⟨_, hn0, hl⟩ hnr ht0).1 hj
  rcases SA.acOnTick_votes y _ ℓ.frame hjo (by rw [htj, hslot])
      (by rw [htj, hslot, projAC_state hrun.toLocalRun hy j]; exact hmv j) with hv | ⟨e, he', hes⟩
  · rw [htj, hslot] at hv
    rcases SA.cast_of_votedSlot hr hrun.vstart hy j s hv with
      ⟨k, hk, e, hve, hes⟩ | hmf
    · exact ⟨k, e, hve, hes, (hr.time_mono hk.le).trans htj.le⟩
    · rw [projAC_state hrun.toLocalRun hy j, hmv j] at hmf
      exact absurd hmf (by decide)
  · refine ⟨j, e, ⟨ℓ, hc, hemit ▸ he'⟩, ?_, htj.le⟩
    rwa [htj, hslot] at hes

/-- `hmv` from any starts up to the vote permission: the start's own permission, kept along the
trace (`trace_mayVote`). -/
theorem mayVote_of_start {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n}
    (hy : y ∈ H) {s : Nat} (h₀ : SA.SAState.mayVote (ini y) s = true) :
    ∀ i, (tr.state y i).ac.mayVote s = true := fun i => by
  rw [← projAC_state hrun.toLocalRun hy i,
    SA.trace_mayVote (goldilocks_ac_projection_from hrun hnc).localRun hy i]
  exact h₀

/-- `hmv` on a stock run: `mayVote_of_start` at the initial starts, whose permission is
`fun _ => true`. -/
theorem mayVote_stock (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (s : Nat) : ∀ i, (tr.state y i).ac.mayVote s = true :=
  mayVote_of_start hrun hnc hy rfl

/-- **The honest validators awake and joined at `t_s + Δ` are participants** of an honest update
of slot `s`: their slot-`s` votes reach the writer, whose restarts are at or before `t_s`. -/
private theorem awake_participant (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {s : Nat}
    (hsync : SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) (sp.ts s) (sp.ts s + sp.Δ)
      tr.projAC) {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hy hmv hw hj
  obtain ⟨hval, hsl', -, -⟩ := SA.castAt_spec hr hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have := SA.sync_forward hr hsync hy
    ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩
    hsk hk hX hu.1 (fun k' hk' hr' => (SA.update_restarts hr hX hu k' hk' hr').trans hsk)
    (by
      rw [hu.2.2.1]
      exact (add_le_add hk le_rfl).trans
        (by rw [SA.add_delta_add_delta]; exact SA.add_mul_delta_le (by norm_num)))
    fun t h₁ h₂ => by
      have : sp.slot t = s := SA.slot_of_mem sp s (hsk.trans h₁) (by
        rw [hts]
        exact h₂.trans_le ((add_le_add hk le_rfl).trans
          (by rw [SA.add_delta_add_delta]; exact SA.add_mul_delta_le (by norm_num))))
      omega
  rw [hes] at this
  rcases this with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact ⟨e.msg, h, hval⟩
  · exact ⟨a, ha, hav.trans hval⟩

/-- Awake joined validators participate in a result observed before the finite deadline
cutoff. Only their vote deadlines are used; later receiver wakes are irrelevant. -/
theorem awake_participant_window_before {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {s : Nat} {a b : Time}
    (hsync : SA.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hy hmv hw hj
  obtain ⟨hval, hsl', -, -⟩ := SA.castAt_spec hr hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  change tr.time k ≤ sp.ts s + sp.Δ at hk
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hkb : tr.projAC.time k + sp.Δ ≤ b := by
    change tr.time k + sp.Δ ≤ b
    exact (add_le_add hk le_rfl).trans (((SA.add_delta_add_delta _).trans_le
      (SA.add_mul_delta_le (by norm_num))).trans (ht.symm.trans_le hib))
  have hki : tr.projAC.time k + sp.Δ ≤ tr.projAC.time i₀ := by
    change tr.time k + sp.Δ ≤ tr.time i₀
    exact (add_le_add hk le_rfl).trans (((SA.add_delta_add_delta _).trans_le
      (SA.add_mul_delta_le (by norm_num))).trans_eq ht.symm)
  have := SA.sync_window_before_forward hr hsync hy ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩
    (ha.trans hsk) hkb hX hu.1
    (fun k' hk' hr' => (SA.update_restarts hr hX hu k' hk' hr').trans hsk) hki
    fun t h₁ h₂ => by
      change t < tr.time k + sp.Δ at h₂
      have : sp.slot t = s := SA.slot_of_mem sp s (hsk.trans h₁) (by
        rw [hts]
        exact h₂.trans_le ((add_le_add hk le_rfl).trans
          (by rw [SA.add_delta_add_delta]; exact SA.add_mul_delta_le (by norm_num))))
      omega
  rw [hes] at this
  rcases this with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact ⟨e.msg, h, hval⟩
  · exact ⟨a, ha, hav.trans hval⟩

/-- `awake_participant_before` when the update itself is after `b`: the votes are due by
`t_s + 2Δ ≤ b`, so only the early cutoff needs to be within the service horizon. -/
theorem awake_participant_early {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {s : Nat} {b : Time}
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC) (hb : sp.ts s + 2 * sp.Δ ≤ b)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX)
    {y : Fin sp.n} (hy : y ∈ H) (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, e, ⟨ℓ, hc, he⟩, hes, hk⟩ := vote_of_awake_joined hrun hnc hy hmv hw hj
  obtain ⟨hval, hsl', -, -⟩ := SA.castAt_spec hr hy ⟨hc, he⟩
  have hsk : sp.ts s ≤ tr.projAC.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
  have ht : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  change tr.time k ≤ sp.ts s + sp.Δ at hk
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hkb : tr.projAC.time k + sp.Δ ≤ b := by
    change tr.time k + sp.Δ ≤ b
    exact (add_le_add hk le_rfl).trans ((SA.add_delta_add_delta _).trans_le hb)
  have hki : tr.projAC.time k + sp.Δ ≤ tr.projAC.time i₀ := by
    change tr.time k + sp.Δ ≤ tr.time i₀
    exact (add_le_add hk le_rfl).trans (((SA.add_delta_add_delta _).trans_le
      (SA.add_mul_delta_le (by norm_num))).trans_eq ht.symm)
  have := SA.sync_window_before_forward hr ⟨hsync.message, hsync.relay⟩ hy
    ⟨ℓ, hc, Or.inl ⟨e, he, rfl⟩⟩ ((ts_nonneg s).trans hsk) hkb hX hu.1
    (fun k' hk' hr' => (SA.update_restarts hr hX hu k' hk' hr').trans hsk) hki
    fun t h₁ h₂ => by
      change t < tr.time k + sp.Δ at h₂
      have : sp.slot t = s := SA.slot_of_mem sp s (hsk.trans h₁) (by
        rw [hts]
        exact h₂.trans_le ((add_le_add hk le_rfl).trans
          (by rw [SA.add_delta_add_delta]; exact SA.add_mul_delta_le (by norm_num))))
      omega
  rw [hes] at this
  rcases this with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact ⟨e.msg, h, hval⟩
  · exact ⟨a, ha, hav.trans hval⟩

/-- The zero-source finite participant theorem retains its original interface. -/
theorem awake_participant_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat} {b : Time}
    (hsync : SA.ServiceBefore H (tr.HonestBlocks H) b tr.projAC)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b) {y : Fin sp.n} (hy : y ∈ H)
    (hmv : ∀ i, (tr.state y i).ac.mayVote s = true)
    (hw : tr.awake y (sp.ts s + sp.Δ)) (hj : tr.JoinedAt y (sp.ts s + sp.Δ)) :
    y ∈ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} :=
  awake_participant_window_before hrun hnc ⟨hsync.message, hsync.relay⟩
    (ts_nonneg s) hX hu hib hy hmv hw hj

/-- If every honest validator is awake and joined, windowed forwarding gives more than
twice the faulty population in the actual update pool. No head resolution is needed. -/
theorem honest_participants_window_before
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {a b : Time} {s : Nat}
    (hsync : SA.ServiceWindowBefore H (tr.HonestBlocks H) a b tr.projAC)
    (ha : a ≤ sp.ts s) {X : Fin sp.n} (hX : X ∈ H) {i₀ : Nat}
    {ℓX : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC X i₀ s ℓX)
    (hib : tr.time i₀ ≤ b)
    (hready : ∀ y ∈ H, tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ))
    (hf : 3 * Hᶜ.ncard < sp.n) :
    2 * Hᶜ.ncard < (SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s}).ncard := by
  have hsub : H ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := fun y hy =>
    awake_participant_window_before hrun hnc hsync ha hX hu hib hy (mayVote_stock hrun hnc hy s)
      (hready y hy).1 (hready y hy).2
  have hcount := Set.ncard_le_ncard hsub
  have htotal : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- **A result and an optimistic selection of one slot are compatible** (RO): the `≥ 3n/4`
optimistic seats reach the writer, where none supports the result. -/
private theorem result_optimistic_compatible
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {s : Nat}
    (hsync : SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) (sp.ts s)
      (sp.ts (s + 1 : Nat) + sp.Δ) tr.projAC) {X x : Fin sp.n} (hX : X ∈ H) (hx : x ∈ H)
    {i i' : Nat} {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {CV CV' : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i s C CV) (hO : SA.OptimisticLockAt tr.projAC x i' s C' CV') :
    Compatible (tr.HonestBlocks H) C C' := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hle : ∀ T : Set (Fin sp.n), T.ncard ≤ sp.n := fun T =>
    (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])
  by_contra hnc'
  obtain ⟨ℓ, S, hc, ht, hrs, hmaj, -, hS⟩ := SA.result_side hrun' hX hR
  obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := SA.optimistic_seats hrun' hx hO
  have := SA.relayed_against hrun'.localRun hsync hx hX hc ht hrs hS hT fun h => hnc' (Or.symm h)
  have := hle (SA.voters {v | v ∈ (tr.projAC.state X i).pool s})
  omega

/-- `honest_vote_exists_upTo` on the window from slot `s₀ ≤ s` to `b`. -/
private theorem honest_vote_exists_win (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hwin : SleepyWindow tr H ΔF s₀ b) {s : Nat} (hs₀ : s₀ ≤ s) (hs : sp.ts s + sp.Δ ≤ b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s := by
  obtain ⟨y, hy, hw, hj⟩ := Set.nonempty_of_ncard_ne_zero
    (Nat.zero_lt_of_lt (faults_lt_awake_joined_win hwin hs₀ hs)).ne'
  obtain ⟨k, e, hv, hs, -⟩ := vote_of_awake_joined hrun hnc hy (mayVote_stock hrun hnc hy s) hw hj
  exact ⟨y, hy, k, e, hv, hs⟩

/-- **Every slot up to `b` has an honest vote**: an honest validator awake and joined at
`t_s + Δ ≤ b` (there are more than `f ≥ 0` of them) votes in slot `s`. -/
theorem honest_vote_exists_upTo (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) (s : Nat) (hs : sp.ts s + sp.Δ ≤ b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ e.msg.slot = s :=
  honest_vote_exists_win hrun hnc hpre.window (Nat.zero_le s) hs

/-- `honest_supporter_upTo` on the window from slot `s₀ ≤ s` to `b`. -/
private theorem honest_supporter_win
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hwin : SleepyWindow tr H ΔF s₀ b) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hs₀ : s₀ ≤ s) (hC : OriginWithin tr H C s b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨X, hX, i₀, CV, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · -- a result: a counted validator is honest, by the strict majority over the participants
    have hmaj := SA.result_majority hR
    obtain ⟨ℓX, hu, -, hCV⟩ := hR
    have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hJ := faults_lt_awake_joined_win hwin hs₀ ((add_le_add le_rfl
      (le_mul_of_one_le_left hΔ.le (by norm_num))).trans (ht₀.symm.trans_le hi₀))
    have hsync := syncAC_of_window hrun hwin (a := sp.ts s) (b' := sp.ts s + sp.Δ) (ts_le_ts hs₀)
      (le_sub_iff_add_le.2 ((SA.add_delta_add_delta _).trans_le
        ((SA.add_mul_delta_le (by norm_num)).trans (ht₀.symm.trans_le hi₀))))
    have hJV : {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := fun y hy =>
      awake_participant hrun hnc hsync hX hu hy.1 (mayVote_stock hrun hnc hy.1 s) hy.2.1 hy.2.2
    have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
      rintro w ⟨v, hv, rfl⟩
      rw [hCV] at hv
      exact ⟨v, hv.1, rfl⟩
    obtain ⟨w, ⟨v, hv, rfl⟩, hwH⟩ : ∃ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∈ H := by
      by_contra hno'
      have hno : ∀ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∉ H := fun w hw hwH => hno' ⟨w, hw, hwH⟩
      have hdisj : Disjoint
          {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}
          {w | ∃ v ∈ CV, v.val = w} :=
        Set.disjoint_left.2 fun y hyJ hyS => hno y hyS hyJ.1
      have h1 := Set.ncard_union_eq hdisj
      have h2 := Set.ncard_le_ncard (Set.union_subset hJV hSV)
      have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Hᶜ.ncard :=
        Set.ncard_le_ncard fun y hy => hno y hy
      omega
    rw [hCV] at hv
    obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
    obtain ⟨j, hj, e, hve, rfl⟩ := hrun'.honest.pool_vote X hX i₀ s _ hvp hwH
    obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hX hu.1
    exact ⟨_, hwH, j, e, hve, (hrun.time_mono hj.le).trans hi₀,
      SA.state_pool_slot sp hr hX i₀ s _ hvp, R, hΦU hR, hRr, Anc.mono hΦU hCR⟩
  · -- an optimistic selection: `3n/4 > f` voters
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := SA.optimistic_seats hrun' hX hO
    have hf := two_faults_lt_of_window hwin
    obtain ⟨u, ⟨v, hv, rfl, R, hR, hRr, hCR⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C) (by omega)
    have huH : v.val ∈ H := not_not.1 huH
    obtain ⟨hvs, j, hj, e, hve, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hX hpt hv huH
    exact ⟨_, huH, j, e, hve, (hrun.time_mono hj).trans hi₀, hvs, R, hΦU hR, hRr,
      Anc.mono hΦU hCR⟩

/-- An origin within the finite horizon has an honest supporter using only deadline-bounded
service and the fault bounds at slot points inside the horizon. -/
theorem honest_supporter_before
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hC : OriginWithin tr H C s b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨X, hX, i₀, CV, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · have hmaj := SA.result_majority hR
    obtain ⟨ℓX, hu, -, hCV⟩ := hR
    have ht₀ : tr.time i₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hJ := hfb s sp.Δ (by simp) (by linarith)
    change Hᶜ.ncard <
      {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}.ncard at hJ
    have hJV : {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)} ⊆
        SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := fun y hy =>
      awake_participant_before hrun hnc hsync.ac
        hX hu hi₀ hy.1 (mayVote_stock hrun hnc hy.1 s) hy.2.1 hy.2.2
    have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆ SA.voters {v | v ∈ (tr.projAC.state X i₀).pool s} := by
      rintro w ⟨v, hv, rfl⟩
      rw [hCV] at hv
      exact ⟨v, hv.1, rfl⟩
    obtain ⟨w, ⟨v, hv, rfl⟩, hwH⟩ : ∃ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∈ H := by
      by_contra hno'
      have hno : ∀ w ∈ {w | ∃ v ∈ CV, v.val = w}, w ∉ H := fun w hw hwH => hno' ⟨w, hw, hwH⟩
      have hdisj : Disjoint
          {y | y ∈ H ∧ tr.awake y (sp.ts s + sp.Δ) ∧ tr.JoinedAt y (sp.ts s + sp.Δ)}
          {w | ∃ v ∈ CV, v.val = w} :=
        Set.disjoint_left.2 fun y hyJ hyS => hno y hyS hyJ.1
      have h1 := Set.ncard_union_eq hdisj
      have h2 := Set.ncard_le_ncard (Set.union_subset hJV hSV)
      have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Hᶜ.ncard :=
        Set.ncard_le_ncard fun y hy => hno y hy
      omega
    rw [hCV] at hv
    obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
    obtain ⟨j, hj, e, hve, rfl⟩ := hrun'.honest.pool_vote X hX i₀ s _ hvp hwH
    obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hX hu.1
    exact ⟨_, hwH, j, e, hve, (hrun.time_mono hj.le).trans hi₀,
      SA.state_pool_slot sp hr hX i₀ s _ hvp, R, hΦU hR, hRr, Anc.mono hΦU hCR⟩
  · obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := SA.optimistic_seats hrun' hX hO
    have hf : 2 * Hᶜ.ncard < sp.n := by
      have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
      change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
      have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
        Set.ncard_le_ncard fun x hx => hx.1
      have hn : H.ncard + Hᶜ.ncard = sp.n := by
        rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    obtain ⟨u, ⟨v, hv, rfl, R, hR, hRr, hCR⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C) (by omega)
    have huH : v.val ∈ H := not_not.1 huH
    obtain ⟨hvs, j, hj, e, hve, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hX hpt hv huH
    exact ⟨_, huH, j, e, hve, (hrun.time_mono hj).trans hi₀, hvs, R, hΦU hR, hRr,
      Anc.mono hΦU hCR⟩

/-- **Up to `b`, an origin within `b` has an honest supporter**: an honest slot-`s` vote at a
time `≤ b` whose head extends it. -/
theorem honest_supporter_upTo
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s b) :
    ∃ x ∈ H, ∃ j e, SA.VoteAt tr.projAC x j e ∧ tr.time j ≤ b ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg C :=
  honest_supporter_win hrun hnc hpre.window (Nat.zero_le s) hC

/-- `same_label_compatible_upTo` on the window from slot `s₀ ≤ s` to `b`. -/
private theorem same_label_compatible_win
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hwin : SleepyWindow tr H ΔF s₀ b)
    {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hs₀ : s₀ ≤ s)
    (hC : OriginWithin tr H C s b) (hC' : OriginWithin tr H C' s b) :
    Compatible (tr.HonestBlocks H) C C' := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  -- `Sync` up to `t_{s+1} + Δ` from a result within `b`, at `t_s + 6Δ`
  have hsync : ∀ {Y i CV D}, tr.time i ≤ b → SA.ResultAt tr.projAC Y i s D CV →
      SyncAC (goldilocksNode sp ro) H (tr.HonestBlocks H) (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ)
        tr.projAC := fun hi ⟨_, hu, _⟩ => by
    have ht : tr.time _ = sp.ts s + 6 * sp.Δ := hu.2.2.1
    exact syncAC_of_window hrun hwin (ts_le_ts hs₀) (by
      rw [hts]
      refine le_sub_iff_add_le.2 ?_
      rw [SA.add_mul_delta_add_delta, SA.add_mul_delta_add_delta]
      exact (SA.add_mul_delta_le (by norm_num)).trans (ht.symm.trans_le hi))
  obtain ⟨X, hX, i, CV, hi, hR | hO⟩ := originWithin_iff.1 hC <;>
    obtain ⟨X', hX', i', CV', hi', hR' | hO'⟩ := originWithin_iff.1 hC'
  · -- RR: each side's counted validators reach the other writer, where none supports it
    by_contra hnc'
    obtain ⟨ℓ, S, hc, ht, hrs, hmaj, hSF, hS⟩ := SA.result_side hrun' hX hR
    obtain ⟨ℓ', S', hc', ht', hrs', hmaj', hSF', hS'⟩ := SA.result_side hrun' hX' hR'
    have h1 := SA.relayed_against hrun'.localRun (hsync hi hR) hX' hX hc ht hrs hS hSF'
      fun h => hnc' (Or.symm h)
    have h2 := SA.relayed_against hrun'.localRun (hsync hi hR) hX hX' hc' ht' hrs' hS' hSF hnc'
    omega
  · exact result_optimistic_compatible hrun hnc (hsync hi hR) hX hX' hR hO'
  · exact Or.symm (result_optimistic_compatible hrun hnc (hsync hi' hR') hX' hX hR' hO)
  · -- OO: an honest validator in common, with one slot-`s` vote
    have hr := hrun'.localRun
    have hU := hr.coherent
    have hf := two_faults_lt_of_window hwin
    have hle : ∀ T : Set (Fin sp.n), T.ncard ≤ sp.n := fun T =>
      (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])
    by_contra hnc'
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := SA.optimistic_seats hrun' hX hO
    obtain ⟨ℓ', A', hpt', hΦU', h34', -⟩ := SA.optimistic_seats hrun' hX' hO'
    have hI := Set.ncard_inter_add_ncard_union (SA.optimisticVoters sp A ℓ.frame s C)
      (SA.optimisticVoters sp A' ℓ'.frame s C')
    have := hle (SA.optimisticVoters sp A ℓ.frame s C ∪ SA.optimisticVoters sp A' ℓ'.frame s C')
    obtain ⟨u, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, ⟨v', hv', hv'u, R', hR', hR'r, hBR'⟩⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C ∩ SA.optimisticVoters sp A' ℓ'.frame s C')
        (by omega)
    have huH := not_not.1 huH
    obtain ⟨hvs, j₁, -, e₁, he₁, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hX hpt hv huH
    obtain ⟨hv's, j₂, -, e₂, he₂, rfl⟩ :=
      SA.optimisticPoint_pool_vote hrun' hX' hpt' hv' (hv'u ▸ huH)
    rw [hv'u] at he₂
    obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr _ huH j₁ j₂ e₁ e₂ he₁ he₂
      (hvs.trans hv's.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hnc' (SA.anc_total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hBR'))

/-- A result and an optimistic selection of one label compare once the label's relayed
votes have deadlines within `b`, whatever the time of the result's update. -/
theorem result_optimistic_compatible_label_before
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    {s : Nat} (hs : sp.ts s + 3 * sp.Δ ≤ b) {X x : Fin sp.n} (hX : X ∈ H) (hx : x ∈ H)
    {i i' : Nat} {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {CV CV' : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC X i s C CV) (hO : SA.OptimisticLockAt tr.projAC x i' s C' CV') :
    Compatible (tr.HonestBlocks H) C C' := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  by_contra hnc'
  obtain ⟨ℓ, S, hc, ht, hrs, hmaj, -, hS⟩ := SA.result_side hrun' hX hR
  obtain ⟨ℓo, Ao, -, -, h34, hT⟩ := SA.optimistic_seats hrun' hx hO
  have := SA.relayed_against_of_held hrun'.localRun
    (SA.relayed_held_before hrun'.localRun hsync.ac hx hX hc ht hs hrs) hS hT
    fun h => hnc' (Or.symm h)
  have := (Set.ncard_le_ncard
    (Set.subset_univ (SA.voters {v | v ∈ (tr.projAC.state X i).pool s}))).trans
    (by rw [Set.ncard_univ, Nat.card_fin])
  omega

/-- Origins of one label compare using recipient deadlines only up to `b`. -/
theorem same_label_compatible_before
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hf : 2 * Hᶜ.ncard < sp.n)
    {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s b) (hC' : OriginWithin tr H C' s b) :
    Compatible (tr.HonestBlocks H) C C' := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hs := hsync.ac
  have hle : ∀ T : Set (Fin sp.n), T.ncard ≤ sp.n := fun T =>
    (Set.ncard_le_ncard (Set.subset_univ T)).trans (by rw [Set.ncard_univ, Nat.card_fin])
  have hro : ∀ {X x i i' D D' CV CV'}, X ∈ H → x ∈ H → tr.time i ≤ b →
      SA.ResultAt tr.projAC X i s D CV → SA.OptimisticLockAt tr.projAC x i' s D' CV' →
      Compatible (tr.HonestBlocks H) D D' := by
    intro X x i i' D D' CV CV' hX hx hi hR hO
    have ht : tr.time i = sp.ts s + 6 * sp.Δ := by
      obtain ⟨_, hu, _⟩ := hR
      exact hu.2.2.1
    exact result_optimistic_compatible_label_before hrun hnc hsync
      ((SA.add_mul_delta_le (by norm_num)).trans (ht.symm.trans_le hi)) hX hx hR hO
  obtain ⟨X, hX, i, CV, hi, hR | hO⟩ := originWithin_iff.1 hC <;>
    obtain ⟨X', hX', i', CV', hi', hR' | hO'⟩ := originWithin_iff.1 hC'
  · by_contra hnc'
    obtain ⟨ℓ, S, hc, ht, hrs, hmaj, hSF, hS⟩ := SA.result_side hrun' hX hR
    obtain ⟨ℓ', S', hc', ht', hrs', hmaj', hSF', hS'⟩ := SA.result_side hrun' hX' hR'
    have ht : tr.time i = sp.ts s + 6 * sp.Δ := ht
    have ht' : tr.time i' = sp.ts s + 6 * sp.Δ := ht'
    have h1 := SA.relayed_against_of_held hrun'.localRun
      (SA.relayed_held_before hrun'.localRun hs hX' hX hc ht
        ((SA.add_mul_delta_le (by norm_num)).trans (ht.symm.trans_le hi)) hrs) hS hSF'
      fun h => hnc' (Or.symm h)
    have h2 := SA.relayed_against_of_held hrun'.localRun
      (SA.relayed_held_before hrun'.localRun hs hX hX' hc' ht'
        ((SA.add_mul_delta_le (by norm_num)).trans (ht'.symm.trans_le hi')) hrs') hS' hSF hnc'
    omega
  · exact hro hX hX' hi hR hO'
  · exact Or.symm (hro hX' hX hi' hR' hO)
  · have hr := hrun'.localRun
    have hU := hr.coherent
    by_contra hnc'
    obtain ⟨ℓ, A, hpt, hΦU, h34, -⟩ := SA.optimistic_seats hrun' hX hO
    obtain ⟨ℓ', A', hpt', hΦU', h34', -⟩ := SA.optimistic_seats hrun' hX' hO'
    have hI := Set.ncard_inter_add_ncard_union (SA.optimisticVoters sp A ℓ.frame s C)
      (SA.optimisticVoters sp A' ℓ'.frame s C')
    have := hle (SA.optimisticVoters sp A ℓ.frame s C ∪ SA.optimisticVoters sp A' ℓ'.frame s C')
    obtain ⟨u, ⟨⟨v, hv, rfl, R, hR, hRr, hBR⟩, ⟨v', hv', hv'u, R', hR', hR'r, hBR'⟩⟩, huH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A ℓ.frame s C ∩ SA.optimisticVoters sp A' ℓ'.frame s C')
        (by omega)
    have huH := not_not.1 huH
    obtain ⟨hvs, j₁, -, e₁, he₁, rfl⟩ := SA.optimisticPoint_pool_vote hrun' hX hpt hv huH
    obtain ⟨hv's, j₂, -, e₂, he₂, rfl⟩ :=
      SA.optimisticPoint_pool_vote hrun' hX' hpt' hv' (hv'u ▸ huH)
    rw [hv'u] at he₂
    obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr _ huH j₁ j₂ e₁ e₂ he₁ he₂
      (hvs.trans hv's.symm)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦU' hR') (hRr.trans hR'r.symm)
    exact hnc' (SA.anc_total hU (Anc.mono hΦU hBR) (Anc.mono hΦU' hBR'))

/-- **Up to `b`, origins within `b` of one label are compatible** (RR, RO, OO). -/
theorem same_label_compatible_upTo
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {C C' : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin tr H C s b) (hC' : OriginWithin tr H C' s b) :
    Compatible (tr.HonestBlocks H) C C' :=
  same_label_compatible_win hrun hnc hpre.window (Nat.zero_le s) hC hC'

/-- Two blocks below the head of one vote are compatible. -/
private theorem compatible_of_voteExtends (hU : Coherent (tr.HonestBlocks H)) {v : Vote sp.n}
    {C C' : SA.Blk sp.n (List (FG.Att sp.n))} (h : SA.VoteExtends (tr.HonestBlocks H) v C)
    (h' : SA.VoteExtends (tr.HonestBlocks H) v C') : Compatible (tr.HonestBlocks H) C C' := by
  obtain ⟨Hd, hHd, hHdr, hC⟩ := h
  obtain ⟨Hd', hHd', hHd'r, hC'⟩ := h'
  obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
  exact Anc.total hU hC hC'

/-- **Extending the origin frontier up to `b`**: `P_s` and `V_s` up to `b` give `P_{s+1}` up to
`b`. -/
theorem origins_below_succ_upTo
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H s b)
    (hV : VotesBelowUpTo tr H s b) : OriginsBelowUpTo tr H (s + 1) b := by
  have hU := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  rw [originsBelowUpTo_iff] at hP ⊢
  -- an origin of label `s` and one of label `j < s` are below the honest supporter's head
  have hnew : ∀ C C' j, j < s → OriginWithin tr H C s b → OriginWithin tr H C' j b →
      Compatible (tr.HonestBlocks H) C C' := by
    intro C C' j hj hC hC'
    obtain ⟨x, hx, i, e, hv, hib, hs, hext⟩ := honest_supporter_upTo hrun hnc hpre hC
    exact compatible_of_voteExtends hU hext
      (votesBelowUpTo_iff.1 hV C' j hC' x hx i e hv hib (by omega) (by omega))
  intro C j C' j' hj hj' hC hC'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact hP C j C' j' hj hj' hC hC'
  · exact Or.symm (hnew C' C j hj hC' hC)
  · exact hnew C C' j' hj' hC hC'
  · exact same_label_compatible_upTo hrun hnc hpre hC hC'

/-- The finite-deadline origin step preserves the horizon on every vote witness. -/
theorem origins_below_succ_before
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {s : Nat} (hP : OriginsBelowUpTo tr H s b) (hV : VotesBelowUpTo tr H s b) :
    OriginsBelowUpTo tr H (s + 1) b := by
  have hU := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  rw [originsBelowUpTo_iff] at hP ⊢
  have hnew : ∀ C C' j, j < s → OriginWithin tr H C s b → OriginWithin tr H C' j b →
      Compatible (tr.HonestBlocks H) C C' := by
    intro C C' j hj hC hC'
    obtain ⟨x, hx, i, e, hv, hib, hs, hext⟩ := honest_supporter_before hrun hnc hb hsync hfb hC
    exact compatible_of_voteExtends hU hext
      (votesBelowUpTo_iff.1 hV C' j hC' x hx i e hv hib (by omega) (by omega))
  intro C j C' j' hj hj' hC hC'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact hP C j C' j' hj hj' hC hC'
  · exact Or.symm (hnew C' C j hj hC' hC)
  · exact hnew C C' j' hj' hC hC'
  · exact same_label_compatible_before hrun hnc hsync hf hC hC'

/-- **Extending the origin frontier**: `P_s` and `V_s` give `P_{s+1}`. -/
theorem origins_below_succ
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H s) (hV : VotesBelow tr H s) :
    OriginsBelow tr H (s + 1) := by
  refine originsBelow_iff.2 fun C j C' j' hj hj' hC hC' => ?_
  obtain ⟨b, hb⟩ := hC.exists_within
  obtain ⟨b', hb'⟩ := hC'.exists_within
  exact originsBelowUpTo_iff.1 (origins_below_succ_upTo hrun hnc
    (hsl.prefix (le_max_right (max b b') 0)) (hP.upTo _) (hV.upTo _)) C j C' j' hj hj'
    (hb.mono ((le_max_left b b').trans (le_max_left _ 0)))
    (hb'.mono ((le_max_right b b').trans (le_max_left _ 0)))

end Consensus.Goldilocks.Compose

end
