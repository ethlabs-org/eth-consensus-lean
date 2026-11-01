module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset

public section

/-! # Goldilocks Healing, HR.4: the premises, the invariant and the run facts

`ResetPremises`, the two parts of the invariant over the cut index (`VoteInv`, `CacheInv`; see
`Lemmas/Healing/Retention`), and the facts of `Healthy(g)` the steps use (`syncRun_of_gst`,
`restart_le`, `fault_bound_late`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- `GST(g)` gives `Sync[a, b]` for every window that starts at or after `g`: an object sent at
`τ ≥ g` is processed as if sent at `max τ g = τ`. -/
theorem syncRun_of_gst {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Set (Fin P.n)}
    {ΔF g a b : Time} (h : tr.GSTRun H ΔF g) (hga : g ≤ a) : tr.SyncRun H ΔF a b := by
  have he : ∀ τ, a ≤ τ → max τ g = τ := fun τ hτ => max_eq_left (hga.trans hτ)
  refine ⟨h.deltaF, fun x hx i m hs hw => ?_, fun x hx i B hB hw => ?_,
    fun x hx i B hB hw => ?_, fun x hx i at' hs hw => ?_⟩
  · have := h.message x hx i m hs trivial
    simp only [he _ hw.1] at this
    exact this
  · have := h.block x hx i B hB trivial
    simp only [he _ hw.1] at this
    exact this
  · have := h.relay x hx i B hB (hga.trans hw.1)
    simp only [he _ hw.1] at this
    exact this
  · have := h.attestation x hx i at' hs trivial
    simp only [he _ hw.1] at this
    exact this

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **The premises of HR.4** for the reset `a`: a Goldilocks run under `Healthy(g)` and `NoColl`,
and `a` is the reset `a_z`. -/
structure ResetPremises (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a : Time) :
    Prop where
  run : GoldilocksRun proposer dg H tr
  healthy : tr.HealthyRun H ΔF g
  noColl : Compose.NoCollRun dg tr
  reset : IsReset tr H g a

/-- GST service at actual receiver calls through `b`. Effective send times and strict
delivery deadlines agree with `GSTRun`; no service after the observation horizon is required. -/
structure GSTRunUpTo (g ΔF b : Time) : Prop where
  deltaF : sp.Δ ≤ ΔF
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmitAt x i m →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (max (tr.time i) g) m
  block : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (max (tr.time i) g) B
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → g ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (max (tr.time i) g) B
  attestation : ∀ x ∈ H, ∀ i att, tr.SendOrAdmitAttAt x i att →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.time j ≤ b →
      tr.deadline y j (max (tr.time i) g) ΔF ≤ tr.time j →
      tr.AttDeliveredBy y j (tr.time i) (max (tr.time i) g) ΔF att

/-- Finite reset premises. Reset existence and its cutoff are inputs, not consequences of
bounded health. GST quantifies actual receiver calls, so remains finite-satisfiable.
Progress and Catch are separate premises of the consumers that need them. -/
structure ResetPremisesUpTo (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a b : Time) : Prop where
  run : GoldilocksRun proposer dg H tr
  noColl : Compose.NoCollRun dg tr
  sync : tr.GSTRun H ΔF g
  awake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t
  faults : 3 * Hᶜ.ncard ≤ sp.n - 1
  reset : IsReset tr H g a
  reset_le : a ≤ b
  snapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b

/-- Whole-run premises restrict to any horizon containing the actual reset. -/
theorem ResetPremises.toUpTo {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a b : Time}
    (hp : ResetPremises tr H proposer dg g ΔF a) (hab : a ≤ b) :
    ResetPremisesUpTo tr H proposer dg g ΔF a b := by
  classical
  have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
  obtain ⟨⟨y, hy, k, att, hs, hh, hka⟩, _⟩ := hp.reset
  change tr.time k = a at hka
  have hck : cutZ sp.toParams g < tr.time k := hka ▸ hca
  have hex : ∃ k, cutZ sp.toParams g < tr.time k := ⟨k, hck⟩
  have hfirst : FirstCutAfter tr (Nat.find hex) (cutZ sp.toParams g) :=
    ⟨fun q hq => not_lt.1 (Nat.find_min hex hq), Nat.find_spec hex⟩
  have hkb : tr.time (Nat.find hex) ≤ b :=
    (hp.run.time_mono (Nat.find_min' hex hck)).trans (hka ▸ hab)
  refine ⟨hp.run, hp.noColl, ?_, fun y hy t ht _ => hp.healthy.2.1 y hy t ht,
    hp.healthy.2.2, hp.reset, hab, Nat.find hex, hfirst, hkb⟩
  exact hp.healthy.1

/-- Bounded wakefulness supplies an actual frontier snapshot by `b` when the tick
at `c_z + Δ` fits. No continuation or calls beyond `b` are assumed. -/
theorem cutZ_snapshot_of_awake_before {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g b : Time}
    (hrun : GoldilocksRun proposer dg H tr)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : 3 * Hᶜ.ncard ≤ sp.n - 1)
    (hbudget : cutZ sp.toParams g + sp.Δ ≤ b) :
    ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b := by
  classical
  have hH : H.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hfaults
    have hn : 0 < sp.n := sp.toParams.hn
    change 3 * sp.n ≤ sp.n - 1 at hfaults
    omega
  obtain ⟨y, hy⟩ := hH
  have hΔ := sp.toParams.hΔ
  have hgt : gbar g ≤ cutZ sp.toParams g + sp.Δ := by
    have := lt_cutZ sp g
    linarith
  obtain ⟨j, _, hne, hcs, _⟩ := hrun.tick_of_awake y hy
    (cutZ sp.toParams g + sp.Δ) ((gbar_nonneg g).trans hgt)
    ⟨4 * ((sp.slot (gbar g) + 3 : Nat) : Int) + 1, by
      rw [cutZ_eq]; simp only [SAParams.ts]; ring⟩
    (hawake y hy _ hgt hbudget)
  obtain ⟨_, ht, _, _, _⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
  simp only [Nat.add_zero] at ht
  have hj : cutZ sp.toParams g < tr.time j := by linarith
  have hex : ∃ k, cutZ sp.toParams g < tr.time k := ⟨j, hj⟩
  exact ⟨Nat.find hex,
    ⟨fun k hk => not_lt.1 (Nat.find_min hex hk), Nat.find_spec hex⟩,
    (hrun.time_mono (Nat.find_min' hex hj)).trans (ht ▸ hbudget)⟩

/-- (R3) at the honest votes cast at cut `k`, for every high origin `(B, j)` of the run: a vote
of a slot `> j` extends `B`, and at that vote `B` is in the viable voter block tree or
`B ⪯ fc_root` (in the honest blocks). -/
def VoteInv (g : Time) (k : Nat) : Prop :=
  ∀ x i j B, HighOrigin tr H g x i j B → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
    j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
      (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)

/-- (R2) after an honest call at cut `k` at a time `≥ a`, for every high origin `(B, j)` written
at a cut `≤ k` or activated by then (`t_{j+1} ≤` the time of `k`; JointRet §13): `Σ.F` is
compatible with `B`, and so is `Σ.J` when `Σ.h_j ≥ H_z + 1`. -/
def CacheInv (g a : Time) (k : Nat) : Prop :=
  ∀ y ∈ H, tr.IsCall y k → a ≤ tr.time k →
    ∀ x i j B, HighOrigin tr H g x i j B → (i ≤ k ∨ sp.ts (j + 1 : Nat) ≤ tr.time k) →
      Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
        (HZ tr H g + 1 ≤ (tr.post k).fg.hj → Compatible (tr.HonestBlocks H) (tr.post k).fg.J B)

variable {tr H} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
  {proposer : Nat → Fin sp.n}

theorem voteInv_iff {g : Time} {k : Nat} : VoteInv tr H g k ↔
    ∀ x i j B, HighOrigin tr H g x i j B → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
      j < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
        (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
          Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) := Iff.rfl

theorem cacheInv_iff {g a : Time} {k : Nat} : CacheInv tr H g a k ↔
    ∀ y ∈ H, tr.IsCall y k → a ≤ tr.time k →
      ∀ x i j B, HighOrigin tr H g x i j B → (i ≤ k ∨ sp.ts (j + 1 : Nat) ≤ tr.time k) →
        Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
          (HZ tr H g + 1 ≤ (tr.post k).fg.hj →
            Compatible (tr.HonestBlocks H) (tr.post k).fg.J B) := Iff.rfl


/-- **No honest restart after `t_{slot(ḡ)+1}`** (`Healthy(g)`): a restart follows a time `u` at
which the node was asleep with no call in `[u, restart)`; `u ≥ ḡ` contradicts `Healthy(g)`, and
`u < ḡ` contradicts the tick at the public time `t_{slot(ḡ)+1} ≥ ḡ`, at which the node is awake. -/
theorem restart_le_before {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : tr.RestartAt y k) (hkb : tr.time k ≤ b) :
    tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  by_contra hlt
  obtain ⟨u, -, huk, hu, hprev⟩ := hp.run.sleep_of_restart y hy k hk
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (SA.ts_le_iff_le_slot sp (gbar_nonneg g) ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr
      (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu (hp.awake y hy u hgu (huk.le.trans hkb))
  · obtain ⟨j, _x, hne, hcs, -⟩ := hp.run.tick_of_awake y hy _ ((gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [SAParams.ts]; ring⟩
      (hp.awake y hy _ hp₀ ((lt_of_not_ge hlt).le.trans hkb))
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    have hjk : j < k := by
      by_contra h
      have := hp.run.time_mono (not_lt.mp h)
      exact hlt (ht ▸ this)
    have := hprev j hjk ⟨_, hn, hl⟩
    exact hgu (by linarith)

/-- Whole-run specialization of the causal restart bound. -/
theorem restart_le (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : tr.RestartAt y k) : tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) :=
  restart_le_before (hp.toUpTo tr H (le_max_left a (tr.time k))) hy hk (le_max_right _ _)

/-- **`f < h_t` after the cut** (`Healthy(g)`): from `c_z` on every honest validator is awake
and joined (its restarts are at or before `t_{slot(ḡ)+1} < t_{slot(t) − 1}`, `restart_le`), and
`3f ≤ n − 1`. -/
theorem fault_bound_late_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {t : Time}
    (ht : cutZ sp.toParams g ≤ t) (htb : t ≤ b) : tr.FaultBound H t := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ t := (gbar_nonneg g).trans hgt
  have hs : sp.slot (gbar g) + 3 ≤ sp.slot t := by
    have h := (SA.ts_le_iff_le_slot sp ht0 ((sp.slot (gbar g) + 3 : Nat) : Int)).mp
      ((cutZ_eq sp g) ▸ ht)
    exact_mod_cast h
  have hsub : H ⊆ {y | y ∈ H ∧ tr.awake y t ∧ tr.JoinedAt y t} := by
    refine fun y hy => ⟨hy, hp.awake y hy t hgt htb, fun k hk hkt => ?_⟩
    change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
    have he : sp.toParams.slotTime (sp.slot t - 1) = sp.ts ((sp.slot t - 1 : Nat) : Int) :=
      sp.slotTime_eq _
    refine ⟨by omega, (restart_le_before hp hy hk (hkt.trans htb)).trans ?_⟩
    rw [he]
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hle : H.ncard ≤ tr.honestAwakeJoined H t := Set.ncard_le_ncard hsub
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hp.faults
  have hn' : sp.n = sp.toParams.n := rfl
  have hpos := sp.toParams.hn
  unfold RunTrace.FaultBound
  omega

/-- Whole-run specialization of the finite late fault bound. -/
theorem fault_bound_late (hp : ResetPremises tr H proposer dg g ΔF a) {t : Time}
    (ht : cutZ sp.toParams g ≤ t) : tr.FaultBound H t :=
  fault_bound_late_before (hp.toUpTo tr H (le_max_left a t)) ht (le_max_right _ _)

end Consensus.Goldilocks.Healing

end
