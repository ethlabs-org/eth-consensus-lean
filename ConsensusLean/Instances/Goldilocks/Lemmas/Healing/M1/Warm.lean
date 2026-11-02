module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Drain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Range

public section

/-! # A warm honest proposal above the snapshot floor

The proposal gap supplies an actual proposal, while snapshot delivery supplies
`HZ ≤ hmax` at its honest cast. These are separate inputs: a frozen frame alone
does not supply the snapshot range. No reset envelope or whole-run progress is assumed.
-/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An actual honest proposal in the warm part of a finite frame has height at
least `HZ − 1`. The snapshot call is obtained at the actual cast, not at the
proposal's post-state; immutable held-block state then transports the height. -/
theorem FrameWindow.warm_proposal_height
    {g ΔF b : Time} {s₀ u N floor : Nat} {contest kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    (hcallZ : ∀ z ∈ H, ∀ m, sp.ts s₀ ≤ tr.time m → tr.time m ≤ sp.ts N + 2 * sp.Δ →
      ∃ j < m, tr.IsCall z j ∧
        tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (huN : u ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u) :
    HZ tr H g ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + 1 := by
  have hk := sp.two_le_k
  have hΔ := sp.toParams.hΔ
  have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hsu := hts (show s₀ ≤ u by omega)
  have huN' := hts huN
  obtain ⟨c, e, hv, hes, hhi⟩ := honest_votes_before_of_service hrun hnc hsvc hawake hf
    hcatch hnr (m := u) (by linarith) (by linarith) z hz
  obtain ⟨ell, hc, he⟩ := hv
  have hcast : SA.CastAt tr.projAC z c ell e := ⟨hc, he⟩
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hslot : sp.slot (tr.time c) = u := (SA.castAt_spec hr hz hcast).2.1.symm.trans hes
  have hlo : sp.ts s₀ ≤ tr.time c := hsu.trans
    ((SA.ts_le_iff_le_slot sp (hr.time_nonneg c) _).2 (by
      change (u : Int) ≤ sp.slot (tr.time c)
      rw [hslot]))
  have hsub : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts u + sp.Δ)
      floor contest kindJ J :=
    ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i hlo (by linarith),
      fun y hy i hlo hhi => hframe.contest_iff y hy i hlo (by linarith),
      fun y hy i hlo hhi => hframe.kind_iff y hy i hlo (by linarith),
      fun y hy i hlo hhi hc => hframe.root_eq y hy i hlo (by linarith) hc⟩
  have hvP := (hsub.proposal_viable_at_cast hrun hnc hsvc hawake hf hcatch hnr
    (by linarith) (by omega) (by omega) (by linarith) hz hdes hP hPs hz hcast hes).1
  rw [Compose.frame_of_projAC hrun hz hc] at hvP
  have hf2 : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hZ := HZ_le_hmax hrun hnc hf2 hsvc hcatch ⟨z, hz⟩ hsnap hz
    (hcallZ z hz c hlo (by linarith)) (by linarith)
  have hh := Store.height_le_of_isViable hvP.2.2.2 hZ
  have hPm := (accept_of_proposesAt hrun hnc hz hP).2.1
  have hσ := σ_eq_honest hrun hnc hz hz hvP.1 hPm
  rwa [hσ] at hh

/-- A finite proposer gap selects the warm proposal. Snapshot delivery, rather
than the frame alone, discharges its height requirement. The gap need only hold
on the indicated slot window, so an HPQ caller can keep its endpoint before heal. -/
theorem FrameWindow.exists_warm_proposal
    {g ΔF b : Time} {s₀ N G floor : Nat} {contest kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    (hcallZ : ∀ z ∈ H, ∀ m, sp.ts s₀ ≤ tr.time m → tr.time m ≤ sp.ts N + 2 * sp.Δ →
      ∃ j < m, tr.IsCall z j ∧
        tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hN : s₀ + 2 * sp.k + G ≤ N + 1) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    (hgp : ∃ u, s₀ + 2 * sp.k ≤ u ∧ u < s₀ + 2 * sp.k + G ∧ proposer u ∈ H ∧
      ∃ kP P, tr.ProposesAt (proposer u) kP P ∧ P.slot = u) :
    ∃ u, s₀ + 2 * sp.k ≤ u ∧ u < s₀ + 2 * sp.k + G ∧ ∃ z ∈ H, z = proposer u ∧
      ∃ kP P, tr.ProposesAt z kP P ∧ P.slot = u ∧
        HZ tr H g ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + 1 := by
  obtain ⟨u, hlu, hhu, hz, kP, P, hP, hPs⟩ := hgp
  exact ⟨u, hlu, hhu, proposer u, hz, rfl, kP, P, hP, hPs,
    hframe.warm_proposal_height hrun hnc hsvc hawake hf hcatch hnr hsnap hcallZ hm hlu
      (by omega) hmb hz rfl hP hPs⟩

end Consensus.Goldilocks.Healing
