module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Warm
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The warm proposal is at or above the frame floor

Let `P` be the actual honest proposal of slot `u` in
the warm part of a `FrameWindow [t_{s₀}, t_N + 2Δ]` with floor `floor`. The proposer's own
vote of slot `u` is cast at a cut `c` with `t_u ≤ t_c ≤ t_u + Δ`, inside the window. At that
cast, `P` is a viable head (`FrameWindow.proposal_viable_at_cast`, spec fg.tex viable head
selection), so `head_height_floor ≤ σ[P].h` at cut `c`. The window gives
`head_height_floor = floor` at cut `c`, and the immutable held-block state transports the
height to the post-proposal cut `kP + 1`.

The floor is the frame floor of the `FrameWindow`: the common `head_height_floor` of every
honest cut in the window, in particular at the proposer's cast in slot `u`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **The warm proposal is at or above the frame floor.** The premises are those of
`FrameWindow.warm_proposal_height`. -/
theorem FrameWindow.floor_le_warm_proposal
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (huN : u ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u) (hstock : sp.committeeSize = sp.n) :
    floor ≤ ((tr.state z (kP + 1)).fg.σ P.root).h := by
  have hk := sp.two_le_k
  have hΔ := sp.toParams.hΔ
  have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hsu := hts (show s₀ ≤ u by omega)
  have huN' := hts huN
  obtain ⟨c, e, hv, hes, hhi⟩ := honest_votes_before_of_service hrun hnc hsvc hawake hf
    hcatch hnr (m := u) (by linarith) (by linarith) hstock z hz
  obtain ⟨ell, hc, he⟩ := hv
  have hcast : SA.CastAt tr.projAC z c ell e := ⟨hc, he⟩
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hslot : sp.slot (tr.time c) = u := (SA.castAt_spec hr hz hcast).2.1.symm.trans hes
  have huc : sp.ts u ≤ tr.time c :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg c) _).2 (by
      change (u : Int) ≤ sp.slot (tr.time c)
      rw [hslot])
  have hlo : sp.ts s₀ ≤ tr.time c := hsu.trans huc
  have hsub : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts u + sp.Δ)
      floor kindJ J :=
    ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i hlo (by linarith),
      fun y hy i hlo hhi => hframe.kind_iff y hy i hlo (by linarith),
      fun y hy i hlo hhi hc => hframe.root_eq y hy i hlo (by linarith) hc⟩
  have hvP := (hsub.proposal_viable_at_cast hrun hnc hsvc hawake hf hcatch hnr
    (by linarith) (by omega) (by omega) (by linarith) hz hdes hP hPs hz hcast hes hstock).1
  rw [Compose.frame_of_projAC hrun hz hc] at hvP
  have hfl := hframe.floor_eq z hz c hlo (by linarith)
  have hh : (tr.state z c).fg.headHeightFloor ≤ ((tr.state z c).fg.σ P.root).h := hvP.2.2.2
  have hPm := (accept_of_proposesAt hrun hnc hz hP).2.1
  have hσ := σ_eq_honest hrun hnc hz hz hvP.1 hPm
  rw [hσ, hfl] at hh
  exact hh

end Consensus.Goldilocks.Healing

end
