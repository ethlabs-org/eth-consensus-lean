module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Cache
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Recovery: a finalizing carrier covers every later honest cache (C1.3, C5)

`coverage_of_finalizing_carrier`: an honest acceptance of a carrier `X` at a time in `[g, D)`
whose replay-finalized block `F_x` extends a high honest proposal `P` puts `P` below the `Σ.F`
of every honest node at every call from `D + Δ` on, and so makes `Σ.F` high there
(`HighFinalityFrom (D + Δ)`).

At such a call, FG safety compares `F_x` with the reader's `Σ.F` (`replay_finalized_safety`). If
`F_x ⪯ Σ.F` we are done. Otherwise `Σ.F ⪯ F_x ⪯ X`, so the acceptance relay of `GST(g)` applies:
the reader accepted `X` at an earlier cut, strictly before the deadline `time(k_X) + Δ ≤ D + Δ`
(no honest restart after `ḡ`, `restart_le_gbar`), and that acceptance cached `F_x`
(`accepted_finality_cached`, HR.5's FG-level form). Acceptance is the actual relayed one; no
delivery is turned into acceptance. -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- **No honest restart after `ḡ`** (`Healthy(g)`): a restart follows a time `u` at which the
node was asleep, so `u < ḡ`; the wake after `u` is a restart at or before `ḡ`, and it is a call
after `u`, so it is the restart itself. -/
theorem restart_le_gbar (hp : ResetPremises tr H proposer dg g ΔF a) :
    NoRestartAfter tr H (gbar g) := by
  intro y hy w hw
  obtain ⟨u, hu0, -, hus, hprev⟩ := hp.run.sleep_of_restart y hy w hw
  have hug : u < gbar g := by
    by_contra h
    exact hus (hp.healthy.2.1 y hy u (not_lt.1 h))
  obtain ⟨k', hk', huk', hk'g⟩ := hp.run.restart_at_wake y hy u (gbar g) hu0 hug hus
    (hp.healthy.2.1 y hy _ le_rfl)
  by_contra hwg
  have hk'w : k' < w := by
    by_contra h
    have := hp.run.time_mono (not_lt.1 h)
    linarith [not_le.1 hwg]
  obtain ⟨ℓ, hc, -⟩ := hk'
  have := hprev k' hk'w ⟨_, hc⟩
  linarith

/-- The deadline at an honest node of an object of time `τ ≥ ḡ` is `τ + Δ'`. -/
theorem deadline_le_of_gbar (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n}
    (hy : y ∈ H) (k : Nat) {τ : Time} (hτ : gbar g ≤ τ) (Δ' : Time) :
    tr.deadline y k τ Δ' ≤ τ + Δ' := by
  have h := deadline_le_restarts (T := tr.projAC) (c := k)
    (fun k' _ hk' => restart_le_gbar hp y hy k' (Compose.projAC_restartAt.1 hk')) τ
  simp only [ACTrace.deadline, RunTrace.deadline, Compose.projAC_lastWake] at h ⊢
  rw [max_eq_left hτ] at h
  linarith

/-- **C5: a finalizing carrier covers every later honest cache.** -/
theorem coverage_of_finalizing_carrier (hp : ResetPremises tr H proposer dg g ΔF a)
    {q : Fin sp.n} {iP : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hq : q ∈ H) (hP : tr.AcceptAt q iP P)
    (hPh : HZ tr H g + 1 ≤ ((tr.post iP).fg.σ P.root).h)
    {x : Fin sp.n} {kX : Nat} {X Fx : SA.Blk sp.n (List (FG.Att sp.n))} {D : Time}
    (hx : x ∈ H) (hX : tr.AcceptAt x kX X)
    (hFx : Fx ∈ (tr.post kX).fg.tree)
    (hroot : Fx.root = ((tr.post kX).fg.σ X.root).F)
    (hPF : Anc (tr.HonestBlocks H) P Fx)
    (hgX : g ≤ tr.time kX) (hXD : tr.time kX < D) (_hgD : gbar g ≤ D) :
    (∀ y ∈ H, ∀ k, tr.IsCall y k → D + sp.Δ ≤ tr.time k →
      Anc (tr.HonestBlocks H) P (tr.state y k).fg.F) ∧
    HighFinalityFrom tr H g (D + sp.Δ) := by
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have hfg := Compose.fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hp.run.genesis_root_ok hp.run.toLocalRun hp.noColl
  have hst : ∀ {z}, z ∈ H → ∀ i, tr.projFG.store z i = (tr.state z i).fg :=
    fun hz i => by simp only [FGTrace.store, Compose.projFG_state hp.run.toLocalRun hz i]
  have hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
    have hf := hp.healthy.2.2
    have hn := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    omega
  have hU := honest_coherent hp
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hsub : ∀ {z}, z ∈ H → ∀ i, (tr.state z i).fg.tree ⊆ tr.HonestBlocks H :=
    fun hz i X hX => ⟨_, hz, i, hX⟩
  have accept_mem : ∀ {z k B}, z ∈ H → tr.AcceptAt z k B → B ∈ (tr.state z (k + 1)).fg.tree :=
    fun {z k B} hz h => by
      rw [tr.state_succ_of_call h, (Store.tree_grows _ _ _ _
        (Compose.fg_reachable hp.run.toLocalRun hz k)).1 B _ (hp.run.cutLaw z hz k _ h).2.1]
      exact Set.mem_insert _ _
  -- the carrier's store after its acceptance: `F_x ⪯ X`
  have hpostX : tr.post kX = tr.state x (kX + 1) := (tr.state_succ_of_call hX).symm
  rw [hpostX] at hFx hroot
  have hXm := accept_mem hx hX
  have hRx := Compose.fg_reachable hp.run.toLocalRun hx (kX + 1)
  have hFxX : Anc (tr.HonestBlocks H) Fx X := by
    obtain ⟨-, ⟨X', hX', hX'r, hXB⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hRx X hXm
    obtain rfl : X' = Fx := hU.1 (hsub hx _ hX') (hsub hx _ hFx) (hX'r.trans hroot.symm)
    exact hXB.mono (hsub hx _)
  have hgk : gbar g ≤ tr.time kX := max_le hgX (hp.run.time_nonneg kX)
  have cover : ∀ y ∈ H, ∀ k, tr.IsCall y k → D + sp.Δ ≤ tr.time k →
      Anc (tr.HonestBlocks H) P (tr.state y k).fg.F := by
    intro y hy k hc ht
    have hcomp := Store.replay_finalized_safety hfg hf hx hy (i := kX + 1) (j := k)
      (by rw [hst hx]; exact hXm) (by rw [hst hx]; exact hFx) (by rw [hst hx]; exact hroot)
    rw [hst hy] at hcomp
    rcases hcomp with hFxF | hFFx
    · exact hPF.trans hFxF
    -- the reader's `Σ.F` is below the carrier: the relay delivers an actual acceptance
    have hrel := hp.healthy.1.relay x hx kX X hX hgX y hy k hc (by
        rw [max_eq_left hgX]
        have := deadline_le_of_gbar hp hy k hgk sp.Δ
        linarith) (hFFx.trans hFxX)
    obtain ⟨k', hk'k, hacc, hk't⟩ := hrel
    rw [max_eq_left hgX] at hk't
    have hk'lt : k' < k := by
      by_contra h
      obtain rfl : k' = k := le_antisymm hk'k (not_lt.1 h)
      have := deadline_le_of_gbar hp hy k' hgk sp.Δ
      linarith
    have hXy := accept_mem hy hacc
    have hFxy := mem_tree_of_anc hp hy hFxX hXy
    have hcache := accepted_finality_cached hfg hf hy (Compose.projFG_callAt.mpr hacc)
      (by rw [hst hy]; exact hFxy)
      (by rw [hst hy, σ_eq_run hp hy hx hXy hXm]; exact hroot)
    rw [hst hy] at hcache
    exact hPF.trans ((hcache.mono (hsub hy _)).trans
      (Healing.run_F_mono hp.run.toLocalRun hy hk'lt))
  refine ⟨cover, ⟨fun y hy k hc ht => ?_⟩⟩
  have hPFy := cover y hy k hc ht
  have hRy := Compose.fg_reachable hp.run.toLocalRun hy k
  have hFm := (Store.cache_invariants _ _ _ _ hRy).1
  have hPy := mem_tree_of_anc hp hy hPFy hFm
  have hpostP : tr.post iP = tr.state q (iP + 1) := (tr.state_succ_of_call hP).symm
  rw [hpostP, ← σ_eq_run hp hy hq hPy (accept_mem hq hP)] at hPh
  exact hPh.trans (σ_h_le_of_anc hRy (anc_tree_of_anc hp hy hPFy hFm))

end Consensus.Goldilocks.Healing.Recovery

end
