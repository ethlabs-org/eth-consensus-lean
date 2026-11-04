module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen

public section

/-! # Goldilocks Obligations: the outage reader's network inputs (O4, cut 1)

Workbench `notes/outage/outage_reader_bridge.md` §10.4 (rev 4.3), cut 1. `outage_psync` is the
engine's partial synchrony from the outage's end `b₁ = Q.stop`. `outage_pool_delivery` is the pool
delivery `OutageLockOthers.pg` consumes: an honest slot-`m` vote is in the pool of every honest
updater of slot `m` with `b₁ ≤ t_m + Δ`. The vote is cast in `[t_m, t_m + Δ]`, delivered under
PSync from `b₁` by `max(τ, b₁) + Δ ≤ t_m + 2Δ`, before the update at `t_m + 6Δ`, and kept: the
updater does not restart after `t_m`. No vote head, frame or voter tree is read. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- PSync from the outage's GST on the engine log (wrapper erasure, as `outage_pre_service`). -/
theorem outage_psync (Q : OutageQuery S A V) : Q.run.2.log.PSync Q.run.2.point Q.stop :=
  (Model.sysOf_delivers_iff _ _ _ _).mp Q.outage.2.1.2

/-- PG for the lock module (`OutageLockOthers.pg`). -/
theorem outage_pool_delivery (Q : OutageQuery S A V) :
    ∀ w ∈ honestKeys S Q.run.2, ∀ c m ℓ, SA.UpdateAt Q.trace.projAC w c m ℓ →
      Q.stop ≤ Q.params.ts m + Q.params.Δ →
      ∀ x ∈ honestKeys S Q.run.2, ∀ i e, SA.VoteAt Q.trace.projAC x i e → e.msg.slot = m →
        e.msg ∈ (Q.trace.state w c).ac.pool m := by
  intro w hw c m ℓ hu hstop x hx i e hv hes
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hrun' := Compose.goldilocks_ac_projection _ _ _ _ _ _ hrun
    (noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision)
  have hr := hrun'.localRun
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hts : Q.params.ts (m + 1 : Nat) = Q.params.ts m + 4 * Q.params.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  -- 1. the updater's restarts up to `c` are at or before `t_m`
  have hrsy := Compose.update_restarts hr hw hu
  have htc : Q.trace.time c = Q.params.ts m + 6 * Q.params.Δ := hu.2.2.1
  -- 2. the vote is `x`'s, cast at `τ ∈ [t_m, t_m + Δ]`
  have hsl := (SA.vote_signer_slot hr hx hv).2
  have hτ := SA.vote_time_le hr hx hv
  rw [← hsl, hes] at hτ
  have hmτ : Q.params.ts m ≤ Q.trace.time i :=
    (SA.ts_le_iff_le_slot Q.params (hr.time_nonneg i) m).2 (by rw [← hsl, hes])
  -- 3. delivery deadlines at the updater, up to cut `c`
  have hdl : ∀ k ≤ c, Q.trace.deadline w k (max (Q.trace.time i) Q.stop) Q.params.Δ ≤
      Q.params.ts m + 2 * Q.params.Δ := by
    intro k hk
    have h := Compose.deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) (Compose.projAC_restartAt.mpr hr'))
      (max (Q.trace.time i) Q.stop) Q.params.Δ
    have h₁ : max (max (Q.trace.time i) Q.stop) (Q.params.ts m) ≤
        Q.params.ts m + Q.params.Δ :=
      max_le (max_le hτ hstop) (by linarith)
    linarith
  -- 4. delivery under PSync from `b₁`
  have hj : Q.trace.IsCall w c := ⟨_, Compose.projAC_callAt.mp hu.1⟩
  have hb : Q.trace.time c ≤ Q.run.2.horizon := by
    obtain ⟨l, hl⟩ := hj
    exact simTrace_labelled_time_le S Q.run.2 Q.hn Q.valid (by rw [hl.2]; simp)
  have hi : Q.trace.SendOrAdmitAt x i e.msg := by
    obtain ⟨ℓx, hcx, hex⟩ := hv
    exact ⟨ℓx, Compose.projAC_callAt.mp hcx, Or.inl ⟨e, hex, rfl⟩⟩
  obtain ⟨k, hkc, hik, hp, hkdl⟩ := message_service_psync S Q.run.2 Q.hn Q.valid
    (outage_psync S A V Q) hx hi hw hj hb (by linarith [hdl c le_rfl])
  have hk_lt : Q.trace.time k < Q.params.ts m + 2 * Q.params.Δ :=
    hkdl.trans_le (hdl k hkc)
  have hkc' : k < c := lt_of_le_of_ne hkc (by rintro rfl; linarith)
  have hsk : Q.params.slot (Q.trace.time k) = m :=
    SA.slot_of_mem Q.params m (hmτ.trans hik) (by rw [hts]; linarith)
  have hpA : Q.trace.projAC.ProcessAt w k e.msg := by
    rcases hp with ⟨l, hcl, hm⟩ | ⟨l, hcl, hm⟩
    · exact ⟨l, Compose.projAC_callAt.mpr hcl, Or.inl hm⟩
    · exact ⟨l, Compose.projAC_callAt.mpr hcl, Or.inr hm⟩
  -- 5. the vote is held after `k` and kept to `c` (pool block of `Batch.lean`)
  have hnr : ∀ r, k + 1 ≤ r → r < c + 1 → ¬ Q.trace.projAC.RestartAt w r := by
    rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
    obtain ⟨u, -, hu', -, hprev⟩ := hr.sleep_of_restart w hw r ℓr hcr hrr
    obtain ⟨ℓ', hc', -⟩ := hpA
    have h₁ := hprev k (by omega) ℓ' hc'
    have h₂ := hrsy r (by omega) ⟨ℓr, hcr, hrr⟩
    change Q.trace.time k < _ at h₁
    linarith
  have hskA : Q.params.slot (Q.trace.projAC.time k) = m := hsk
  have hpk : e.msg ∈ (Q.trace.projAC.state w (k + 1)).pool m := by
    rcases SA.held_of_processAt hr hw hpA (by rw [hes, hskA]; omega) (by rw [hes, hskA]) with
      h | ⟨a, ha, b, hb', hab, hav, hbv⟩
    · rwa [hes] at h
    · rw [hes] at ha hb'
      have hxv := (SA.vote_signer_slot hr hx hv).1
      obtain ⟨ja, -, ea, hea, hea'⟩ :=
        hrun'.honest.pool_vote w hw _ m a ha (by rw [hav, hxv]; exact hx)
      obtain ⟨jb, -, eb, heb, heb'⟩ :=
        hrun'.honest.pool_vote w hw _ m b hb' (by rw [hbv, hxv]; exact hx)
      rw [hav, hxv] at hea
      rw [hbv, hxv] at heb
      obtain ⟨-, rfl⟩ := SA.one_vote_per_slot _ _ _ _ _ _ hr x hx ja jb ea eb hea heb
        (by rw [hea', heb', SA.state_pool_slot _ hr hw _ m a ha,
          SA.state_pool_slot _ hr hw _ m b hb'])
      exact absurd (hea'.symm.trans heb') hab
  have hpool : e.msg ∈ (Q.trace.projAC.state w c).pool m :=
    SA.pool_mono hr hw (show k + 1 ≤ c by omega) (fun r h₁ h₂ => hnr r h₁ (by omega)) m hpk
  rwa [Compose.projAC_state hrun.toLocalRun hw] at hpool

end Consensus.Goldilocks.Obligations

end
