module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Pool evidence after timely processing

A compromised voter can fill both of its pool places before its genuine vote arrives.
Processing therefore gives membership or equivocation evidence, and both survive until
the joined updater's read. No honesty of the voter after its cast is used.
-/

namespace Consensus.Goldilocks.Simulation

open SA (SAParams ReplayOrder)

private theorem pool_evidence_at_update {sp : SAParams} {FGP : Type}
    {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)}
    {tr : SA.SATrace sp FGP ro} (hr : ACLocalRun (SA.goldilocksSA sp FGP ro) H U tr)
    {w : Fin sp.n} (hw : w ∈ H) {c m : Nat} {ℓ}
    (hu : SA.UpdateAt tr w c m ℓ) {k : Nat} {v : SA.Vote sp.n}
    (hkc : k ≤ c) (hlo : sp.ts m ≤ tr.time k)
    (hhi : tr.time k < sp.ts m + 2 * sp.Δ)
    (hp : tr.ProcessAt w k v) (hslot : v.slot = m) :
    v ∈ (tr.state w c).pool m ∨
      v.val ∈ SA.equivocators {a | a ∈ (tr.state w c).pool m} := by
  have hΔ := sp.toParams.hΔ
  have htc : tr.time c = sp.ts m + 6 * sp.Δ := hu.2.2.1
  have hkc' : k < c := lt_of_le_of_ne hkc (by rintro rfl; linarith)
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hsk : sp.slot (tr.time k) = m :=
    SA.slot_of_mem sp m hlo (by rw [hts]; linarith)
  have hrs := Compose.update_restarts hr hw hu
  have hnr : ∀ r, k + 1 ≤ r → r < c → ¬ tr.RestartAt w r := by
    rintro r hrk hrc ⟨ℓr, hcr, hrr⟩
    obtain ⟨u, -, hu', -, hprev⟩ := hr.sleep_of_restart w hw r ℓr hcr hrr
    obtain ⟨ℓ', hc', -⟩ := hp
    have h₁ := hprev k (by omega) ℓ' hc'
    have h₂ := hrs r hrc.le ⟨ℓr, hcr, hrr⟩
    linarith
  have hm := SA.pool_mono hr hw (show k + 1 ≤ c by omega) hnr m
  rcases SA.held_of_processAt hr hw hp (by rw [hslot, hsk]; omega)
      (by rw [hslot, hsk]) with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · exact Or.inl (hm (hslot ▸ h))
  · exact Or.inr ⟨a, hm (hslot ▸ ha), b, hm (hslot ▸ hb), hab, hav, hbv⟩

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

private theorem pool_evidence_at_update_at (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {w : Fin (Fintype.card V)} {c m : Nat} {ℓ}
    (hw : w ∈ honestKeysAt S rho ((simTraceAt S rho hn).time c))
    (hu : SA.UpdateAt (simTraceAt S rho hn).projAC w c m ℓ)
    {k : Nat} {v : SA.Vote (Fintype.card V)} (hkc : k ≤ c)
    (hlo : (S.params (pubOf E) hn).ts m ≤ (simTraceAt S rho hn).time k)
    (hhi : (simTraceAt S rho hn).time k <
      (S.params (pubOf E) hn).ts m + 2 * (S.params (pubOf E) hn).Δ)
    (hp : (simTraceAt S rho hn).projAC.ProcessAt w k v) (hslot : v.slot = m) :
    v ∈ ((simTraceAt S rho hn).state w c).ac.pool m ∨
      v.val ∈ SA.equivocators {a | a ∈ ((simTraceAt S rho hn).state w c).ac.pool m} := by
  let tr := simTraceAt S rho hn
  have hr := simTraceAt_goldilocksRun S rho hn hv
  have hprefix := hr.upTo (hr.time_nonneg c)
  have hac := (Compose.goldilocks_ac_projection _ _ _ _ _ _ hprefix
    (hnc.upTo (tr.time c))).localRun
  have hs (j : Nat) (hj : j ≤ c) :
      ((tr.upTo (tr.time c)).projAC.state w j) = (tr.state w j).ac := by
    rw [Compose.projAC_state hprefix.toLocalRun hw,
      Trace.upTo_state tr w (fun q hq => hr.time_mono (hq.le.trans hj))]
  have hsorig : tr.projAC.state w c = (tr.state w c).ac := by
    have he := hs c le_rfl
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC w
      (fun q hq => hr.time_mono hq.le)] at he
    exact he
  have huc : SA.UpdateAt (tr.upTo (tr.time c)).projAC w c m ℓ := by
    refine ⟨Compose.projAC_callAt.mpr ((Trace.upTo_callAt tr).mpr
      ⟨le_rfl, Compose.projAC_callAt.mp hu.1⟩), hu.2.1, hu.2.2.1, ?_⟩
    change SA.joined _ _ (tr.time c)
    rw [hs c le_rfl, ← hsorig]
    exact hu.2.2.2
  have hpc : (tr.upTo (tr.time c)).projAC.ProcessAt w k v := by
    obtain ⟨l, hc, hm⟩ := hp
    exact ⟨l, Compose.projAC_callAt.mpr ((Trace.upTo_callAt tr).mpr
      ⟨hr.time_mono hkc, Compose.projAC_callAt.mp hc⟩), hm⟩
  have he := pool_evidence_at_update (tr := (tr.upTo (tr.time c)).projAC)
    hac hw huc hkc hlo hhi hpc hslot
  simpa only [hs c le_rfl] using he

/-- A slot vote reaches a joined updater as the vote itself or as evidence that its
validator equivocated. Honesty at the cast does not prohibit later forged votes. -/
theorem outage_pool_delivery_at (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {g : Time}
    (hnet : rho.log.PSync rho.point g) :
    ∀ w c m ℓ, w ∈ honestKeysAt S rho ((simTraceAt S rho hn).time c) →
      SA.UpdateAt (simTraceAt S rho hn).projAC w c m ℓ →
      g ≤ (S.params (pubOf E) hn).ts m + (S.params (pubOf E) hn).Δ →
      ∀ x i e, x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
        SA.VoteAt (simTraceAt S rho hn).projAC x i e → e.msg.slot = m →
        e.msg ∈ ((simTraceAt S rho hn).state w c).ac.pool m ∨
          e.msg.val ∈ SA.equivocators {v | v ∈ ((simTraceAt S rho hn).state w c).ac.pool m} := by
  intro w c m ℓ hw hu hstop x i e hx hvote hes
  let tr := simTraceAt S rho hn
  let sp := S.params (pubOf E) hn
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have htc : tr.time c = sp.ts m + 6 * sp.Δ := hu.2.2.1
  have hprefix := hrun.upTo (hrun.time_nonneg c)
  have hr := (Compose.goldilocks_ac_projection _ _ _ _ _ _ hprefix
    (hnc.upTo (tr.time c))).localRun
  have hstate : (tr.upTo (tr.time c)).projAC.state w c = tr.projAC.state w c := by
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC w
      (fun q hq => hrun.time_mono hq.le)]
  have hu' : SA.UpdateAt (tr.upTo (tr.time c)).projAC w c m ℓ := by
    refine ⟨Compose.projAC_callAt.mpr ((Trace.upTo_callAt tr).mpr
      ⟨le_rfl, Compose.projAC_callAt.mp hu.1⟩), hu.2.1, hu.2.2.1, ?_⟩
    change SA.joined _ _ (tr.time c)
    rw [hstate]
    exact hu.2.2.2
  have hrsy : ∀ r ≤ c, tr.RestartAt w r → tr.time r ≤ sp.ts m := by
    intro r hrc hrs
    exact Compose.update_restarts hr hw hu' r hrc
      (Compose.projAC_restartAt.mpr ((RunTrace.upTo_restartAt tr).mpr
        ⟨hrun.time_mono hrc, hrs⟩))
  have hprefixX := hrun.upTo (hrun.time_nonneg i)
  have hrx := (Compose.goldilocks_ac_projection _ _ _ _ _ _ hprefixX
    (hnc.upTo (tr.time i))).localRun
  have hv' : SA.VoteAt (tr.upTo (tr.time i)).projAC x i e := by
    obtain ⟨l, hc, he⟩ := hvote
    exact ⟨l, Compose.projAC_callAt.mpr ((Trace.upTo_callAt tr).mpr
      ⟨le_rfl, Compose.projAC_callAt.mp hc⟩), he⟩
  have hsl := (SA.vote_signer_slot hrx hx hv').2
  have hτ := SA.vote_time_le hrx hx hv'
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hτ
  change e.msg.slot = sp.slot (tr.time i) at hsl
  rw [← hsl, hes] at hτ
  have hmτ : sp.ts m ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) m).mpr (by rw [← hsl, hes])
  have hdl : ∀ k ≤ c, tr.deadline w k (max (tr.time i) g) sp.Δ ≤ sp.ts m + 2 * sp.Δ := by
    intro k hk
    have h := Compose.deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr')
      (max (tr.time i) g) sp.Δ
    have h₁ : max (max (tr.time i) g) (sp.ts m) ≤ sp.ts m + sp.Δ :=
      max_le (max_le hτ hstop) (by linarith)
    linarith
  have hj : tr.IsCall w c := ⟨_, Compose.projAC_callAt.mp hu.1⟩
  have hb : tr.time c ≤ rho.horizon := by
    obtain ⟨l, hl⟩ := hj
    change (simTraceAt S rho hn).time c ≤ rho.horizon
    rw [simTraceAt_eq]
    exact simTrace_labelled_time_le S rho hn hv (by rw [← simTraceAt_eq, hl.2]; simp)
  have hi : tr.SendOrAdmitAt x i e.msg := by
    obtain ⟨l, hc, he⟩ := hvote
    exact ⟨l, Compose.projAC_callAt.mp hc, Or.inl ⟨e, he, rfl⟩⟩
  obtain ⟨k, hkc, hik, hp, hkdl⟩ := Obligations.Growing.message_service_psync_at S rho hn hv
    hnet hx hi hw hj hb (by linarith [hdl c le_rfl])
  have hpA : tr.projAC.ProcessAt w k e.msg := by
    rcases hp with ⟨l, hc, hm⟩ | ⟨l, hc, hm⟩
    · exact ⟨l, Compose.projAC_callAt.mpr hc, Or.inl hm⟩
    · exact ⟨l, Compose.projAC_callAt.mpr hc, Or.inr hm⟩
  exact pool_evidence_at_update_at S rho hn hv hnc hw hu hkc (hmτ.trans hik)
    (hkdl.trans_le (hdl k hkc)) hpA hes

end Consensus.Goldilocks.Simulation
