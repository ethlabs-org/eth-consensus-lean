module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Pool evidence after timely processing

A compromised voter can fill both of its pool places before its genuine vote arrives.
Processing therefore gives membership or equivocation evidence, and both survive until
the joined updater's read. No honesty of the voter after its cast is used.
-/

namespace Consensus.Goldilocks.Simulation

open AC (ACParams ReplayOrder)

private theorem pool_evidence_at_update {sp : ACParams} {FGP : Type}
    {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (AC.Blk sp.n FGP)}
    {tr : AC.GTrace sp FGP ro} {ini : Fin sp.n → AC.ACState sp.n}
    (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    {w : Fin sp.n} (hw : w ∈ H) {c m : Nat} {ℓ}
    (hu : AC.UpdateAt tr w c m ℓ) {k : Nat} {v : AC.Vote sp.n}
    (hkc : k ≤ c) (hlo : sp.ts m ≤ tr.time k)
    (hhi : tr.time k < sp.ts m + 2 * sp.Δ)
    (hp : tr.ProcessAt w k v) (hslot : v.slot = m) :
    v ∈ (tr.state w c).pool m ∨
      v.val ∈ AC.equivocators {a | a ∈ (tr.state w c).pool m} := by
  have hΔ := sp.toParams.hΔ
  have htc : tr.time c = sp.ts m + 6 * sp.Δ := hu.2.2.1
  have hkc' : k < c := lt_of_le_of_ne hkc (by rintro rfl; linarith)
  have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hsk : sp.slot (tr.time k) = m :=
    AC.slot_of_mem sp m hlo (by rw [hts]; linarith)
  have hrs := Compose.update_restarts hr hw hu
  have hnr : ∀ r, k + 1 ≤ r → r < c → ¬ tr.RestartAt w r := by
    rintro r hrk hrc ⟨ℓr, hcr, hrr⟩
    obtain ⟨u, -, hu', -, hprev⟩ := hr.sleep_of_restart w hw r ℓr hcr hrr
    obtain ⟨ℓ', hc', -⟩ := hp
    have h₁ := hprev k (by omega) ℓ' hc'
    have h₂ := hrs r hrc.le ⟨ℓr, hcr, hrr⟩
    linarith
  have hm := AC.pool_mono hr hw (show k + 1 ≤ c by omega) hnr m
  rcases AC.held_of_processAt hr hw hp (by rw [hslot, hsk]; omega)
      (by rw [hslot, hsk]) with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · exact Or.inl (hm (hslot ▸ h))
  · exact Or.inr ⟨a, hm (hslot ▸ ha), b, hm (hslot ▸ hb), hab, hav, hbv⟩

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

private theorem pool_evidence_at_update_at (hr : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {w : Fin sp.n} {c m : Nat} {ℓ}
    (hw : w ∈ H (tr.time c))
    (hu : AC.UpdateAt tr.projAC w c m ℓ)
    {k : Nat} {v : AC.Vote sp.n} (hkc : k ≤ c)
    (hlo : sp.ts m ≤ tr.time k)
    (hhi : tr.time k < sp.ts m + 2 * sp.Δ)
    (hp : tr.projAC.ProcessAt w k v) (hslot : v.slot = m) :
    v ∈ (tr.state w c).ac.pool m ∨
      v.val ∈ AC.equivocators {a | a ∈ (tr.state w c).ac.pool m} := by
  have hprefix := hr.upTo (hr.time_nonneg c)
  have hac := Compose.ac_projection _ _ _ _ _ _ _
    (fun y _ U _ s Φ t₀ h =>
      AC.proposal_payload_valid_from _ (hr.vstart y).pool y U s Φ t₀ h)
    hprefix.toLocalRun (hnc.upTo (tr.time c))
  have hs (j : Nat) (hj : j ≤ c) :
      ((tr.upTo (tr.time c)).projAC.state w j) = (tr.state w j).ac := by
    rw [Compose.projAC_state hprefix.toLocalRun hw,
      Trace.upTo_state tr w (fun q hq => hr.time_mono (hq.le.trans hj))]
  have hsorig : tr.projAC.state w c = (tr.state w c).ac := by
    have he := hs c le_rfl
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC w
      (fun q hq => hr.time_mono hq.le)] at he
    exact he
  have huc : AC.UpdateAt (tr.upTo (tr.time c)).projAC w c m ℓ := by
    refine ⟨Compose.projAC_callAt.mpr ((Trace.upTo_callAt tr).mpr
      ⟨le_rfl, Compose.projAC_callAt.mp hu.1⟩), hu.2.1, hu.2.2.1, ?_⟩
    change AC.joined _ _ (tr.time c)
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
validator equivocated, on any Goldilocks run. Honesty at the cast does not prohibit later forged
votes. The only network input is the message service of post-stop service. -/
theorem outage_pool_delivery_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time} (hs : Generic.PostStopService tr H g) :
    ∀ w c m ℓ, w ∈ H (tr.time c) → AC.UpdateAt tr.projAC w c m ℓ →
      g ≤ sp.ts m + sp.Δ →
      ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = m →
        e.msg ∈ (tr.state w c).ac.pool m ∨
          e.msg.val ∈ AC.equivocators {v | v ∈ (tr.state w c).ac.pool m} := by
  intro w c m ℓ hw hu hstop x i e hx hvote hes
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have htc : tr.time c = sp.ts m + 6 * sp.Δ := hu.2.2.1
  have hprefix := hrun.upTo (hrun.time_nonneg c)
  have hr := Compose.ac_projection _ _ _ _ _ _ _
    (fun y _ U _ s Φ t₀ h =>
      AC.proposal_payload_valid_from _ (hrun.vstart y).pool y U s Φ t₀ h)
    hprefix.toLocalRun (hnc.upTo (tr.time c))
  have hstate : (tr.upTo (tr.time c)).projAC.state w c = tr.projAC.state w c := by
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC w
      (fun q hq => hrun.time_mono hq.le)]
  have hu' : AC.UpdateAt (tr.upTo (tr.time c)).projAC w c m ℓ := by
    refine ⟨Compose.projAC_callAt.mpr ((Trace.upTo_callAt tr).mpr
      ⟨le_rfl, Compose.projAC_callAt.mp hu.1⟩), hu.2.1, hu.2.2.1, ?_⟩
    change AC.joined _ _ (tr.time c)
    rw [hstate]
    exact hu.2.2.2
  have hrsy : ∀ r ≤ c, tr.RestartAt w r → tr.time r ≤ sp.ts m := by
    intro r hrc hrs
    exact Compose.update_restarts hr hw hu' r hrc
      (Compose.projAC_restartAt.mpr ((RunTrace.upTo_restartAt tr).mpr
        ⟨hrun.time_mono hrc, hrs⟩))
  have hprefixX := hrun.upTo (hrun.time_nonneg i)
  have hrx := Compose.ac_projection _ _ _ _ _ _ _
    (fun y _ U _ s Φ t₀ h =>
      AC.proposal_payload_valid_from _ (hrun.vstart y).pool y U s Φ t₀ h)
    hprefixX.toLocalRun (hnc.upTo (tr.time i))
  have hv' : AC.VoteAt (tr.upTo (tr.time i)).projAC x i e := by
    obtain ⟨l, hc, he⟩ := hvote
    exact ⟨l, Compose.projAC_callAt.mpr ((Trace.upTo_callAt tr).mpr
      ⟨le_rfl, Compose.projAC_callAt.mp hc⟩), he⟩
  have hsl := (AC.vote_signer_slot hrx hx hv').2
  have hτ := AC.vote_time_le hrx hx hv'
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hτ
  change e.msg.slot = sp.slot (tr.time i) at hsl
  rw [← hsl, hes] at hτ
  have hmτ : sp.ts m ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) m).mpr (by rw [← hsl, hes])
  have hdl : ∀ k ≤ c, tr.deadline w k (max (tr.time i) g) sp.Δ ≤ sp.ts m + 2 * sp.Δ := by
    intro k hk
    have h := Compose.deadline_le_of_restarts
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr')
      (max (tr.time i) g) sp.Δ
    have h₁ : max (max (tr.time i) g) (sp.ts m) ≤ sp.ts m + sp.Δ :=
      max_le (max_le hτ hstop) (by linarith)
    linarith
  have hj : tr.IsCall w c := ⟨_, Compose.projAC_callAt.mp hu.1⟩
  have hi : tr.SendOrAdmitAt x i e.msg := by
    obtain ⟨l, hc, he⟩ := hvote
    exact ⟨l, Compose.projAC_callAt.mp hc, Or.inl ⟨e, he, rfl⟩⟩
  obtain ⟨k, hkc, hik, hp, hkdl⟩ := hs.message x i e.msg hx hi w c hw hj
    (by linarith [hdl c le_rfl])
  have hpA : tr.projAC.ProcessAt w k e.msg := by
    rcases hp with ⟨l, hc, hm⟩ | ⟨l, hc, hm⟩
    · exact ⟨l, Compose.projAC_callAt.mpr hc, Or.inl hm⟩
    · exact ⟨l, Compose.projAC_callAt.mpr hc, Or.inr hm⟩
  exact pool_evidence_at_update_at hrun hnc hw hu hkc (hmτ.trans hik)
    (hkdl.trans_le (hdl k hkc)) hpA hes

end Consensus.Goldilocks.Simulation
