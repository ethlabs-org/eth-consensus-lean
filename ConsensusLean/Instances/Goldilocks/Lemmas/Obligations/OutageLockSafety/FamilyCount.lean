module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Observation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FamilyFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage counts over family observations

Pool provenance and slot typing need execution. Frame containment and the counting
argument do not. Keep those responsibilities separate, rather than assuming an SA run.
-/

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload Vote SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

/-- Pool facts needed by the count consumers, stated over observations only. -/
structure PoolFacts (ac : SA.SATrace sp (List (FG.Att sp.n)) ro) (H : Set (Fin sp.n)) : Prop where
  slot : ∀ y ∈ H, ∀ i s, ∀ v ∈ (ac.state y i).pool s, v.slot = s
  honest : ∀ y ∈ H, ∀ i s, ∀ v ∈ (ac.state y i).pool s, v.val ∈ H →
    ∃ j < i, ∃ e, SA.VoteAt ac v.val j e ∧ e.msg = v

/-- The cast schedule, independent of locks and the chosen vote head. -/
def VoteTiming (ac : SA.SATrace sp (List (FG.Att sp.n)) ro) (H : Set (Fin sp.n)) : Prop :=
  ∀ x ∈ H, ∀ k e, SA.VoteAt ac x k e →
    sp.ts e.msg.slot ≤ ac.time k ∧ ac.time k ≤ sp.ts e.msg.slot + sp.Δ

/-- Only the head's membership is needed in the genesis branch. -/
def VoteHead (ac : SA.SATrace sp (List (FG.Att sp.n)) ro) (H : Set (Fin sp.n))
    (U : Set (SA.Blk sp.n (List (FG.Att sp.n)))) : Prop :=
  ∀ x ∈ H, ∀ k e, SA.VoteAt ac x k e → ∃ B ∈ U, B.root = e.msg.head

/-- The existing honest-head theorem supplies the weakest head-membership fact. -/
theorem voteHead_goldilocks {tr : GoldilocksTrace sp ro} (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) : VoteHead tr.projAC H (tr.HonestBlocks H) := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc
  intro x hx k e hv
  obtain ⟨B, hB, hBr, -⟩ := SA.honest_head hac hx hv
  exact ⟨B, hB, hBr⟩

/-- The ordinary cast specification discharges only the schedule fact. -/
theorem voteTiming_goldilocks {tr : GoldilocksTrace sp ro} (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) : VoteTiming tr.projAC H := by
  have hac := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc).localRun
  intro x hx k e hv
  obtain ⟨ℓ, hc, he⟩ := hv
  have hsl := (SA.castAt_spec hac hx ⟨hc, he⟩).2.1
  refine ⟨(SA.ts_le_iff_le_slot sp (hac.time_nonneg k) _).2 (by rw [hsl]), ?_⟩
  have ht := SA.vote_time_le hac hx ⟨ℓ, hc, he⟩
  rw [hsl]
  exact ht

/-- The concrete pool invariant and unforgeability discharge the observation facts. -/
theorem poolFacts_goldilocks {tr : GoldilocksTrace sp ro} (hr : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) : PoolFacts tr.projAC H := by
  have h := Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc
  exact ⟨fun _ hy => SA.state_pool_slot sp h.localRun hy, h.honest.pool_vote⟩

/-- Participation and delivery are milestone exits, not consequences of frame laws. -/
structure Participants (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) : Prop where
  vote : ∀ x ∈ H, ∀ s : Nat, tr.awake x (sp.ts s + sp.Δ) → tr.JoinedAt x (sp.ts s + sp.Δ) →
    ∃ k e, SA.VoteAt (F.proj tr.projAC) x k e ∧ e.msg.val = x ∧ e.msg.slot = s
  early : ∀ (s : Nat) (b : Time), SA.ServiceBefore H (tr.HonestBlocks H) b (F.proj tr.projAC) →
    sp.ts s + 2 * sp.Δ ≤ b → ∀ X ∈ H, ∀ i ℓ,
    SA.UpdateAt (F.proj tr.projAC) X i s ℓ → ∀ x ∈ H,
    tr.awake x (sp.ts s + sp.Δ) → tr.JoinedAt x (sp.ts s + sp.Δ) →
      x ∈ SA.voters {v | v ∈ ((F.proj tr.projAC).state X i).pool s}

/-- Goldilocks supplies the two existing participation milestones. -/
theorem participants_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    Participants (SA.goldilocksFamily sp _ ro) tr H := by
  constructor
  · intro x hx s hw hj
    obtain ⟨k, e, hv, hs, -⟩ := Compose.vote_of_awake_joined hr hnc hx hw hj
    obtain ⟨ℓ, hc, he⟩ := hv
    have hvx := (SA.castAt_spec
      (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc).localRun hx ⟨hc, he⟩).1
    exact ⟨k, e, ⟨ℓ, hc, he⟩, hvx, hs⟩
  · intro s b hsvc hb X hX i ℓ hu x hx hw hj
    exact Compose.awake_participant_early hr hnc hsvc hb hX hu hx hw hj

/-- A counted vote's provenance uses only pool facts and structural frame containment. -/
theorem counted_honest_vote_family (hr : FamilyRun F proposer dg H sg tr)
    (hp : PoolFacts (F.proj tr.projAC) H)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt (F.proj tr.projAC) X i₀ s C CV)
    {v : Vote sp.n} (hv : v ∈ CV) (hvH : v.val ∈ H) :
    ∃ j < i₀, ∃ e, SA.VoteAt (F.proj tr.projAC) v.val j e ∧ e.msg = v ∧ v.slot = s ∧
      ∃ R ∈ tr.HonestBlocks H, R.root = v.head ∧ Anc (tr.HonestBlocks H) C R := by
  obtain ⟨ℓ, hu, -, hCV⟩ := hR
  rw [hCV] at hv
  obtain ⟨hvp, -, -, R, hR, hRr, hCR⟩ := hv
  obtain ⟨j, hj, e, hve, he⟩ := hp.honest X hX i₀ s v hvp hvH
  obtain ⟨-, hΦU⟩ := hr.observation.frameIn hX hu.1
  exact ⟨j, hj, e, hve, he, hp.slot X hX i₀ s v hvp, R, hΦU hR, hRr,
    Anc.mono hΦU hCR⟩

/-- Result membership needs no step-law contract field. -/
theorem result_mem_family (hr : FamilyRun F proposer dg H sg tr)
    {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt (F.proj tr.projAC) X i₀ s C CV) :
    C ∈ tr.HonestBlocks H := by
  obtain ⟨ℓ, hu, hC, -⟩ := hR
  exact (hr.observation.frameIn hX hu.1).2 (SA.deepest_mem hC).1.1

/-- An ancestor of a compatible head is compatible, in any coherent universe. -/
theorem compatible_of_head_anc_family {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {C R B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hCR : Anc U C R) (hR : Compatible U R B) : Compatible U C B := by
  rcases hR with h | h
  · exact Or.inl (hCR.trans h)
  · exact Anc.total hU hCR h

/-- Vote compatibility reads only the head's root and ancestry. -/
theorem compatible_of_voteCompat_family {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {v : Vote sp.n} {C R B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ U) (hRr : R.root = v.head) (hCR : Anc U C R)
    (hv : Compose.VoteCompat U v B) : Compatible U C B := by
  obtain ⟨Hd, hHd, hHdr, hHdB⟩ := Compose.voteCompat_iff.1 hv
  obtain rfl : Hd = R := hU.1 hHd hR (hHdr.trans hRr.symm)
  exact compatible_of_head_anc_family hU hCR hHdB

/-- Ancestor compatibility is the same vocabulary-only argument. -/
theorem compatible_of_anc_family {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {L C B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hLC : Anc U L C) (hC : Compatible U C B) : Compatible U L B :=
  compatible_of_head_anc_family hU hLC hC

/-- The quorum intersection is vocabulary-only; the projected trace need not execute SA. -/
theorem exists_counted_of_participants_family {X : Fin sp.n} {i₀ s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt (F.proj tr.projAC) X i₀ s C CV) {T Q : Set (Fin sp.n)}
    (hT : T ⊆ SA.voters {v | v ∈ ((F.proj tr.projAC).state X i₀).pool s})
    (hQT : Q.ncard < T.ncard) : ∃ v ∈ CV, v.val ∈ T ∨ v.val ∉ Q := by
  by_contra hno
  push Not at hno
  have hmaj := SA.result_majority hR
  obtain ⟨ℓ, -, -, hCV⟩ := hR
  have hSV : {w | ∃ v ∈ CV, v.val = w} ⊆
      SA.voters {v | v ∈ ((F.proj tr.projAC).state X i₀).pool s} := by
    rintro w ⟨v, hv, rfl⟩
    rw [hCV] at hv
    exact ⟨v, hv.1, rfl⟩
  have hdisj : Disjoint T {w | ∃ v ∈ CV, v.val = w} :=
    Set.disjoint_left.2 fun w hwT ⟨v, hv, hvw⟩ => (hno v hv).1 (hvw ▸ hwT)
  have h1 := Set.ncard_union_eq hdisj
  have h2 := Set.ncard_le_ncard (Set.union_subset hT hSV)
  have h3 : {w | ∃ v ∈ CV, v.val = w}.ncard ≤ Q.ncard :=
    Set.ncard_le_ncard fun w ⟨v, hv, hvw⟩ => hvw ▸ (hno v hv).2
  omega

namespace OutageLockPremises

variable (D : OutageLockPremises F tr H proposer dg sg)

include D

/-- Coherence is observational, not an execution consequence. -/
theorem coherent : Coherent (tr.HonestBlocks H) := D.hrun.observation.coherent

/-- N6 uses only the cohort cardinalities. -/
theorem two_mul_lt : 2 * (Hᶜ ∪ D.W).ncard < sp.n := by
  have hdisj : Disjoint D.A₀ (Hᶜ ∪ D.W) := by
    rw [Set.disjoint_union_right]
    exact ⟨Set.disjoint_left.2 fun x hx hxc => hxc (D.hA₀ hx), D.hW.2⟩
  have h1 := Set.ncard_union_eq hdisj
  have h2 : (D.A₀ ∪ (Hᶜ ∪ D.W)).ncard ≤ sp.n := by
    calc (D.A₀ ∪ (Hᶜ ∪ D.W)).ncard ≤ (Set.univ : Set (Fin sp.n)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = sp.n := by simp
  have h3 := D.hcohort
  omega

theorem two_faults_lt : 2 * Hᶜ.ncard < sp.n :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 2
    (Set.ncard_le_ncard (show Hᶜ ⊆ Hᶜ ∪ D.W from Set.subset_union_left))) D.two_mul_lt

/-- The protected genesis block is below every honest block of the actual run. -/
theorem anc_of_genesis (hg : D.P.root = sp.genesisRoot)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ tr.HonestBlocks H) :
    Anc (tr.HonestBlocks H) D.P C := by
  obtain ⟨-, hgC⟩ := honest_genesis_anc D.hrun.toLocalRun hC
  obtain ⟨hgU, -⟩ := honest_genesis_anc D.hrun.toLocalRun D.hP.1
  have he : sp.toParams.genesisBlock A.genesisPayload = D.P :=
    D.coherent.1 hgU D.hP.1 (by rw [hg]; rfl)
  exact he ▸ hgC

/-- Compatibility with the protected origin only needs the prefix invariant. -/
theorem compatible_of {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ tr.HonestBlocks H)
    (h : OriginWithin F tr H D.P D.σ D.b₀ → Compatible (tr.HonestBlocks H) C D.P) :
    Compatible (tr.HonestBlocks H) C D.P := by
  rcases D.hP.2 with hg | hP
  · exact Or.inr (D.anc_of_genesis hg hC)
  · exact h hP

theorem compatible_of_within {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : OriginWithin F tr H C s D.b₀) (hCU : C ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) C D.P :=
  D.compatible_of hCU fun hP => D.hpre.origins_compatible C s D.P D.σ hC hP

/-- A genesis protected block is extended by any vote with an honest-universe head. -/
theorem vote_extends_of_genesis (hh : VoteHead (F.proj tr.projAC) H (tr.HonestBlocks H))
    (hg : D.P.root = sp.genesisRoot) {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt (F.proj tr.projAC) x k e) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  obtain ⟨B, hB, hBr⟩ := hh x hx k e hv
  exact ⟨B, hB, hBr, D.anc_of_genesis hg hB⟩

/-- Pre-outage vote extension is supplied by the prefix invariant or genesis. -/
theorem vote_extends_pre (hh : VoteHead (F.proj tr.projAC) H (tr.HonestBlocks H))
    {x : Fin sp.n} (hx : x ∈ H) {k : Nat} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.VoteAt (F.proj tr.projAC) x k e) (hk : tr.time k ≤ D.b₀)
    (hs : D.σ < e.msg.slot) : SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  rcases D.hP.2 with hg | hP
  · exact D.vote_extends_of_genesis hh hg hx hv
  · exact D.hpre.vote_extends D.P D.σ hP x hx k e hv hk hs

end OutageLockPremises

namespace OutageVoteInv

/-- Cohort readiness is entirely a fact about the actual run's wake and restart schedule. -/
theorem cohort_ready (D : OutageLockPremises F tr H proposer dg sg) {x : Fin sp.n}
    (hx : x ∈ D.A₀) {m : Nat} (hm : D.j₀ + 1 ≤ m) (hmK : m ≤ D.j₀ + sp.k)
    (hcall : ∃ y ∈ H, ∃ i, tr.IsCall y i ∧ sp.ts m + sp.Δ ≤ tr.time i) :
    tr.awake x (sp.ts m + sp.Δ) ∧ tr.JoinedAt x (sp.ts m + sp.Δ) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hj := Compose.ts_le_ts (sp := sp) (show D.j₀ ≤ m - 1 by omega)
  have hmK' := Compose.ts_le_ts (sp := sp) hmK
  have hm1 : sp.ts (m - 1 : Nat) + 4 * sp.Δ = sp.ts m := by
    simp only [SAParams.ts]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hz := D.hz (sp.ts m + sp.Δ) (by linarith) hcall
  refine ⟨D.hA₀awake x hx _ (by linarith [D.ha, sp.toParams.hΔ]) hz, fun k hk hkt => ?_⟩
  have hslot : sp.slot (sp.ts m + sp.Δ) = m :=
    SA.slot_of_mem sp m (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  change 0 < sp.slot (sp.ts m + sp.Δ) ∧
    tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts m + sp.Δ) - 1)
  rw [hslot, sp.slotTime_eq]
  refine ⟨by omega, ?_⟩
  have := (D.hA₀join x hx k hk (hkt.trans hz)).trans D.ha
  have h' : sp.ts (m - 1 : Nat) = 4 * sp.Δ * ((m - 1 : Nat) : Int) := rfl
  rw [← h']
  linarith

/-- The vote schedule transfers without a handler equality. -/
theorem ts_le_cast (_D : OutageLockPremises F tr H proposer dg sg)
    (ht : VoteTiming (F.proj tr.projAC) H) {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt (F.proj tr.projAC) x k e) :
    sp.ts e.msg.slot ≤ tr.time k ∧ tr.time k ≤ sp.ts e.msg.slot + sp.Δ := by
  simpa only [F.time, RunTrace.projAC] using ht x hx k e hv

/-- OL-W uses only the cast schedule, observed wakefulness and the vote invariant. -/
theorem voteCompat_of_not_lateWaker {D : OutageLockPremises F tr H proposer dg sg}
    (ht : VoteTiming (F.proj tr.projAC) H) {i : Nat} (hinv : OutageVoteInv D i)
    {x : Fin sp.n} (hx : x ∈ H) (hxW : x ∉ D.W) {k : Nat} (hk : k < i)
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt (F.proj tr.projAC) x k e)
    (hs : D.j₀ ≤ e.msg.slot) : Compose.VoteCompat (tr.HonestBlocks H) e.msg D.P := by
  by_cases hlate : D.j₀ + sp.k < e.msg.slot
  · exact hinv.late x hx k hk e hv hlate
  have hσ := D.hσ
  by_cases hpre : tr.time k ≤ D.b₀ ∨ x ∈ D.A₀
  · exact (hinv.votes x hx k hk e hv (by omega) (by omega) hpre).voteCompat
  exfalso
  push Not at hpre
  obtain ⟨hts, hte⟩ := ts_le_cast D ht hx hv
  obtain ⟨ℓ, hc, he⟩ := hv
  have haw := D.hrun.observation.awake_of_call x hx k ℓ hc
  rw [F.awake, F.time] at haw
  have hjs := Compose.ts_le_ts (sp := sp) hs
  have hsK := Compose.ts_le_ts (sp := sp) (show e.msg.slot ≤ D.j₀ + sp.k by omega)
  have hcall : tr.IsCall x k := by
    obtain ⟨ℓ', hlabel, -⟩ := F.frame tr.projAC k ℓ hc.2
    exact ⟨_, Compose.projAC_callAt.mp ⟨by simpa only [F.node] using hc.1, hlabel⟩⟩
  have hz := D.hz (tr.time k) (by linarith) ⟨x, hx, k, hcall, le_rfl⟩
  rcases D.hawake x hx (tr.time k) (by linarith [D.ha, sp.toParams.hΔ]) hz haw with h | h
  · exact hpre.2 h
  · exact hxW h

/-- Result compatibility uses pool provenance, voting schedule and participant delivery.
None of these are silently obtained from a concrete projected execution law. -/
theorem result_compatible {D : OutageLockPremises F tr H proposer dg sg}
    (hp : PoolFacts (F.proj tr.projAC) H) (htime : VoteTiming (F.proj tr.projAC) H)
    (hpart : Participants F tr H) {i : Nat} (hinv : OutageVoteInv D i)
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt (F.proj tr.projAC) y i m C CV)
    (hm : m ≤ D.j₀ ∨ D.r ≤ m) : Compatible (tr.HonestBlocks H) C D.P := by
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hCU := result_mem_family D.hrun hy hR
  obtain ⟨ℓ, hu, -, -⟩ := id hR
  have ht : tr.time i = sp.ts m + 6 * sp.Δ := by
    simpa only [F.time, RunTrace.projAC] using hu.2.2.1
  have hcall : ∃ x ∈ H, ∃ j, tr.IsCall x j ∧ sp.ts m + sp.Δ ≤ tr.time j := by
    obtain ⟨ℓ', hlabel, -⟩ := F.frame tr.projAC i ℓ hu.1.2
    exact ⟨y, hy, i, ⟨_, Compose.projAC_callAt.mp
      ⟨by simpa only [F.node] using hu.1.1, hlabel⟩⟩, by linarith⟩
  have hj₀ := D.hj₀
  have hrk := D.hrk
  have hσ := D.hσ
  have finish : ∀ v ∈ CV, v.val ∈ H →
      (∀ j < i, ∀ e, SA.VoteAt (F.proj tr.projAC) v.val j e → e.msg = v →
        Compose.VoteCompat (tr.HonestBlocks H) e.msg D.P) →
      Compatible (tr.HonestBlocks H) C D.P := by
    intro v hv hvH hcompat
    obtain ⟨j, hj, e, hve, rfl, -, R, hRU, hRr, hCR⟩ :=
      counted_honest_vote_family D.hrun hp hy hR hv hvH
    exact compatible_of_voteCompat_family hU hRU hRr hCR (hcompat j hj e hve rfl)
  rcases lt_or_ge m D.j₀ with hlt | hge
  · have hmj : sp.ts m + 6 * sp.Δ ≤ D.b₀ := by
      have := Compose.ts_le_ts (sp := sp) (show m + 1 ≤ D.j₀ by omega)
      have hts : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith
    exact D.compatible_of_within ⟨y, hy, i, CV, ht ▸ hmj, Or.inl hR⟩ hCU
  rcases hm with hm | hm
  · have hmeq : m = D.j₀ := le_antisymm hm hge
    have hT : {x | x ∈ H ∧ tr.awake x (sp.ts m + sp.Δ) ∧ tr.JoinedAt x (sp.ts m + sp.Δ)} ⊆
        SA.voters {v | v ∈ ((F.proj tr.projAC).state y i).pool m} := fun x hx =>
      hpart.early m D.b₀ D.hpreSvc.ac (hmeq ▸ hj₀.1) y hy i ℓ hu x hx.1 hx.2.1 hx.2.2
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants_family hR hT (D.hFB m hcall)
    have hvH : v.val ∈ H := hvT.elim (fun h => h.1) not_not.1
    refine finish v hv hvH fun j hj e hve he => ?_
    have hs : e.msg.slot = m := by
      obtain ⟨-, -, -, -, -, hvs, -⟩ := counted_honest_vote_family D.hrun hp hy hR hv hvH
      rw [he]; exact hvs
    obtain ⟨-, hte⟩ := ts_le_cast D htime hvH hve
    rw [hs, hmeq] at hte
    exact (hinv.votes v.val hvH j hj e hve (by omega) (by omega) (Or.inl (by linarith))).voteCompat
  have participant : ∀ x ∈ H, tr.awake x (sp.ts m + sp.Δ) →
      tr.JoinedAt x (sp.ts m + sp.Δ) →
      x ∈ SA.voters {v | v ∈ ((F.proj tr.projAC).state y i).pool m} := by
    intro x hx haw hjn
    obtain ⟨k, e, hve, hev, hes⟩ := hpart.vote x hx m haw hjn
    exact ⟨e.msg, D.PG y hy i m ℓ hu hm x hx k e hve hes, hev⟩
  rcases le_or_gt m (D.j₀ + sp.k) with hmK | hmK
  · have hT : D.A₀ ⊆ SA.voters {v | v ∈ ((F.proj tr.projAC).state y i).pool m} := by
      intro x hx
      obtain ⟨haw, hjn⟩ := cohort_ready D hx (by omega) hmK hcall
      exact participant x (D.hA₀ hx) haw hjn
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants_family hR hT D.hcohort
    have hvH : v.val ∈ H := by
      rcases hvT with h | h
      · exact D.hA₀ h
      · by_contra hn; exact h (Or.inl hn)
    refine finish v hv hvH fun j hj e hve he => ?_
    have hs : e.msg.slot = m := by
      obtain ⟨-, -, -, -, -, hvs, -⟩ := counted_honest_vote_family D.hrun hp hy hR hv hvH
      rw [he]; exact hvs
    rcases hvT with hA | hQ
    · exact (hinv.votes v.val hvH j hj e hve (by omega) (by omega) (Or.inr hA)).voteCompat
    · exact hinv.voteCompat_of_not_lateWaker htime hvH (fun h => hQ (Or.inr h)) hj hve (by omega)
  · have hT : {x | x ∈ H ∧ tr.awake x (sp.ts m + sp.Δ) ∧ tr.JoinedAt x (sp.ts m + sp.Δ)} ⊆
        SA.voters {v | v ∈ ((F.proj tr.projAC).state y i).pool m} :=
      fun x hx => participant x hx.1 hx.2.1 hx.2.2
    obtain ⟨v, hv, hvT⟩ := exists_counted_of_participants_family hR hT (D.hFB m hcall)
    have hvH : v.val ∈ H := hvT.elim (fun h => h.1) not_not.1
    refine finish v hv hvH fun j hj e hve he => ?_
    have hs : e.msg.slot = m := by
      obtain ⟨-, -, -, -, -, hvs, -⟩ := counted_honest_vote_family D.hrun hp hy hR hv hvH
      rw [he]; exact hvs
    exact hinv.late v.val hvH j hj e hve (by omega)

end OutageVoteInv

end Consensus.Goldilocks.FamilySafety

end
