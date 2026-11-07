module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Retained-record provenance under growing faults

The node-local record facts of `Lemmas/Obligations/HealthyRecordGeometry` for a node honest at a
read time `t`, every earlier cut at a time `≤ t`: each holds on the prefix through `t`, where the
node is honest throughout, and is read back on the run. -/

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- **An unchanged record keeps its lookup back to an earlier cut**: for a node honest at `t`,
every cut before `j` at a time `≤ t`, a record looked up before `j` and unchanged since `i ≤ j` is
already looked up before `i` (advancing finalization cannot re-admit it to the frame). -/
theorem record_lookup_of_later_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i j : Nat} {t : Time} (ht : 0 ≤ t)
    (hjt : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t) (hij : i ≤ j)
    (heq : (tr.state y j).ac.latestConfirmed = (tr.state y i).ac.latestConfirmed)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed = some R) :
    SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed = some R := by
  have hj := Trace.upTo_state tr y hjt
  have hi := Trace.upTo_state tr y fun k hk => hjt k (hk.trans_le hij)
  have h := record_lookup_of_later (hrun.upTo ht) (hnc.upTo t) hy hij
    (by rw [hi, hj]; exact heq) (by rw [hj]; exact hR)
  rwa [hi] at h

/-- **One step of a node's record**, for a node honest at the step: the record is unchanged, or
it names a block of its tree with a result or optimistic-lock source of its own at the step. -/
theorem record_step_origin_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    (tr.state y (i + 1)).ac.latestConfirmed = (tr.state y i).ac.latestConfirmed ∨
      ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        ∃ s CV, SA.ResultAt tr.projAC y i s C CV ∨
          SA.OptimisticLockAt tr.projAC y i s C CV := by
  have hle : ∀ k < i + 1, tr.time k ≤ tr.time i :=
    fun k hk => hrun.time_mono (Nat.le_of_lt_succ hk)
  have h1 := Trace.upTo_state tr y hle
  have h0 := Trace.upTo_state tr y fun k hk => hle k (hk.trans (Nat.lt_succ_self i))
  rcases Compose.record_step_origin (hrun.upTo (hrun.time_nonneg i)) hy i with
    h | ⟨C, hC, hCr, s, CV, hs⟩
  · rw [h1, h0] at h
    exact Or.inl h
  · rw [h0] at hC
    rw [h1] at hCr
    rw [RunTrace.upTo_projAC] at hs
    refine Or.inr ⟨C, hC, hCr, s, CV, ?_⟩
    rcases hs with hs | hs
    · exact Or.inl ((Compose.Growing.sa_resultAt_upTo hrun.time_mono).mp hs).2
    · exact Or.inr ((Compose.Growing.sa_optimisticLockAt_upTo hrun.time_mono).mp hs).2

/-- A node's tree only grows over a step at which it is honest. -/
theorem tree_succ_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    (tr.state y i).fg.tree ⊆ (tr.state y (i + 1)).fg.tree := by
  have hle : ∀ k < i + 1, tr.time k ≤ tr.time i :=
    fun k hk => hrun.time_mono (Nat.le_of_lt_succ hk)
  have h := Compose.tree_mono (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy (Nat.le_succ i)
  rwa [Trace.upTo_state tr y hle,
    Trace.upTo_state tr y fun k hk => hle k (hk.trans (Nat.lt_succ_self i))] at h

open Healing.Growing in
/-- **Every later archival record has a recent source** before its cut: after the operational
update of label `u`, the record of a node honest at `t` before a later cut `n`, every cut before
`n` at a time `≤ t`, names a block of its tree with an origin of label at least `u` before `n`,
even if advancing finalization has removed it from the filtered frame. -/
theorem archival_record_source_after_operational_update_at {g ΔF a b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) {n : Nat} {t : Time} (hjn : j < n)
    (hnt : ∀ q < n, tr.time q ≤ t) (hyt : y ∈ H t) :
    ∃ C ∈ (tr.state y n).fg.tree,
      C.root = (tr.state y n).ac.latestConfirmed ∧
      ∃ l, u ≤ l ∧ Compose.Growing.OriginBefore tr H C l n := by
  classical
  have hrun := hp.run
  have hyq : ∀ q < n, y ∈ H (tr.time q) := fun q hq => hrun.antitone (hnt q hq) hyt
  have hy := hyq j hjn
  have hind : ∀ m, j + 1 ≤ m → m ≤ n →
      ∃ C ∈ (tr.state y m).fg.tree,
        C.root = (tr.state y m).ac.latestConfirmed ∧
        ∃ l, u ≤ l ∧ Compose.Growing.OriginBefore tr H C l m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      obtain ⟨hPt, _, _, _, _, hrecord⟩ :=
        operational_update_selection_at hp hc hhold hdesignated hactual hPs hR hgu hTb hy hup
      have hc' := Compose.projAC_callAt.mp hup.1
      have hlaw := hrun.cutLaw y j _ hc' hy
      have hframe : Node.frame (tr.state y (j + 1)) = ell.frame := by
        rw [tr.state_succ_of_call hc', hlaw.1]
        exact congrArg Store.toFrame hlaw.2.2.1
      have hstate : tr.projAC.post j = (tr.state y (j + 1)).ac := by
        rw [tr.state_succ_of_call hc']
        rfl
      have hex : ∃ C ∈ ell.frame.tree,
          C.root = (tr.projAC.post j).latestConfirmed := by
        rw [hrecord]
        by_cases hguard : SA.AncR ell.frame P (tr.projAC.state y j).latestConfirmed
        · simp only [SA.updateLatestConfirmed, ite_eq_left hguard]
          obtain ⟨C, hC, hCr, _⟩ := hguard
          exact ⟨C, hC, hCr⟩
        · exact ⟨P, hPt, by simp only [SA.updateLatestConfirmed, ite_eq_right hguard]⟩
      obtain ⟨C, hC, hCr⟩ := hex
      have hlookup : SA.lookup ell.frame (tr.projAC.post j).latestConfirmed = some C := by
        cases hk : SA.lookup ell.frame (tr.projAC.post j).latestConfirmed with
        | none => exact False.elim (SA.lookup_eq_none hk ⟨C, hC, hCr⟩)
        | some B =>
          obtain ⟨hB, hBr⟩ := SA.lookup_eq_some hk
          exact congrArg some ((Compose.Growing.frameIn_at hrun hp.noColl hy hup.1).1.coherent.1
            hB hC (hBr.trans hCr.symm))
      rw [← hframe, hstate] at hlookup
      obtain ⟨x, q, s, CV, hx, hqj, -, hs, hsource⟩ :=
        operational_update_recent_source_at hp hc hhold hdesignated hactual hPs hR hgu hTb hy
          hup hlookup
      refine ⟨C, ?_, hCr.trans (congrArg SA.SAState.latestConfirmed hstate), s, hs,
        Compose.Growing.originBefore_iff.2 ⟨x, q, CV, by omega, hx, hsource⟩⟩
      rw [← hframe] at hC
      exact hC.1
    | succ m hjm ih =>
      intro hmn
      have hym := hyq m hmn
      have htree := tree_succ_at hrun hym
      rcases record_step_origin_at hrun hym with heq | ⟨B, hB, hBr, s, CV, hsource⟩
      · obtain ⟨C, hC, hCr, s, hs, hsource⟩ := ih (Nat.le_of_succ_le hmn)
        obtain ⟨x, q, CV, hqm, hx, hsource⟩ := Compose.Growing.originBefore_iff.1 hsource
        exact ⟨C, htree hC, hCr.trans heq.symm, s, hs,
          Compose.Growing.originBefore_iff.2 ⟨x, q, CV, by omega, hx, hsource⟩⟩
      · have htime : sp.ts u + 6 * sp.Δ ≤ tr.time m := by
          rw [← hup.2.2.1]
          exact hrun.time_mono (by omega)
        have hus : u ≤ s := by
          rcases hsource with ⟨e, hu, _⟩ | ⟨e, A, ho, hslot, _⟩
          · have ht : tr.time m = sp.ts s + 6 * sp.Δ := hu.2.2.1
            have := (SA.ts_le_iff sp).mp (show sp.ts u ≤ sp.ts s by linarith)
            omega
          · have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg m) u).mp
              (show sp.ts u ≤ tr.time m by linarith [sp.toParams.hΔ])
            change sp.slot (tr.time m) = s at hslot
            omega
        exact ⟨B, htree hB, hBr, s, hus,
          Compose.Growing.originBefore_iff.2 ⟨y, m, CV, Nat.lt_succ_self _, hym, hsource⟩⟩
  exact hind n (by omega) le_rfl

open Healing.Growing in
/-- **Every later successful record lookup has a recent source**: after the operational update of
label `u`, a record looked up by a node honest at `t` before a later cut `n`, every cut before `n`
at a time `≤ t`, has a raw or optimistic source of label at least `u` before `n`, of a node honest
at its own cut. -/
theorem record_source_after_operational_update_at {g ΔF a b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) {n : Nat} {t : Time} (ht0 : 0 ≤ t) (hjn : j < n)
    (hnt : ∀ q < n, tr.time q ≤ t) (hyt : y ∈ H t)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlookup : SA.lookup (Node.frame (tr.state y n))
      (tr.state y n).ac.latestConfirmed = some R) :
    ∃ x q s CV, x ∈ H (tr.time q) ∧ q < n ∧ u ≤ s ∧
      (SA.ResultAt tr.projAC x q s R CV ∨ SA.OptimisticLockAt tr.projAC x q s R CV) := by
  obtain ⟨C, hC, hCr, s, hs, hsource⟩ :=
    archival_record_source_after_operational_update_at hp hc hhold hdesignated hactual hPs
      hR hgu hTb hup hjn hnt hyt
  obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hlookup
  have hsub := Compose.Growing.tree_subset_at (tr := tr) (H := H) ht0 hnt hyt
  have heq : C = R := (Compose.Growing.honestBlocksAt_coherent hp.run hp.noColl).1 (hsub hC)
    (hsub hR.1) (hCr.trans hRr.symm)
  subst C
  obtain ⟨x, q, CV, hq, hx, hsource⟩ := Compose.Growing.originBefore_iff.1 hsource
  exact ⟨x, q, s, CV, hx, hq, hs, hsource⟩

end Consensus.Goldilocks.Obligations.Growing

end
