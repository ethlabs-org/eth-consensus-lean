module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

namespace Consensus.Goldilocks.FamilySafety

set_option backward.isDefEq.respectTransparency false

open SA (SAParams ReplayOrder Payload Vote SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

/-- The interval vocabulary reads the projected record, not a concrete node AC state. -/
structure EffectiveRecordInterval (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) (y : Fin sp.n) (i j : Nat)
    (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  step : ∀ q, i ≤ q → q < j →
    (∃ New : SA.Blk sp.n (List (FG.Att sp.n)) → Prop,
      Compose.Writes (Node.frame (tr.state y q)) New
        ((F.proj tr.projAC).state y q).latestConfirmed
        ((F.proj tr.projAC).state y (q + 1)).latestConfirmed ∧
      (∀ D, New D → Compatible (tr.HonestBlocks H) O D) ∧
      Compatible (tr.HonestBlocks H) (tr.state y (q + 1)).fg.F O) ∨
    Anc (tr.HonestBlocks H) O ((SA.lookup (Node.frame (tr.state y (q + 1)))
      ((F.proj tr.projAC).state y (q + 1)).latestConfirmed).getD (tr.state y (q + 1)).fg.F)

/-- The only execution fact used to produce an interval: every write has an observed origin. -/
def RecordWrites (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ q ℓ, (F.proj tr.projAC).CallAt y q ℓ →
    Compose.Writes ℓ.frame
      (fun C => ∃ s CV, SA.ResultAt (F.proj tr.projAC) y q s C CV ∨
        SA.OptimisticLockAt (F.proj tr.projAC) y q s C CV)
      ((F.proj tr.projAC).state y q).latestConfirmed ((F.proj tr.projAC).post q).latestConfirmed

theorem recordWrites_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    RecordWrites (SA.goldilocksFamily sp _ ro) tr H := by
  intro y hy q ℓ hc
  exact Compose.call_writes
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc).localRun hy hc

theorem record_interval_after_family (hw : RecordWrites F tr H) (hf : LockFacts F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H) {D : OutageLockPremises F tr H proposer dg sg}
    (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {i j : Nat} (hi : sp.ts D.r + 6 * sp.Δ ≤ tr.time i) :
    EffectiveRecordInterval F tr H y i j D.P := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  refine ⟨fun q hiq hqj => Or.inl ?_⟩
  refine ⟨(fun C => ∃ s CV, SA.ResultAt (F.proj tr.projAC) y q s C CV ∨
    SA.OptimisticLockAt (F.proj tr.projAC) y q s C CV), ?_, ?_,
    ((hinv (q + 1)).caches y hy (q + 1) le_rfl).1⟩
  · by_cases hc : ∃ ℓ, (F.proj tr.projAC).CallAt y q ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      have h := hw y hy q ℓ hc
      rw [← (F.proj tr.projAC).state_succ_of_call hc, frame_of_observation D.hrun hy hc] at h
      exact h
    · rw [(F.proj tr.projAC).state_succ_of_not (fun ℓ h => hc ⟨ℓ, h⟩)]
      exact Compose.writes_iff.mpr .refl
  · rintro C ⟨s, CV, hR | hO⟩
    · obtain ⟨ℓ, hu, -, -⟩ := id hR
      have htt : tr.time q = sp.ts s + 6 * sp.Δ := by
        simpa only [F.time, RunTrace.projAC] using hu.2.2.1
      have hqi := D.hrun.time_mono hiq
      have hrs : D.r ≤ s := by
        by_contra h
        have hh := Compose.ts_le_ts (sp := sp) (show s + 1 ≤ D.r by omega)
        have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
          simp only [SAParams.ts]; push_cast; ring
        linarith
      exact ((hinv (q + 1)).results y hy q (Nat.lt_succ_self q) s C CV hR (Or.inr hrs)).symm
    · exact (fastLock_compatible_family hf ht hinv hy (Or.inr hO)).symm

/-- Generic FG retention: the frame can change without consulting AC execution. -/
theorem effective_record_frame (hr : Node.LocalRun proposer dg H sg tr)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin sp.n} (hy : y ∈ H) {i j r : Nat} (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hFO : Compatible (tr.HonestBlocks H) (tr.state y j).fg.F O)
    (hO : Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y i)) r).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y j)) r).getD (tr.state y j).fg.F) := by
  have hΨ := Compose.frameOK_state hr hy j
  apply Obligations.effective_record_frame_of_compatible hfg.coherent
    (Φ := Node.frame (tr.state y i)) hΨ
    (fun X hX => ⟨y, hy, i, hX.1⟩) (fun X hX => ⟨y, hy, j, hX.1⟩)
    (Healing.run_F_mono hr hy hij) hFO ?_ hO
  intro C hC hFC
  have hCj := Compose.tree_mono hr hy hij hC.1
  exact ⟨hCj, honest_held_anc hr hfg hy hFC hCj⟩

theorem effective_record_of_interval_family (hr : FamilyRun F proposer dg H sg tr)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (hint : EffectiveRecordInterval F tr H y i j O)
    (hO : Anc (tr.HonestBlocks H) O ((SA.lookup (Node.frame (tr.state y i))
      ((F.proj tr.projAC).state y i).latestConfirmed).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocks H) O ((SA.lookup (Node.frame (tr.state y j))
      ((F.proj tr.projAC).state y j).latestConfirmed).getD (tr.state y j).fg.F) := by
  have step : ∀ q, i ≤ q → q ≤ j → Anc (tr.HonestBlocks H) O
      ((SA.lookup (Node.frame (tr.state y q)) ((F.proj tr.projAC).state y q).latestConfirmed).getD
        (tr.state y q).fg.F) := by
    intro q hiq
    induction q, hiq using Nat.le_induction with
    | base => exact fun _ => hO
    | succ q hiq ih =>
      intro hqj
      rcases hint.step q hiq (by omega) with ⟨New, hw, hnew, hF⟩ | hreset
      · have hwritten := Obligations.effective_record_writes_of_compatible hr.observation.coherent
          (Compose.frameOK_state hr.toLocalRun hy q)
          (fun X hX => ⟨y, hy, q, hX.1⟩) hw hnew (ih (by omega))
        exact effective_record_frame hr.toLocalRun hfg hy (Nat.le_succ q) hF hwritten
      · exact hreset
  exact step j hij le_rfl

/-- A veto only needs the record-above-live-lock consequence of AcceptLaws′. -/
def RecordAboveLive (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) : Prop :=
  ∀ y ∈ H, ∀ c s ℓ, SA.UpdateAt (F.proj tr.projAC) y c s ℓ →
    ∀ L ∈ SA.liveLockBlocks sp ((F.proj tr.projAC).state y c).locks ℓ.frame (tr.time c),
    ∃ E ∈ ℓ.frame.tree, E.root = ((F.proj tr.projAC).state y c).latestConfirmed ∧ ℓ.frame.Anc L E

theorem recordAboveLive_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    RecordAboveLive (SA.goldilocksFamily sp _ ro) tr H := by
  have hac := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc).localRun
  intro y hy c s ℓ hu L hL
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hac hy hu.1
  obtain ⟨Φp, tp, hreach, -, hok⟩ := Compose.pre_reachable hac hy hu.1
  obtain ⟨hin, -, hinv⟩ := SA.lockInv_of_reachable hac.coherent hreach
  exact (hinv.callOK hac.coherent hin hok).liveBlock_anc hac.coherent hΦ hΦU hL

theorem record_above_from_family (hrec : SA.UpdateRecordAt (F.proj tr.projAC) H)
    (hw : RecordWrites F tr H) (hf : LockFacts F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H) (hra : RecordAboveLive F tr H)
    {D : OutageLockPremises F tr H proposer dg sg}
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hinv : ∀ i, OutageLockInv D i) {w : Fin sp.n} (hwH : w ∈ H)
    {c m : Nat} {ℓ} (hu : SA.UpdateAt (F.proj tr.projAC) w c m ℓ)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt (F.proj tr.projAC) w c m C CV) (hrm : D.r ≤ m)
    (hPC : Anc (tr.HonestBlocks H) D.P C) :
    ∀ i, c < i → Anc (tr.HonestBlocks H) D.P ((SA.lookup (Node.frame (tr.state w i))
      ((F.proj tr.projAC).state w i).latestConfirmed).getD (tr.state w i).fg.F) := by
  intro i hci
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hfr := frame_of_observation D.hrun hwH hu.1
  have htt : tr.time c = sp.ts m + 6 * sp.Δ := by
    simpa only [F.time, RunTrace.projAC] using hu.2.2.1
  have hrm' := Compose.ts_le_ts (sp := sp) hrm
  obtain ⟨hΦ, hΦU⟩ := D.hrun.observation.frameIn hwH hu.1
  obtain ⟨ℓR, huR, hCR, -⟩ := hR
  have heq : ℓR = ℓ := Option.some.inj (huR.1.2.symm.trans hu.1.2)
  subst ℓR
  have hCt := (SA.deepest_mem hCR).1.1
  have hpost : Anc (tr.HonestBlocks H) D.P
      ((SA.lookup ℓ.frame ((F.proj tr.projAC).post c).latestConfirmed).getD ℓ.frame.F) := by
    by_cases hnv : SA.conflictsWithLock sp ((F.proj tr.projAC).state w c).locks ℓ.frame
        ((F.proj tr.projAC).time c) C
    · obtain ⟨L, hL, hCL⟩ := hnv
      have hconflict : ¬ Compatible (tr.HonestBlocks H) C L := by
        rintro (h | h)
        · exact hCL (Or.inl (SA.anc_tree_of_anc_U hU hΦ hΦU hCt h hL.1))
        · exact hCL (Or.inr (SA.anc_tree_of_anc_U hU hΦ hΦU hL.1 h hCt))
      have hL' : L ∈ SA.liveLockBlocks sp ((F.proj tr.projAC).state w c).locks ℓ.frame
          (tr.time c) := by simpa only [F.time, RunTrace.projAC] using hL
      have hcomp := liveLockBlocks_compatible_family hinv hwH c (tr.time c) (B := D.P) .refl
      rw [← hfr] at hcomp
      have hPL := Obligations.cover_of_veto hU hPC (hcomp L hL') hconflict
      obtain ⟨E, hE, hEr, hLE⟩ := hra w hwH c m ℓ hu L hL'
      have hlookup : SA.lookup ℓ.frame ((F.proj tr.projAC).state w c).latestConfirmed = some E := by
        cases he : SA.lookup ℓ.frame ((F.proj tr.projAC).state w c).latestConfirmed with
        | none => exact False.elim (SA.lookup_eq_none he ⟨E, hE, hEr⟩)
        | some E' => exact congrArg some (hΦ.coherent.1 (SA.lookup_eq_some he).1 hE
            ((SA.lookup_eq_some he).2.trans hEr.symm))
      rw [(hrec w hwH c m ℓ hu).2]
      simp only [hCR]
      rw [ite_eq_left ⟨L, hL, hCL⟩, hlookup]
      exact hPL.trans (hLE.mono hΦU)
    · exact hPC.trans ((Obligations.effective_record_after_update_family F
        (fun y hy k ℓ hc => (D.hrun.observation.frameIn hy hc).1) hrec hwH hu
        ⟨ℓ, huR, hCR, rfl⟩ hnv).mono hΦU)
  apply effective_record_of_interval_family D.hrun hfg hwH (Nat.succ_le_of_lt hci)
    (record_interval_after_family hw hf ht hinv hwH
      (by linarith [D.hrun.time_mono (Nat.le_succ c)]))
  have hn : tr.node c = w := by simpa only [F.node, RunTrace.projAC] using hu.1.1
  obtain ⟨ℓ', hl', hframe⟩ := F.frame tr.projAC c ℓ hu.1.2
  have hc := Compose.projAC_callAt.mp ⟨hn, hl'⟩
  have hfg' : (tr.state w (c + 1)).fg = (tr.state w c).fg := by
    rw [tr.state_succ_of_call hc]
    exact (D.hrun.cutLaw w hwH c _ hc).2.2.1
  have hframe' : Node.frame (tr.state w (c + 1)) = ℓ.frame := by
    rw [Node.frame, hfg', ← Node.frame]
    exact hfr.symm
  rw [← (F.proj tr.projAC).state_succ_of_call hu.1, ← hframe'] at hpost
  exact hpost

theorem effectiveRecordInterval_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} :
    EffectiveRecordInterval (SA.goldilocksFamily sp _ ro) tr H y i j B ↔
      Obligations.EffectiveRecordInterval tr H y i j B := by
  have hp : (SA.goldilocksFamily sp _ ro).proj tr.projAC = tr.projAC := rfl
  constructor <;> intro h <;> constructor <;> intro q hiq hqj
  · simpa only [hp, Compose.projAC_state hr.toLocalRun hy] using h.step q hiq hqj
  · simpa only [hp, Compose.projAC_state hr.toLocalRun hy] using h.step q hiq hqj

theorem record_interval_after_instance {tr : GoldilocksTrace sp ro}
    {D : Compose.OutageLockPremises tr H proposer dg}
    (hinv : ∀ i, Compose.OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {i j : Nat} (hi : sp.ts D.r + 6 * sp.Δ ≤ tr.time i) :
    Obligations.EffectiveRecordInterval tr H y i j D.P := by
  apply (effectiveRecordInterval_goldilocks D.hrun hy).mp
  simpa only [Compose.OutageLockPremises.family_P] using
    record_interval_after_family (recordWrites_goldilocks D.hrun D.hnc)
      (lockFacts_goldilocks D.hrun D.hnc) (voteTiming_goldilocks D.hrun D.hnc)
      (fun i => Compose.OutageLockInv.family_iff.mpr (hinv i)) hy
      (by simpa only [Compose.OutageLockPremises.family_r] using hi)

theorem record_above_from_instance {tr : GoldilocksTrace sp ro}
    {D : Compose.OutageLockPremises tr H proposer dg}
    (hinv : ∀ i, Compose.OutageLockInv D i) {w : Fin sp.n} (hw : w ∈ H)
    {c m : Nat} {ℓ} (hu : SA.UpdateAt tr.projAC w c m ℓ)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC w c m C CV) (hrm : D.r ≤ m)
    (hPC : Anc (tr.HonestBlocks H) D.P C) :
    ∀ i, c < i → Anc (tr.HonestBlocks H) D.P ((SA.lookup (Node.frame (tr.state w i))
      (tr.state w i).ac.latestConfirmed).getD (tr.state w i).fg.F) := by
  have hac := (Compose.goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  intro i hci
  rw [← Compose.projAC_state D.hrun.toLocalRun hw i]
  have hp : (SA.goldilocksFamily sp _ ro).proj tr.projAC = tr.projAC := rfl
  simpa only [hp, Compose.OutageLockPremises.family_P] using
    record_above_from_family (SA.goldilocksContract hac).updateRecord
      (recordWrites_goldilocks D.hrun D.hnc) (lockFacts_goldilocks D.hrun D.hnc)
      (voteTiming_goldilocks D.hrun D.hnc) (recordAboveLive_goldilocks D.hrun D.hnc)
      (Compose.projFG_localRun D.hrun D.hnc)
      (fun i => Compose.OutageLockInv.family_iff.mpr (hinv i)) hw hu hR
      (by simpa only [Compose.OutageLockPremises.family_r] using hrm)
      (by simpa only [Compose.OutageLockPremises.family_P] using hPC) i hci

end Consensus.Goldilocks.FamilySafety

end
