module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance

public section

/-! # Static consequences of the run-facts bundle

The frame, accepted tree and height facts use the cut law with its finality update,
without choosing the stock or shadow node frame.
-/

namespace Consensus.Goldilocks.StaticRunCore

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini}
  {u frameOf} (rc : StaticRunCore u frameOf proposer dg H tr ini)

include rc

/-- The frame at an honest projected AC call is the chosen node frame. -/
theorem frame_of_projAC {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ) :
    ℓ.frame = frameOf (tr.state y k) :=
  ((cutStepWith_ac ℓ).mp (rc.cutLaw y hy k _ (Compose.projAC_callAt.mp hc))).1

/-- A block in an honest call's frame is held in the caller's FG store. -/
theorem frame_tree_subset {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ) :
    ℓ.frame.tree ⊆ (tr.state y k).fg.tree := by
  intro B hB
  rw [rc.frame_of_projAC hy hc] at hB
  exact (rc.frameOf_tree _ B).mp hB |>.1

/-- An accepted block is held immediately after its cut. -/
theorem accept_mem {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hA : tr.AcceptAt y k B) :
    B ∈ (tr.state y (k + 1)).fg.tree := by
  have hb := ((cutStepWith_block_true B).mp (rc.cutLaw y hy k _ hA)).2.1
  rw [tr.state_succ_of_call hA,
    (Store.tree_grows_with rc.finalitySpec).1 B _ hb]
  exact Set.mem_insert _ _

/-- One honest cut leaves the FG store alone, accepts a block or processes an attestation. -/
theorem fg_step {y : Fin sp.n} (hy : y ∈ H) (m : Nat) :
    (tr.state y (m + 1)).fg = (tr.state y m).fg ∨
      (∃ B, tr.AcceptAt y m B ∧
        (tr.state y m).fg.onBlockWith u B = some (tr.state y (m + 1)).fg) ∨
      ∃ a, tr.AttCallAt y m a ∧
        (tr.state y (m + 1)).fg = (tr.state y m).fg.onAttestation a := by
  by_cases hc : tr.IsCall y m
  · obtain ⟨c, hc⟩ := hc
    rw [tr.state_succ_of_call hc]
    have hs := rc.cutLaw y hy m c hc
    rcases c with ⟨⟨B, _ | _⟩ | a | ⟨C, _ | a⟩⟩ | ℓ
    · exact Or.inl (by rw [((cutStepWith_block_false B).mp hs).2])
    · exact Or.inr (Or.inl ⟨B, hc, ((cutStepWith_block_true B).mp hs).2.1⟩)
    · exact Or.inr (Or.inr ⟨a, hc, ((cutStepWith_attestation a).mp hs).1⟩)
    · exact Or.inl (by rw [((cutStepWith_attest_none C).mp hs).2])
    · exact Or.inl ((cutStepWith_attest_some C a).mp hs).2.1
    · exact Or.inl ((cutStepWith_ac ℓ).mp hs).2.2.1
  · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
    exact Or.inl rfl

/-- The finality specification makes an honest store's maximum height monotone. -/
theorem hmax_mono {y : Fin sp.n} (hy : y ∈ H) :
    Monotone fun m => (tr.state y m).fg.hmax := by
  refine monotone_nat_of_le_succ fun m => ?_
  rcases rc.fg_step hy m with he | ⟨B, -, hB⟩ | ⟨a, -, he⟩
  · rw [he]
  · obtain ⟨pr, σ', -, -, -, -, -, he⟩ := Store.onBlockWith_eq_some hB
    obtain ⟨atts, ha⟩ := Store.addAtts_eq (u { (tr.state y m).fg with
      blocks := Function.update (tr.state y m).fg.blocks B.root (some B),
      σ := Function.update (tr.state y m).fg.σ B.root σ' } σ') B.fgPayload
    rw [he, ha, rc.finalitySpec.hmax]
    exact le_max_left _ _
  · obtain ⟨atts, ha⟩ := (tr.state y m).fg.onAttestation_eq a
    rw [he, ha]

/-- A signing names an entry of the signer's store at its signing cut. -/
theorem signAt_entry {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) :
    ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧
      ((tr.state y k).fg.σ E.root).h = att.h := by
  obtain ⟨src, hc⟩ := hs
  have he := ((cutStepWith_attest_some src att).mp (rc.cutLaw y hy k _ hc)).1
  unfold Store.attest at he
  exact Store.exists_entry_of_createAtt_with rc.finalitySpec (rc.reachable y hy k) he

/-- A fast-lock write satisfies the run's joined test. -/
theorem joinedAt_of_fastLockAt (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i s : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (h : AC.FastLockAt tr.projAC y i s D CV) : tr.JoinedAt y (tr.time i) := by
  obtain ⟨hj, ℓ, hc, hnr⟩ := Healing.joined_of_fastLockAt (rc.acRun hnc).localRun hy h
  have hc' := Compose.projAC_callAt.mp hc
  apply (rc.joined_at_call y hy i _ ⟨_, hc'⟩ ?_ rfl).mpr
  · rwa [rc.projAC_state y hy i] at hj
  · intro hr
    obtain ⟨ℓ', hcR, hR⟩ := Compose.projAC_restartAt.mpr hr
    obtain rfl : ℓ = ℓ' := Option.some.inj (hc.2.symm.trans hcR.2)
    exact hnr hR

end Consensus.Goldilocks.StaticRunCore

namespace Consensus.Goldilocks.GoldilocksRunCore

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini}
  {u frameOf} (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)

include rc

/-- Read the signed entry on the signer's own honest prefix. -/
theorem signAt_entry {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) :
    ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧
      ((tr.state y k).fg.σ E.root).h = att.h := by
  have h := (rc.upTo (rc.time_nonneg k)).signAt_entry hy
    ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  rwa [RunTrace.upTo_state_of_le rc.time_mono le_rfl] at h

/-- A signing follows the source call on the signer's retained prefix. -/
theorem attest_source {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    ∃ j', j = j' + 1 ∧ ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.CallAt y j' (.ac ℓ) ∧ ℓ.call = .toFG ∧ tr.time j' = tr.time j ∧
      ((goldilocksNode sp ro).toFG (tr.state y j').ac ℓ.frame (tr.time j')).2 = some C ∧
      (tr.state y j).fg = (tr.state y j').fg := by
  obtain ⟨j', hj, ℓ, hc', hto, ht, hC, hs⟩ :=
    (rc.upTo (rc.time_nonneg j)).attest_source y hy
      ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩)
  change tr.time j' = tr.time j at ht
  rw [RunTrace.upTo_state_of_le rc.time_mono ht.le] at hC
  rw [RunTrace.upTo_state_of_le rc.time_mono le_rfl,
    RunTrace.upTo_state_of_le rc.time_mono ht.le] at hs
  exact ⟨j', hj, ℓ, ((Trace.upTo_callAt tr).mp hc').2, hto, ht, hC, hs⟩

end Consensus.Goldilocks.GoldilocksRunCore

end
