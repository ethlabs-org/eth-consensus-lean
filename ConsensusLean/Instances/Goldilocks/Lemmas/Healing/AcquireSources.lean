module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProvenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the origin of the report record

The report record of an honest node names genesis or the block of an earlier `ac_to_fg` return of
the node (`fgReported_origin`). The current sources above a protected honest proposal, which HS.4
and HS.5 shared, are removed with HS.4 and HR.3 (retired, owner decision). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload gbar)

/-! ## The report record -/

section Report

variable {FGP : Type} {sp : ACParams}

private theorem admitVote_fgr (A : AC.ACState sp.n) (t : Time) (v : AC.Vote sp.n) :
    (AC.admitVote sp A t v).fgReported = A.fgReported := by
  unfold AC.admitVote
  split_ifs <;> rfl

private theorem ulc_fgr (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (C : AC.Blk sp.n FGP) :
    (AC.updateLatestConfirmed sp A Φ C).fgReported = A.fgReported := by
  unfold AC.updateLatestConfirmed
  split_ifs <;> rfl

private theorem optimistic_fgr (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) :
    (AC.optimisticConfirmation sp A Φ t).fgReported = A.fgReported := by
  unfold AC.optimisticConfirmation
  split
  · rfl
  · exact ulc_fgr _ _ _

private theorem update_fgr (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) (s : Nat) :
    (AC.updateConfirmation sp A Φ t s).fgReported = A.fgReported := by
  unfold AC.updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs
    · rfl
    all_goals exact ulc_fgr _ _ _

private theorem tryVote_fgr (self : Fin sp.n) (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP)
    (t : Time) : (AC.tryVote sp self A Φ t).1.fgReported = A.fgReported := by
  unfold AC.tryVote
  dsimp only
  split_ifs <;> first | rfl | exact (optimistic_fgr _ _ _).trans (admitVote_fgr _ _ _)

private theorem blockReceipt_fgr (A : AC.ACState sp.n) (t : Time) (B : AC.Blk sp.n FGP) :
    (AC.blockReceipt sp A t B).fgReported = A.fgReported :=
  rfl

/-- `ac_to_fg` keeps the report record, or sets it to the block it returns. -/
private theorem acToFG_fgr (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time) :
    (AC.acToFG sp A Φ t).1.fgReported = A.fgReported ∨
      ∃ C, (AC.acToFG sp A Φ t).2 = some C ∧ (AC.acToFG sp A Φ t).1.fgReported = C.root := by
  unfold AC.acToFG
  split_ifs
  · split
    · exact Or.inl rfl
    · split_ifs
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl, rfl⟩
  · exact Or.inl rfl

variable {ro : AC.ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (AC.Blk sp.n FGP)}
  {tr : AC.GTrace sp FGP ro}

/-- **The origin of the report record**: the report record of an honest node names genesis (the
initial record, and a restart's), or the block of an earlier `ac_to_fg` return of the node (its
only writer). -/
theorem fgReported_origin {ini} (hr : ACLocalRun (AC.goldilocksAC sp FGP ro) H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) : ∀ i, (tr.state y i).fgReported = sp.genesisRoot ∨
      ∃ k < i, ∃ ℓ C, AC.ToFGAt tr y k ℓ C ∧ C.root = (tr.state y i).fgReported
  | 0 => by
    left
    change (tr.init y).fgReported = _
    obtain ⟨m, hm⟩ := hini y
    rw [hr.init y hy, hm]
    rfl
  | i + 1 => by
    have ih := fgReported_origin hr hini hy i
    have old : (tr.state y (i + 1)).fgReported = (tr.state y i).fgReported →
        (tr.state y (i + 1)).fgReported = sp.genesisRoot ∨
          ∃ k < i + 1, ∃ ℓ C, AC.ToFGAt tr y k ℓ C ∧
            C.root = (tr.state y (i + 1)).fgReported := fun he => by
      rw [he]
      exact ih.imp_right fun ⟨k, hk, h⟩ => ⟨k, by omega, h⟩
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      have hst : tr.state y (i + 1) = tr.post i := by simp [Trace.state, hc.1, hc.2]
      have hΦ := (AC.frameIn_of_callAt hr hy hc).1
      have he := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      have hpost := congrArg Prod.fst he
      simp only at hpost
      cases hcall : ℓ.call with
      | tick =>
        refine old ?_
        rw [hst, ← hpost, hcall]
        change (AC.acOnTick sp y _ _ _).1.fgReported = _
        unfold AC.acOnTick
        dsimp only
        split_ifs <;> first | rfl | exact (update_fgr _ _ _ _).trans (tryVote_fgr _ _ _ _) |
          exact update_fgr _ _ _ _ | exact tryVote_fgr _ _ _ _
      | message m =>
        refine old ?_
        rw [hst, ← hpost, hcall]
        exact ((tryVote_fgr _ _ _ _).trans (optimistic_fgr _ _ _)).trans (admitVote_fgr _ _ _)
      | block B =>
        refine old ?_
        rw [hst, ← hpost, hcall]
        exact ((tryVote_fgr _ _ _ _).trans (optimistic_fgr _ _ _)).trans (blockReceipt_fgr _ _ _)
      | proposal =>
        refine old ?_
        rw [hst, ← hpost, hcall]
        change (AC.acProposal sp _ _ _).1.fgReported = _
        unfold AC.acProposal
        split_ifs <;> rfl
      | toFG =>
        rw [hst, ← hpost, hcall]
        change (AC.acToFG sp (tr.state y i) ℓ.frame (tr.time i)).1.fgReported = _ ∨
          ∃ k < i + 1, ∃ ℓ₁ C, AC.ToFGAt tr y k ℓ₁ C ∧
            C.root = (AC.acToFG sp (tr.state y i) ℓ.frame (tr.time i)).1.fgReported
        rcases acToFG_fgr (tr.state y i) ℓ.frame (tr.time i) with h | ⟨C, hC, h⟩
        · rw [h]
          exact ih.imp_right fun ⟨k, hk, h'⟩ => ⟨k, by omega, h'⟩
        · exact Or.inr ⟨i, by omega, ℓ, C, ⟨hc, hcall, hC⟩, h.symm⟩
      | restart =>
        left
        rw [hst, ← hpost, hcall]
        change (AC.acRestart sp ro y _ _ _).1.fgReported = _
        exact ((AC.restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ
          (hr.time_nonneg i)).2.2.2.2.1
    · refine old ?_
      rw [Trace.state]
      split_ifs with h
      · exact absurd ⟨_, h.1, (Option.ne_none_iff_exists'.1 h.2).choose_spec⟩ hc
      · rfl

end Report

/-! ## The slot-`s` update -/

section Update

variable {FGP : Type} {sp : ACParams}

end Update

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF Gp w : Time}
  {i₀ m : Nat}
  {c : PhaseCase (AC.Blk sp.n (List (FG.Att sp.n)))}

/-! ## Run facts -/

/-! ## Every live lock at the update compares with `Y` -/

/-! ## The sources -/

end Consensus.Goldilocks.Healing

end
