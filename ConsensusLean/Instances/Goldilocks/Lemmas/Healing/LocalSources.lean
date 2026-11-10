module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.LocalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # Store-local high roots from authentic rows and strictly prior sources -/

namespace Consensus.Goldilocks.LocalSources

variable {P : Params} {ACP : Type}

/-- Authentic observation followed by source provenance preserves both strict cuts. -/
theorem observed_high_row_source_before
    (st : Fin P.n → Nat → Store P ACP) (time : Nat → Time)
    (H : Time → Set (Fin P.n)) (Sign : Fin P.n → Nat → FG.Att P.n → Prop)
    (Origin : Fin P.n → Nat → Nat → NodeBlock P ACP → Prop)
    (Joined : Fin P.n → Time → Prop) (U : Set (NodeBlock P ACP)) (Hz : Nat) (b : Time) :
    ObservedHighRowSourceBefore st time H Sign Origin Joined U Hz b := by
  intro hmono _ hobs hsource y k E W att hy hkb hE hEh hET hW ha haT haH
  obtain ⟨d, hdk, hs, hv, Es, _, _, hEsh, hEsE⟩ :=
    hobs y k hy hkb E hE hEh hET W hW att ha haT haH
  have hdb := (hmono hdk.le).trans hkb
  obtain ⟨r, hrd, l, O, ho, hrH, hrJ, hrb, hO, hOh, E0, hE0, hEO, hEr, hh, hTh⟩ :=
    hsource att.val d att hv hdb hs (by omega)
  exact ⟨d, hdk, hs, hv, r, hrd, l, O, ho, hrd.trans hdk, hrH, hrJ, hrb,
    hO, hOh, E0, hE0, hEO, hEr.trans haT, hh, hTh⟩

/-- An incompatible high entry has no surviving honest row, so the existing quorum core
compares J; reachable-store ancestry compares F and the actual fork-choice root as well. -/
theorem high_roots_before (acp₀ : ACP)
    (st : Fin P.n → Nat → Store P ACP) (time : Nat → Time)
    (H : Time → Set (Fin P.n)) (Sign : Fin P.n → Nat → FG.Att P.n → Prop)
    (Origin : Fin P.n → Nat → Nat → NodeBlock P ACP → Prop)
    (Joined : Fin P.n → Time → Prop) (U : Set (NodeBlock P ACP)) (Hz : Nat) (b : Time) :
    HighRootsBefore acp₀ st time H Sign Origin Joined U Hz b := by
  intro hU hmono hsub hobs hsource y k B hy hkb hreach hgen hq hhigh hprior
  have hrow : ∀ E ∈ (st y k).tree, Hz + 1 ≤ ((st y k).σ E.root).h →
      ((st y k).σ E.root).Th = E.root → ¬ Compatible U E B →
      ∀ W ∈ (st y k).tree, ∀ att ∈ W.fgPayload, att.T = E.root → att.val ∉ H (time k) := by
    intro E hE hEh hET hnc W hW att ha haT haH
    obtain ⟨d, _, _, _, r, _, l, O, ho, hrk, hrH, _, hrb, _, _, E0, hE0, hEO, hEr, _⟩ :=
      observed_high_row_source_before st time H Sign Origin Joined U Hz b
        hmono hsub hobs hsource y k E W att hy hkb hE hEh hET hW ha haT haH
    obtain rfl : E0 = E := hU.1 (hsub _ _ hrH hrb hE0) (hsub _ _ hy hkb hE) hEr
    rcases hprior _ r l O hrk hrb ho with hBO | hOB
    · exact hnc (Anc.total hU hEO hBO)
    · exact hnc (Or.inl (hEO.trans hOB))
  have hJ := Healing.Store.J_compatible_of_rows hreach hq hU (hsub _ _ hy hkb)
    hgen hrow hhigh
  have hF : Compatible U (st y k).F B := by
    obtain ⟨_, _, hFJ, _⟩ := Store.cache_invariants _ _ _ _ hreach
    rcases hJ with hJB | hBJ
    · exact Or.inl ((hFJ.mono (hsub _ _ hy hkb)).trans hJB)
    · exact Anc.total hU (hFJ.mono (hsub _ _ hy hkb)) hBJ
  refine ⟨hJ, hF, ?_⟩
  unfold Store.fcRoot
  split_ifs <;> assumption

/-- The call-facing result uses equality with the store's actual frame. -/
theorem high_frame_root_before (acp₀ : ACP)
    (st : Fin P.n → Nat → Store P ACP) (time : Nat → Time)
    (H : Time → Set (Fin P.n)) (Sign : Fin P.n → Nat → FG.Att P.n → Prop)
    (Origin : Fin P.n → Nat → Nat → NodeBlock P ACP → Prop)
    (Joined : Fin P.n → Time → Prop) (U : Set (NodeBlock P ACP)) (Hz : Nat) (b : Time) :
    HighFrameRootBefore acp₀ st time H Sign Origin Joined U Hz b := by
  intro hU hmono hsub hobs hsource y k B frame hy hkb hreach hgen hq hhigh hprior hframe
  rw [hframe]
  exact (high_roots_before acp₀ st time H Sign Origin Joined U Hz b
    hU hmono hsub hobs hsource y k B hy hkb hreach hgen hq hhigh hprior).2.2

end Consensus.Goldilocks.LocalSources

end
