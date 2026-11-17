module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Inv
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Persist: the vote step of C1.1's induction

The induction of C1.1 (claims C1.1, "Proof shape"; F.5 (run)) over the cut index of the run, for
fixed premises `PersistPremises … s m B …`, has an invariant at cut `k` with two parts:

* `VoteInv k`, (i) and (ii) at the honest votes cast at cut `k` of a slot in `(s, m]`;
* `CutInv k`, G1.10 at the scope of C1.1 at an honest call at cut `k` in `[t_s, t_m + 2Δ)`: the
  caches after the call are compatible with `B`, and an accepted block satisfies (a) and (b).

This file holds the vote step (`vote_step`), from the invariant at strictly earlier cuts; the
persistence kernel of the obligations endpoint (`Lemmas/Compose/PersistKernelGoldilocks`) joins
it with the cut step over the cut index. `not_proposesAt_mid`: no proposal is made at `t_{s'} + 2Δ`.
-/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

variable {tr H}
variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {ΔF : Time} {x : Fin sp.n}
  {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
  {proposer : Nat → Fin sp.n}

/-- **The vote step**: (i) and (ii) at the honest votes of cut `k`, from the invariant at every
earlier cut: the caches at the vote (`state_caches`) and (K2) give (i) (`vote_viable`), and (i)
with the earlier votes gives (ii) (`vote_extends`). -/
theorem vote_step (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV)
    (k : Nat) (ih : ∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j) :
    VoteInv tr H s m B k := by
  rw [voteInv_iff]
  intro y hy ℓ e hc hs hsm
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl).localRun
  obtain ⟨-, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hle : tr.time k ≤ sp.ts e.msg.slot + sp.Δ := (cast_head_fcRoot hr hy hc).2
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr
      (by rw [(SA.castAt_spec hr hy hc).2.1])
  have hk : sp.ts s ≤ tr.time k := ((SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hs.le)).trans hts
  have hlt : ∀ j < k, tr.time j < sp.ts m + 2 * sp.Δ := fun j hj => by
    have := hrun.time_mono hj.le
    have := (SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hsm)
    linarith
  have hcache := state_caches hrun hp k (fun j hj => (ih j hj).2) y hy hk hlt
  have hK2 := hp.clean.heightLead y hy k ℓ e hc hs hsm
  have hvi := vote_viable hrun hp.noColl hy hc hcache hK2
  exact ⟨hvi, vote_extends hrun hp hy hc hs hsm hvi
    fun z hz j hj e' ⟨ℓ', hc', he'⟩ h₁ h₂ =>
      (voteInv_iff.mp (ih j hj).1 z hz ℓ' e' ⟨hc', he'⟩ h₁ h₂).2⟩

/-- No proposal is processed at `t_{s'} + 2Δ`: slots start at multiples of `4Δ`. -/
theorem not_proposesAt_mid {y : Fin sp.n} {k : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    {s' : Nat} (hX : tr.ProposesAt y k X) (hk : tr.time k = sp.ts s' + sp.Δ + sp.Δ) : False := by
  have h₁ := hX.2.2
  rw [sp.slotTime_eq] at h₁
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  unfold SA.SAParams.ts at hk
  have e : 4 * sp.Δ * (X.slot : Int) = 4 * sp.Δ * s' + sp.Δ + sp.Δ := h₁.symm.trans hk
  have h₂ : sp.Δ * (4 * (X.slot : Int) - 4 * s' - 2) = 0 := by
    ring_nf
    ring_nf at e
    linarith
  rcases mul_eq_zero.mp h₂ with h | h
  · exact hΔ.ne' h
  · have h' : 4 * (X.slot : Int) - 4 * (s' : Int) - 2 = 0 := h
    omega

end Consensus.Goldilocks.Compose

end
