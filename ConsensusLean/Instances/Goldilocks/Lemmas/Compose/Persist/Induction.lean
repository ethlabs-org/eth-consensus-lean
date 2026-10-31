module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Inv
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Cut

public section

/-! # Goldilocks Persist, part 2: C1.1 by the first violating event

The induction of C1.1 (claims C1.1, "Proof shape"; F.5 (run)) over the cut index of the run, for
fixed premises `PersistPremises … s m B …`. The invariant at cut `k` has two parts:

* `VoteInv k`, (i) and (ii) at the honest votes cast at cut `k` of a slot in `(s, m]`;
* `CutInv k`, G1.10 at the scope of C1.1 at an honest call at cut `k` in `[t_s, t_m + 2Δ)`: the
  caches after the call are compatible with `B`, and an accepted block satisfies (a) and (b).

The steps (`vote_step`, `cut_step`) use the invariant at strictly earlier cuts only, and
`state_caches` reads the caches of a state off the last call before it (or (K0)). The join
(`persist_inv`) is strong induction on the cut index, and `honest_fast_confirmations_persist`
assembles C1.1's conclusion from the invariant. -/

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

/-- **The cut step**: G1.10 at the scope of C1.1 at the honest call of cut `k`, from the
invariant at every earlier cut. The honest rows it needs are signed at
earlier cuts, with sources compatible with `B` by A1.9 (its stored-block form, #75). -/
theorem cut_step (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV)
    (k : Nat) (ih : ∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j) :
    CutInv tr H s m B k :=
  cut_inv_step hrun hp k ih

/-- **The join**: the invariant holds at every cut (strong induction on the cut index, F.5). -/
theorem persist_inv (hrun : GoldilocksRun proposer dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) :
    ∀ k, VoteInv tr H s m B k ∧ CutInv tr H s m B k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih => exact ⟨vote_step hrun hp k ih, cut_step hrun hp k ih⟩

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

/-- **C1.1, honest fast confirmations persist.** -/
theorem honest_fast_confirmations_persist : HonestFastConfirmationsPersist := by
  intro sp ro dg H tr ΔF x i₀ s m B CV proposer hrun hp s' hs hsm
  have hinv := persist_inv hrun hp
  have hts : sp.ts s' ≤ sp.ts m := (SA.ts_le_iff sp).mpr (by exact_mod_cast hsm)
  have hts₀ : sp.ts s ≤ sp.ts s' := (SA.ts_le_iff sp).mpr (by exact_mod_cast hs.le)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  refine ⟨fun y hy => ⟨fun i X hacc hi hwin => ?_, fun k hk => ?_, fun k X hX hk _ => ?_⟩,
    fun y hy i ℓ e hc hsl => ?_, fun y hy i e ⟨ℓ, hc, he⟩ hsl => ?_⟩
  · refine (cutInv_iff.mp (hinv i).2 y hy ⟨_, hacc⟩ hi ?_).2 X hacc
    rcases hwin with h | ⟨h, hX⟩
    · linarith
    · exact (not_proposesAt_mid hX h).elim
  · rcases hk with ⟨-, hk₀, hk₁⟩ | ⟨hk₀, hk₁⟩
    · exact state_caches hrun hp k (fun j _ => (hinv j).2) y hy hk₀
        fun j hj => by have := hrun.time_mono hj.le; linarith
    · exact state_caches hrun hp k (fun j _ => (hinv j).2) y hy (by linarith)
        fun j hj => by have := hk₁ j hj; linarith
  · exact (not_proposesAt_mid hX hk).elim
  · have := (voteInv_iff.mp (hinv i).1 y hy ℓ e hc (hsl ▸ hs) (hsl ▸ hsm)).1
    rwa [hsl] at this
  · exact (voteInv_iff.mp (hinv i).1 y hy ℓ e ⟨hc, he⟩ (hsl ▸ hs) (hsl ▸ hsm)).2

/-- **C1.1's corollary, recent source, next vote**: C1.1 (ii) at slot `m + 1`. -/
theorem recent_source_next_vote : RecentSourceNextVote := by
  intro sp ro dg H tr ΔF x i₀ i j m ℓ B CV proposer hrun hp _ _ hjm _ y hy k e hv hsl
  exact (honest_fast_confirmations_persist sp ro dg H tr ΔF
    x i₀ j (m + 1) B CV proposer hrun hp (m + 1)
    (by omega) le_rfl).extends_ y hy k e hv hsl

end Consensus.Goldilocks.Compose

end
