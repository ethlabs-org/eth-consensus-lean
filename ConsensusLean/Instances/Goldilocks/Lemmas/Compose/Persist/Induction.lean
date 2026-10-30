module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups

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

/-- C1.1 (i) and (ii) at the honest votes cast at cut `k` of a slot in `(s, m]`. (i) reads "at or
below `fc_root`" in the honest blocks (claims C1.1; the frame-tree reading of `ViableAtVote` fails
once honest finality passes `B`, consensus-lean#78). -/
def VoteInv (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (k : Nat) : Prop :=
  ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot → e.msg.slot ≤ m →
    (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) ∧
    SA.VoteExtends (tr.HonestBlocks H) e.msg B

/-- G1.10 at the scope of C1.1 at an honest call at cut `k` in `[t_s, t_m + 2Δ)`: the caches
after the call are compatible with `B`, and a block it accepts satisfies (a) and (b). -/
def CutInv (s m : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))) (k : Nat) : Prop :=
  ∀ y ∈ H, tr.IsCall y k → sp.ts s ≤ tr.time k → tr.time k < sp.ts m + 2 * sp.Δ →
    (Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.post k).fg.J B) ∧
    ∀ X, tr.AcceptAt y k X →
      let S := (tr.post k).fg
      (∀ A' ∈ S.tree, S.Anc A' X → ∀ Jb, S.blocks (S.σ A'.root).J = some Jb →
        Compatible (tr.HonestBlocks H) Jb B) ∧
      (¬ Compatible (tr.HonestBlocks H) X B →
        ∀ Pc, Anc (tr.HonestBlocks H) Pc X → Anc (tr.HonestBlocks H) Pc B →
          (∀ Q, Anc (tr.HonestBlocks H) Q X → Anc (tr.HonestBlocks H) Q B →
            Anc (tr.HonestBlocks H) Q Pc) →
          (S.σ X.root).h ≤ (S.σ Pc.root).h + 1)

variable {tr H}
variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {ΔF : Time} {x : Fin sp.n}
  {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}

/-- **The vote step**: (i) and (ii) at the honest votes of cut `k`, from the invariant at every
earlier cut. (i) from the caches at the vote (`state_caches`, (K0)) and (K2); (ii) by A1.2 /
A1.4 (a) for slot `s + 1` and A1.3 after (their stored-block forms, #75). -/
theorem vote_step (hrun : GoldilocksRun dg H tr) (hp : PersistPremises tr H dg ΔF x i₀ s m B CV)
    (k : Nat) (ih : ∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j) :
    VoteInv tr H s m B k := by
  sorry

/-- **The cut step**: G1.10 at the scope of C1.1 at the honest call of cut `k`, from the
invariant at every earlier cut and the votes of cut `k`. The honest rows it needs are signed at
earlier cuts, with sources compatible with `B` by A1.9 (its stored-block form, #75). -/
theorem cut_step (hrun : GoldilocksRun dg H tr) (hp : PersistPremises tr H dg ΔF x i₀ s m B CV)
    (k : Nat) (ih : ∀ j < k, VoteInv tr H s m B j ∧ CutInv tr H s m B j)
    (hv : VoteInv tr H s m B k) : CutInv tr H s m B k := by
  sorry

/-- The state of `y` before cut `k` is its state before cut `j ≤ k`, or the state after a call of
`y` at a cut in `[j, k)`. -/
theorem state_of_le {y : Fin sp.n} {j k : Nat} (h : j ≤ k) :
    tr.state y k = tr.state y j ∨ ∃ j', j ≤ j' ∧ j' < k ∧ tr.IsCall y j' ∧
      tr.state y k = tr.post j' := by
  induction k, h using Nat.le_induction with
  | base => exact Or.inl rfl
  | succ k hjk ih =>
    by_cases hc : tr.IsCall y k
    · obtain ⟨c, hc'⟩ := hc
      exact Or.inr ⟨k, hjk, k.lt_succ_self, ⟨c, hc'⟩, Trace.state_succ_of_call _ hc'⟩
    · rw [Trace.state_succ_of_not _ fun c hc' => hc ⟨c, hc'⟩]
      exact ih.imp_right fun ⟨j', h₁, h₂, h₃, h₄⟩ => ⟨j', h₁, h₂.trans k.lt_succ_self, h₃, h₄⟩

/-- **The caches of a state**: at a cut `k` at or after `t_s` whose earlier cuts are in the
window, the caches of an honest node's state are those after its last call (`CutInv`) or, when
that call is before `t_s`, those at `t_s` ((K0)). -/
theorem state_caches (hrun : GoldilocksRun dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) (k : Nat)
    (hcut : ∀ j < k, CutInv tr H s m B j) (y : Fin sp.n) (hy : y ∈ H) (hk : sp.ts s ≤ tr.time k)
    (hle : ∀ j < k, tr.time j < sp.ts m + 2 * sp.Δ) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B ∧
      Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B := by
  classical
  have hex : ∃ j, sp.ts s ≤ tr.time j := ⟨k, hk⟩
  have hj₀k : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hfirst : tr.FirstCutFrom (Nat.find hex) (sp.ts s) :=
    ⟨Nat.find_spec hex, fun j hj => not_le.mp (Nat.find_min hex hj)⟩
  rcases state_of_le (tr := tr) (y := y) hj₀k with h | ⟨j', hj', hj'k, hc, h⟩
  · rw [h]
    exact hp.clean.caches y hy _ hfirst
  · rw [h]
    exact (hcut j' hj'k y hy hc
      ((Nat.find_spec hex).trans (hrun.time_mono hj')) (hle j' hj'k)).1

/-- **The join**: the invariant holds at every cut (strong induction on the cut index, F.5). -/
theorem persist_inv (hrun : GoldilocksRun dg H tr)
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) :
    ∀ k, VoteInv tr H s m B k ∧ CutInv tr H s m B k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih => exact ⟨vote_step hrun hp k ih, cut_step hrun hp k ih (vote_step hrun hp k ih)⟩

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
  intro sp ro dg H tr ΔF x i₀ s m B CV hrun hp s' hs hsm
  have hinv := persist_inv hrun hp
  have hts : sp.ts s' ≤ sp.ts m := (SA.ts_le_iff sp).mpr (by exact_mod_cast hsm)
  have hts₀ : sp.ts s ≤ sp.ts s' := (SA.ts_le_iff sp).mpr (by exact_mod_cast hs.le)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  refine ⟨fun y hy => ⟨fun i X hacc hi hwin => ?_, fun k hk => ?_, fun k X hX hk _ => ?_⟩,
    fun y hy i ℓ e hc hsl => ?_, fun y hy i e ⟨ℓ, hc, he⟩ hsl => ?_⟩
  · refine ((hinv i).2 y hy ⟨_, hacc⟩ hi ?_).2 X hacc
    rcases hwin with h | ⟨h, hX⟩
    · linarith
    · exact (not_proposesAt_mid hX h).elim
  · rcases hk with ⟨-, hk₀, hk₁⟩ | ⟨hk₀, hk₁⟩
    · exact state_caches hrun hp k (fun j _ => (hinv j).2) y hy hk₀
        fun j hj => by have := hrun.time_mono hj.le; linarith
    · exact state_caches hrun hp k (fun j _ => (hinv j).2) y hy (by linarith)
        fun j hj => by have := hk₁ j hj; linarith
  · exact (not_proposesAt_mid hX hk).elim
  · -- C1.1 (i) as stated reads "at or below `fc_root`" in the frame tree, which fails once
    -- honest finality passes `B` (consensus-lean#78); `VoteInv` proves the claims' reading.
    sorry
  · exact ((hinv i).1 y hy ℓ e ⟨hc, he⟩ (hsl ▸ hs) (hsl ▸ hsm)).2

/-- **C1.1's corollary, recent source, next vote**: C1.1 (ii) at slot `m + 1`. -/
theorem recent_source_next_vote : RecentSourceNextVote := by
  intro sp ro dg H tr ΔF x i₀ i j m ℓ B CV hrun hp _ _ hjm _ y hy k e hv hsl
  exact (honest_fast_confirmations_persist sp ro dg H tr ΔF x i₀ j (m + 1) B CV hrun hp (m + 1)
    (by omega) le_rfl).extends_ y hy k e hv hsl

end Consensus.Goldilocks.Compose

end
