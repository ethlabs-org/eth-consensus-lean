module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutSteps

public section

/-! # Goldilocks Healing, HR.4: the cut step and the attestations

The cut step (`retention_cut_step`, G1.10 at the height-scoped scope) and (R1)'s attestations
(`high_rows`, the provenance of the high sources).

* **Attestations**: an honest attestation of height `≥ H_z + 1` signed at cut `d` names the
  entry of the chain of a high origin written by the signer before `d` (`high_row_source`, from the
  stored fast-lock provenance).
* **Prefix comparison**: with `VoteInv` through cut `k`, every high origin written by `k` is
  comparable with every high origin active at `k` (`origins_compatible_prefix`): earlier labels
  by the honest votes of the later label (`fastLock_compatible_of_votes`; the votes of a pending
  label precede `t_{j+1}`), the same label by TSQ (`fastLock_same_slot`).
* **The cut step**: every honest attestation on a block of the store after cut `k` was
  signed before `k`, so (attestations, prefix comparison) none names a high entry that conflicts
  with `B`; the prefix-local core (`Store.entry_kept`) keeps such an entry unjustified, so a high
  `Σ.J` is compatible with `B` (`Store.J_compatible_of_rows`); `Σ.F ⪯ Σ.J` follows it, and a low
  one is below `B` by G1.2 at strict height (`low_finalized_below_origin`). No (K0) is used. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### Run facts -/

/-! ### The prefix comparison of origins -/

/-- Finite prefix comparison bounds both writes and the votes used by the
induction hypothesis. Activation may precede the target's eventual write. -/
theorem ResetPremisesUpTo.origins_compatible_prefix {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {k : Nat}
    (hvote : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
      ∀ z ∈ H, ∀ c ≤ k, tr.time c ≤ b → ∀ e, SA.VoteAt tr.projAC z c e →
        j₀ < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hact : i ≤ k ∨ sp.ts (j + 1 : Nat) ≤ tr.time k) {x' : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho' : HighOrigin tr H g x' r l O)
    (hrk : r ≤ k) (hrb : tr.time r ≤ b) : Compatible (tr.HonestBlocks H) B O := by
  have hg : g ≤ sp.ts j := by
    have h₁ := hp.cutZ_le_ts_of_highOrigin ho
    have h₂ := lt_cutZ sp g
    have h₃ := le_gbar g
    have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
    linarith
  apply hp.origins_compatible_before (k := k + 1)
    (fun ho₀ hi₀ z hz c hc => hvote ho₀ hi₀ z hz c (by omega)) ho hg ?_ ho'
    (by omega) hib hrb
  rcases hact with h | h
  · exact Or.inl (by omega)
  · refine Or.inr fun c hc => ?_
    by_contra hck
    exact (not_lt_of_ge (h.trans (hp.run.time_mono (show k ≤ c by omega)))) hc

/-! ### The cut step and the attestations -/

/-- A signed high attestation before a bounded cut names an entry comparable with an
active bounded origin, using only vote extension through that cut. -/
theorem ResetPremisesUpTo.row_compatible {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {k : Nat}
    (hvote : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
      ∀ z ∈ H, ∀ c ≤ k, tr.time c ≤ b → ∀ e, SA.VoteAt tr.projAC z c e →
        j₀ < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hact : i ≤ k ∨ sp.ts (j + 1 : Nat) ≤ tr.time k) {v : Fin sp.n} (hv : v ∈ H) {d : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hdk : d ≤ k) (hdb : tr.time d ≤ b)
    (hh : HZ tr H g + 1 ≤ att.h) {E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hEU : E ∈ tr.HonestBlocks H) (hEr : E.root = att.T) :
    Compatible (tr.HonestBlocks H) E B := by
  have hU := hp.honest_coherent
  obtain ⟨r, hrd, l, O, hoO, E₀, hE₀, hE₀O, hE₀r, -⟩ := hp.high_row_source hv hs hh
  obtain rfl : E = E₀ := hU.1 hEU ⟨v, hv, r, hE₀⟩ (hEr.trans hE₀r.symm)
  have hBO := hp.origins_compatible_prefix hvote ho hib hact hoO (by omega)
    ((hp.run.time_mono hrd.le).trans hdb)
  exact Goldilocks.Store.compatible_of_anc hU (hE₀O.mono fun X hX => ⟨v, hv, r, hX⟩) hBO.symm

/-- **The cut step: G1.10 at the height-scoped scope** (claims HR.4, G1.10 "The healing reset
induction uses the same node with a height-scoped `𝓔`"). (R2) after the honest call at cut `k`, from
the invariant at the earlier cuts and the votes of cut `k`. With `𝓔_B` the entries of height
`≥ H_z + 1` that conflict with `B`: every honest attestation on a block of the store after cut `k`
was signed before `k` (unforgeability), so it names no entry of `𝓔_B` (`row_compatible`: its entry
is below a high origin written before the signing, comparable with `B` by the votes through `k`); so
the counted attestations naming an entry of `𝓔_B` are faulty, fewer than `q`, and no entry of `𝓔_B`
is justified on the store (`Store.J_compatible_of_rows`): a high `Σ.J` is compatible with `B`, and
so is `Σ.F ⪯ Σ.J`; when `Σ.J` is low, `Σ.F` is below `B` by G1.2 (`low_finalized_below_origin`). No
(K0) is used: `Store.cut_scope` (C1.1's scope) does not apply, since it assumes (K0) for `Σ.J` and
(K1) for every conflicting entry above an honest `Σ.F` at `Ts`, low ones included, which fail at
`a_z`. -/
theorem ResetPremisesUpTo.retention_cut_step {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {k : Nat}
    (hvote : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
      ∀ z ∈ H, ∀ c ≤ k, tr.time c ≤ b → ∀ e, SA.VoteAt tr.projAC z c e →
        j₀ < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    (hkb : tr.time k ≤ b) {y : Fin sp.n} (hy : y ∈ H) (hc : tr.IsCall y k)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hact : i ≤ k ∨ sp.ts (j + 1 : Nat) ≤ tr.time k) :
    Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.post k).fg.hj → Compatible (tr.HonestBlocks H) (tr.post k).fg.J B) := by
  obtain ⟨c, hc'⟩ := hc
  rw [← Trace.state_succ_of_call _ hc']
  have hU := Compose.honest_blocks_coherent hp.run.toLocalRun hp.noColl
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy (k + 1)
  have hsub : (tr.state y (k + 1)).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, k + 1, hX⟩
  obtain ⟨CV, hst⟩ := ho.2.2.1
  obtain ⟨hBt, -⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
  have hgB := ((Goldilocks.Store.accepted_tree _ _ _ _
    (Compose.fg_reachable hp.run.toLocalRun ho.1 i)).2.2.2 B hBt).mono
      (fun X hX => (⟨x, ho.1, i, hX⟩ : X ∈ tr.HonestBlocks H))
  -- no honest attestation on the store names a high entry that conflicts with `B`
  have hrow : ∀ E ∈ (tr.state y (k + 1)).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y (k + 1)).fg.σ E.root).h →
      ((tr.state y (k + 1)).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocks H) E B →
      ∀ W ∈ (tr.state y (k + 1)).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root → att.val ∉ H := by
    intro E hE hEh _ hnc W hW att ha haT haH
    rcases tree_accepted hp.run.toLocalRun hy hW with rfl | ⟨i', hi', hA⟩
    · cases ha
    obtain ⟨d, hdi, hsd⟩ :=
      hp.run.toLocalRun.att_unforgeable y hy i' att (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) haH
    obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run haH hsd
    obtain rfl : E' = E := hU.1 ⟨_, haH, d, hE'⟩ (hsub hE) (hE'r.trans haT)
    have hσ := σ_eq_honest hp.run hp.noColl haH hy hE' hE
    exact hnc (hp.row_compatible hvote ho hib hact haH hsd (by omega)
      ((hp.run.time_mono (by omega)).trans hkb)
      (by rw [← hE'h, hσ]; exact hEh) (hsub hE) haT.symm)
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have hf := hp.faults
    have hn := sp.toParams.hn
    change 3 * Hᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change Hᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  have hJ : HZ tr H g + 1 ≤ (tr.state y (k + 1)).fg.hj →
      Compatible (tr.HonestBlocks H) (tr.state y (k + 1)).fg.J B :=
    Store.J_compatible_of_rows hreach hq hU hsub hgB hrow
  refine ⟨?_, hJ⟩
  obtain ⟨-, -, hFJ, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  by_cases hlow : (tr.state y (k + 1)).fg.hj ≤ HZ tr H g
  · exact Or.inl (low_finalized_below_high_block_of_run hp.run hp.noColl hp.faults
      hy ho.1 hBt ho.2.2.2 hlow)
  · exact Goldilocks.Store.compatible_of_anc hU (hFJ.mono hsub) (hJ (by omega))

/-- Whole-run specialization of the finite cut step. -/
theorem retention_cut_step (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') (hv : VoteInv tr H g k) :
    CacheInv tr H g a k := by
  refine cacheInv_iff.2 fun y hy hc _ x i j B ho hact => ?_
  have hvk : ∀ k' ≤ k, VoteInv tr H g k' := fun k' hk' => by
    rcases hk'.lt_or_eq with h | rfl
    · exact (ih k' h).1
    · exact hv
  apply (hp.toUpTo tr H (le_max_left a (max (tr.time i) (tr.time k)))).retention_cut_step
    (fun ho₀ _ z hz c hc _ e ⟨ℓ, hcl, he⟩ hsl =>
      ((voteInv_iff.1 (hvk c hc)) _ _ _ _ ho₀ z hz ℓ e ⟨hcl, he⟩ hsl).1)
    ((le_max_right _ _).trans (le_max_right _ _)) hy hc ho
    ((le_max_left _ _).trans (le_max_right _ _)) hact

/-- **(R1), the attestations** (HR.1 (a), A1.5 with `τ = ḡ`). The source
`C` of an honest attestation of height `≥ H_z + 1` is the viable ancestor of a live fast lock's
block, which is at or below the stored block `B` of a fast-lock write of the signer before the
signing (`stored_fast_lock_provenance`); the attestation's height pair is `C`'s height and entry, so
`B` has state height `≥ σ[C].h ≥ H_z + 1` (a high origin), and the named entry is the entry at that
height on `B`'s chain in the writer's tree (`high_row_source`). -/
theorem high_rows (hp : ResetPremises tr H proposer dg g ΔF a) :
    ∀ y ∈ H, ∀ k att, tr.SignAt y k att → a ≤ tr.time k → HZ tr H g + 1 ≤ att.h →
      ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
        (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
        ((tr.state x i).fg.σ E.root).Th = E.root := by
  intro y hy k att hs _ hh
  obtain ⟨r, -, l, O, ho, E, hE, hEO, hEr, hEh, hETh⟩ := high_row_source hp hy hs hh
  exact ⟨y, r, l, O, ho, E, hE, hEO, hEr, hEh, hETh⟩

end Consensus.Goldilocks.Healing

end
