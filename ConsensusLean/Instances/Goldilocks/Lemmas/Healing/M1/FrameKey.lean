module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Phase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.WeakBase

public section

/-! # The frame key of an honest store

The frame key of a store is
`κ = 3·h_max + c`, with `c = 2` in a contest, `c = 1` at `h_max = h_j + 1` without a contest,
and `c = 0` otherwise. This is the lexicographic key `(h_max, b, C)` coded in `ℕ`
(a contest implies `b`).

* `frameKey_eq_*`: equal keys (at any two honest cuts) give equal `head_height_floor`, contest
  status and root kind, and, in kind J, equal `Σ.J`. So the key determines the `FrameWindow`
  fields. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

open Classical in
/-- The frame key `3·h_max + c`; equal keys give the fields of a `FrameWindow`. -/
noncomputable def frameKey {P : Params} {ACP : Type} (st : Store P ACP) : Nat :=
  3 * st.hmax + (if st.Contest then 2 else if st.hmax = st.hj + 1 then 1 else 0)

open Classical in
theorem frameKey_def {P : Params} {ACP : Type} (st : Store P ACP) : frameKey st =
    3 * st.hmax + (if st.Contest then 2 else if st.hmax = st.hj + 1 then 1 else 0) := by
  unfold frameKey
  rfl

/-- The merge map `φ(3h + c) = 2h + c` (`c < 3`). It identifies `3h + 2` (contest at `h`) with
`3(h + 1)` (gap at `h + 1`): both frames have floor `h`, root `Σ.F` and no `J` constraint. -/
def keyMerge (n : Nat) : Nat := 2 * (n / 3) + n % 3

theorem keyMerge_eq (n : Nat) : keyMerge n = 2 * (n / 3) + n % 3 := by
  unfold keyMerge
  rfl

theorem keyMerge_mono {m n : Nat} (h : m ≤ n) : keyMerge m ≤ keyMerge n := by
  unfold keyMerge
  omega

/-- The merged frame key `κ′ = φ(κ)`. For `h_max ≥ 1` it is `2·floor + 2 + [kind J]`, so a
contest at `h` and a gap at `h + 1` have the same key. -/
noncomputable def frameKey' {P : Params} {ACP : Type} (st : Store P ACP) : Nat :=
  keyMerge (frameKey st)

theorem frameKey'_def {P : Params} {ACP : Type} (st : Store P ACP) :
    frameKey' st = keyMerge (frameKey st) := by
  unfold frameKey'
  rfl

section Store

variable {P : Params} {ACP : Type} {a b : Store P ACP}

theorem frameKey_bounds (st : Store P ACP) :
    3 * st.hmax ≤ frameKey st ∧ frameKey st ≤ 3 * st.hmax + 2 := by
  unfold frameKey
  split_ifs <;> omega

theorem frameKey'_bounds {HZ : Nat} (h1 : HZ ≤ a.hmax) (h2 : a.hmax ≤ HZ + 1) :
    2 * HZ ≤ frameKey' a ∧ frameKey' a ≤ 2 * HZ + 4 := by
  have := frameKey_bounds a
  unfold frameKey' keyMerge
  omega

/-- Equal merged keys give equal `head_height_floor` and equal root kind. The contest flag and
`h_max` can differ. -/
theorem frameKey'_eq_floor_kind (ha : 1 ≤ a.hmax) (hb : 1 ≤ b.hmax)
    (h : frameKey' a = frameKey' b) :
    a.headHeightFloor = b.headHeightFloor ∧
      ((a.hmax = a.hj + 1 ∧ ¬a.Contest) ↔ (b.hmax = b.hj + 1 ∧ ¬b.Contest)) := by
  classical
  unfold frameKey' keyMerge at h
  rw [frameKey_def, frameKey_def] at h
  unfold Store.headHeightFloor
  by_cases ca : a.Contest <;> by_cases cb : b.Contest <;>
    by_cases ka : a.hmax = a.hj + 1 <;> by_cases kb : b.hmax = b.hj + 1 <;>
    (simp [ca, cb, ka, kb] at h ⊢) <;> omega

end Store

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

theorem store_eq_fg (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) : tr.projFG.store y i = (tr.state y i).fg := by
  simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]

/-- `h_j < h_max` in every honest store. -/
theorem hj_lt_hmax (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) : (tr.state y i).fg.hj < (tr.state y i).fg.hmax := by
  have hR := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨-, -, -, ⟨Bj, hBj, -, hBjhj⟩, hge, -, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hR
  exact hBjhj ▸ (Store.hj_lt_h hR hBj).trans_le (hge Bj hBj)

/-- `h_j` of an honest store does not decrease. -/
theorem hj_mono (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {i j : Nat} (hij : i ≤ j) : (tr.state y i).fg.hj ≤ (tr.state y j).fg.hj := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    apply ih.trans
    by_cases hc : ∃ c, tr.CallAt y j c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      have h := hrun.cutLaw y hy j c hc
      cases c with
      | ac ℓ => rw [h.2.2.1]
      | fg c =>
        cases c with
        | block B ok =>
          cases ok with
          | false => rw [h.2]
          | true =>
            obtain ⟨pr, σ, _, _, _, _, _, he⟩ := Store.onBlock_eq_some h.2.1
            rw [he]
            obtain ⟨atts, hatt⟩ := Store.addAtts_eq
              (Store.updateFinality _ σ) B.fgPayload
            rw [hatt]
            exact Healing.updateFinality_hj_le
              { (tr.state y j).fg with
                blocks := Function.update (tr.state y j).fg.blocks B.root (some B),
                σ := Function.update (tr.state y j).fg.σ B.root σ } σ
        | attestation a =>
          rw [h.1]
          obtain ⟨atts, he⟩ := Store.onAttestation_eq (tr.state y j).fg a
          rw [he]
        | attest C att =>
          cases att with
          | none => rw [h.2]
          | some att => rw [h.2.1]
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

/-- PhaseCount (a) at store level: two honest stores with equal `h_j` have equal `Σ.J`. -/
theorem J_eq_of_hj_eq_run (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H)
    {i m : Nat} (he : (tr.state y i).fg.hj = (tr.state z m).fg.hj) :
    (tr.state y i).fg.J = (tr.state z m).fg.J := by
  have hRy := Compose.fg_reachable hrun.toLocalRun hy i
  have hRz := Compose.fg_reachable hrun.toLocalRun hz m
  obtain ⟨-, hJy, -, ⟨By, hBy, hByJ, hByhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hRy
  obtain ⟨-, hJz, -, ⟨Bz, hBz, hBzJ, hBzhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hRz
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have hfg := Compose.fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc
  have h := J_eq_of_hj_eq hfg hf hy hz (i := i) (j := m) (B := By) (B' := Bz)
    (by rw [store_eq_fg hrun hy]; exact hBy) (by rw [store_eq_fg hrun hz]; exact hBz)
    (by rw [store_eq_fg hrun hy, store_eq_fg hrun hz]; omega)
  rw [store_eq_fg hrun hy, store_eq_fg hrun hz] at h
  exact (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1 ⟨y, hy, i, hJy⟩ ⟨z, hz, m, hJz⟩
    (hByJ.symm.trans (h.trans hBzJ))

/-- `Σ.F` of an honest store is below every honest-held block of state height `≥ h_max`
(G1.2 with `h_F ≤ h_j < h ≤ h_max`). -/
theorem F_anc_of_hmax_le (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H)
    {i m : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z m).fg.tree)
    (hh : (tr.state y i).fg.hmax ≤ ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocks H) (tr.state y i).fg.F W := by
  have hR := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨hF, -, -, -, hge, -, X, hX, hXF⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hR
  obtain ⟨c, -, -, -, hc⟩ := Goldilocks.Store.chain_state_of_chain _ _ _ _ hR X hX
  have hinv := FG.chain_invariants _ _ _ hc
  have hXh := hge X hX
  have hstrict : ((tr.state y i).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h := by
    have h1 := hinv.2.1
    have h2 := hinv.2.2.1
    omega
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have hfg := Compose.fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc
  have h := finalized_anc_of_lt_fg hfg hf hy hz (k := i) (m := m)
    (X := X) (F := (tr.state y i).fg.F) (W := W)
  rw [store_eq_fg hrun hy, store_eq_fg hrun hz] at h
  exact h hX hF hXF.symm hW hstrict

/-- Equal merged keys at two honest cuts in kind J give equal `Σ.J`. -/
theorem frameKey'_eq_J (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H)
    {i m : Nat} (h : frameKey' (tr.state y i).fg = frameKey' (tr.state z m).fg)
    (hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧ ¬(tr.state y i).fg.Contest) :
    (tr.state y i).fg.J = (tr.state z m).fg.J := by
  classical
  have h1 := hj_lt_hmax hrun hy i
  have h2 := hj_lt_hmax hrun hz m
  obtain ⟨hfl, hkd⟩ := frameKey'_eq_floor_kind (by omega) (by omega) h
  have hk' := hkd.1 hk
  apply J_eq_of_hj_eq_run hrun hnc hf hy hz
  unfold Store.headHeightFloor at hfl
  simp [hk.2, hk'.2] at hfl
  omega

end Consensus.Goldilocks.Healing

end
