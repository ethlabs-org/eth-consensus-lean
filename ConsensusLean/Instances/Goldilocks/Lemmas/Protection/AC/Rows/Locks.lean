module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Rows.Counts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutagePostStop
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection, the lock rows over AC traces: no honest lock conflicting with `P`

The lock rows of the outage protection (`Compose/Regimes/OutagePostStop`,
`Obligations/OutageLockSafety/Locks`, `…/Reader`) as standalone lemmas over an AC trace with the
unlock given at a write mode (`ACLocalRunU wm u`, `ACRunU wm u`), with the honest blocks read as
`U` and the node's frame as the call's frame. Every input the composite rows take from the
premise package or the cut invariant is an explicit hypothesis of the same content: the
compatibility of the results at unpolluted labels with `P` (`hres`), the compatibility with `P`
of the votes of slots `≥ j₀` by honest validators outside the late wakers `W` (`hvc`), the count
`2·|Hᶜ ∪ W| < n` (`hcount`), the compatibility with `P` of the origins within `b₀` (`hpre`, the
pre-`b₀` frontier's `FrontierAC.origins_compatible` against `P`), and the stored locks' own
compatibility (`hlocks`). The unlock is read only through the unlock relation
(`UnlockRel.movesBack`). The gap lemma `Compose.exists_unpolluted_label` is already generic in
the parameters and is reused as it is.

* `slow_lock_compatibleAC` (width `k`): a compatible result at one label of a stored slow lock's
  window makes the lock compatible;
* `locks_compatible_slowAC` (width `k`), `locks_compatible_fastAC`, `locks_compatibleAC`: every
  stored honest lock is on a block compatible with `P` (the slow branch by an unpolluted label of
  the window, the fast branch by the count of the counted validators);
* `fastLock_countedU`: the counted votes of an honest fast lock (`SA.fastLock_counted` with the
  unlock given), whose honest votes were cast by the lock's cut (`fastLock_honest_voteAC`,
  `Rows/Counts`);
* `fastLock_compatible_atAC`, `fastLock_compatibleAC`: an honest fast lock block is compatible
  with `P`;
* `compatible_of_anc_rightAC`, `liveLockBlocks_compatibleAC`: the live lock blocks before an
  honest call are compatible with every block `B ⪯ P`;
* `readPoint_locks_provenance_strictAC` (`SA.readPoint_locks_provenance_strict` with the unlock
  given) and `readPoint_liveLockBlocks_compatible_atAC`: the live lock blocks of an honest vote's
  read point are compatible with every block `B ⪯ P`. -/

namespace Consensus.Goldilocks.Comparison

open SA Compose

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n}

/-! ### Compatibility along ancestry -/

private theorem compat_of_ancAC (hU : Coherent U) {L C B : Blk sp.n FGP} (hLC : Anc U L C)
    (hC : Compatible U C B) : Compatible U L B := by
  rcases hC with h | h
  · exact Or.inl (hLC.trans h)
  · exact Anc.total hU hLC h

private theorem compat_of_voteCompatAC (hU : Coherent U) {v : Vote sp.n} {C R B : Blk sp.n FGP}
    (hR : R ∈ U) (hRr : R.root = v.head) (hCR : Anc U C R) (hv : VoteCompat U v B) :
    Compatible U C B := by
  obtain ⟨Hd, hHd, hHdr, hHdB⟩ := voteCompat_iff.1 hv
  obtain rfl : Hd = R := hU.1 hHd hR (hHdr.trans hRr.symm)
  exact compat_of_ancAC hU hCR hHdB

/-- **Transfer to a block below `P`**: a block compatible with `P` is compatible with every block
`B ⪯ P`. -/
theorem compatible_of_anc_rightAC (hU : Coherent U) {X B P : Blk sp.n FGP} (hBP : Anc U B P)
    (hX : Compatible U X P) : Compatible U X B := by
  rcases hX with h | h
  · exact Anc.total hU h hBP
  · exact Or.inr (hBP.trans h)

/-! ### Slow locks -/

/-- **A single compatible result in the slow window suffices** (at width `k`): for a stored slow
lock of an honest node, when every result of the node at an earlier cut at one label `m` of the
lock's window is compatible with `B`, the lock names a block of `U` compatible with `B`. -/
theorem slow_lock_compatibleAC (hr : ACLocalRunU wm u H U tr) (hw : wm.width = sp.k)
    {B : Blk sp.n FGP} {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {l : Lock}
    (hl : l ∈ (tr.state x i).locks) (hlf : l.fast = false)
    (hgood : ∃ m : Int, (l.slot : Int) - sp.k < m ∧ m ≤ l.slot ∧ 0 ≤ m ∧
      ∀ c C CV, c < i → ResultAt tr x c m.toNat C CV → Compatible U C B) :
    ∃ L ∈ U, L.root = l.block ∧ Compatible U L B := by
  have hU := hr.coherent
  obtain ⟨j, hji, D, hsl, L, hL, hLr, hLD⟩ := slow_lock_provenanceU hr hw hx i l hl hlf
  obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := hsl
  obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hx hupd.1
  obtain ⟨⟨-, -, hDC⟩, -, hslow⟩ := (deepest_mem hdeep).1
  obtain ⟨m, hm, hms, hm0, hgood⟩ := hgood
  refine ⟨L, hL, hLr, compat_of_ancAC hU hLD ?_⟩
  have hmn : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg hm0
  rcases hms.lt_or_eq with hms | hms
  · obtain ⟨S, hS, hSr, hDS⟩ := hslow m hm hms
    obtain ⟨k, hk, R, CV, hR, hRr⟩ := saved_resultU hr hx j m.toNat (by rw [hmn]; exact hSr)
    have hRU : R ∈ U := by
      obtain ⟨ℓ', hu', hR', -⟩ := hR
      exact (frameIn_of_callAtU hr hx hu'.1).2 (deepest_mem hR').1.1
    obtain rfl : R = S := hU.1 hRU (hΦU hS) hRr
    exact compat_of_ancAC hU (Anc.mono hΦU hDS) (hgood k R CV (hk.trans hji) hR)
  · have hmn' : m.toNat = l.slot := by omega
    exact compat_of_ancAC hU (Anc.mono hΦU hDC)
      (hgood j C _ hji (by rw [hmn']; exact ⟨ℓX, hupd, hconf, rfl⟩))

/-- **(i), the slow branch** (at width `k`): under the gap budget `b₁ − b₀ ≤ (4k − 5)Δ`, a stored
slow lock of an honest node at cut `n` names a block of `U` compatible with `P`, when the
results before `n` at the unpolluted labels (`≤ j₀` or `≥ r`) are compatible with `P`: its window
holds an unpolluted label (`Compose.exists_unpolluted_label`). -/
theorem locks_compatible_slowAC (hr : ACLocalRunU wm u H U tr) (hw : wm.width = sp.k)
    {b₀ b₁ : Time} {j₀ r : Nat} {P : Blk sp.n FGP}
    (hj₀ : b₀ < sp.ts (j₀ + 1 : Nat) + 2 * sp.Δ)
    (hrst : ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → r ≤ s)
    (hgap : b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ) {n : Nat}
    (hres : ∀ y ∈ H, ∀ k < n, ∀ m C CV, ResultAt tr y k m C CV → (m ≤ j₀ ∨ r ≤ m) →
      Compatible U C P)
    {y : Fin sp.n} (hy : y ∈ H) {l : Lock} (hl : l ∈ (tr.state y n).locks)
    (hf : l.fast = false) :
    ∃ L ∈ U, L.root = l.block ∧ Compatible U L P := by
  obtain ⟨m, h1, h2, h3⟩ := exists_unpolluted_label sp hgap l.slot
  refine slow_lock_compatibleAC hr hw hy hl hf ?_
  by_cases hm0 : 0 ≤ m
  · refine ⟨m, h1, h2, hm0, fun c C CV hc hR => hres y hy c hc m.toNat C CV hR ?_⟩
    have hmn : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg hm0
    rcases h3 with h | h
    · left
      by_contra hgt
      have := ts_le_tsAC (sp := sp) (show j₀ + 1 ≤ m.toNat by omega)
      rw [hmn] at this
      linarith
    · right
      exact hrst m.toNat (by rw [hmn]; exact h)
  · exact ⟨0, by omega, by omega, le_rfl, fun c C CV hc hR =>
      hres y hy c hc 0 C CV hR (Or.inl (Nat.zero_le _))⟩

/-! ### Fast locks -/

/-- `SA.fastLock_counted` with the unlock given: the counted votes of an honest fast lock of slot
`s` on `B` have at least half of the committee as validators, and each is a slot-`s` vote whose
head, of slot at most `s`, extends `B` inside `U`. -/
theorem fastLock_countedU (hr : ACLocalRunU wm u H U tr) {w : Fin sp.n} (hw : w ∈ H)
    {i₀ s : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr w i₀ s B CV) :
    sp.n ≤ 2 * {x | ∃ v ∈ CV, v.val = x}.ncard ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ U, R.root = v.head ∧ R.slot ≤ s ∧ Anc U B R := by
  rcases hfl with ⟨ℓ, C, ⟨hc, -, -, -⟩, -, hD, rfl⟩ | ⟨ℓ, A, hpt, hsl, hsel, rfl⟩
  · obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hw hc
    refine ⟨?_, ?_⟩
    · have hfast := (deepest_mem hD).1.2.2
      unfold FastTest confirmationScore at hfast
      refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
      rintro x ⟨hx, y, ⟨hy, hres⟩, hval, -, hanc⟩
      exact ⟨y, ⟨hy, hval ▸ hx, hres, hanc⟩, hval⟩
    · rintro v ⟨hvp, -, hres, R, hR, hRr, hBR⟩
      have hvs := state_pool_slotU sp hr hw i₀ s v hvp
      refine ⟨hvs, R, hΦU hR, hRr, ?_, Anc.mono hΦU hBR⟩
      unfold resolutionTime at hres
      split at hres
      · exact absurd hres (by simp [ETime.of])
      · rename_i Hd hl
        obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
        obtain rfl : Hd = R := hΦ.coherent.1 hHd hR (hHdr.trans hRr.symm)
        split_ifs at hres with hlt
        · exact absurd hres (by simp [ETime.of])
        · omega
  · obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hw hpt.1
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h34 := (deepest_mem hsel).1.2.1
    refine ⟨?_, ?_⟩
    · have hsub : optimisticVoters sp A ℓ.frame (sp.slot (tr.time i₀)) B ⊆
          {x | ∃ v ∈ {v | v ∈ A.pool s ∧ AncR ℓ.frame B v.head}, v.val = x} := by
        rintro x ⟨v, hv, rfl, hanc⟩
        exact ⟨v, ⟨hsl ▸ hv, hanc⟩, rfl⟩
      have := Set.ncard_le_ncard hsub
      omega
    · rintro v ⟨hv, R, hR, hRr, hBR⟩
      refine ⟨optimisticPoint_pool_slotU hr hw hpt hv, R, hΦU hR, hRr, ?_, Anc.mono hΦU hBR⟩
      have := frame_slot_leU sp hr hw hpt.1 R hR
      omega

/-- **An honest fast lock block is compatible with `P`, cut-indexed**: a fast update lock or an
optimistic selection of slot `s` of an honest node, whose counted honest votes were cast at cuts
before `n`. Below `j₀` the lock is written at a time `≤ b₀` (`t_{j₀} + 2Δ ≤ b₀`), so its block
is an origin within `b₀`, compatible with `P` (`hpre`); from `j₀` on, a block conflicting with
`P` would have its counted validators in `Hᶜ ∪ W` (`hvc`), against `n ≤ 2·|counted|` and
`2·|Hᶜ ∪ W| < n`. -/
theorem fastLock_compatible_atAC (hr : ACLocalRunU wm u H U tr) {b₀ : Time} {j₀ n : Nat}
    {W : Set (Fin sp.n)} {P : Blk sp.n FGP} (hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀)
    (hpre : ∀ C s, OriginWithinAC tr H C s b₀ → C ∈ U → Compatible U C P)
    (hvc : ∀ x ∈ H, x ∉ W → ∀ k < n, ∀ e, VoteAt tr x k e → j₀ ≤ e.msg.slot →
      VoteCompat U e.msg P)
    (hcount : 2 * (Hᶜ ∪ W).ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr y c s B CV)
    (hcut : ∀ v ∈ CV, v.val ∈ H → ∃ j < n, ∃ e, VoteAt tr v.val j e ∧ e.msg = v) :
    Compatible U B P := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hcnt, hCV⟩ := fastLock_countedU hr hy hfl
  by_cases hs : s < j₀
  · have hsj := ts_le_tsAC (sp := sp) (show s + 1 ≤ j₀ by omega)
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rcases hfl with ⟨ℓ, C, hu, hC, hD, -⟩ | hO
    · have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
      obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hy hu.1
      have hBC : ℓ.frame.Anc B C := (deepest_mem hD).1.1.2.2
      have hCU : C ∈ U := hΦU (deepest_mem hC).1.1
      exact compat_of_ancAC hU (hBC.mono hΦU) (hpre C s
        (originWithinAC_iff.2 ⟨y, hy, c, _, by linarith, Or.inl ⟨ℓ, hu, hC, rfl⟩⟩) hCU)
    · obtain ⟨ℓ, A, hpt, hslot, hsel, -⟩ := id hO
      have hlt : tr.time c < sp.ts (s + 1 : Nat) := by
        by_contra h
        have := (ts_le_iff_le_slot sp (hr.time_nonneg c) ((s + 1 : Nat) : Int)).1 (not_lt.1 h)
        rw [hslot] at this
        omega
      obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hy hpt.1
      have hBt : B ∈ ℓ.frame.tree := by
        unfold optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact (deepest_mem hsel).1.1
      exact hpre B s (originWithinAC_iff.2 ⟨y, hy, c, CV, by linarith, Or.inr hO⟩) (hΦU hBt)
  refine by_contra fun hB => ?_
  have hsub : {x | ∃ v ∈ CV, v.val = x} ⊆ Hᶜ ∪ W := by
    rintro x ⟨v, hv, rfl⟩
    by_contra hx
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hx
    obtain ⟨hvs, R, hRU, hRr, -, hBR⟩ := hCV v hv
    obtain ⟨j', hj', e, hve, rfl⟩ := hcut v hv hx.1
    exact hB (compat_of_voteCompatAC hU hRU hRr hBR (hvc _ hx.1 hx.2 j' hj' e hve (by omega)))
  have := Set.ncard_le_ncard hsub
  omega

/-- **Every honest fast lock block is compatible with `P`**: a fast update lock or an optimistic
selection of an honest node at cut `c`, from the vote compatibility at the cuts up to `c`. -/
theorem fastLock_compatibleAC (hrun : ACRunU wm u proposer tr H U) {b₀ : Time} {j₀ : Nat}
    {W : Set (Fin sp.n)} {P : Blk sp.n FGP} (hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀)
    (hpre : ∀ C s, OriginWithinAC tr H C s b₀ → C ∈ U → Compatible U C P)
    {c : Nat}
    (hvc : ∀ x ∈ H, x ∉ W → ∀ k < c + 1, ∀ e, VoteAt tr x k e → j₀ ≤ e.msg.slot →
      VoteCompat U e.msg P)
    (hcount : 2 * (Hᶜ ∪ W).ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {s : Nat}
    {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr y c s B CV) :
    Compatible U B P :=
  fastLock_compatible_atAC hrun.localRun hj₀ hpre hvc hcount hy hfl fun _ hv hvH =>
    let ⟨j', hj', e, hve, he⟩ := fastLock_honest_voteAC hrun hy hfl hv hvH
    ⟨j', Nat.lt_succ_of_le hj', e, hve, he⟩

/-- **(i), the fast branch**: a stored fast lock of an honest node at cut `n` names a block of
`U` compatible with `P` (`fast_lock_provenanceU`, `fastLock_compatible_atAC`). -/
theorem locks_compatible_fastAC (hrun : ACRunU wm u proposer tr H U) {b₀ : Time} {j₀ n : Nat}
    {W : Set (Fin sp.n)} {P : Blk sp.n FGP} (hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀)
    (hpre : ∀ C s, OriginWithinAC tr H C s b₀ → C ∈ U → Compatible U C P)
    (hvc : ∀ x ∈ H, x ∉ W → ∀ k < n, ∀ e, VoteAt tr x k e → j₀ ≤ e.msg.slot →
      VoteCompat U e.msg P)
    (hcount : 2 * (Hᶜ ∪ W).ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {l : Lock}
    (hl : l ∈ (tr.state y n).locks) (hf : l.fast = true) :
    ∃ L ∈ U, L.root = l.block ∧ Compatible U L P := by
  have hU := hrun.localRun.coherent
  obtain ⟨j, hj, B, CV, hfl, L, hL, hLr, hLB⟩ := fast_lock_provenanceU hrun.localRun hy n l hl hf
  refine ⟨L, hL, hLr, compat_of_ancAC hU hLB
    (fastLock_compatible_atAC hrun.localRun hj₀ hpre hvc hcount hy hfl fun v hv hvH => ?_)⟩
  obtain ⟨j', hj', e, hve, he⟩ := fastLock_honest_voteAC hrun hy hfl hv hvH
  exact ⟨j', by omega, e, hve, he⟩

/-- **(i) at a cut** (at width `k`, `OutageVoteInv.locks_compatible` with its inputs explicit):
every lock stored at cut `n` by an honest node names a block of `U` compatible with `P`. -/
theorem locks_compatibleAC (hrun : ACRunU wm u proposer tr H U) (hw : wm.width = sp.k)
    {b₀ b₁ : Time} {j₀ r n : Nat} {W : Set (Fin sp.n)} {P : Blk sp.n FGP}
    (hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀ ∧ b₀ < sp.ts (j₀ + 1 : Nat) + 2 * sp.Δ)
    (hrst : ∀ s : Nat, b₁ ≤ sp.ts s + sp.Δ → r ≤ s)
    (hgap : b₁ - b₀ ≤ (4 * (sp.k : Time) - 5) * sp.Δ)
    (hpre : ∀ C s, OriginWithinAC tr H C s b₀ → C ∈ U → Compatible U C P)
    (hres : ∀ y ∈ H, ∀ k < n, ∀ m C CV, ResultAt tr y k m C CV → (m ≤ j₀ ∨ r ≤ m) →
      Compatible U C P)
    (hvc : ∀ x ∈ H, x ∉ W → ∀ k < n, ∀ e, VoteAt tr x k e → j₀ ≤ e.msg.slot →
      VoteCompat U e.msg P)
    (hcount : 2 * (Hᶜ ∪ W).ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {l : Lock}
    (hl : l ∈ (tr.state y n).locks) :
    ∃ L ∈ U, L.root = l.block ∧ Compatible U L P := by
  cases hf : l.fast
  · exact locks_compatible_slowAC hrun.localRun hw hj₀.2 hrst hgap hres hy hl hf
  · exact locks_compatible_fastAC hrun hj₀.1 hpre hvc hcount hy hl hf

/-! ### The live locks at a reader and at a read point -/

/-- **(i) at a reader**: before an honest call, when the stored locks name blocks of `U`
compatible with `P`, the live lock blocks in the call's frame are compatible with every block
`B ⪯ P`, at every time. -/
theorem liveLockBlocks_compatibleAC (hr : ACLocalRunU wm u H U tr) {P : Blk sp.n FGP}
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y i ℓ)
    (hlocks : ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ Compatible U L P)
    (τ : Time) {B : Blk sp.n FGP} (hBP : Anc U B P) :
    ∀ X ∈ liveLockBlocks sp (tr.state y i).locks ℓ.frame τ, Compatible U X B := by
  intro X hX
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := mem_liveLockBlocks hΦ hX
  obtain ⟨L, hL, hLr, hLP⟩ := hlocks l hl
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) hL (hB₀r.trans hLr.symm)
  exact compatible_of_anc_rightAC hU hBP
    (compat_of_ancAC hU ((viableAncestor_anc hΦ hB₀).2.mono hΦU) hLP)

private theorem admit_pool_memAC {A : SAState sp.n} {t : Time} {m v : Vote sp.n} {σ : Nat}
    (h : v ∈ (admitVote sp A t m).pool σ) : v ∈ A.pool σ ∨ v = m ∧ m.slot = σ := by
  unfold admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hs
    · subst hs
      rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_singleton.1 h, rfl⟩
    · exact Or.inl h

private theorem receipt_pool_memAC {A : SAState sp.n} {t : Time} {B : Blk sp.n FGP}
    {v : Vote sp.n} {σ : Nat} (h : v ∈ (blockReceipt sp A t B).pool σ) :
    v ∈ A.pool σ ∨ v ∈ blockVotes B ∧ v.slot = σ := by
  have key : ∀ (l : List (Vote sp.n)) (A₀ : SAState sp.n),
      v ∈ (l.foldl (fun A v => admitVote sp A t v) A₀).pool σ →
        v ∈ A₀.pool σ ∨ v ∈ l ∧ v.slot = σ := by
    intro l
    induction l with
    | nil => exact fun _ h => Or.inl h
    | cons x l ih =>
      intro A₀ h
      rcases ih _ h with h | h
      · rcases admit_pool_memAC h with h | ⟨rfl, hs⟩
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_self, hs⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩
  unfold blockReceipt at h
  exact (key _ _ h :)

/-- The honest votes of a pool after the receipt of a message or a block at cut `j` were emitted
before `j`. -/
private theorem receipt_pool_voteAC (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ)
    {A : SAState sp.n}
    (h : (∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state y j) (tr.time j) m) ∨
      ∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state y j) (tr.time j) B)
    {σ : Nat} {v : Vote sp.n} (hv : v ∈ A.pool σ) (hvH : v.val ∈ H) :
    ∃ j' < j, ∃ e', VoteAt tr v.val j' e' ∧ e'.msg = v := by
  rcases h with ⟨m, hm, rfl⟩ | ⟨B, hB, rfl⟩
  · rcases admit_pool_memAC hv with hv | ⟨rfl, -⟩
    · exact hrun.honest.pool_vote y hy j σ v hv hvH
    · exact hrun.honest.message_vote y hy j ℓ _ hc hm hvH
  · rcases receipt_pool_memAC hv with hv | ⟨hv, -⟩
    · exact hrun.honest.pool_vote y hy j σ v hv hvH
    · exact hrun.honest.carried_vote y hy j ℓ hc B
        ((accept_newU sp hrun.localRun hy ⟨ℓ, hc, hB⟩).1 ℓ hc) v hv hvH

/-- `SA.readPoint_locks_provenance_strict` with the unlock given: at an honest vote of a slot
`> 0`, every lock of the read point names a frame block below the block of a stored lock, or below
the block that the receipt's optimistic check at the same cut selects, whose counted honest votes
were cast at cuts before `i`. The read-point locks move back from the call's unlock input
(`UnlockRel.movesBack`). -/
theorem readPoint_locks_provenance_strictAC (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hpos : 0 < sp.slot (tr.time i)) :
    ∀ l' ∈ e.readPoint.locks, ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧
      ((∃ l ∈ (tr.state y i).locks, ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc B' B) ∨
       ∃ B CV, OptimisticLockAt tr y i (sp.slot (tr.time i)) B CV ∧
         (∀ v ∈ CV, v.val ∈ H → ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) ∧
         ℓ.frame.Anc B' B) := by
  have hr := hrun.localRun
  obtain ⟨P, he, hPi, -, -⟩ := vote_tryVote_inputU hr hy hc
  have hΦ := (frameIn_of_callAtU hr hy hc.1).1
  have hlaw := hr.lawfulAt hy hc.1 hΦ
  rw [← hPi] at hlaw
  intro l' hl'
  rw [tryVote_readPoint_locks_eqWith he] at hl'
  simp only [hpos, ↓reduceIte] at hl'
  obtain ⟨l₁, hl₁, -, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩ := hlaw.movesBack hΦ l' hl'
  refine ⟨B', hB', hB'r, ?_⟩
  subst hPi
  have opt : ∀ A : SAState sp.n, OptimisticPoint tr y i ℓ A →
      ((∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state y i) (tr.time i) m) ∨
        ∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state y i) (tr.time i) B) →
      A.locks = (tr.state y i).locks →
      l₁ ∈ (optimisticConfirmationM sp wm A ℓ.frame (tr.time i)).locks →
      ((∃ l ∈ (tr.state y i).locks, ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧
          ℓ.frame.Anc B' B) ∨
        ∃ B CV, OptimisticLockAt tr y i (sp.slot (tr.time i)) B CV ∧
          (∀ v ∈ CV, v.val ∈ H → ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) ∧
          ℓ.frame.Anc B' B) := by
    intro A hpt hrcpt hAl hl₁
    rw [optimisticConfirmationM_eq] at hl₁
    split_ifs at hl₁
    · unfold optimisticConfirmation at hl₁
      split at hl₁
      · exact Or.inl ⟨l₁, hAl ▸ hl₁, B₁, hB₁, hB₁r, hA⟩
      rename_i B hsel
      rw [updateLatestConfirmed_keeps_locks] at hl₁
      obtain ⟨l₂, hl₂, -, -, -, B₂, hB₂, hB₂r, B₁', hB₁', hB₁'r, hA'⟩ :=
        ((locks_move_back sp) FGP ℓ.frame A.locks (tr.time i) hΦ).2.1 _ _ l₁ hl₁
      obtain rfl : B₁' = B₁ := hΦ.coherent.1 hB₁' hB₁ (hB₁'r.trans hB₁r.symm)
      rcases hl₂ with hl₂ | ⟨p, hp, rfl⟩
      · exact Or.inl ⟨l₂, hAl ▸ hl₂, B₂, hB₂, hB₂r, hA.trans hA'⟩
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        have hBt : B ∈ ℓ.frame.tree := by
          have h := hsel
          unfold optimisticSelect at h
          dsimp only at h
          split_ifs at h
          exact (deepest_mem h).1.1
        obtain rfl : B₂ = B := hΦ.coherent.1 hB₂ hBt hB₂r
        exact Or.inr ⟨B₂, _, ⟨ℓ, A, hpt, rfl, hsel, rfl⟩,
          fun v hv hvH => receipt_pool_voteAC hrun hy hc.1 hrcpt hv.1 hvH, hA.trans hA'⟩
    · exact Or.inl ⟨l₁, hAl ▸ hl₁, B₁, hB₁, hB₁r, hA⟩
  cases hcall : ℓ.call with
  | message m =>
    rw [hcall] at hl₁
    exact opt _ ⟨hc.1, Or.inl ⟨m, hcall, rfl⟩⟩ (Or.inl ⟨m, hcall, rfl⟩)
      (admitVote_locks_eq _ _ _) hl₁
  | block C =>
    rw [hcall] at hl₁
    exact opt _ ⟨hc.1, Or.inr (Or.inl ⟨C, hcall, rfl⟩)⟩ (Or.inr ⟨C, hcall, rfl⟩)
      (blockReceipt_locks _ _ _) hl₁
  | tick => rw [hcall] at hl₁; exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩
  | proposal => rw [hcall] at hl₁; exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩
  | toFG => rw [hcall] at hl₁; exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩
  | restart => rw [hcall] at hl₁; exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩

/-- **(i) at a read point, cut-indexed**: at an honest vote of a slot `> 0` cast at cut `i`, the
live lock blocks of the read point are compatible with every block `B ⪯ P`, from the
compatibility of the locks stored at `i` (`hlocks`) and the inputs of `fastLock_compatible_atAC`
at the cuts before `i`: a read-point lock is moved back from a stored lock, or below the
receipt's optimistic selection, whose counted honest votes were cast before `i`. -/
theorem readPoint_liveLockBlocks_compatible_atAC (hrun : ACRunU wm u proposer tr H U)
    {b₀ : Time} {j₀ i : Nat} {W : Set (Fin sp.n)} {P : Blk sp.n FGP}
    (hj₀ : sp.ts j₀ + 2 * sp.Δ ≤ b₀)
    (hpre : ∀ C s, OriginWithinAC tr H C s b₀ → C ∈ U → Compatible U C P)
    (hvc : ∀ x ∈ H, x ∉ W → ∀ k < i, ∀ e, VoteAt tr x k e → j₀ ≤ e.msg.slot →
      VoteCompat U e.msg P)
    (hcount : 2 * (Hᶜ ∪ W).ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H)
    (hlocks : ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ Compatible U L P)
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hpos : 0 < sp.slot (tr.time i)) {B : Blk sp.n FGP} (hBP : Anc U B P) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B := by
  intro L hL
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc.1
  obtain ⟨l', hl', B₀, hB₀, hB₀r, -, rfl⟩ := mem_liveLockBlocks hΦ hL
  obtain ⟨B', hB', hB'r, h⟩ := readPoint_locks_provenance_strictAC hrun hy hc hpos l' hl'
  obtain rfl : B₀ = B' := hΦ.coherent.1 hB₀ hB' (hB₀r.trans hB'r.symm)
  refine compatible_of_anc_rightAC hU hBP
    (compat_of_ancAC hU ((viableAncestor_anc hΦ hB₀).2.mono hΦU) ?_)
  rcases h with ⟨l, hl, B₁, hB₁, hB₁r, hanc⟩ | ⟨B₁, CV, hfl, hcut, hanc⟩
  · obtain ⟨L', hL', hL'r, hcomp⟩ := hlocks l hl
    obtain rfl : B₁ = L' := hU.1 (hΦU hB₁) hL' (hB₁r.trans hL'r.symm)
    exact compat_of_ancAC hU (hanc.mono hΦU) hcomp
  · exact compat_of_ancAC hU (hanc.mono hΦU)
      (fastLock_compatible_atAC hr hj₀ hpre hvc hcount hy (Or.inr hfl) hcut)

end Consensus.Goldilocks.Comparison

end
