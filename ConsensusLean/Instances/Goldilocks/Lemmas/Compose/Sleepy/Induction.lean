module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer

public section

/-! # Goldilocks under `Sleepy`: the record invariant from genesis

workbench#11 §4 (the bounded frontier, at workbench `40d6006`): `P_0` and `V_0` hold vacuously;
`P_s, V_s ⊢ P_{s+1}` (`origins_below_succ`) and `P_{s+1}, V_s ⊢ V_{s+1}` (`votes_below_succ`), so
every finite frontier holds (`frontier`), and unbounded S1 and S2 follow. With the provenance of
records, locks, sources and caches (`Sleepy/Provenance`) and full viability (`held_origin_viable`)
this is `SleepyInvariant` (`sleepy_invariant`), and R.1's safety part, pairwise compatibility of
the honest confirmed outputs (`sleepy_confirmed_compatible`).

The same induction runs up to a horizon `b` under the prefix premises of `SleepySafePrefix`
(`SleepyPrefix`: `Sync[0, b − Δ]`, `f < h_t` at the slot points `≤ b`), for the origins within
`b`, the honest votes at times `≤ b` and the cuts within `b` (`frontier_upTo`,
`sleepy_invariant_upTo`): each step reads deliveries of sends at times `≤ b − Δ` and `f < h_t`
at slot points `≤ b` only.

From a start label `s₀` (R.6, after a heal), the same induction runs over the origins of labels
`≥ s₀` under `SleepyFrom` (`Sync[t_{s₀}, ∞)`, `f < h_t` at the slot points from `t_{s₀}`) and the
base facts `SleepyBase` (the pre-`s₀` history the steps read: the live locks of slots `< s₀` at
the votes, the honest rows whose sources predate the window, the heads accepted before `t_{s₀}`,
and the records, caches and sources the invariant states): `frontier_from`,
`sleepy_invariant_from`; at `s₀ = 0` the base facts hold of every run (`sleepyBase_zero`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **Every finite frontier**: `P_s` and `V_s` for every `s`. -/
theorem frontier (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) : ∀ s, OriginsBelow tr H s ∧ VotesBelow tr H s := by
  intro s
  induction s with
  | zero =>
    refine ⟨originsBelow_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      votesBelow_iff.2 fun _ _ _ _ _ _ _ _ h₁ h₂ => ?_⟩
    omega
  | succ s ih =>
    have hP := origins_below_succ hrun hnc hsl ih.1 ih.2
    exact ⟨hP, votes_below_succ hrun hnc hsl hP ih.2⟩

/-- **The Sleepy record invariant** (S1–S3) holds of every Goldilocks run under `Sleepy` and
`NoColl`. -/
theorem sleepy_invariant (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) : SleepyInvariant tr H := by
  have hF := frontier hrun hnc hsl
  have hcomp : ∀ C s C' s', Origin tr H C s → Origin tr H C' s' →
      Compatible (tr.HonestBlocks H) C C' := fun C s C' s' h h' =>
    originsBelow_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega) h h'
  refine ⟨hcomp, fun C s hC y hy i e he hs => ?_, fun y hy i => record_origin hrun hnc hy i,
    fun y hy i => caches_on_chain hrun hnc hsl hy i, fun y hy i l hl => ?_,
    fun y hy i ℓ C h => source_on_chain hrun hnc hy h,
    fun y hy i C s hC hCt => held_origin_viable hrun hnc hsl (fun s => (hF s).1) hy i
      (fun C' s' hC' => hcomp C s C' s' hC hC'.origin) hCt⟩
  · exact votesBelow_iff.1 (hF e.msg.slot).2 C s hC y hy i e he hs le_rfl
  · obtain ⟨L, hL, hLr, C, hC, hLC⟩ := lock_origin hrun hnc hy i l hl
    exact ⟨L, hL, hLr, onOriginChain_iff.2 (Or.inr ⟨C, l.slot, hC.origin, hLC⟩)⟩

/-- **Every finite frontier up to `b`**: `P_s` and `V_s` up to `b` for every `s`, under the
prefix premises up to `b`. -/
theorem frontier_upTo {b : Time} (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) : ∀ s, OriginsBelowUpTo tr H s b ∧ VotesBelowUpTo tr H s b := by
  intro s
  induction s with
  | zero =>
    refine ⟨originsBelowUpTo_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      votesBelowUpTo_iff.2 fun _ _ _ _ _ _ _ _ _ h₁ h₂ => ?_⟩
    omega
  | succ s ih =>
    have hP := origins_below_succ_upTo hrun hnc hpre ih.1 ih.2
    exact ⟨hP, votes_below_succ_upTo hrun hnc hpre hP ih.2⟩

/-- Both frontiers at a finite horizon, with recipient-bounded rather than whole-run service. -/
theorem frontier_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : tr.SyncBefore H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d)) :
    ∀ s, OriginsBelowUpTo tr H s b ∧ VotesBelowUpTo tr H s b := by
  intro s
  induction s with
  | zero =>
    refine ⟨originsBelowUpTo_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      votesBelowUpTo_iff.2 fun _ _ _ _ _ _ _ _ _ h₁ h₂ => ?_⟩
    omega
  | succ s ih =>
    have hP := origins_below_succ_before hrun hnc hb hsync hfb ih.1 ih.2
    exact ⟨hP, votes_below_succ_before hrun hnc hb hsync hfb hP ih.2⟩

/-- **The Sleepy record invariant up to `b`** (S1–S3 for the origins within `b`, the honest votes
at times `≤ b` and the cuts within `b`) holds of every Goldilocks run under `NoColl` and the
prefix premises of `SleepySafePrefix` up to `b`, whatever happens after `b`. -/
theorem sleepy_invariant_upTo {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) : SleepyInvariantUpTo tr H b := by
  have hF := frontier_upTo hrun hnc hpre
  have hcomp : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
      Compatible (tr.HonestBlocks H) C C' := fun C s C' s' h h' =>
    originsBelowUpTo_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega) h h'
  have hfb : tr.FaultBound H (sp.ts (0 : Nat) + 0) := (sleepyPrefix_iff.1 hpre).2.2 0 0
    (by simp) (by simpa [SAParams.ts] using (sleepyPrefix_iff.1 hpre).1)
  refine ⟨hcomp, fun C s hC y hy i e he hib hs => ?_,
    fun y hy i hi => record_origin_upTo hrun hnc hy hi,
    fun y hy i hi => caches_on_chain_upTo hrun hnc hfb hy hi, fun y hy i hi l hl => ?_,
    fun y hy i hi ℓ C h => source_on_chain_upTo hrun hnc hy hi h,
    fun y hy i hi C s hC hCt => held_origin_viable_upTo hrun hnc hpre (fun s => (hF s).1) hy i hi
      (fun C' s' hC' => hcomp C s C' s' hC (hC'.within hi)) hCt⟩
  · exact votesBelowUpTo_iff.1 (hF e.msg.slot).2 C s hC y hy i e he hib hs le_rfl
  · obtain ⟨L, hL, hLr, C, hC, hLC⟩ := lock_origin hrun hnc hy i l hl
    exact ⟨L, hL, hLr, onOriginChainWithin_iff.2 (Or.inr ⟨C, l.slot, hC.within hi, hLC⟩)⟩

/-- The complete finite record invariant under recipient-bounded service. -/
theorem sleepy_invariant_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : tr.SyncBefore H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d)) : SleepyInvariantUpTo tr H b := by
  have hF := frontier_before hrun hnc hb hsync hfb
  have hcomp : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
      Compatible (tr.HonestBlocks H) C C' := fun C s C' s' h h' =>
    originsBelowUpTo_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega) h h'
  have hzero := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have h := hzero
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  refine ⟨hcomp, fun C s hC y hy i e he hib hs => ?_,
    fun y hy i hi => record_origin_upTo hrun hnc hy hi,
    fun y hy i hi => caches_on_chain_upTo hrun hnc hzero hy hi, fun y hy i hi l hl => ?_,
    fun y hy i hi ℓ C h => source_on_chain_upTo hrun hnc hy hi h,
    fun y hy i hi C s hC hCt => held_origin_viable_before hrun hnc hf (fun s => (hF s).1) hy i hi
      (fun C' s' hC' => hcomp C s C' s' hC (hC'.within hi)) hCt⟩
  · exact votesBelowUpTo_iff.1 (hF e.msg.slot).2 C s hC y hy i e he hib hs le_rfl
  · obtain ⟨L, hL, hLr, C, hC, hLC⟩ := lock_origin hrun hnc hy i l hl
    exact ⟨L, hL, hLr, onOriginChainWithin_iff.2 (Or.inr ⟨C, l.slot, hC.within hi, hLC⟩)⟩

/-- **Every finite frontier from `s₀`**: `P_s` and `V_s` from `s₀` for every `s`, under
`SleepyFrom` and the base facts. Both are vacuous up to `s = s₀` (no origin of a label in
`[s₀, s₀)`, no vote of a slot in `(s₀, s₀]`); the first real steps are `P_{s₀+1}` (same label)
and the votes of slot `s₀ + 1` (first transfer). -/
theorem frontier_from {s₀ : Nat} (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hfrom : SleepyFrom tr H ΔF s₀) (hbase : SleepyBase tr H s₀) :
    ∀ s, OriginsBelowFrom tr H s₀ s ∧ VotesBelowFrom tr H s₀ s := by
  intro s
  induction s with
  | zero =>
    refine ⟨originsBelowFrom_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      votesBelowFrom_iff.2 fun _ _ _ _ _ _ _ _ h₁ h₂ => ?_⟩
    omega
  | succ s ih =>
    have hP := origins_below_succ_from hrun hnc hfrom ih.1 ih.2
    exact ⟨hP, votes_below_succ_from hrun hnc hfrom hbase hP ih.2⟩

/-- **The Sleepy record invariant from a start label `s₀`** (S1–S3 over the origins of labels
`≥ s₀`, at the cuts from `t_{s₀}`) holds of every Goldilocks run under `NoColl`, `SleepyFrom`
(`Sync[t_{s₀}, ∞)`, `f < h_t` at the slot points from `t_{s₀}`) and the base facts at `s₀`. -/
theorem sleepy_invariant_from {s₀ : Nat} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hfrom : SleepyFrom tr H ΔF s₀) (hbase : SleepyBase tr H s₀) : SleepyInvariantFrom tr H s₀ := by
  have hF := frontier_from hrun hnc hfrom hbase
  have hcomp : ∀ C s C' s', OriginFrom tr H C s s₀ → OriginFrom tr H C' s' s₀ →
      Compatible (tr.HonestBlocks H) C C' := fun C s C' s' h h' =>
    originsBelowFrom_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega) h h'
  refine ⟨hcomp, fun C s hC y hy i e he hs =>
    votesBelowFrom_iff.1 (hF e.msg.slot).2 C s hC y hy i e he hs le_rfl, ?_, hbase.caches, ?_,
    ?_, fun y hy i hi C s hC hCt => held_origin_viable_from hrun hnc hfrom hbase hcomp hy i hi
      (fun C' s' hC' => hcomp C s C' s' hC hC') hCt⟩
  · -- a record of a label `≥ s₀` is an origin from `s₀`; an older one is `SleepyBase.records`
    intro y hy i hi
    obtain ⟨C, hC, hCr, h⟩ := record_origin hrun hnc hy i
    refine ⟨C, hC, hCr, ?_⟩
    rcases h with hg | ⟨s, hs⟩
    · exact Or.inl (Or.inl hg)
    by_cases hs₀ : s₀ ≤ s
    · exact Or.inl (Or.inr ⟨s, originFrom_iff.2 ⟨hs, hs₀⟩⟩)
    · exact Or.inr (hbase.records y hy i hi C hC hCr ⟨s, Nat.lt_of_not_le hs₀, hs⟩)
  · -- a stored lock of a slot `≥ s₀` sits below an origin of its slot
    intro y hy i l hl hls
    obtain ⟨L, hL, hLr, C, hC, hLC⟩ := lock_origin hrun hnc hy i l hl
    exact ⟨L, hL, hLr, onOriginChainFrom_iff.2
      (Or.inr ⟨C, l.slot, originFrom_iff.2 ⟨hC.origin, hls⟩, hLC⟩)⟩
  · -- a source below an origin of a label `≥ s₀` is on the chain; an older one is
    -- `SleepyBase.sources`
    intro y hy i ℓ C h hi
    rcases onOriginChain_iff.1 (source_on_chain hrun hnc hy h) with hg | ⟨C', l, hC', hCC'⟩
    · exact onOriginChainFrom_iff.2 (Or.inl hg)
    by_cases hl : s₀ ≤ l
    · exact onOriginChainFrom_iff.2 (Or.inr ⟨C', l, originFrom_iff.2 ⟨hC', hl⟩, hCC'⟩)
    · exact hbase.sources y hy i ℓ C h hi ⟨C', l, hC', Nat.lt_of_not_le hl, hCC'⟩

/-- **The base facts at `s₀ = 0` hold of every Goldilocks run** under `SleepyFrom` slot `0`
(`Sleepy` gives it, `SleepyRun.from_zero`): there is no lock, record, source or origin of a label
`< 0`, no acceptance before `t_0 = 0`, and the caches are on the origin chain
(`caches_on_chain_upTo`). So `sleepy_invariant_from` at `s₀ = 0` runs the induction from
genesis. -/
theorem sleepyBase_zero (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hfrom : SleepyFrom tr H ΔF 0) : SleepyBase tr H 0 := by
  have chain0 : ∀ {B}, OnOriginChain tr H B → OnOriginChainFrom tr H B 0 := fun h =>
    onOriginChainFrom_iff.2
      ((onOriginChain_iff.1 h).imp_right fun ⟨C, s, hC, hBC⟩ => ⟨C, s, hC.from_zero, hBC⟩)
  have hfb : tr.FaultBound H (sp.ts (0 : Nat) + 0) :=
    (sleepyFrom_iff.1 hfrom).2 0 le_rfl 0 (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ L hL
    obtain ⟨-, l, ⟨l₀, ⟨-, h⟩, -⟩, -⟩ := hL
    exact absurd h (Nat.not_lt_zero _)
  · rintro _ _ _ _ _ _ _ ⟨_, h, -⟩
    exact absurd h (Nat.not_lt_zero _)
  · intro y hy i _
    obtain ⟨b, -, hi⟩ := exists_horizon hrun i
    have h := caches_on_chain_upTo hrun hnc hfb hy hi
    exact ⟨chain0 h.1.onOriginChain, chain0 h.2.onOriginChain⟩
  · rintro _ _ _ _ _ _ _ ⟨_, _, -, h, -⟩
    exact absurd h (Nat.not_lt_zero _)
  · rintro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, -, -, h, -⟩
    exact absurd h (Nat.not_lt_zero _)
  · rintro _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, -, -, h, -⟩
    exact absurd h (Nat.not_lt_zero _)
  · intro _ _ _ _ _ _ _ _ _ _ _ m _ _ hm
    exact absurd hm (by rw [ts_natCast_zero]; exact not_lt.2 (hrun.time_nonneg m))

/-- **R.1's safety part under `Sleepy`**: the confirmed outputs of honest nodes at any two cuts
are compatible (inside the honest blocks), whether or not the nodes are served. -/
theorem sleepy_confirmed_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) :
    ∀ y ∈ H, ∀ y' ∈ H, ∀ i i',
      Compatible (tr.HonestBlocks H) (tr.confirmedAt y i) (tr.confirmedAt y' i') :=
  (sleepy_invariant hrun hnc hsl).confirmed_compatible hrun hnc

end Consensus.Goldilocks.Compose

end
