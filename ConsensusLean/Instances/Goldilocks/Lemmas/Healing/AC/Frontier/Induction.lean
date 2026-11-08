module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Provenance

public section

/-! # The pre-`b` frontier over AC traces of a lock rule

**The frontier** (`frontier_beforeAC`) is the AC content of the composite
`Compose.sleepy_invariant_before` under trivial frames: over an AC trace of the SA whose honest
calls execute the handlers at a write mode `m` with the locks after the unlock given by an oracle
`u` (`ACRunU m u`), lawful in the trace law's sense (`ACLocalRunU.lawful`, the unlock relation),
with trivial frames, the tick duty, the deadline-cut service before `b` and `f < h_t` at `t_0` and
at the slot points `t_s + Δ ≤ b`: the origins within `b` compare, the honest votes at times `≤ b`
extend the origins of earlier labels, and the records and stored locks at the cuts within `b`
name genesis or blocks on the chain of the origins within `b` (`FrontierAC`).

The theorem is generic in the oracle: no step reads the parent's unlock, only the unlock relation
(through the read-point locks, `readPoint_locks_below_storedU` and `lock_origin_readPointU`), so
it covers every lock rule whose runs project to `ACLocalRunU m u` (evidence release's through
its forgotten trace). Nor does it read the slow window, so there is no width premise.

The induction (`frontier_inductionAC`) is the composite one: `P_0` and `V_0` hold vacuously,
`P_s, V_s ⊢ P_{s+1}` (`origins_below_succAC`) and `P_{s+1}, V_s ⊢ V_{s+1}`
(`votes_below_succAC`). Every delivery it reads is owed by `SyncUntilAC` with the receiver's
deadline at most `b` (so within the `b + 1` cut): no service of a send whose deadline exceeds
`b + 1` is used. -/

namespace Consensus.Goldilocks.SA


variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {b : Time}

/-- `f < n/2` from `f < h_t` at some `t`. -/
private theorem two_faults_lt_of_faultBound {t : Time} (h : FaultBound tr H t) :
    2 * Hᶜ.ncard < sp.n := by
  have hle : honestAwakeJoined tr H t ≤ H.ncard := Set.ncard_le_ncard fun x hx => hx.1
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold FaultBound at h
  omega

/-- **Every finite frontier up to `b`**: `P_s` and `V_s` up to `b` for every `s`. -/
theorem frontier_inductionAC {wm : WriteMode} (hrun : ACRunU wm u proposer tr H U)
    (htriv : TrivialFrames tr H) (htick : TickDuty tr H)
    (hsync : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr)
    (hf : 2 * Hᶜ.ncard < sp.n)
    (hJ : ∀ s : Nat, sp.ts s + sp.Δ ≤ b → FaultBound tr H (sp.ts s + sp.Δ)) :
    ∀ s, OriginsBelowAC tr H U s b ∧ VotesBelowAC tr H U s b := by
  intro s
  induction s with
  | zero =>
    refine ⟨originsBelowAC_iff.2 fun _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      votesBelowAC_iff.2 fun _ _ _ _ _ _ _ _ _ h₁ h₂ => ?_⟩
    omega
  | succ s ih =>
    have hP := origins_below_succAC hrun htick hsync.service hf hJ ih.1 ih.2
    exact ⟨hP, votes_below_succAC hrun htriv htick hsync hf hJ hP ih.2⟩

/-- **The pre-`b` frontier over AC traces of a lock rule**: the AC content of
`Compose.sleepy_invariant_before` under trivial frames, for any lawful unlock oracle `u` at any
write mode `m`. -/
theorem frontier_beforeAC {m : WriteMode} (hrun : ACRunU m u proposer tr H U)
    (htriv : TrivialFrames tr H) (htick : TickDuty tr H) (hb : 0 ≤ b)
    (hsync : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ} : Set Time), sp.ts s + d ≤ b →
      FaultBound tr H (sp.ts s + d)) :
    FrontierAC tr H U b := by
  have hr := hrun.localRun
  have hf : 2 * Hᶜ.ncard < sp.n :=
    two_faults_lt_of_faultBound (hfb 0 0 (Or.inl rfl)
      (by simpa only [SAParams.ts, Nat.cast_zero, mul_zero, add_zero] using hb))
  have hJ : ∀ s : Nat, sp.ts s + sp.Δ ≤ b → FaultBound tr H (sp.ts s + sp.Δ) :=
    fun s h => hfb s sp.Δ (Or.inr rfl) h
  have hF := frontier_inductionAC hrun htriv htick hsync hf hJ
  refine ⟨fun C s C' s' h h' =>
      originsBelowAC_iff.1 (hF (max s s' + 1)).1 C s C' s' (by omega) (by omega) h h',
    fun C s hC y hy i e he hib hs =>
      votesBelowAC_iff.1 (hF e.msg.slot).2 C s hC y hy i e he hib hs le_rfl,
    fun y hy i hi => record_withinAC hr hy hi, fun y hy i hi => locks_withinAC hr hy hi⟩

end Consensus.Goldilocks.SA

end
