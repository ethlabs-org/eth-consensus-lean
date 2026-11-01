module
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceStep
public import AvailableChainFGSAProofs.Proofs.Outage.ReceiverInputs

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- OUTPUT-DIRECT §8. DC: INTENTIONAL; passed compatible results followed
by normalization retain B, including results strictly below B. -/
theorem outageV_write_and_normalize {S C F B : Block}
    (hBS : Block.Preceq B S) (hCB : Block.Compatible C B) (hFB : Block.Compatible F B) :
    Block.Preceq B (Gen.AC.normalizeOutput F (GridCO.advance S C)) :=
  outage_normalize_covers (outage_advance_covers hBS hCB) hFB

/-- OUTPUT-DIRECT §§8,9. DC: INTENTIONAL; only the current genuine
result can change S. Saved results can affect renewal but need no
compatibility premise. Empty, vetoed, and already-saved gates retain B. -/
theorem outageV_gateStep_covers (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    (s : Slot) (B : Block) (hBS : Block.Preceq B st.base.stableRecord)
    (hFB : Block.Compatible (eraseFG st.fg.F) B)
    (hcurrent : ∀ C, SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
      (actView st) s = some C → Block.Compatible C B) :
    Block.Preceq B (gateStep p st s).base.stableRecord := by
  by_cases hJ : joinedNow p st = true
  swap
  · have hN : joinedNow p st = false := Bool.eq_false_iff.mpr hJ
    unfold gateStep
    rw [hN]
    simp only [Bool.not_false, ite_true]
    split <;> rw [normalizeS_fields] <;> exact outage_normalize_covers hBS hFB
  let Q : State p.n := { onView
    (fun v => SA.Root.gateFrom p.toParams (eraseFG st.fg.F) v s) st with
    fastWrite := st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F) (actView st) s)] }
  have hQ : Block.Preceq B Q.base.stableRecord := by
    change Block.Preceq B
      (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).stableRecord
    have hc := (saGate_cases p.toParams (eraseFG st.fg.F) (actView st) s
      hinv.leaseKeys.1 hinv.leaseKeys.2).2.2
    rcases hc with he | ⟨C, hC, he⟩
    · rw [he]; exact hBS
    · rw [he]; exact outage_advance_covers hBS (hcurrent C hC)
  unfold gateStep
  rw [hJ]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  change Block.Preceq B
    (normalizeS (if (GridCO.savedGenuine st.base s).isSome then st else Q)).base.stableRecord
  have hn (q : State p.n) (hS : Block.Preceq B q.base.stableRecord)
      (hF : Block.Compatible (eraseFG q.fg.F) B) :
      Block.Preceq B (normalizeS q).base.stableRecord := by
    rw [normalizeS_fields]
    change Block.Preceq B (if Block.preceq (eraseFG q.fg.F) q.base.stableRecord
      then q.base.stableRecord else eraseFG q.fg.F)
    exact outage_normalize_covers hS hF
  split
  · exact hn st hBS hFB
  · exact hn Q hQ hFB

/-- OUTPUT-DIRECT §9. DC: INTENTIONAL; every new fast-write source is
below the current passed result, regardless of old saved results. -/
theorem outageV_fastSet_compatible (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (hcurrent : ∀ C, SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
      (actView st) s = some C → Block.Compatible C B) :
    ∀ X ∈ fastSet p (eraseFG st.fg.F) (actView st) s, Block.Compatible X B := by
  intro X hX
  obtain ⟨C, hC, hXC, _, _⟩ := fastSet_prefix p (eraseFG st.fg.F) (actView st) s hX
  exact Gen.Pure.block_compatible_of_preceq_compatible hXC (hcurrent C hC)

/-- OUTPUT-DIRECT §§2,9. DC: INTENTIONAL; the established lease-below-S
invariant makes all live locks compatible once S retains B. -/
theorem outageV_live_locks (p : Params) (st : State p.n) (B : Block)
    (hBS : Block.Preceq B st.base.stableRecord) (hbelow : LeaseBelowOutputStore p st) :
    ∀ row ∈ st.base.obligations, st.base.now < row.2.2 → Block.Compatible row.1 B := by
  intro row hr hl
  exact Gen.Pure.block_compatible_of_common (hbelow row hr hl) hBS

/-- OUTPUT-DIRECT §8. DC: INTENTIONAL; source discipline ties each actual
source to the current gate result. It does not read an arbitrary saved result. -/
theorem outageV_source_compatible {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (htsrc : TSrc p c E rho) {x : V} {r : Nat} {C B : Block}
    (hx : x ∈ rho.honest) (hC : actionSource p c E rho x r = some (some C))
    (hcurrent : ∀ G, gateResult p c E rho x (r * p.R) = some (some G) →
      Block.Compatible G B) : Block.Compatible C B := by
  obtain ⟨X, G, _, hX, hG, hCG, _⟩ := htsrc x r C hx hC
  exact Gen.Pure.block_compatible_of_preceq_compatible (hCG C hX) (hcurrent G hG)


/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; a genuine result extends F even
when the terminal result equals the walk anchor. -/
theorem outageV_result_extends {n : Nat} (p : GridCO.Params) (st : GridCO.State n .root)
    (anchor C : Block) (s : Slot)
    (hresult : GridCO.confirmationFrom p anchor st s = some C) : Block.Preceq anchor C := by
  let score := GridCO.goldfishScoreOn (GridCO.resolutionTree st) st.blocks
    (GridCO.cleanSupport p st s) (GridCO.cleanSupport p st s)
  let eligible := fun b => 2 * score b > GridCO.voterCount (GridCO.lateVotes p st s)
  let result := GridCO.ghost anchor st.blocks score (fun b => decide (eligible b))
  change (if eligible result then some result else none) = some C at hresult
  split at hresult
  · have he : result = C := Option.some.inj hresult
    rw [← he]
    apply Gen.Pure.walk_covers_of_dominated_suffix
    · exact Gen.Pure.block_compatible_of_common
        (Gen.Pure.block_preceq_refl anchor) (Gen.Pure.block_preceq_refl anchor)
    · rw [Gen.Pure.DominatedSuffix_def]
      intro A hA hAF
      change ((!decide (anchor = A)) && Block.preceq anchor A) = true at hA
      obtain ⟨hne, hpre⟩ := Bool.and_eq_true_iff.mp hA
      have he := Gen.Pure.block_preceq_antisymm hpre hAF
      simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hne
  · contradiction

/-- A restored gate consumes only this label's scoped emitted HEAD history.
The regime produces the E count or the healthy joined count and all HEAD services. -/
theorem outageV_restored_gate {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    {i : Nat} {x : V} {s : Slot} {B C : Block}
    (hx : x ∈ rho.honest) (hrs : restoredLabel p b₁ < s)
    (hG : enabledGateAt p c E rho i x s)
    (hHeads : ∀ q K,
      outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
        (SA.voteTime p.toParams s) →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Compatible K B)
    (hresult : gateResultAt p c E rho i = some (some C)) : Block.Compatible C B :=
  outage_continuation_result_of_head_history h hx hrs hG hresult hHeads

end AvailableChain.FGSA.Run
end
