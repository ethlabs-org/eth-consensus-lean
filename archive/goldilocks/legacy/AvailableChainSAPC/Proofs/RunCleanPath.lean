module
public import AvailableChainSAPC.Proofs.CleanTicks
public import AvailableChainSAPC.Proofs.CleanInclusion
public import AvailableChainGridCO.Proofs.HistoryInduction

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A source remains a source at every later event prefix. Mode changes
do not remove historical genuine results or earlier authority uses. -/
theorem CleanRunSource.mono {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {rho : Run V (sapc p)} {i j : Nat} (hij : i ≤ j)
    {b : Block} (h : CleanRunSource p rho i b) : CleanRunSource p rho j b := by
  cases h with
  | genuine k hk v hv r b ht hb => exact .genuine k (hk.trans_le hij) v hv r b ht hb
  | timely r b cap source =>
    obtain ⟨v, hv, k, hk, ht, hb⟩ := source
    exact .timely r b cap ⟨v, hv, k, hk.trans_le hij, ht, hb⟩
  | gate k hk v hv r c ht ha hc => exact .gate k (hk.trans_le hij) v hv r c ht ha hc
  | head k hk v hv r c ht ha hc => exact .head k (hk.trans_le hij) v hv r c ht ha hc
  | proposal k hk v hv r c ht ha hc => exact .proposal k (hk.trans_le hij) v hv r c ht ha hc

theorem cleanRunPath_mono {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j)
    {b : Block} (h : cleanRunPath p rho i b) : cleanRunPath p rho j b := by
  rcases h with hg | ⟨c, hc, hp⟩
  · exact Or.inl hg
  · exact Or.inr ⟨c, hc.mono hij, hp⟩

theorem cleanRunPath_closed {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (i : Nat) (a b : Block)
    (hp : Block.Preceq a b) (hb : cleanRunPath p rho i b) : cleanRunPath p rho i a := by
  rcases hb with rfl | ⟨c, hc, hbc⟩
  · exact Or.inl (by simpa [Block.Preceq, Block.preceq] using hp)
  · exact Or.inr ⟨c, hc, GridCO.prefix_trans a b c hp hbc⟩

theorem cleanRunPath_zero {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) :
    cleanRunPath p rho 0 = (fun b => b = .genesis) := by
  funext b
  apply propext
  constructor
  · rintro (hg | ⟨c, hc, _⟩)
    · exact hg
    · cases hc with
      | genuine j hj => omega
      | timely r b cap source => obtain ⟨v, hv, j, hj, rest⟩ := source; omega
      | gate j hj => omega
      | head j hj => omega
      | proposal j hj => omega
  · exact Or.inl

/-- The old conditional path facts contain the canonical source closure.
The reverse implication is deliberately absent: the old path may contain
an unrelated stored branch. -/
theorem cleanRunPath_le_of_facts {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (i : Nat)
    {path : Block → Prop} (h : CleanPathFacts p E rho i path)
    (b : Block) (hb : cleanRunPath p rho i b) : path b := by
  rcases hb with rfl | ⟨c, hc, hp⟩
  · exact h.chain.genesis
  · apply h.chain.closed b c hp
    cases hc with
    | genuine j hj v hv r c ht hc => exact h.genuine j hj v hv r c ht hc
    | timely r c cap source =>
      obtain ⟨v, hv, j, hj, ht, hc⟩ := source
      exact (h.timely (j + 1) (by omega) v hv r c hc).2 cap
    | gate j hj v hv r c ht ha hc => exact h.gateAuthorities j hj v hv r c ht ha hc
    | head j hj v hv r c ht ha hc => exact h.headAuthorities j hj v hv r c ht ha hc
    | proposal j hj v hv r c ht ha hc => exact h.proposalAuthorities j hj v hv r c ht ha hc

/-- No relevant tick means no new path source. This includes every
receipt, even a receipt that first completes a PC or proves the cap broken. -/
theorem cleanRunPath_eq_of_no_source_tick {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (i : Nat)
    (hg : ∀ v r, rho.events[i]? ≠ some (.tick v (gateTime p r)))
    (he : ∀ v r, rho.events[i]? ≠ some (.tick v (earlyTime p r)))
    (hh : ∀ v r, rho.events[i]? ≠ some (.tick v (voteTime p r)))
    (hp : ∀ v r, rho.events[i]? ≠ some (.tick v (proposalTime p r))) :
    cleanRunPath p rho (i + 1) = cleanRunPath p rho i := by
  have old (j : Nat) (hj : j < i + 1) (v : V) (t : Time)
      (ht : rho.events[j]? = some (.tick v t))
      (hn : rho.events[i]? ≠ some (.tick v t)) : j < i := by
    have hne : j ≠ i := by rintro rfl; exact hn ht
    omega
  funext b
  apply propext
  constructor
  · rintro (hb | ⟨c, hc, hbc⟩)
    · exact Or.inl hb
    · refine Or.inr ⟨c, ?_, hbc⟩
      cases hc with
      | genuine j hj v hv r b ht hb => exact .genuine j (old j hj v _ ht (hg v r)) v hv r _ ht hb
      | timely r b cap source =>
        obtain ⟨v, hv, j, hj, ht, hb⟩ := source
        exact .timely r _ cap ⟨v, hv, j, old j hj v _ ht (he v r), ht, hb⟩
      | gate j hj v hv r c ht ha hc => exact .gate j (old j hj v _ ht (hg v r)) v hv r c ht ha hc
      | head j hj v hv r c ht ha hc => exact .head j (old j hj v _ ht (hh v r)) v hv r c ht ha hc
      | proposal j hj v hv r c ht ha hc =>
        exact .proposal j (old j hj v _ ht (hp v r)) v hv r c ht ha hc
  · exact cleanRunPath_mono p rho (Nat.le_succ i)

/-- Ordered history is unchanged at any event that is not a gate. -/
theorem OrderedGenuine.step_of_no_gate {V : Type} [DecidableEq V]
    {p : Params} {rho : Run V (sapc p)} {i : Nat} (h : OrderedGenuine p rho i)
    (hg : ∀ v r, rho.events[i]? ≠ some (.tick v (gateTime p r))) :
    OrderedGenuine p rho (i + 1) := by
  have old (j : Nat) (hj : j < i + 1) (v : V) (r : Slot)
      (ht : rho.events[j]? = some (.tick v (gateTime p r))) : j < i := by
    have hne : j ≠ i := by rintro rfl; exact hg v r ht
    omega
  intro j hj k hk v hv w hw r s b c hrs htj htk hb hc
  exact h j (old j hj v r htj) k (old k hk w s htk) v hv w hw r s b c hrs htj htk hb hc

/-- The corrected statement holds at genesis. -/
theorem jointClean_initial {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) : JointCleanInvariant p E rho 0 := by
  constructor
  · rw [cleanRunPath_zero]
    exact cleanPathFacts_initial p E rho
  · intro j hj; omega

/-- All receipt kinds preserve the corrected invariant under plain Sleepy.
The old receipt proof is reused; only source-set equality is new. -/
theorem jointClean_delivery_of_sleepy {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (t₀ : Time)
    (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (v : V) (obj : Wire p.n) (t : Time)
    (he : rho.events[i]? = some (.deliver v obj t))
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho (i + 1) := by
  have noTick (w : V) (time : Time) : rho.events[i]? ≠ some (.tick w time) := by
    rw [he]; intro hn; cases hn
  constructor
  · rw [cleanRunPath_eq_of_no_source_tick p rho i
      (fun w r => noTick w _) (fun w r => noTick w _)
      (fun w r => noTick w _) (fun w r => noTick w _)]
    exact cleanPathFacts_delivery_of_sleepy p E rho t₀ hs i v obj t he h.facts
  · exact h.ordered.step_of_no_gate (fun w r => noTick w _)

/-- Existing output proofs now consume a path fixed by the run. This
remains conditional until the duty preservation obligations are proved. -/
theorem clean_safety_of_run_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (h : JointCleanInvariant p E rho rho.events.length)
    (t₀ : Time) : SafeFrom (sapc p) rho (sapcInterface p).stable t₀ ∧
      SafeFrom (sapc p) rho (sapcInterface p).confirmed t₀ :=
  clean_safety_of_joint p E rho hs h.facts t₀

end AvailableChain.SAPC
end
