module
public import AvailableChainPCSAProofs.Proofs.Outage.SlowStore
public import AvailableChainPCSAProofs.Proofs.Shared.Clock

public section

/-! The per-node invariant of the S case (pcsa34-r4.3 §5.5 steps 2–4) and
its steps. Before the pending gate `d_{p*}` the locks are among the boundary
locks and the saved results are the boundary ones; the pending gate writes
the lock on `A`; after it the lock on `A` has the full deadline. Before the
pending gate no lock on `A` is required: no gate runs there. -/

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG Gen.Pure

variable {n : Nat}

/-- [pcsa34-r4.3 §5.5 steps 2–4] The S-case invariant of one store: `S ⪰ A`,
every lock compatible with `A`, `A` stored, and a lock row on `A` of level
`g` with deadline at least `D₂` after the pending gate (`¬ pre`). Before it
(`pre`) the locks are among the `bound` locks and the saved results are those
of `bound`. -/
structure SlowInv (A : Block) (g : Nat) (D₂ : Time) (bound : State n) (pre : Prop)
    (st : State n) : Prop where
  stable : Block.Preceq A st.base.stableRecord
  rows : ∀ row ∈ st.base.obligations, Block.Compatible row.1 A
  tree : A ∈ st.base.blocks
  renewed : ¬ pre → LockRow st A g D₂
  sub : pre → st.base.obligations ⊆ bound.base.obligations
  genuine : pre → st.base.genuine = bound.base.genuine

/-- A lock row with a larger deadline bound is one with a smaller bound. -/
theorem LockRow.row_mono {st : State n} {A : Block} {g : Nat} {D D' : Time}
    (h : LockRow st A g D) (hD : D' ≤ D) : LockRow st A g D' := by
  rw [LockRow_def] at h ⊢
  obtain ⟨row, hr, hA, hg, hd⟩ := h
  exact ⟨row, hr, hA, hg, le_trans hD hd⟩

/-- A lock row on `A` survives a step that deletes only locks conflicting
with a PC compatible with `A`. -/
theorem pcsa_lockRow_of_loss {U : PC n → Prop} {st st' : State n} {A : Block} {g : Nat}
    {D : Time} (hl : LockLoss U st st') (hU : ∀ c, U c → Block.Compatible c.target A)
    (h : LockRow st A g D) : LockRow st' A g D := by
  rw [LockLoss_def] at hl
  rw [LockRow_def] at h ⊢
  obtain ⟨row, hr, hA, hg, hd⟩ := h
  refine ⟨row, ?_, hA, hg, hd⟩
  by_contra hn
  obtain ⟨c, hc, hx⟩ := hl.2 row hr hn
  have := hU c hc
  rw [Block.Compatible, ← hA, hx] at this
  exact absurd this (by decide)

/-- [pcsa34-r4.3 §5.5 step 3] A stage-1 delivery keeps the invariant when
every PC the result uses is compatible with `A`. -/
theorem pcsa_process_inv (p : Params) (st : State p.n) (o : Wire p.n) {A : Block} {g : Nat}
    {D₂ : Time} {bound : State p.n} {pre : Prop}
    (hinv : SlowInv A g D₂ bound pre st) (hF0 : st.fg.F = .genesis)
    (hF : (process p st o).fg.F = .genesis)
    (hU : ∀ c, UsedPC (process p st o) c → Block.Compatible c.target A) :
    SlowInv A g D₂ bound pre (process p st o) := by
  obtain ⟨hb, hl, hbl⟩ := pcsa_process_slow p st o hF0 hF
  have hsub := hl
  rw [LockLoss_def] at hsub
  refine ⟨hb.stable ▸ hinv.stable, fun row hr => hinv.rows row (hsub.1 hr), hbl hinv.tree,
    fun hn => pcsa_lockRow_of_loss hl hU (hinv.renewed hn),
    fun hp => List.Subset.trans hsub.1 (hinv.sub hp),
    fun hp => hb.genuine.trans (hinv.genuine hp)⟩

/-- [pcsa34-r4.3 §5.5 step 2] The pre-gate clock keeps a live lock row on `A`
that the release does not release. -/
theorem pcsa_clockPre_lockRow (p : Params) (st : State p.n) (t : Time) {A : Block} {D : Time}
    (hrow : LockRow st A (SA.releaseThreshold p.toParams) D) (ht : t < D)
    (hrel : 0 ≤ t - 5 * p.Δ → t = SA.releaseTime p.toParams ((t - 5 * p.Δ) / (4 * p.Δ)).toNat →
      ∀ X : State p.n, X.base.votes = st.base.votes → X.base.blocks = st.base.blocks →
      GridCO.releaseCount p.toParams.engine (actView X)
        ((t - 5 * p.Δ) / (4 * p.Δ)).toNat A < SA.releaseThreshold p.toParams) :
    LockRow (clockPre p st t) A (SA.releaseThreshold p.toParams) D := by
  rw [LockRow_def] at hrow ⊢
  obtain ⟨row, hr, hA, hg, hd⟩ := hrow
  refine ⟨row, (pcsa_clockPre_slow p st t).2.2.2.2 row hr (lt_of_lt_of_le ht hd) ?_, hA, hg, hd⟩
  intro h1 h2 X hv hb
  rw [hA, hg]
  exact hrel h1 h2 X hv hb

/-- The pre-gate clock keeps the base facts of the invariant. -/
theorem pcsa_clockPre_inv (p : Params) (st : State p.n) (t : Time) {A : Block}
    {D₂ : Time} {bound : State p.n} {pre : Prop}
    (hinv : SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre st)
    (hrow₂ : ¬ pre → LockRow (clockPre p st t) A (SA.releaseThreshold p.toParams) D₂) :
    SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre (clockPre p st t) := by
  obtain ⟨c1, c2, -, c4, -⟩ := pcsa_clockPre_slow p st t
  refine ⟨c1 ▸ hinv.stable, fun row hr => hinv.rows row (c4 hr), ?_, hrow₂,
    fun hp => List.Subset.trans c4 (hinv.sub hp), fun hp => c2.trans (hinv.genuine hp)⟩
  rw [(pcsa_clockPre_frame p st t).2.2.2.2]
  exact hinv.tree

/-- [pcsa34-r4.3 §5.5 step 2] A tick before the pending gate that runs no
gate keeps the invariant. -/
theorem pcsa_tick_pre_inv (p : Params) (st : State p.n) (t : Time) {A : Block}
    {D₂ : Time} {bound : State p.n} {pre : Prop}
    (hinv : SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre st) (hpre : pre)
    (hng : clock p st t = clockPre p st t) :
    SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre (clock p st t) := by
  rw [hng]
  exact pcsa_clockPre_inv p st t hinv (fun hn => absurd hpre hn)

/-- [pcsa34-r4.3 §5.5 step 2, the pending gate] The tick of the pending gate
`d_s` renews the lock on `A`: the label is not saved, the result `h ⪰ A` is
compatible with every boundary lock, the held PCs are compatible with `A`,
and the `k − 1` previous saved results are `⪰ A`. -/
theorem pcsa_tick_renew_inv (p : Params) (st : State p.n) (t : Time) (s : Slot) {A : Block}
    {D₂ : Time} {bound : State p.n} {pre : Prop}
    (hinv : SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre st) (hpre : pre)
    (hF : st.fg.F = .genesis)
    (hgate : clock p st t = gateStep p (clockPre p st t) s)
    (hunsaved : GridCO.savedGenuine bound.base s = none)
    (hres : ∃ h, SA.Root.confirmationFrom p.toParams .genesis (actView (clockPre p st t)) s =
      some h ∧ Block.Preceq A h ∧ ∀ row ∈ bound.base.obligations, Block.Compatible row.1 h)
    (hAg : A ≠ .genesis) (hpcs : ∀ c ∈ st.pcs, Block.Compatible c.target A)
    (hk : p.k ≤ s + 1)
    (hsaved : ∀ j < p.k - 1, ∃ C, GridCO.savedGenuine bound.base (s - (j + 1)) =
      some (some C) ∧ Block.Preceq A C)
    (hD₂ : D₂ ≤ SA.gateTime p.toParams s + SA.lifetime p.toParams)
    (pre' : Prop) (hpre' : ¬ pre') :
    SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre' (clock p st t) := by
  have hc := pcsa_clockPre_inv p st t hinv (fun hn => absurd hpre hn)
  have hF' : (clockPre p st t).fg.F = .genesis := by
    rw [(pcsa_clockPre_frame p st t).2.2.2.1]
    exact hF
  have hgen : (clockPre p st t).base.genuine = bound.base.genuine := hc.genuine hpre
  rw [hgate, pcsa_gateStep_genesis p _ s hF']
  have hns : (GridCO.savedGenuine (clockPre p st t).base s).isSome = false := by
    change (((clockPre p st t).base.genuine.find? (fun row => row.1 == s)).map
      Prod.snd).isSome = false
    rw [hgen]
    change (GridCO.savedGenuine bound.base s).isSome = false
    rw [hunsaved]
    rfl
  rw [hns, ite_eq_right (by decide)]
  obtain ⟨h, hh, hAh, hb⟩ := hres
  obtain ⟨g1, g2, g3, -, -⟩ := pcsa_gateFrom_renew p .genesis (clockPre p st t).pcs
    (gateRank p (clockPre p st t) s) (clockPre p st t) s A h hc.rows hh hAh
    (fun row hr => hb row (hc.sub hpre hr)) hc.tree hAg hF'
    (by
      rw [leaseWriteOK_iff]
      intro c hcm _
      rw [(pcsa_clockPre_frame p st t).1] at hcm
      exact hpcs c hcm)
    hk (fun j hj => by
      obtain ⟨C, hC, hAC⟩ := hsaved j hj
      refine ⟨C, ?_, hAC⟩
      change ((clockPre p st t).base.genuine.find? (fun row => row.1 == s - (j + 1))).map
        Prod.snd = _
      rw [hgen]
      exact hC)
  have hrow₂ := LockRow.row_mono g3 hD₂
  have hgf := pcsa_gateFrom_frame p .genesis (clockPre p st t).pcs
    (gateRank p (clockPre p st t) s) (clockPre p st t) s
  refine ⟨g1, g2, ?_, fun _ => hrow₂, fun hp => absurd hp hpre', fun hp => absurd hp hpre'⟩
  rw [hgf.2.2.2.2.2]
  exact hc.tree

/-- [pcsa34-r4.3 §5.5 steps 2, 4] A tick after the pending gate keeps the
invariant: the lock on `A` is live with the full deadline, so a gate keeps
`S ⪰ A` and renews or keeps the lock. -/
theorem pcsa_tick_post_inv (p : Params) (st : State p.n) (t : Time) {A : Block}
    {D₂ : Time} {bound : State p.n} {pre : Prop}
    (hinv : SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre st) (hnpre : ¬ pre)
    (hF : st.fg.F = .genesis) (ht : t < D₂)
    (hrel : 0 ≤ t - 5 * p.Δ → t = SA.releaseTime p.toParams ((t - 5 * p.Δ) / (4 * p.Δ)).toNat →
      ∀ X : State p.n, X.base.votes = st.base.votes → X.base.blocks = st.base.blocks →
      GridCO.releaseCount p.toParams.engine (actView X)
        ((t - 5 * p.Δ) / (4 * p.Δ)).toNat A < SA.releaseThreshold p.toParams)
    (hgates : ∀ s, t = SA.gateTime p.toParams s →
      D₂ ≤ SA.gateTime p.toParams s + SA.lifetime p.toParams)
    (pre' : Prop) (hpre' : ¬ pre') :
    SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre' (clock p st t) := by
  have hrow₂ := pcsa_clockPre_lockRow p st t (hinv.renewed hnpre) ht hrel
  have hc := pcsa_clockPre_inv p st t hinv (fun _ => hrow₂)
  have hF' : (clockPre p st t).fg.F = .genesis := by
    rw [(pcsa_clockPre_frame p st t).2.2.2.1]
    exact hF
  have hnow : (clockPre p st t).base.now = t := (pcsa_clockPre_slow p st t).2.2.1
  have hkeep : SlowInv A (SA.releaseThreshold p.toParams) D₂ bound pre' (clockPre p st t) :=
    ⟨hc.stable, hc.rows, hc.tree, fun _ => hrow₂, fun hp => absurd hp hpre',
      fun hp => absurd hp hpre'⟩
  rcases pcsa_clock_cases p st t with ⟨he, -⟩ | ⟨-, hts, he⟩
  · rw [he]
    exact hkeep
  · rw [he, pcsa_gateStep_genesis p _ _ hF']
    split
    · exact hkeep
    · obtain ⟨g1, g2, g3, -, g5⟩ := pcsa_gateFrom_slow p .genesis (clockPre p st t).pcs
        (gateRank p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) (clockPre p st t)
        ((t - 6 * p.Δ) / (4 * p.Δ)).toNat A D₂ hc.stable hc.rows hrow₂ (by rw [hnow]; exact ht)
        (hgates _ hts)
      refine ⟨g1, g2, g5 ▸ hc.tree, fun _ => g3, fun hp => absurd hp hpre',
        fun hp => absurd hp hpre'⟩

/-! ### The time -/

/-- A gate keeps the time. -/
theorem pcsa_gateFrom_now (p : Params) (a : Block) (cs : List (PC p.n)) (ρ : Option PCRank)
    (st : State p.n) (s : Slot) : (gateFrom p a cs ρ st s).base.now = st.base.now := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s
  · rfl
  · dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun a : State p.n => a.base.now = st.base.now)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun a : State p.n => a.base.now = st.base.now)
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-! ### Saved labels -/

/-- A label saved after a gate record is saved before it or is the recorded label. -/
theorem pcsa_savedGenuine_of_record (v : GridCO.State n .root) (d r : Slot) (res : Option Block)
    (h : (GridCO.savedGenuine { v with genuine :=
      (@GridCO.recordGenuine GridCO.slowLeasePolicy n .root v d res) } r).isSome) :
    (GridCO.savedGenuine v r).isSome ∨ r = d := by
  change (((@GridCO.recordGenuine GridCO.slowLeasePolicy n .root v d res).find?
    (fun row => row.1 == r)).map Prod.snd).isSome at h
  change ((v.genuine.find? (fun row => row.1 == r)).map Prod.snd).isSome ∨ r = d
  delta GridCO.recordGenuine at h
  split at h
  · rw [List.find?_append] at h
    cases hf : v.genuine.find? (fun row => row.1 == r) with
    | some y => exact Or.inl rfl
    | none =>
      rw [hf] at h
      right
      cases hd : (d == r) with
      | true => exact (beq_iff_eq.mp hd).symm
      | false =>
        exfalso
        change ((([(d, res)] : List (Slot × Option Block)).find?
          (fun row => row.1 == r)).map Prod.snd).isSome = true at h
        rw [List.find?_singleton] at h
        dsimp only at h
        rw [hd] at h
        cases h
  · exact Or.inl h

/-- A gate records at most its own label. -/
theorem pcsa_gateFrom_genuine (p : Params) (a : Block) (cs : List (PC p.n)) (ρ : Option PCRank)
    (st : State p.n) (s r : Slot)
    (h : (GridCO.savedGenuine (gateFrom p a cs ρ st s).base r).isSome) :
    (GridCO.savedGenuine st.base r).isSome ∨ r = s := by
  have hrec : ∀ res, (GridCO.savedGenuine { (actView st) with genuine :=
      (@GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s res) } r).isSome →
      (GridCO.savedGenuine st.base r).isSome ∨ r = s :=
    fun res hr => pcsa_savedGenuine_of_record (actView st) s r res hr
  revert h
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact hrec none
  | some hh =>
    dsimp only
    split
    · exact hrec (some hh)
    · intro hs
      apply hrec (some hh)
      revert hs
      apply List.foldlRecOn (motive := fun acc : State p.n =>
        (GridCO.savedGenuine acc.base r).isSome = true →
        (GridCO.savedGenuine { (actView st) with genuine :=
          (@GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some hh)) }
          r).isSome = true)
      · exact id
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc : State p.n =>
          (GridCO.savedGenuine acc.base r).isSome = true →
          (GridCO.savedGenuine { (actView st) with genuine :=
            (@GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some hh)) }
            r).isSome = true)
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- [stage 1] The clock saves at most the label of its gate. -/
theorem pcsa_clock_genuine (p : Params) (st : State p.n) (t : Time) (r : Slot)
    (hF : st.fg.F = .genesis)
    (h : (GridCO.savedGenuine (clock p st t).base r).isSome) :
    (GridCO.savedGenuine st.base r).isSome ∨ t = SA.gateTime p.toParams r := by
  have hpre : (clockPre p st t).base.genuine = st.base.genuine := (pcsa_clockPre_slow p st t).2.1
  have hsv : GridCO.savedGenuine (clockPre p st t).base r = GridCO.savedGenuine st.base r := by
    change ((clockPre p st t).base.genuine.find? (fun row => row.1 == r)).map Prod.snd = _
    rw [hpre]
    rfl
  have hF' : (clockPre p st t).fg.F = .genesis := by
    rw [(pcsa_clockPre_frame p st t).2.2.2.1]
    exact hF
  rcases pcsa_clock_cases p st t with ⟨he, -⟩ | ⟨-, hts, he⟩
  · rw [he, hsv] at h
    exact Or.inl h
  · rw [he, pcsa_gateStep_genesis p _ _ hF'] at h
    split at h
    · rw [hsv] at h
      exact Or.inl h
    · rcases pcsa_gateFrom_genuine p _ _ _ _ _ r h with h1 | h1
      · rw [hsv] at h1
        exact Or.inl h1
      · right
        rw [h1]
        exact hts

end AvailableChain.PCSA
end
