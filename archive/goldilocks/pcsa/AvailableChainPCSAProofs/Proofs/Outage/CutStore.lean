module
public import AvailableChainPCSAProofs.Proofs.Outage.SlowStep

public section

/-! Store facts for the clean side of the cut (pcsa34-r4.3 §5.5 steps 1–2): a
gate sets `S` only to its result, records exactly its own label and keeps the
other saved labels, and every block between the anchor and a gate result is
in the walked tree. -/

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG Gen.Pure

variable {n : Nat}

/-! ### The walk path -/

/-- Every block between the anchor and the end of a GHOST walk is the anchor
or a member of the walked tree. -/
theorem pcsa_ghostWalk_path (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat) (anchor b : Block) (h1 : Block.Preceq anchor b)
    (h2 : Block.Preceq b (GridCO.ghostWalk tree score eligible fuel anchor)) :
    b = anchor ∨ b ∈ tree := by
  induction fuel generalizing anchor with
  | zero => exact Or.inl (block_preceq_antisymm h2 h1)
  | succ fuel ih =>
    cases hs : GridCO.ghostStep tree score eligible anchor with
    | none =>
      have hw : GridCO.ghostWalk tree score eligible (fuel + 1) anchor = anchor := by
        change (match GridCO.ghostStep tree score eligible anchor with
          | none => anchor
          | some c => GridCO.ghostWalk tree score eligible fuel c) = anchor
        rw [hs]
      rw [hw] at h2
      exact Or.inl (block_preceq_antisymm h2 h1)
    | some child =>
      have hw : GridCO.ghostWalk tree score eligible (fuel + 1) anchor =
          GridCO.ghostWalk tree score eligible fuel child := by
        change (match GridCO.ghostStep tree score eligible anchor with
          | none => anchor
          | some c => GridCO.ghostWalk tree score eligible fuel c) = _
        rw [hs]
      rw [hw] at h2
      obtain ⟨hct, hpar, -⟩ := @GridCO.ghostStep_child GridCO.slowLeasePolicy tree score
        eligible anchor child hs
      by_cases hcb : Block.Preceq child b
      · rcases ih child hcb h2 with he | hm
        · exact Or.inr (he ▸ hct)
        · exact Or.inr hm
      · have hcw : Block.Preceq child (GridCO.ghostWalk tree score eligible fuel child) :=
          @GridCO.ghostWalk_extends GridCO.slowLeasePolicy tree score eligible fuel child
        have hbc : Block.Preceq b child := by
          rcases Bool.or_eq_true_iff.mp (block_compatible_of_common h2 hcw) with h | h
          · exact h
          · exact absurd h hcb
        cases child with
        | genesis => cases hpar
        | node q s r x =>
          have hq : q = anchor := Option.some.inj hpar
          subst hq
          have hb' : b = Block.node q s r x ∨ Block.Preceq b q := by
            change (decide (b = Block.node q s r x) || Block.preceq b q) = true at hbc
            rcases Bool.or_eq_true_iff.mp hbc with h | h
            · exact Or.inl (of_decide_eq_true h)
            · exact Or.inr h
          rcases hb' with he | hbq
          · exact absurd (he ▸ block_preceq_refl _) hcb
          · exact Or.inl (block_preceq_antisymm hbq h1)

/-- Every block between the anchor and a gate result is the anchor or in the
walked tree. -/
theorem pcsa_confirmationFrom_path (p : Params) (a : Block) (v : GridCO.State n .root)
    (s : Slot) (h b : Block) (hc : SA.Root.confirmationFrom p.toParams a v s = some h)
    (h1 : Block.Preceq a b) (h2 : Block.Preceq b h) : b = a ∨ b ∈ v.blocks := by
  delta SA.Root.confirmationFrom GridCO.confirmationFrom at hc
  dsimp only at hc
  split at hc
  · have he := Option.some.inj hc
    rw [← he] at h2
    rcases pcsa_ghostWalk_path _ _ _ _ a b h1 h2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (List.mem_eraseDups.mp h')
  · cases hc

/-! ### Saved labels -/

/-- The saved labels after a gate are those recorded by its result. -/
theorem pcsa_gateFrom_genuine_eq (p : Params) (a : Block) (cs : List (PC p.n))
    (ρ : Option PCRank) (st : State p.n) (s : Slot) :
    (gateFrom p a cs ρ st s).base.genuine = @GridCO.recordGenuine GridCO.slowLeasePolicy p.n
      .root (actView st) s (SA.Root.confirmationFrom p.toParams a (actView st) s) := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some h =>
    dsimp only
    split
    · rfl
    · generalize hst1 : ({ st with base := { st.base with
        goldfishRecord := GridCO.advance (actView st).goldfishRecord h
        genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some h)
        stableRecord := GridCO.advance st.base.stableRecord h } } : State p.n) = st1
      have e5 : st1.base.genuine =
          @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some h) := by
        rw [← hst1]
      rw [(pcsa_lockFold_slow p s ρ .genesis _ _
        (fun b _ => block_compatible_of_common (block_preceq_refl b) (block_genesis_preceq b))
        le_rfl st1 (fun row _ => block_compatible_of_common (block_preceq_refl _)
          (block_genesis_preceq _))).2.2.genuine, e5]

/-- A gate on an unsaved label saves its result. -/
theorem pcsa_gateFrom_saved_self (p : Params) (a : Block) (cs : List (PC p.n))
    (ρ : Option PCRank) (st : State p.n) (s : Slot) (hns : GridCO.savedGenuine st.base s = none) :
    GridCO.savedGenuine (gateFrom p a cs ρ st s).base s =
      some (SA.Root.confirmationFrom p.toParams a (actView st) s) := by
  change ((gateFrom p a cs ρ st s).base.genuine.find? (fun row => row.1 == s)).map
    Prod.snd = _
  rw [pcsa_gateFrom_genuine_eq]
  have hf : st.base.genuine.find? (fun row => row.1 == s) = none := by
    change (st.base.genuine.find? (fun row => row.1 == s)).map Prod.snd = none at hns
    exact Option.map_eq_none_iff.mp hns
  delta GridCO.recordGenuine
  split
  · change ((st.base.genuine ++ [(s, SA.Root.confirmationFrom p.toParams a (actView st) s)]).find?
      (fun row => row.1 == s)).map Prod.snd = _
    rw [List.find?_append, hf]
    simp
  · rename_i hn
    exfalso
    apply hn
    change (true && !((st.base.genuine.find? (fun row => row.1 == s)).map Prod.snd).isSome) = true
    rw [hf]
    rfl

/-- A gate keeps every saved label. -/
theorem pcsa_gateFrom_saved_keep (p : Params) (a : Block) (cs : List (PC p.n))
    (ρ : Option PCRank) (st : State p.n) (s r : Slot) (y : Option Block)
    (hy : GridCO.savedGenuine st.base r = some y) :
    GridCO.savedGenuine (gateFrom p a cs ρ st s).base r = some y := by
  change ((gateFrom p a cs ρ st s).base.genuine.find? (fun row => row.1 == r)).map
    Prod.snd = _
  rw [pcsa_gateFrom_genuine_eq]
  exact pcsa_savedGenuine_record (actView st) s r _ y hy

/-- [stage 1] The clock keeps every saved label. -/
theorem pcsa_clock_saved_keep (p : Params) (st : State p.n) (t : Time) (r : Slot)
    (y : Option Block) (hF : st.fg.F = .genesis) (hy : GridCO.savedGenuine st.base r = some y) :
    GridCO.savedGenuine (clock p st t).base r = some y := by
  have hpre : (clockPre p st t).base.genuine = st.base.genuine := (pcsa_clockPre_slow p st t).2.1
  have hsv : GridCO.savedGenuine (clockPre p st t).base r = some y := by
    change ((clockPre p st t).base.genuine.find? (fun row => row.1 == r)).map Prod.snd = _
    rw [hpre]
    exact hy
  have hF' : (clockPre p st t).fg.F = .genesis := by
    rw [(pcsa_clockPre_frame p st t).2.2.2.1]
    exact hF
  rcases pcsa_clock_cases p st t with ⟨he, -⟩ | ⟨-, -, he⟩
  · rw [he]
    exact hsv
  · rw [he, pcsa_gateStep_genesis p _ _ hF']
    split
    · exact hsv
    · exact pcsa_gateFrom_saved_keep p _ _ _ _ _ r y hsv

/-! ### The record -/

/-- A gate keeps `S`, or sets it to its result. -/
theorem pcsa_gateFrom_record (p : Params) (a : Block) (cs : List (PC p.n)) (ρ : Option PCRank)
    (st : State p.n) (s : Slot) :
    (gateFrom p a cs ρ st s).base.stableRecord = st.base.stableRecord ∨
      SA.Root.confirmationFrom p.toParams a (actView st) s =
        some (gateFrom p a cs ρ st s).base.stableRecord := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact Or.inl rfl
  | some h =>
    dsimp only
    split
    · exact Or.inl rfl
    · generalize hst1 : ({ st with base := { st.base with
        goldfishRecord := GridCO.advance (actView st).goldfishRecord h
        genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some h)
        stableRecord := GridCO.advance st.base.stableRecord h } } : State p.n) = st1
      have e2 : st1.base.stableRecord = GridCO.advance st.base.stableRecord h := by rw [← hst1]
      rw [(pcsa_lockFold_slow p s ρ .genesis _ _
        (fun b _ => block_compatible_of_common (block_preceq_refl b) (block_genesis_preceq b))
        le_rfl st1 (fun row _ => block_compatible_of_common (block_preceq_refl _)
          (block_genesis_preceq _))).2.2.stable, e2]
      rcases pcsa_advance_cases st.base.stableRecord h with he | he
      · exact Or.inl he
      · rw [he]
        exact Or.inr rfl

/-- [pcsa34-r4.3 §5.5 step 2] A gate whose result `h ⪰ A` is compatible with
every lock sets `S ⪰ A` and keeps the tree. -/
theorem pcsa_gateFrom_pass (p : Params) (a : Block) (cs : List (PC p.n)) (ρ : Option PCRank)
    (st : State p.n) (s : Slot) (A h : Block)
    (hc : SA.Root.confirmationFrom p.toParams a (actView st) s = some h)
    (hAh : Block.Preceq A h)
    (hguard : ∀ row ∈ st.base.obligations, Block.Compatible row.1 h) :
    Block.Preceq A (gateFrom p a cs ρ st s).base.stableRecord ∧
      (gateFrom p a cs ρ st s).base.blocks = st.base.blocks := by
  rw [gateFrom_def]
  dsimp only
  rw [hc]
  dsimp only
  split
  · rename_i hg
    exfalso
    obtain ⟨row, hr, hx⟩ := List.any_eq_true.mp hg
    rw [Bool.and_eq_true] at hx
    have := hguard row hr
    rw [Block.Compatible] at this
    rw [this] at hx
    exact absurd hx.2 (by decide)
  · generalize hst1 : ({ st with base := { st.base with
      goldfishRecord := GridCO.advance (actView st).goldfishRecord h
      genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s (some h)
      stableRecord := GridCO.advance st.base.stableRecord h } } : State p.n) = st1
    have e2 : st1.base.stableRecord = GridCO.advance st.base.stableRecord h := by rw [← hst1]
    have e4 : st1.base.blocks = st.base.blocks := by rw [← hst1]
    have h3 := (pcsa_lockFold_slow p s ρ .genesis _ ((actView st).blocks.filter
      (fun b => b != Block.genesis && Block.preceq b h && leaseWriteOK cs ρ b))
      (fun b _ => block_compatible_of_common (block_preceq_refl b) (block_genesis_preceq b))
      le_rfl st1 (fun row _ => block_compatible_of_common (block_preceq_refl _)
        (block_genesis_preceq _))).2.2
    exact ⟨h3.stable ▸ e2 ▸ pcsa_advance_of_above hAh, h3.blocks.trans e4⟩

/-! ### Live rows -/

/-- After the pre-gate clock every lock row is live. -/
theorem pcsa_clockPre_live (p : Params) (st : State p.n) (t : Time) :
    ∀ row ∈ (clockPre p st t).base.obligations, t < row.2.2 := by
  obtain ⟨X, h6, he⟩ : ∃ X : State p.n,
      X.base.obligations = st.base.obligations.filter (fun row => decide (t < row.2.2)) ∧
      clockPre p st t = if (0 ≤ t - 5 * p.Δ && t == SA.releaseTime p.toParams
          ((t - 5 * p.Δ) / (4 * p.Δ)).toNat) = true then
        onView (fun v => SA.Root.release p.toParams v ((t - 5 * p.Δ) / (4 * p.Δ)).toNat) X
        else X := by
    unfold clockPre
    dsimp only
    refine ⟨_, ?_, rfl⟩
    split <;> split <;> rfl
  have hX : ∀ row ∈ X.base.obligations, t < row.2.2 := by
    intro row hr
    rw [h6, List.mem_filter, decide_eq_true_iff] at hr
    exact hr.2
  rw [he]
  split
  · intro row hr
    change row ∈ (actView X).obligations.filter _ at hr
    exact hX row (List.mem_filter.mp hr).1
  · exact hX

/-- A gate whose deadline is after `t` keeps every lock row live at `t`. -/
theorem pcsa_gateFrom_live (p : Params) (a : Block) (cs : List (PC p.n)) (ρ : Option PCRank)
    (st : State p.n) (s : Slot) (t : Time) (hl : ∀ row ∈ st.base.obligations, t < row.2.2)
    (ht : t < SA.gateTime p.toParams s + SA.lifetime p.toParams) :
    ∀ row ∈ (gateFrom p a cs ρ st s).base.obligations, t < row.2.2 := by
  have hw : ∀ (acc : State p.n) b g, (∀ row ∈ acc.base.obligations, t < row.2.2) →
      ∀ row ∈ (writeLease acc b g (SA.gateTime p.toParams s + SA.lifetime p.toParams)
        ρ).base.obligations, t < row.2.2 := by
    intro acc b g ha row hr
    rcases (pcsa_writeLease_rows acc b g _ ρ row).mp hr with ⟨hr', -⟩ | ⟨-, -, hd⟩
    · exact ha row hr'
    · rw [hd]
      exact lt_of_lt_of_le ht (le_max_right _ _)
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact hl
  | some h =>
    dsimp only
    split
    · exact hl
    · apply List.foldlRecOn (motive := fun acc : State p.n =>
        ∀ row ∈ acc.base.obligations, t < row.2.2)
      · exact hl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc : State p.n =>
          ∀ row ∈ acc.base.obligations, t < row.2.2)
        · exact ha
        · intro acc' ha' g _
          exact hw acc' b g ha'

/-- [stage 1] After a tick every lock row is live. -/
theorem pcsa_clock_live (p : Params) (st : State p.n) (t : Time) (hF : st.fg.F = .genesis)
    (hL : (1 : Time) ≤ SA.lifetime p.toParams) :
    ∀ row ∈ (clock p st t).base.obligations, t < row.2.2 := by
  have hF' : (clockPre p st t).fg.F = .genesis := by
    rw [(pcsa_clockPre_frame p st t).2.2.2.1]
    exact hF
  rcases pcsa_clock_cases p st t with ⟨he, -⟩ | ⟨-, hts, he⟩
  · rw [he]
    exact pcsa_clockPre_live p st t
  · rw [he, pcsa_gateStep_genesis p _ _ hF']
    split
    · exact pcsa_clockPre_live p st t
    · refine pcsa_gateFrom_live p _ _ _ _ _ t (pcsa_clockPre_live p st t) ?_
      rw [← hts]
      linarith

end AvailableChain.PCSA
end
