module
public import AvailableChainPCSAProofs.Proofs.Recovery.ProposalStore
public import AvailableChainPCSAProofs.Proofs.Recovery.FirstHonestSlot
public import AvailableChainFGSA.Proofs.WindowStore
public import AvailableChainFGSARun.Proofs.Excludes
public import AvailableChainGeneric.Proofs.V2.Duty.Reads

-- Use a private matcher for the model's parent-invalidity test.
namespace AvailableChain.PCSA.Run
private def recoveryInvalid (p : Params) (st : State p.n) (N : NamedProposal p.n) : Bool :=
  if !namedParentHeld st N then false else
    match parentFG st N.erase with
    | none => false
    | some P => !rowsValidForParent p P N.slot N.rows
private theorem recoveryInvalid_eq : @invalidForParent = @recoveryInvalid := rfl
end AvailableChain.PCSA.Run

public section

/-! Permanent exclusions and the F1 deadline transport in recovery. -/

namespace AvailableChain.PCSA

private def ExFrame {n : Nat} (old st : State n) : Prop :=
  st.base.now = old.base.now ∧ SimplexFG.FGBlock.Preceq old.fg.F st.fg.F ∧ old.fg.TF ⊆ st.fg.TF

private theorem ex_normalize {n : Nat} (old st : State n) (h : ExFrame old st) :
    ExFrame old (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem ex_reconcile {n : Nat} (old st : State n) (h : ExFrame old st) :
    ExFrame old (reconcile st) := ex_normalize old _ h

private theorem ex_install {n : Nat} (old st : State n) (pc : PC n) (h : ExFrame old st) :
    ExFrame old (installPC st pc) := by
  rw [installPC_def]
  split <;> exact h

private theorem ex_raw {n : Nat} (old st : State n) (a : AckWire n) (h : ExFrame old st) :
    ExFrame old (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem ex_row (p : Params) (old st : State p.n) (a : RowWire p.n)
    (h : ExFrame old st) : ExFrame old (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

/-- Delivery keeps the clock, extends finality, and retains the FG tree. -/
theorem recovery_process_frame (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.now = st.base.now ∧
      SimplexFG.FGBlock.Preceq st.fg.F (process p st o).fg.F ∧
      st.fg.TF ⊆ (process p st o).fg.TF := by
  have hi : ExFrame st st := ⟨rfl, KitFG.preceq_refl _, Finset.Subset.refl _⟩
  have hc := collectPCs_invariant (ExFrame st) (fun acc pc h _ => ex_install st acc pc h)
  have ha (acc : State p.n) (as : List (AckWire p.n)) (h : ExFrame st acc) :
      ExFrame st (as.foldl poolAckRaw acc) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => ex_raw st acc a hh)
  change ExFrame st (process p st o)
  delta process
  cases hd : o.decode with
  | none => exact hi
  | some msg => cases msg with
    | vote s i r =>
      exact ⟨FGSA.Run.Internal.grid_admitVote_now _ _, KitFG.preceq_refl _, Finset.Subset.refl _⟩
    | row i body => exact ex_row p st st _ hi
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact hi
      · cases hp : parentFG st N.erase with
        | none => exact hi
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hn : ExFrame st { st with
                  base := (GridCO.admitProposal p.toParams.engine st.base
                    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead))
                  fg := FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) } :=
                ⟨FGSA.Run.Internal.grid_admitProposal_now _ _ _ _,
                  FGSA.Window.window_on_block_F_mono p p.K_W st.fg _,
                  FGSA.Window.window_on_block_TF_subset p p.K_W st.fg _⟩
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply ex_reconcile; exact hn)
                | exact hn
            · intro acc hh a _
              exact ex_row p st acc a hh
          · exact hi
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact hi
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact hi
        · split <;> exact hi
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ hi)
      · exact hi

private def ExGrid (p : Params) (v : GridCO.Wire p.n .root) (st : State p.n) : Prop :=
  GridCO.excludes p.toParams.engine st.base v = true

private theorem ex_grid_normalize (p : Params) (v : GridCO.Wire p.n .root)
    (st : State p.n) (h : ExGrid p v st) : ExGrid p v (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem ex_grid_reconcile (p : Params) (v : GridCO.Wire p.n .root)
    (st : State p.n) (h : ExGrid p v st) : ExGrid p v (reconcile st) :=
  ex_grid_normalize p v _ h

private theorem ex_grid_install (p : Params) (v : GridCO.Wire p.n .root)
    (st : State p.n) (pc : PC p.n) (h : ExGrid p v st) : ExGrid p v (installPC st pc) := by
  rw [installPC_def]
  split <;> exact h

private theorem ex_grid_raw (p : Params) (v : GridCO.Wire p.n .root)
    (st : State p.n) (a : AckWire p.n) (h : ExGrid p v st) : ExGrid p v (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some val => dsimp only; split <;> exact h

private theorem ex_grid_row (p : Params) (v : GridCO.Wire p.n .root)
    (st : State p.n) (a : RowWire p.n) (h : ExGrid p v st) : ExGrid p v (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some val => dsimp only; split <;> exact h

set_option maxHeartbeats 800000 in
-- The proposal case expands two pool folds and nested record updates.
private theorem ex_grid_process (p : Params) (st : State p.n) (o : Wire p.n)
    (v : GridCO.Wire p.n .root) (h : ExGrid p v st) : ExGrid p v (process p st o) := by
  have hc := collectPCs_invariant (ExGrid p v) (fun acc pc h _ => ex_grid_install p v acc pc h)
  have ha (acc : State p.n) (as : List (AckWire p.n)) (h : ExGrid p v acc) :
      ExGrid p v (as.foldl poolAckRaw acc) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => ex_grid_raw p v acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact FGSA.Run.Internal.grid_admitVote_keeps _ _ _ h
    | row i body => exact ex_grid_row p v st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hn := FGSA.Run.Internal.grid_admitProposal_keeps
                st.base (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) v h
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply ex_grid_reconcile; exact hn)
                | exact hn
            · intro acc hh a _
              exact ex_grid_row p v acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some val =>
        rcases val with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h

/-- Clock steps keep vote and FG inputs and set the local time. -/
theorem recovery_clock_fields (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.now = t ∧ (clock p st t).base.votes = st.base.votes ∧
      (clock p st t).fg = st.fg := by
  have hn (st : State p.n) : (normalizeS st).base.now = st.base.now ∧
      (normalizeS st).base.votes = st.base.votes ∧ (normalizeS st).fg = st.fg := by
    delta normalizeS
    split <;> exact ⟨rfl, rfl, rfl⟩
  have hg (st : State p.n) (a : Block) (cs : List (PC p.n)) (rank : Option PCRank)
      (s : Slot) :
      (gateFrom p a cs rank st s).base.now = st.base.now ∧
      (gateFrom p a cs rank st s).base.votes = st.base.votes ∧
      (gateFrom p a cs rank st s).fg = st.fg := by
    rw [gateFrom_def]
    dsimp only
    cases SA.Root.confirmationFrom p.toParams a (actView st) s with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some C =>
      dsimp only
      split
      · exact ⟨rfl, rfl, rfl⟩
      · apply List.foldlRecOn (motive := fun acc : State p.n =>
          acc.base.now = st.base.now ∧ acc.base.votes = st.base.votes ∧ acc.fg = st.fg)
        · exact ⟨rfl, rfl, rfl⟩
        · intro acc hh b _
          apply List.foldlRecOn (motive := fun acc : State p.n =>
            acc.base.now = st.base.now ∧ acc.base.votes = st.base.votes ∧ acc.fg = st.fg)
          · exact hh
          · intro acc' hh' g _
            exact hh'
  have hp : (clockPre p st t).base.now = t ∧ (clockPre p st t).base.votes = st.base.votes ∧
      (clockPre p st t).fg = st.fg := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact ⟨rfl, rfl, rfl⟩
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    rw [(hn _).1, (hn _).2.1, (hn _).2.2]
    split
    · exact hp
    · rw [(hg _ _ _ _ _).1, (hg _ _ _ _ _).2.1, (hg _ _ _ _ _).2.2]
      exact hp
  · exact hp

end AvailableChain.PCSA

namespace AvailableChain.PCSA

private theorem ex_parent_spec {n : Nat} (st : State n) (B : Block)
    (P : SimplexFG.FGBlock (Fin n)) :
    parentFG st B = some P ↔ P ∈ st.fg.TF ∧ eraseFG P = B.parent := by
  constructor
  · intro hp
    obtain ⟨hm, he⟩ := FGSA.pickPair_some_spec _ _ hp
    exact ⟨hm, of_decide_eq_true he⟩
  · rintro ⟨hm, he⟩
    delta parentFG
    apply KitFG.pickPair_eq_of_unique _ _ P hm (decide_eq_true he)
    intro P' _ hp
    have hh := (of_decide_eq_true hp).trans he.symm
    rw [pcsa_eraseFG_eq, pcsa_eraseFG_eq] at hh
    exact FGSA.eraseFG_injective hh

private theorem ex_invalid_mono (p : Params) (st st' : State p.n)
    (ht : st.fg.TF ⊆ st'.fg.TF) (hn : st.namedBodies ⊆ st'.namedBodies)
    (N : NamedProposal p.n) (h : Run.invalidForParent p st N = true) :
    Run.invalidForParent p st' N = true := by
  have hp : namedParentHeld st N = true := by
    rw [Run.recoveryInvalid_eq] at h
    delta Run.recoveryInvalid at h
    split at h
    · cases h
    · simpa only [Bool.not_eq_true', Bool.not_eq_false] using ‹¬(!namedParentHeld st N) = true›
  have hp' : namedParentHeld st' N = true := decide_eq_true (hn (of_decide_eq_true hp))
  rw [Run.recoveryInvalid_eq] at h ⊢
  delta Run.recoveryInvalid at h ⊢
  simp only [hp, hp', Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
  cases hP : parentFG st N.erase with
  | none => simp only [hP, Bool.false_eq_true] at h
  | some P =>
    obtain ⟨hm, he⟩ := (ex_parent_spec st N.erase P).mp hP
    have hP' := (ex_parent_spec st' N.erase P).mpr ⟨ht hm, he⟩
    simpa only [hP, hP'] using h

private theorem ex_block_mono {n : Nat} (st st' : State n)
    (hf : SimplexFG.FGBlock.Preceq st.fg.F st'.fg.F) (B : Block)
    (h : blockExcluded st B = true) : blockExcluded st' B = true := by
  change (!Block.compatible B (eraseFG st.fg.F)) = true at h
  rw [Bool.not_eq_true'] at h
  have hn : ¬ Block.Compatible B (eraseFG st.fg.F) := Bool.eq_false_iff.mp h
  have hp : Block.Preceq (eraseFG st.fg.F) (eraseFG st'.fg.F) := by
    rw [pcsa_eraseFG_eq, pcsa_eraseFG_eq]
    exact FGSA.eraseFG_preceq hf
  change (!Block.compatible B (eraseFG st'.fg.F)) = true
  rw [Bool.not_eq_true']
  exact Bool.eq_false_iff.mpr (Gen.Pure.block_incompatible_of_preceq hn hp)

/-- Delivery preserves each permanent exclusion. -/
theorem recovery_excludes_process (p : Params) (st : State p.n) (w : Wire p.n)
    (o : Run.Obj p) (h : Run.excludesS p st o = true) :
    Run.excludesS p (process p st w) o = true := by
  delta Run.excludesS at h ⊢
  cases hd : (Run.toWire p o).decode with
  | none => simp only [hd, Bool.false_eq_true] at h
  | some msg =>
    rw [hd] at h
    cases msg with
    | vote s i r => exact ex_grid_process p st w _ h
    | block s N =>
      dsimp only at h ⊢
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl
          (ex_block_mono st _ (recovery_process_frame p st w).2.1 N.erase h))
      · exact Bool.or_eq_true_iff.mpr (Or.inr
          (ex_invalid_mono p st _ (recovery_process_frame p st w).2.2
            (recovery_process_names_mono p st w) N h))
    | row i body => cases h
    | ack s i r => cases h
    | pc pc => cases h

/-- A forward clock step preserves each permanent exclusion. -/
theorem recovery_excludes_clock (p : Params) (st : State p.n) (t : Time)
    (ht : st.base.now ≤ t) (o : Run.Obj p) (h : Run.excludesS p st o = true) :
    Run.excludesS p (clock p st t) o = true := by
  obtain ⟨hnow, hvotes, hfg⟩ := recovery_clock_fields p st t
  delta Run.excludesS at h ⊢
  cases hd : (Run.toWire p o).decode with
  | none => simp only [hd, Bool.false_eq_true] at h
  | some msg =>
    rw [hd] at h
    cases msg with
    | vote s i r =>
      change GridCO.excludes p.toParams.engine (clock p st t).base ⟨.seat s i, .head r⟩ = true
      change GridCO.excludes p.toParams.engine st.base ⟨.seat s i, .head r⟩ = true at h
      rw [FGSA.Run.Internal.grid_excludes_head_iff] at h ⊢
      have hva : GridCO.votesAt (clock p st t).base s = GridCO.votesAt st.base s := by
        delta GridCO.votesAt
        rw [hvotes]
      rw [hvotes, hnow, hva]
      refine ⟨h.1, h.2.imp (fun hs => lt_of_lt_of_le hs ?_) id⟩
      exact FGSA.Run.Internal.slotOf_mono (p := p) ht
    | block s N =>
      dsimp only at h ⊢
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl (ex_block_mono st _
          (by rw [hfg]; exact KitFG.preceq_refl _) N.erase h))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (ex_invalid_mono p st _
          (by rw [hfg]) (by rw [recovery_clock_names]) N h))
    | row i body => cases h
    | ack s i r => cases h
    | pc pc => cases h

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

private def recoveryClockLaws : V2.D.Engine.ClockLaws (pcsaWith m p c) where
  now nd := nd.st.base.now
  init := rfl
  clock nd t := (recovery_clock_fields p nd.st t).1
  process nd o := (recovery_process_frame p nd.st (toWire p o)).1
  recordOwn_now _ _ := rfl

/-- A no-restart run preserves exclusions between strict time readers. -/
theorem recovery_excludes_time_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (x : V) (o : Obj p) (t t' : Time) (ht : t ≤ t')
    (h : (pcsaWith m p c).excludes (V2.D.Run.stateBeforeTime E rho t x) o = true) :
    (pcsaWith m p c).excludes (V2.D.Run.stateBeforeTime E rho t' x) o = true := by
  have hij : V2.D.Run.idxBefore rho t ≤ V2.D.Run.idxBefore rho t' := by
    change (rho.events.filter (fun e => decide (e.time < t))).length ≤
      (rho.events.filter (fun e => decide (e.time < t'))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true he) ht)
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho t hs] at h
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho t' hs]
  apply V2.D.Engine.stateBefore_stable_clock (recoveryClockLaws (p := p) (c := c) (m := m))
    (fun _ => le_refl 0) E rho hs
    (fun nd => (pcsaWith m p c).excludes nd o = true)
    (fun nd u hu ho => recovery_excludes_clock p nd.st u hu o ho)
    (fun nd w ho => recovery_excludes_process p nd.st (toWire p w) o ho)
    (fun _ _ ho => ho) hij x (hnr.restartFree x _ _) h

variable [Fintype V]

/-- F1 follows from RECOVERY without an exclusion-transport input. -/
theorem recovery_delivery_from_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (s : Slot) (hs : 0 < s)
    (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon) :
    Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
      (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ)
      (SA.gateTime p.toParams s) := by
  apply recovery_delivery E rho h s hs ha hh
  intro y _ o _ t hn
  apply Bool.eq_false_iff.mpr
  intro he
  have hb : max t E.t_GST + E.Δ ≤
      max t (SA.freezeTime p.toParams (s - 1)) + E.Δ :=
    Int.add_le_add_right (max_le_max_left t (recovery_freeze_after_gst E s hs ha)) E.Δ
  have hf := recovery_excludes_time_mono E rho h.base.valid.toScheduleWellFormed
    h.base.noRestart y o _ _ hb he
  rw [hn] at hf
  cases hf

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA

/-- An immutable valid parent prevents proposal exclusion in the genesis frame. -/
theorem recovery_path_not_excluded (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (hf : st.fg.F = .genesis) (hp : eraseFG P = N.erase.parent)
    (hv : rowsValidForParent p P N.slot N.rows = true) :
    Run.excludesS p st (Run.ofWire p ⟨.proposer s, .proposal N⟩) = false := by
  have hb : blockExcluded st N.erase = false := by
    change (!Block.compatible N.erase (eraseFG st.fg.F)) = false
    rw [hf]
    change (!Block.compatible N.erase .genesis) = false
    have hg : Block.compatible N.erase .genesis = true :=
      Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq _))
    rw [hg]
    rfl
  change (blockExcluded st N.erase || Run.invalidForParent p st N) = false
  rw [hb, Bool.false_or]
  rw [Run.recoveryInvalid_eq]
  delta Run.recoveryInvalid
  split
  · rfl
  · cases hq : parentFG st N.erase with
    | none => rfl
    | some Q =>
      have he := (ex_parent_spec st N.erase Q).mp hq
      have heq := he.2.trans hp.symm
      rw [pcsa_eraseFG_eq, pcsa_eraseFG_eq] at heq
      obtain rfl := FGSA.eraseFG_injective heq
      dsimp only
      rw [hv]
      rfl

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- F5's network step for an accepted path object with its immutable R6 witness. -/
theorem recovery_accepted_path_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hframe : StageOneFrame p c E rho)
    (s : Slot) (hs : 0 < s) (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon)
    (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (i : Nat) (u : Time) (r : Slot) (N : NamedProposal p.n)
    (P : SimplexFG.FGBlock (Fin p.n))
    (hp : eraseFG P = N.erase.parent) (hv : rowsValidForParent p P N.slot N.rows = true)
    (hu : u ≤ SA.proposalTime p.toParams s)
    (hc : V2.D.Run.acceptsAt E rho i x (ofWire p ⟨.proposer r, .proposal N⟩) u) :
    (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (i + 1) y)
        (ofWire p ⟨.proposer r, .proposal N⟩) = true ∨
      ∃ u', u ≤ u' ∧ u' < SA.voteTime p.toParams s ∧
        ∃ j, V2.D.Run.handlesAt E rho j y (ofWire p ⟨.proposer r, .proposal N⟩) u' := by
  try delta Slot Time at *
  let dl := fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
  have hz : SA.freezeTime p.toParams (s - 1) ≤ SA.proposalTime p.toParams s := by
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int)
    rw [hcast]
    linarith
  have hdl : dl u ≤ SA.voteTime p.toParams s := by
    have hm := max_le hu hz
    change max u (SA.freezeTime p.toParams (s - 1)) + E.Δ ≤ _
    rw [h.base.delta]
    exact Int.add_le_add_right hm p.Δ
  have hvg : SA.voteTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hF : (V2.D.Run.stateBeforeTime E rho (dl u) y).st.fg.F = .genesis := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl u) h.base.valid.toScheduleWellFormed]
    exact (hframe y hy _).1
  by_cases hn : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (i + 1) y)
      (ofWire p ⟨.proposer r, .proposal N⟩) = true
  · exact Or.inl hn
  · right
    obtain ⟨u', hlu, hdu, j, hj⟩ := (recovery_delivery_from_run E rho h s hs ha hh).relay
      x hx i (ofWire p ⟨.proposer r, .proposal N⟩) (by trivial) u hc y hy
      (Bool.eq_false_iff.mpr hn) (hdl.trans hvg)
      (recovery_path_not_excluded p _ r N P hF hp hv)
    exact ⟨u', hlu, hdu.trans_le hdl, j, hj⟩

end AvailableChain.PCSA.Run
end
