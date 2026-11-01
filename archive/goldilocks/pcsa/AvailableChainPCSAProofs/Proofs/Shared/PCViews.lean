module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Foundations.Snapshot
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.Rank
public import AvailableChainPCSAProofs.Proofs.Shared.Relay

public section

/-! PC views and PC retention (pcsa34-r4.3b §3.3, §5.3), shared by the lanes.
A carried PC installed by a call is accepted as a whole object. Stage 1 keeps
installed PCs. A carried maximum rank fixes a view target; root collision
freedom is needed only for PCs with the same rank. Copied from the Formation
lane (Clean/FormationRelay.lean, 6a5fc76) under lane-neutral names; each lane
keeps its own delivery-premise wrapper. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA
variable {n : Nat}
private abbrev pcViewKey (C : PC n) : Nat ×ₗ (Nat ×ₗ BlockId) :=
  toLex (C.slot, toLex (C.target.depth, C.target.root))

private theorem pcview_pcBelow_key (A B : PC n) :
    pcBelow A B = true ↔ pcViewKey A < pcViewKey B := by
  delta pcBelow
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Prod.Lex.toLex_lt_toLex]

private theorem pcview_prefer_key (old : Option (PC n)) (A C : PC n)
    (h : preferPC old A = some C) :
    pcViewKey A ≤ pcViewKey C ∧
      ∀ B, old = some B → pcViewKey B ≤ pcViewKey C := by
  cases old with
  | none =>
    change some A = some C at h
    cases h
    exact ⟨le_refl _, by intro B hB; cases hB⟩
  | some B =>
    change (if pcBelow B A then some A else some B) = some C at h
    split at h
    · rename_i hlt
      cases h
      refine ⟨le_refl _, ?_⟩
      intro D hD
      cases hD
      exact le_of_lt ((pcview_pcBelow_key B A).mp hlt)
    · rename_i hlt
      have he : B = C := Option.some.inj h
      subst C
      exact ⟨le_of_not_gt (fun hBA => hlt ((pcview_pcBelow_key B A).mpr hBA)),
        by intro D hD; cases hD; exact le_refl _⟩

private theorem pcview_fold_key (cs : List (PC n)) (old : Option (PC n))
    (C : PC n) (h : cs.foldl preferPC old = some C) :
    (∀ A ∈ cs, pcViewKey A ≤ pcViewKey C) ∧
      ∀ B, old = some B → pcViewKey B ≤ pcViewKey C := by
  induction cs generalizing old with
  | nil =>
    constructor
    · intro A hA
      exact (List.not_mem_nil hA).elim
    · intro B hB
      have he := Option.some.inj (hB.symm.trans h)
      subst C
      exact le_refl _
  | cons A cs ih =>
    have htail := ih (preferPC old A) h
    obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (pcsa_preferPC_isSome old A)
    have hstep := pcview_prefer_key old A D hD
    have hDC := htail.2 D hD
    refine ⟨?_, fun B hB => (hstep.2 B hB).trans hDC⟩
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hstep.1.trans hDC
    · exact htail.1 B hB

theorem pcsa_bestPC_rank_max (cs : List (PC n)) (A C : PC n)
    (hA : A ∈ cs) (hC : bestPC cs = some C) : pcBelow C A = false := by
  apply Bool.eq_false_iff.mpr
  intro hlt
  exact not_lt_of_ge ((pcview_fold_key cs none C hC).1 A hA)
    ((pcview_pcBelow_key C A).mp hlt)

end AvailableChain.PCSA

namespace AvailableChain.PCSA
variable {n : Nat}
private theorem pcview_fold_some (cs : List (PC n)) (old : Option (PC n))
    (h : old.isSome = true) : (cs.foldl preferPC old).isSome = true := by
  induction cs generalizing old with
  | nil => exact h
  | cons A cs ih => exact ih _ (pcsa_preferPC_isSome old A)

/-- An empty best-PC choice has no candidate. -/
theorem pcsa_bestPC_none (cs : List (PC n)) (h : bestPC cs = none) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons A cs =>
    have hs := pcview_fold_some cs (preferPC none A) (pcsa_preferPC_isSome none A)
    change (cs.foldl preferPC (preferPC none A)).isSome = true at hs
    change cs.foldl preferPC (preferPC none A) = none at h
    rw [h] at hs
    cases hs

/-- A carried rank bound fixes the selected target, including frozen PCs.
Root collision freedom is needed only for PCs with the same rank. -/
theorem pcsa_view_target_of_rank (cs : List (PC n)) (D : PC n)
    (hD : D ∈ cs) (hBound : ∀ C ∈ cs, pcBelow D C = false)
    (hRoots : ∀ C ∈ cs, ∀ A ∈ cs, C.target.root = A.target.root → C.target = A.target) :
    (bestPC cs).map PC.target = some D.target := by
  cases he : bestPC cs with
  | none =>
    rw [pcsa_bestPC_none cs he] at hD
    exact (List.not_mem_nil hD).elim
  | some C =>
    have hC := bestPC_mem cs C he
    have hCD : pcViewKey C ≤ pcViewKey D :=
      le_of_not_gt (fun hlt => by
        have hb := hBound C hC
        rw [← pcview_pcBelow_key D C, hb] at hlt
        cases hlt)
    have hDC := (pcview_fold_key cs none C he).1 D hD
    have hkey := le_antisymm hCD hDC
    have hroot : C.target.root = D.target.root :=
      congrArg (fun k : Nat ×ₗ (Nat ×ₗ BlockId) => (ofLex (ofLex k).2).2) hkey
    exact congrArg some (hRoots C hC D hD hroot)
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
open AvailableChain
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A delivery that installs a carried PC accepts the whole PC object. -/
theorem pcsa_installed_pc_accepted (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (j : Nat) (y : V) (o : Obj p) (t : Time)
    (C : PC p.n) (hj : rho.events[j]? = some (.deliver y o t))
    (hCarry : carriesS p o (⟨.none, .pc C⟩ : Obj p))
    (hNeed : processedS p (V2.D.Run.stateBefore E rho j y).st ⟨.none, .pc C⟩ = false)
    (hInstall : C ∈ (PCSA.process p (V2.D.Run.stateBefore E rho j y).st (toWire p o)).pcs) :
    V2.D.Run.acceptsAt E rho j y (⟨.none, .pc C⟩ : Obj p) t := by
  have hNot : C ∉ (V2.D.Run.stateBefore E rho j y).st.pcs := by
    intro hC
    have hDone : processedS p (V2.D.Run.stateBefore E rho j y).st ⟨.none, .pc C⟩ = true := by
      change ((V2.D.Run.stateBefore E rho j y).st.pcs.any
        (fun D => D.slot == C.slot && D.target == C.target)) = true
      exact List.any_eq_true.mpr ⟨C, hC, by simp only [BEq.rfl, Bool.and_self]⟩
    rw [hNeed] at hDone
    cases hDone
  refine ⟨⟨o, hj, ?_⟩, hNeed, ?_⟩
  · change handlesS p (V2.D.Run.stateBefore E rho j y).st o _
    right
    right
    exact ⟨hCarry, C, rfl, hInstall, hNot⟩
  · rw [V2.D.Run.stateBefore_succ E rho hj]
    delta V2.D.World.step
    dsimp only
    rw [Function.update_self]
    change ((PCSA.process p (V2.D.Run.stateBefore E rho j y).st (toWire p o)).pcs.any
      (fun D => D.slot == C.slot && D.target == C.target)) = true
    exact List.any_eq_true.mpr ⟨C, hInstall, by simp only [BEq.rfl, Bool.and_self]⟩
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA
variable {n : Nat}
private theorem pcview_normalize_pcs (st : State n) : (normalizeS st).pcs = st.pcs := by
  delta normalizeS
  split <;> rfl

private theorem pcview_reconcile_pcs (st : State n) (hF : st.fg.F = .genesis) :
    (reconcile st).pcs = st.pcs := by
  delta reconcile
  rw [pcview_normalize_pcs]
  apply List.filter_eq_self.mpr
  intro C _
  change Block.compatible C.target (eraseFG st.fg.F) = true
  rw [hF]
  exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq C.target))

private theorem pcview_normalize_fg (st : State n) : (normalizeS st).fg = st.fg := by
  delta normalizeS
  split <;> rfl

private theorem pcview_reconcile_fg (st : State n) : (reconcile st).fg = st.fg := by
  delta reconcile
  rw [pcview_normalize_fg]

private theorem pcview_rows_fg (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).fg = st.fg := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    delta admitRow
    cases hdecode : a.decode? <;> dsimp only
    split <;> rfl

private theorem pcview_raw_acks_fg (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).fg = st.fg := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.2]

private theorem pcview_row_pcs (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).pcs = st.pcs := by
  delta admitRow
  cases h : a.decode? <;> dsimp only
  split <;> rfl

private theorem pcview_rows_pcs (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).pcs = st.pcs := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, pcview_row_pcs]

private theorem pcview_raw_acks_pcs (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).pcs = st.pcs := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).1]

private abbrev pcViewAccepted (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) : State p.n :=
  let st1 : State p.n := { st with
    base := GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
  let st1 := match N.pc with
    | none => st1
    | some C => if pcValid st1 C &&
        !st1.pcs.any (fun old => old.slot == C.slot && old.target == C.target)
      then deleteConflictingLeases st1 C else st1
  let st1 := { st1 with
    fg := FGSA.Window.on_block p p.K_W st1.fg (fgBlock P N.erase N.rows)
    proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
  let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
  N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw st2))

/-- A delivery keeps every installed PC when its finality remains genesis. -/
theorem pcsa_process_pcs_mono (p : Params) (st : State p.n) (o : Wire p.n)
    (hF : (process p st o).fg.F = .genesis) : st.pcs ⊆ (process p st o).pcs := by
  delta process at hF ⊢
  cases hd : o.decode with
  | none => exact List.Subset.refl _
  | some d =>
    rw [hd] at hF
    cases d with
    | vote s i root => exact List.Subset.refl _
    | row i body => rw [pcview_row_pcs]
    | ack s i root =>
      change st.pcs ⊆ (collectPCs (poolAck p st ⟨o.auth, root⟩)).pcs
      apply List.Subset.trans (show st.pcs ⊆ (poolAck p st ⟨o.auth, root⟩).pcs from ?_)
        (collectPCs_pcs_mono _)
      delta poolAck
      cases h : AckWire.decode? (⟨o.auth, root⟩ : AckWire p.n) <;> dsimp only
      · exact List.Subset.refl _
      · rename_i val
        rcases val with ⟨s, i, root⟩
        split_ifs <;> exact List.Subset.refl _
    | pc C =>
      change st.pcs ⊆ (admitPC st C).pcs
      delta admitPC
      split
      · have hm := collectPCs_pcs_mono (C.acks.foldl poolAckRaw st)
        rw [pcview_raw_acks_pcs] at hm
        exact hm
      · exact List.Subset.refl _
    | block s N =>
      change st.pcs ⊆ (admitBlock p st s N).pcs
      change (admitBlock p st s N).fg.F = .genesis at hF
      delta admitBlock at hF ⊢
      split
      · exact List.Subset.refl _
      · rename_i hnamed
        rw [ite_eq_right hnamed] at hF
        cases hp : parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          rw [hp] at hF
          change (if blockAccepted p st s N P then pcViewAccepted p st s N P else st).fg.F =
            .genesis at hF
          change st.pcs ⊆
            (if blockAccepted p st s N P then pcViewAccepted p st s N P else st).pcs
          split
          · rename_i hacc
            rw [ite_eq_left hacc] at hF
            delta pcViewAccepted at hF ⊢
            rw [pcview_rows_fg, (collectPCs_frame _).2.2.2.2,
              pcview_raw_acks_fg] at hF
            rw [pcview_rows_pcs]
            apply List.Subset.trans (show st.pcs ⊆
              (N.pcAcks.foldl poolAckRaw _).pcs from ?_) (collectPCs_pcs_mono _)
            rw [pcview_raw_acks_pcs]
            cases hpc : N.pc <;> rw [hpc] at hF <;> dsimp only at hF ⊢ <;> split_ifs at hF ⊢
            all_goals first
              | exact List.Subset.refl _
              | (rw [pcview_reconcile_pcs _] <;> first
                  | exact List.Subset.refl _
                  | simpa only [pcview_reconcile_fg, deleteConflictingLeases_def] using hF)
          · exact List.Subset.refl _

/-- A tick keeps the complete installed PC list. -/
theorem pcsa_clock_pcs (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).pcs = st.pcs := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def, pcview_normalize_pcs]
    split
    · exact clockPre_pcs p st t
    · rw [(gateFrom_pc_frame p _ _ _ _ _).1, clockPre_pcs]
  · exact clockPre_pcs p st t
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Without a restart, stage 1 keeps every installed PC at an honest node. -/
theorem pcsa_run_pcs_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hFrame : StageOneFrame p c E rho)
    (hNR : V2.D.NoRestart rho) (y : V) (hy : y ∈ rho.honest)
    (i j : Nat) (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i y).st.pcs ⊆ (V2.D.Run.stateBefore E rho j y).st.pcs := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i y).st.pcs ⊆ nd.st.pcs)
    hij y ?_ (List.Subset.refl _)
  intro k e _ _ he hn hm
  cases e with
  | restart x t => exact (hNR k x t he).elim
  | tick x t =>
    change x = y at hn
    subst x
    change (V2.D.Run.stateBefore E rho i y).st.pcs ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.pcs
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht, pcsa_clock_pcs]
    exact hm
  | deliver x o t =>
    change x = y at hn
    subst x
    have hOut : (PCSA.process p (V2.D.Run.stateBefore E rho k y).st (toWire p o)).fg.F =
        .genesis := by
      have hf := (hFrame y hy (k + 1)).1
      rw [V2.D.Run.stateBefore_succ E rho he] at hf
      delta V2.D.World.step at hf
      dsimp only at hf
      rw [Function.update_self] at hf
      exact hf
    change (V2.D.Run.stateBefore E rho i y).st.pcs ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.pcs
    rw [Function.update_self]
    exact List.Subset.trans hm (pcsa_process_pcs_mono p _ (toWire p o) hOut)
end AvailableChain.PCSA.Run

end
