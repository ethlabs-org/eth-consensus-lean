module
public import AvailableChainPCSAProofs.Proofs.Shared.StageRun
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun
public import AvailableChainPCSAProofs.Proofs.Foundations.StampRun
public import AvailableChainPCSAProofs.Proofs.Shared.CollectClosed
public import AvailableChainPCSAProofs.Proofs.Shared.PCViews

public section

/-! A held PC keeps its first-acceptance stamp (pcsa34-r4.3 §3.6, §3.7 (i)).
Installation rewrites a stamp key only when no held PC has that slot and target;
with one block per stored root, a held PC owns its key. -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- A gate step keeps the PC stamps. -/
theorem pcsa_gateFrom_pcStamps (p : Params) (a : Block) (cs : List (PC n))
    (ρ : Option PCRank) (st : State n) (s : Slot) :
    (gateFrom p a cs ρ st s).pcStamps = st.pcStamps := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s
  · rfl
  · dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => acc.pcStamps = st.pcStamps)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc' : State n => acc'.pcStamps = st.pcStamps)
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- A clock keeps the PC stamps. -/
theorem pcsa_clock_pcStamps (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).pcStamps = st.pcStamps := by
  unfold clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    have hn : ∀ st : State p.n, (normalizeS st).pcStamps = st.pcStamps := by
      intro st
      delta normalizeS
      split <;> rfl
    rw [hn]
    split
    · exact clockPre_pcStamps p st t
    · rw [pcsa_gateFrom_pcStamps, clockPre_pcStamps]
  · exact clockPre_pcStamps p st t

private theorem find_filter_append {α : Type} (q r : α → Bool) (l : List α) (y : α)
    (hqr : ∀ z, q z = true → r z = true) (hy : q y = false) :
    (l.filter r ++ [y]).find? q = l.find? q := by
  induction l with
  | nil => simp [hy]
  | cons z l ih =>
    by_cases hz : q z = true
    · simp [hqr z hz, hz]
    · have hz' : q z = false := by simpa using hz
      by_cases hr : r z = true
      · simp [hr, hz', ih]
      · have hr' : r z = false := by simpa using hr
        simp [hr', hz', ih]

/-- The facts a held PC keeps through a step: held, same stamp, and the blocks of
the step's end. -/
private def StampKeep (C : PC n) (τ : Time) (B₀ : List Block) (st : State n) : Prop :=
  C ∈ st.pcs ∧ pcStamp? st C = some τ ∧ st.base.blocks = B₀

private theorem keep_install (C : PC n) (τ : Time) (B₀ : List Block)
    (hU : ∀ b ∈ B₀, b.root = C.target.root → b = C.target)
    (st : State n) (d : PC n) (h : StampKeep C τ B₀ st) (hv : pcValid st d = true) :
    StampKeep C τ B₀ (installPC st d) := by
  obtain ⟨hC, hτ, hB⟩ := h
  refine ⟨installPC_pcs_mono st d hC, ?_, (installPC_frame st d).2.1.trans hB⟩
  rw [installPC_def]
  split
  · exact hτ
  · rename_i hn
    have hne : ¬(d.slot = C.slot ∧ d.target.root = C.target.root) := by
      rintro ⟨hs, hr⟩
      have hd : d.target ∈ st.base.blocks := by
        delta pcValid at hv
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2
      have ht := hU d.target (hB ▸ hd) hr
      apply hn
      apply List.any_eq_true.mpr
      refine ⟨C, hC, ?_⟩
      rw [hs, ht]
      simp
    rw [deleteConflictingLeases_def]
    simp only [pcStamp?_def] at hτ ⊢
    rw [find_filter_append]
    · exact hτ
    · intro z hz
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hz
      rw [beq_iff_eq.mp h1, beq_iff_eq.mp h2]
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      exact not_and_or.mp fun h => hne ⟨h.1.symm, h.2.symm⟩
    · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      exact not_and_or.mp hne

private theorem keep_collect (C : PC n) (τ : Time) (B₀ : List Block)
    (hU : ∀ b ∈ B₀, b.root = C.target.root → b = C.target)
    (st : State n) (h : StampKeep C τ B₀ st) : StampKeep C τ B₀ (collectPCs st) :=
  collectPCs_invariant (StampKeep C τ B₀) (keep_install C τ B₀ hU) st h

private theorem keep_raws (C : PC n) (τ : Time) (B₀ : List Block) (st : State n)
    (acks : List (AckWire n)) (h : StampKeep C τ B₀ st) :
    StampKeep C τ B₀ (acks.foldl poolAckRaw st) := by
  obtain ⟨h1, -, -, -, h5, -⟩ := pcsa_fold_poolAckRaw_frame st acks
  have hs : (acks.foldl poolAckRaw st).pcStamps = st.pcStamps := by
    apply List.foldlRecOn (motive := fun acc : State n => acc.pcStamps = st.pcStamps)
    · rfl
    · intro acc ha a _
      exact (poolAckRaw_frame acc a).2.1.trans ha
  refine ⟨h1 ▸ h.1, ?_, by rw [h5]; exact h.2.2⟩
  simp only [pcStamp?_def, hs] at h ⊢
  exact h.2.1

private theorem keep_row (p : Params) (C : PC p.n) (τ : Time) (B₀ : List Block)
    (st : State p.n) (a : RowWire p.n) (h : StampKeep C τ B₀ st) :
    StampKeep C τ B₀ (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem keep_rows (p : Params) (C : PC p.n) (τ : Time) (B₀ : List Block)
    (st : State p.n) (rows : List (RowWire p.n)) (h : StampKeep C τ B₀ st) :
    StampKeep C τ B₀ (rows.foldl (admitRow p) st) := by
  apply List.foldlRecOn (motive := StampKeep C τ B₀)
  · exact h
  · intro acc ha a _
    exact keep_row p C τ B₀ acc a ha

private theorem keep_poolAck (p : Params) (C : PC p.n) (τ : Time) (B₀ : List Block)
    (st : State p.n) (a : AckWire p.n) (h : StampKeep C τ B₀ st) :
    StampKeep C τ B₀ (poolAck p st a) := by
  delta poolAck
  cases a.decode? with
  | none => exact h
  | some v =>
    rcases v with ⟨_, _, _⟩
    dsimp only
    split
    · exact h
    · split <;> exact h

private theorem keep_frame (C : PC n) (τ : Time) (B₀ : List Block) (st st' : State n)
    (h : StampKeep C τ B₀ st) (hp : st'.pcs = st.pcs) (hs : st'.pcStamps = st.pcStamps)
    (hb : st'.base.blocks = st.base.blocks) : StampKeep C τ B₀ st' := by
  refine ⟨hp ▸ h.1, ?_, hb.trans h.2.2⟩
  simp only [pcStamp?_def, hs]
  exact h.2.1

/-- A delivery keeps a held PC and its stamp when F does not change and the
end blocks have one block on its root. -/
theorem pcsa_process_stamp_keep (p : Params) (st : State p.n) (o : Wire p.n) (C : PC p.n)
    (τ : Time) (hC : C ∈ st.pcs) (hτ : pcStamp? st C = some τ)
    (hF : (process p st o).fg.F = st.fg.F)
    (hU : ∀ b ∈ (process p st o).base.blocks, b.root = C.target.root → b = C.target) :
    C ∈ (process p st o).pcs ∧ pcStamp? (process p st o) C = some τ := by
  suffices hk : ∀ B₀, (process p st o).base.blocks = B₀ →
      (∀ b ∈ B₀, b.root = C.target.root → b = C.target) → StampKeep C τ B₀ (process p st o) by
    obtain ⟨h1, h2, -⟩ := hk _ rfl hU
    exact ⟨h1, h2⟩
  intro B₀ hB hU
  revert hB hF
  delta process
  cases o.decode with
  | none => intro _ hB; exact ⟨hC, hτ, hB⟩
  | some msg => cases msg with
    | vote s i r => intro _ hB; exact ⟨hC, hτ, hB⟩
    | row i body =>
      intro _ hB
      obtain ⟨-, -, -, -, -, h6⟩ := pcsa_admitRow_frame p st ⟨o.auth, body⟩
      exact keep_row p C τ B₀ st _ ⟨hC, hτ, by rw [← hB, h6]⟩
    | ack s i r =>
      intro _ hB
      dsimp only at hB ⊢
      delta admitAck at hB ⊢
      have h0 := keep_poolAck p C τ st.base.blocks st ⟨o.auth, r⟩ ⟨hC, hτ, rfl⟩
      have hst : st.base.blocks = B₀ := by
        rw [← hB, (collectPCs_frame _).2.1, h0.2.2]
      exact keep_collect C τ B₀ hU _ (hst ▸ h0)
    | pc d =>
      intro _ hB
      dsimp only at hB ⊢
      delta admitPC at hB ⊢
      by_cases hw : d.wellFormed = true
      · simp only [hw, ↓reduceIte] at hB ⊢
        have h0 := keep_raws C τ st.base.blocks st d.acks ⟨hC, hτ, rfl⟩
        have hst : st.base.blocks = B₀ := by
          rw [← hB, (collectPCs_frame _).2.1, h0.2.2]
        exact keep_collect C τ B₀ hU _ (hst ▸ h0)
      · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hB ⊢
        exact ⟨hC, hτ, hB⟩
    | block s N =>
      intro hF hB
      dsimp only at hB hF ⊢
      delta admitBlock at hB hF ⊢
      by_cases hh : (!namedParentHeld st N) = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hh)] at hB ⊢
        exact ⟨hC, hτ, hB⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hh)] at hB hF ⊢
      cases hp : parentFG st N.erase with
      | none => rw [hp] at hB; dsimp only at hB; exact ⟨hC, hτ, hB⟩
      | some P =>
        rw [hp] at hB hF
        dsimp only at hB hF ⊢
        by_cases ha : blockAccepted p st s N P = true
        · rw [ite_eq_left_of_eq_true _ _ (eq_true ha)] at hB hF ⊢
          let st1 : State p.n := { st with
            base := GridCO.admitProposal p.toParams.engine st.base
              (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
          let st2 := match N.pc with
            | none => st1
            | some D => if pcValid st1 D && !st1.pcs.any
                (fun o => o.slot == D.slot && o.target == D.target)
              then deleteConflictingLeases st1 D else st1
          let st3 : State p.n := { st2 with
            fg := FGSA.Window.on_block p p.K_W st2.fg (fgBlock P N.erase N.rows)
            proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
          let st4 := if st3.fg.F = st.fg.F then st3 else reconcile st3
          change (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
            st4))).base.blocks = B₀ at hB
          change (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
            st4))).fg.F = st.fg.F at hF
          change StampKeep C τ B₀ (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
            st4)))
          have h4 : st4 = st3 := by
            have hfg : (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
                st4))).fg = st4.fg := by
              rw [(pcsa_fold_admitRow_frame p _ _).2.2.2.2.1, (collectPCs_frame _).2.2.2.2,
                (pcsa_fold_poolAckRaw_frame _ _).2.2.2.1]
            have hr : (reconcile st3).fg = st3.fg := by
              delta reconcile normalizeS
              dsimp only
              split <;> rfl
            rw [hfg] at hF
            dsimp only [st4] at hF ⊢
            split
            · rfl
            · rename_i hn
              simp only [hn, ↓reduceIte, hr] at hF
          have h3 : StampKeep C τ st3.base.blocks st3 := by
            have h2 : st2.pcs = st.pcs ∧ st2.pcStamps = st.pcStamps := by
              dsimp only [st2]
              cases N.pc with
              | none => exact ⟨rfl, rfl⟩
              | some D => dsimp only; split <;> exact ⟨rfl, rfl⟩
            refine ⟨h2.1 ▸ hC, ?_, rfl⟩
            change pcStamp? st2 C = some τ
            simp only [pcStamp?_def, h2.2]
            exact hτ
          rw [h4] at hB ⊢
          have h0 := keep_raws C τ _ st3 N.pcAcks h3
          have hst : st3.base.blocks = B₀ := by
            rw [← hB, (pcsa_fold_admitRow_frame p _ _).2.2.2.2.2, (collectPCs_frame _).2.1, h0.2.2]
          exact keep_rows p C τ B₀ _ N.rows (keep_collect C τ B₀ hU _ (hst ▸ h0))
        · rw [ite_eq_right_of_eq_false _ _ (eq_false ha)] at hB ⊢
          exact ⟨hC, hτ, hB⟩

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every stamp is below `t` if every earlier own tick is before `t`. -/
theorem pcsa_stampBound_of_ticks (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (i : Nat) (v : V) (t : Time) (ht : 0 < t)
    (hlt : ∀ k < i, ∀ u, rho.events[k]? = some (.tick v u) → u < t) :
    StampBound t (V2.D.Run.stateBefore E rho i v).st := by
  have hz : StampBound t (initial p.n) := by
    rw [StampBound_def]
    dsimp only [initial]
    exact ⟨ht, by simp, by simp⟩
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => StampBound t nd.st) (Nat.zero_le i) v ?_ hz
  intro k e _ hki he hn h
  cases e with
  | restart u a =>
    change u = v at hn
    subst u
    change StampBound t (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact hz
  | tick u a =>
    change u = v at hn
    subst u
    change StampBound t (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    rw [pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k v) v a]
    exact clock_stampBound p t a _ (hlt k hki a he) h
  | deliver u o a =>
    change u = v at hn
    subst u
    change StampBound t (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact process_stampBound p t _ (toWire p o) h

/-- In stage one an honest node keeps a held PC and its first-acceptance stamp. -/
theorem pcsa_run_stamp_keep (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hf : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (i k : Nat) (hik : i ≤ k) (C : PC p.n) (τ : Time)
    (hC : C ∈ (V2.D.Run.stateBefore E rho i x).st.pcs)
    (hτ : pcStamp? (V2.D.Run.stateBefore E rho i x).st C = some τ) :
    pcStamp? (V2.D.Run.stateBefore E rho k x).st C = some τ := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => pcStamp? nd.st C = some τ) hik x ?_ hτ
  intro j e hij hjk he hn hj
  have hCj := pcsa_run_pcs_mono E rho hf h.noRestart x hx i j hij hC
  cases e with
  | restart u a => exact (h.noRestart j u a he).elim
  | tick u a =>
    change u = x at hn
    subst u
    change pcStamp? (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st C = some τ
    rw [Function.update_self, pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x a]
    simp only [pcStamp?_def, pcsa_clock_pcStamps] at hj ⊢
    exact hj
  | deliver u o a =>
    change u = x at hn
    subst u
    have hs := pcsa_deliver_succ E rho he
    rw [← V2.D.Run.stateBefore_succ E rho he, hs]
    have hF : (process p (V2.D.Run.stateBefore E rho j x).st (toWire p o)).fg.F =
        (V2.D.Run.stateBefore E rho j x).st.fg.F := by
      rw [← hs, (hf x hx (j + 1)).1, (hf x hx j).1]
    have hC' : C ∈ (process p (V2.D.Run.stateBefore E rho j x).st (toWire p o)).pcs := by
      rw [← hs]
      exact pcsa_run_pcs_mono E rho hf h.noRestart x hx i (j + 1) (hij.trans (Nat.le_succ j)) hC
    have hU : ∀ b ∈ (process p (V2.D.Run.stateBefore E rho j x).st (toWire p o)).base.blocks,
        b.root = C.target.root → b = C.target := by
      rw [← hs]
      intro b hb hr
      have ho := pcsa_outageStore_stateBefore E rho (j + 1) x hx
      exact (RootsUnique_def _ ▸ pcsa_rootsUnique_stateBefore E rho h (j + 1) x hx) b hb
        C.target (ho.pcBlocks C (hs ▸ hC')) hr
    exact (pcsa_process_stamp_keep p _ (toWire p o) C τ hCj hj hF hU).2

end AvailableChain.PCSA.Run

end
