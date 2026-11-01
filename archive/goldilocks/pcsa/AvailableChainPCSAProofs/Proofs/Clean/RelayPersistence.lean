module
public import AvailableChainPCSAProofs.Proofs.Clean.RelayFrames

public section

/-! C6 RelayPersistence: concrete receipt and count support. -/
namespace AvailableChain.PCSA.CleanPCRelay
open AvailableChain.SimplexFG
variable {n : Nat}
/-- The admission tail keeps every held and frozen PC when its final `F` is genesis. -/
theorem pcsa_admitBlock_tail_genesis (p : Params) (st st1 : State p.n) (C : Prop) [Decidable C]
    (rows : List (RowWire p.n)) (acks : List (AckWire p.n))
    (hpcs : st1.pcs = st.pcs) (hsnap : st1.pcSnapshot = st.pcSnapshot)
    (hF : (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1)))).fg.F = .genesis) :
    st.pcs ⊆ (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1)))).pcs ∧
    (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1)))).pcSnapshot = st.pcSnapshot := by
  obtain ⟨r1, r2, -, -, r5, -⟩ := pcsa_fold_admitRow_frame p (collectPCs (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1))) rows
  obtain ⟨-, -, -, c4, c5⟩ := collectPCs_frame (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1))
  obtain ⟨a1, a2, -, a4, -⟩ := pcsa_fold_poolAckRaw_frame (if C then st1 else reconcile st1) acks
  rw [r5, c5, a4] at hF
  rw [r1, r2, c4, a2, ← hpcs, ← hsnap]
  have hm := collectPCs_pcs_mono (acks.foldl poolAckRaw (if C then st1 else reconcile st1))
  rw [a1] at hm
  by_cases hc : C
  · rw [ite_eq_left hc] at hm ⊢
    exact ⟨hm, rfl⟩
  · rw [ite_eq_right hc] at hm hF ⊢
    rw [(pcsa_reconcile_frame st1).2.2.2.2.1] at hF
    obtain ⟨g1, g2⟩ := pcsa_reconcile_genesis st1 hF
    rw [g1] at hm
    exact ⟨hm, g2⟩

/-- In a stage-1 step (`F` genesis after the delivery), a delivery keeps every
held PC and the frozen PC rows. -/
theorem pcsa_process_stageOne (p : Params) (st : State p.n) (o : Wire p.n)
    (hF : (process p st o).fg.F = .genesis) :
    st.pcs ⊆ (process p st o).pcs ∧ (process p st o).pcSnapshot = st.pcSnapshot := by
  revert hF
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      intro _
      exact ⟨List.Subset.refl _, rfl⟩
    | row i body =>
      intro _
      dsimp only
      obtain ⟨h1, h2, -⟩ := pcsa_admitRow_frame p st ⟨o.auth, body⟩
      rw [h1, h2]
      exact ⟨List.Subset.refl _, rfl⟩
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · intro _; exact ⟨List.Subset.refl _, rfl⟩
      · cases hP : parentFG st N.erase with
        | none => intro _; exact ⟨List.Subset.refl _, rfl⟩
        | some P =>
          dsimp only
          split
          · intro hF
            refine pcsa_admitBlock_tail_genesis p st _ _ N.rows N.pcAcks ?_ ?_ hF
            · cases N.pc <;> dsimp only; split_ifs <;> rfl
            · cases N.pc <;> dsimp only; split_ifs <;> rfl
          · intro _; exact ⟨List.Subset.refl _, rfl⟩
    | ack s i r =>
      intro _
      dsimp only
      delta admitAck
      obtain ⟨h1, h2, -⟩ := pcsa_poolAck_frame p st ⟨o.auth, r⟩
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact collectPCs_pcs_mono _
      · rw [(collectPCs_frame _).2.2.2.1, h2]
    | pc d =>
      intro _
      dsimp only
      delta admitPC
      split
      · obtain ⟨h1, h2, -⟩ := pcsa_fold_poolAckRaw_frame st d.acks
        refine ⟨?_, ?_⟩
        · rw [← h1]; exact collectPCs_pcs_mono _
        · rw [(collectPCs_frame _).2.2.2.1, h2]
      · exact ⟨List.Subset.refl _, rfl⟩
  | none => intro _; exact ⟨List.Subset.refl _, rfl⟩


end AvailableChain.PCSA.CleanPCRelay

namespace AvailableChain.PCSA.Run
open AvailableChain.PCSA.CleanPCRelay
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Stage-one held PCs persist between arbitrary run indices. -/
theorem pcsa_clean_pc_indices_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hnr : V2.D.NoRestart rho)
    (hF : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (a b : Nat) (hab : a ≤ b) :
    (V2.D.Run.stateBefore E rho a x).st.pcs ⊆ (V2.D.Run.stateBefore E rho b x).st.pcs := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho a x).st.pcs ⊆ nd.st.pcs) hab x ?_
    (List.Subset.refl _)
  intro k e _ _ he hn ih
  cases e with
  | restart y t => exact (hnr k y t he).elim
  | tick y t =>
    change y = x at hn
    subst y
    change (V2.D.Run.stateBefore E rho a x).st.pcs ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcs
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    rw [ht, (pcsa_clock_frame p _ t).1]
    exact ih
  | deliver y o t =>
    change y = x at hn
    subst y
    have hf := (hF x hx (k + 1)).1
    rw [V2.D.Run.stateBefore_succ E rho he] at hf
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.fg.F = .genesis at hf
    rw [Function.update_self] at hf
    change (V2.D.Run.stateBefore E rho a x).st.pcs ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.pcs
    rw [Function.update_self]
    exact List.Subset.trans ih (pcsa_process_stageOne p _ (toWire p o) hf).1
end AvailableChain.PCSA.Run

end
