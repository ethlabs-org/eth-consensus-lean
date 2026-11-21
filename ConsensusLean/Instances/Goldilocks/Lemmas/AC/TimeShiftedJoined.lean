module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.TimeShiftedReceipt
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ReceiptCover

public section

namespace Consensus.Goldilocks.SA.TimeShifted

variable {sp : SAParams} {FGP : Type}

private theorem attempt_clock (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (tryVote sp self A Φ t).1.restartTime = A.restartTime ∧
      ((tryVote sp self A Φ t).2 ≠ [] → joined sp A t) := by
  unfold tryVote
  dsimp only
  split_ifs <;> simp_all [(optimistic_keeps ..).2, (admitVote_keeps ..).2]

open Classical in
private theorem step_clock (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (instanceAC sp FGP).Call) :
    let r := (instanceAC sp FGP).step y A Φ t c
    (if c = .restart then r.1.restartTime = (t : WithBot Time) else
      r.1.restartTime = A.restartTime) ∧ (r.2 ≠ [] → joined sp A t) := by
  classical
  cases c with
  | restart => simp [ACInterface.step, instanceAC, reset]
  | proposal => simp [ACInterface.step, instanceAC, acProposal]; split_ifs <;> rfl
  | toFG => simpa [ACInterface.step, instanceAC] using (acToFG_keeps A Φ t).2
  | message m =>
    simpa [ACInterface.step, instanceAC, joined, (optimistic_keeps ..).2, (admitVote_keeps ..).2]
      using attempt_clock y (optimisticConfirmation sp (admitVote sp A t m) Φ t) Φ t
  | block B =>
    simpa [ACInterface.step, instanceAC, joined, (optimistic_keeps ..).2] using
      attempt_clock y (optimisticConfirmation sp
        {A with blockStamp := Function.update A.blockStamp B.root (ETime.of t)} Φ t) Φ t
  | tick =>
    simp only [ACInterface.step, instanceAC, Id.run, pure, reduceCtorEq, ↓reduceIte]
    split_ifs <;> constructor
    all_goals first | rfl | exact (attempt_clock ..).1 | exact (updateConfirmation_keeps ..).2 |
      exact (updateConfirmation_keeps ..).2.trans (attempt_clock ..).1 |
      exact fun h => (h rfl).elim | exact fun _ => by assumption

variable {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : ACTrace (instanceAC sp FGP)}
  {ini : Fin sp.n → SAState sp.n} {y : Fin sp.n}

/-- The input state of every actual emission was joined. A denied attempt is not a cast. -/
theorem joined_of_cast (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (instanceAC sp FGP)} (hc : tr.CallAt y i ℓ) (cast : ℓ.emits ≠ []) :
    joined sp (tr.state y i) (tr.time i) := by
  have exec := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at exec
  exact (step_clock y _ ℓ.frame _ ℓ.call).2 (by simpa only [exec] using cast)

private theorem restart_le_clock (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    {k j : Nat} (wake : tr.RestartAt y k) (before : k < j) :
    (tr.time k : WithBot Time) ≤ (tr.state y j).restartTime := by
  induction j, before using Nat.le_induction with
  | base =>
    obtain ⟨l, hc, hw⟩ := wake
    have exec := hr.exec k l hc.2 (hc.1 ▸ hy)
    have clock := (step_clock (tr.node k) (tr.state (tr.node k) k) l.frame (tr.time k) l.call).1
    rw [exec, ite_eq_left hw] at clock
    simpa [Trace.state, hc.1, hc.2] using clock.ge
  | succ j hkj ih =>
    rw [Trace.state]
    split_ifs with h
    · obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 h.2
      have exec := hr.exec j l hl (h.1 ▸ hy)
      have clock := (step_clock (tr.node j) (tr.state (tr.node j) j) l.frame (tr.time j) l.call).1
      rw [exec] at clock
      by_cases hw : l.call = .restart
      · rw [ite_eq_left hw] at clock
        exact clock ▸ WithBot.coe_le_coe.mpr (hr.time_mono (by omega))
      · rw [ite_eq_right hw, h.1] at clock
        exact clock ▸ ih
    · exact ih

/-- At a cast there was no restart after the previous slot start. At equality in time the
sleep-of-restart law rules out a later reset following a receipt at that same boundary. -/
theorem receipt_covered_at_cast (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    {i j : Nat} {l r : ACLabel (instanceAC sp FGP)} {v : Vote sp.n} (hc : tr.CallAt y i l)
    (msg : l.call = .message v) (lo : (sp.slot (tr.time i) : Int) - 1 ≤ v.slot)
    (hi : v.slot ≤ sp.slot (tr.time i)) (hij : i < j) (rc : tr.CallAt y j r) (cast : r.emits ≠ [])
    (window : sp.ts ((sp.slot (tr.time j) : Int) - 1) ≤ tr.time i) :
    v ∈ (tr.state y j).pool v.slot ∨ v.val ∈ equivocators {w | w ∈ (tr.state y j).pool v.slot} := by
  apply receipt_cover_before_restart hr hy hc msg lo hi hij
  intro k hik hkj wake
  have clock := restart_le_clock hr hy wake hkj
  have bound := joined_of_cast hr hy rc cast
  have hk := WithBot.coe_le_coe.mp (clock.trans bound)
  obtain ⟨lbl, call, eq⟩ := wake
  obtain ⟨u, _, huk, _, gap⟩ := hr.sleep_of_restart y hy k lbl call eq
  exact (not_lt_of_ge ((hk.trans window).trans (gap i hik l hc).le)) huk

private theorem deadline_at_cut {j : Nat} {τ : Time}
    (bounded : ∀ k ≤ j, tr.RestartAt y k → tr.time k ≤ τ) :
    tr.deadline y j τ = τ + sp.Δ := by
  have wake : tr.lastWake y j ≤ (τ : WithBot Time) := by
    induction j with
    | zero =>
      unfold ACTrace.lastWake
      split_ifs with h
      · exact WithBot.coe_le_coe.mpr (bounded 0 le_rfl h)
      · exact bot_le
    | succ j ih =>
      unfold ACTrace.lastWake
      split_ifs with h
      · exact WithBot.coe_le_coe.mpr (bounded _ le_rfl h)
      · exact ih (fun k hk => bounded k (hk.trans (Nat.le_succ j)))
  unfold ACTrace.deadline
  cases h : tr.lastWake y j with
  | bot => rfl
  | coe w =>
    rw [h] at wake
    simp [Option.elim, max_eq_left (WithBot.coe_le_coe.mp wake)]

/-- A forwarded vote from the previous slot's start through its `+5Δ` window is covered in
the actual cast input once its delivery deadline has elapsed. No processing or uninterrupted
participation premise: processing comes from `SyncAC` and the cast bounds the restart clock. -/
theorem relay_at_cast (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) {a b : Time}
    (sync : SyncAC (instanceAC sp FGP) H U a b tr) {x : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {i j : Nat} {v : Vote sp.n} {r : ACLabel (instanceAC sp FGP)} (sent : tr.SendOrAdmit x i v)
    (lo : a ≤ tr.time i) (hi : tr.time i ≤ b) (rc : tr.CallAt y j r) (cast : r.emits ≠ [])
    (slot : (v.slot : Int) = (sp.slot (tr.time j) : Int) - 1) (start : sp.ts v.slot ≤ tr.time i)
    (last : tr.time i ≤ sp.ts v.slot + 5 * sp.Δ) (due : tr.time i + sp.Δ ≤ tr.time j) :
    v ∈ (tr.state y j).pool v.slot ∨ v.val ∈ equivocators {w | w ∈ (tr.state y j).pool v.slot} := by
  have bound (k : Nat) (hk : k ≤ j) (wake : tr.RestartAt y k) : tr.time k ≤ tr.time i := by
    rcases hk.eq_or_lt with rfl | hk
    · obtain ⟨l, hc, hw⟩ := wake
      obtain rfl : l = r := Option.some.inj (hc.2.symm.trans rc.2)
      exact (cast (reset_cut hr hy rc hw).2.2).elim
    have h := WithBot.coe_le_coe.mp
      ((restart_le_clock hr hy wake hk).trans (joined_of_cast hr hy rc cast))
    exact h.trans (slot ▸ start)
  have deadline (k : Nat) (hk : k ≤ j) :=
    deadline_at_cut (fun m hm => bound m (hm.trans hk)) (τ := tr.time i)
  obtain ⟨k, hkj, hik, ⟨l, hc, proc⟩, htime⟩ := sync.1 x hx i v sent lo hi y hy j r rc
    ((deadline j le_rfl).trans_le due)
  rw [deadline k hkj] at htime
  have kj : k < j := hkj.lt_of_ne (by rintro rfl; exact (not_lt_of_ge due) htime)
  obtain ⟨vlo, vhi⟩ := slot_window_of_forward (hr.time_nonneg i) start le_rfl last _ hik htime
  refine cover_before_restart hr hy hc ?_ kj ?_
  · rcases proc with recv | ⟨e, he, rfl⟩
    · exact held_after_receipt hr hy hc recv vlo vhi
    · exact held_after_emit hr hy hc he
  · intro m hkm hmj wake
    obtain ⟨l', hc', hw⟩ := wake
    obtain ⟨u, _, hu, _, gap⟩ := hr.sleep_of_restart y hy m l' hc' hw
    exact (not_lt_of_ge ((bound m hmj.le ⟨l', hc', hw⟩).trans hik)) ((gap k hkm l hc).trans hu)

end Consensus.Goldilocks.SA.TimeShifted

end
