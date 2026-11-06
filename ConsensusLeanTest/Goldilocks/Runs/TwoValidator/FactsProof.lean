module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.World
@[expose] public section

/-! # The healthy two-validator run: its observable events, proved

`run_facts`: the run of `TwoValidator.Run` has the events `RunFacts` states. The "every" fields
read the shape of the events (`plan`) at the cut (`sk_of_label`); the existence fields exhibit
the cut of the shape (`label_at`); the send-or-admission fields read the pools after the cut
(`post_pool_sub`, `post_atts_sub`) against the pools of a later time (`pool_full`, `atts_full`). -/

namespace Consensus.Goldilocks.Witness.TwoRun

open SA Node

/-! ## What a cut of the shape says -/

/-- What a frameless cut of node `y` at time `t` says about the events `RunFacts` reads: an AC
call is not a restart and emits only own votes of their vote time; a block call is an accepted
chain block of slot `s ≥ 1` at `t_s`; a signature is the own row of its signing time. -/
private def SkOk (t : Nat) (y : Fin sp.n) : Sk → Prop
  | .ac c es => c ≠ .restart ∧ ∀ m ∈ es, ∃ σ, m = vote y σ ∧ t = vt σ
  | .fg (.block B acc) => acc = true ∧ ∃ s, 1 ≤ s ∧ B = blk s ∧ t = 4 * s
  | .fg (.attest _ none) => True
  | .fg (.attest _ (some a)) => ∃ q, 1 ≤ q ∧ a = row y q ∧ t = rt q
  | .fg (.attestation _) => True

private theorem vt_four {s : Nat} (hs : 1 ≤ s) : vt s = 4 * s := by unfold vt; split_ifs <;> omega

/-- **Every cut of the shape** says what `SkOk` asks. -/
private theorem plan_ok {t : Nat} {p : Fin sp.n × Node.Event N × List Sk} (hp : p ∈ plan t) {c : Sk}
    (hc : c ∈ p.2.2) : SkOk t p.1 c := by
  unfold plan at hp
  split_ifs at hp with h1 h2 h3 h4 h5 <;>
    simp only [tickSk, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [SkOk, ne_eq, reduceCtorEq, not_false_eq_true, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, true_and, false_implies, implies_true] <;>
    first
    | exact ⟨_, rfl, by unfold vt; split_ifs <;> omega⟩
    | exact ⟨_, by omega, rfl, by omega⟩
    | exact ⟨_, hgt_pos _, rfl, by unfold rt hgt; split_ifs <;> omega⟩

/-- A labelled cut says what `SkOk` asks, at its node and time. -/
private theorem cut_ok {i : Nat} {c : Cut N} (h : run.label i = some c) :
    ∃ t : Nat, run.time i = (t : Int) ∧ SkOk t (run.node i) (sk c) := by
  obtain ⟨t, j, k, p, -, -, -, hp, hc, hn, ht⟩ := sk_of_label h
  exact ⟨t, ht, hn ▸ plan_ok (List.mem_of_getElem? hp) (List.mem_of_getElem? hc)⟩

/-! ## The cuts of the shape -/

private theorem sk_eq_ac {c : Cut N} {call : N.Call} {es : List (Vote sp.n)}
    (h : sk c = .ac call es) :
    ∃ ℓ : ACLabel N, c = .ac ℓ ∧ ℓ.call = call ∧ ℓ.emits.map (·.msg) = es := by
  cases c with
  | fg ℓ => cases h
  | ac ℓ =>
    simp only [sk, Sk.ac.injEq] at h
    exact ⟨ℓ, rfl, h.1, h.2⟩

private theorem sk_eq_fg {c : Cut N} {ℓ : FGLabel sp.toParams N.Payload} (h : sk c = .fg ℓ) :
    c = .fg ℓ := by
  cases c with
  | fg ℓ' => simp only [sk, Sk.fg.injEq] at h; rw [h]
  | ac ℓ' => cases h

section At

variable {t j k : Nat} (hj : j < 128) (hk : k < 8) {p : Fin sp.n × Node.Event N × List Sk}
  (hp : (plan t)[j]? = some p)
include hj hk hp

/-- An FG cut of the shape is an FG call of its node at its time. -/
private theorem fg_at {ℓ : FGLabel sp.toParams N.Payload} (hc : p.2.2[k]? = some (.fg ℓ)) :
    ∃ i, run.CallAt p.1 i (.fg ℓ) ∧ run.time i = (t : Int) := by
  obtain ⟨c, hl, hs, hn, ht⟩ := label_at hj hk hp hc
  exact ⟨_, ⟨hn, sk_eq_fg hs ▸ hl⟩, ht⟩

/-- An AC cut of the shape with one emission is an emission of its node at its time. -/
private theorem emit_at {call : N.Call} {m : Vote sp.n} (hc : p.2.2[k]? = some (.ac call [m])) :
    ∃ i, run.EmitAt p.1 i m ∧ run.time i = (t : Int) := by
  obtain ⟨c, hl, hs, hn, ht⟩ := label_at hj hk hp hc
  obtain ⟨ℓ, rfl, -, he⟩ := sk_eq_ac hs
  have hm : m ∈ ℓ.emits.map (·.msg) := by rw [he]; exact List.mem_singleton_self m
  exact ⟨_, ⟨ℓ, ⟨hn, hl⟩, List.mem_map.1 hm⟩, ht⟩

/-- A message cut of the shape is a receipt of its node at its time. -/
private theorem msg_at {m : Vote sp.n} (hc : p.2.2[k]? = some (.ac (.message m) [])) :
    ∃ i, run.MsgCallAt p.1 i m ∧ run.time i = (t : Int) := by
  obtain ⟨c, hl, hs, hn, ht⟩ := label_at hj hk hp hc
  obtain ⟨ℓ, rfl, hcall, -⟩ := sk_eq_ac hs
  exact ⟨_, ⟨ℓ, ⟨hn, hl⟩, hcall⟩, ht⟩

end At

/-! ## The facts -/

private theorem rowRecv_self (y : Fin sp.n) (q : Nat) : rowRecv y y q = rt q := by
  rw [rowRecv, ite_eq_right (fun h => w1_ne (h.2.symm.trans h.1))]

private theorem hgt_rt (q : Nat) (hq : 1 ≤ q) : hgt (10 * (q - 1) + 1) = q := by
  rw [hgt, ite_eq_right (by omega)]; omega

private theorem facts_emit (y : Fin sp.n) (i : Nat) (m : Vote sp.n) (h : run.EmitAt y i m) :
    ∃ σ, m = vote y σ ∧ run.time i = (vt σ : Int) := by
  obtain ⟨ℓ, ⟨rfl, hl⟩, e, he, rfl⟩ := h
  obtain ⟨t, ht, hok⟩ := cut_ok hl
  obtain ⟨σ, h1, h2⟩ := hok.2 e.msg (List.mem_map_of_mem he)
  exact ⟨σ, h1, by rw [ht, h2]⟩

private theorem facts_sign (y : Fin sp.n) (i : Nat) (a : FG.Att sp.n) (h : run.SignAt y i a) :
    ∃ q, 1 ≤ q ∧ a = row y q ∧ run.time i = (rt q : Int) := by
  obtain ⟨src, rfl, hl⟩ := h
  obtain ⟨t, ht, q, hq, h1, h2⟩ := cut_ok hl
  exact ⟨q, hq, h1, by rw [ht, h2]⟩

/-- **The observable events of the run.** -/
theorem run_facts : RunFacts where
  noRestart y k := by
    rintro ⟨ℓ, ⟨-, hl⟩, hr⟩
    obtain ⟨t, -, hok⟩ := cut_ok hl
    exact hok.1 hr
  emit := facts_emit
  emit_exists y σ := by
    rcases eq_w0_or_w1 y with rfl | rfl <;> rcases σ with _ | s
    · obtain ⟨i, h, ht⟩ := emit_at (t := 1) (j := 0) (k := 0) (by omega) (by omega)
        (by rw [plan_one]; rfl) (by rfl)
      exact ⟨i, h, ht⟩
    · obtain ⟨i, h, ht⟩ := emit_at (t := 4 * (s + 1)) (j := 0) (k := 3) (by omega) (by omega)
        (by rw [plan_four (by omega)]; rfl) (by rfl)
      exact ⟨i, h, by rw [ht, vt_four (by omega)]⟩
    · obtain ⟨i, h, ht⟩ := emit_at (t := 1) (j := 1) (k := 0) (by omega) (by omega)
        (by rw [plan_one]; rfl) (by rfl)
      exact ⟨i, h, ht⟩
    · obtain ⟨i, h, ht⟩ := emit_at (t := 4 * (s + 1)) (j := 2) (k := 1) (by omega) (by omega)
        (by rw [plan_four (by omega)]; rfl) (by rfl)
      exact ⟨i, h, by rw [ht, vt_four (by omega)]⟩
  recv_exists y z σ hzy := by
    rcases eq_w0_or_w1 y with rfl | rfl <;> rcases eq_w0_or_w1 z with rfl | rfl <;>
      first | exact absurd rfl hzy | rcases σ with _ | s
    · obtain ⟨i, h, ht⟩ := msg_at (t := 1) (j := 2) (k := 0) (by omega) (by omega)
        (by rw [plan_one]; rfl) (by rfl)
      exact ⟨i, h, ht⟩
    · obtain ⟨i, h, ht⟩ := msg_at (t := 4 * (s + 1)) (j := 3) (k := 0) (by omega) (by omega)
        (by rw [plan_four (by omega)]; rfl) (by rfl)
      exact ⟨i, h, by rw [ht, vt_four (by omega)]⟩
    · obtain ⟨i, h, ht⟩ := msg_at (t := 1) (j := 3) (k := 0) (by omega) (by omega)
        (by rw [plan_one]; rfl) (by rfl)
      exact ⟨i, h, ht⟩
    · obtain ⟨i, h, ht⟩ := msg_at (t := 4 * (s + 1)) (j := 4) (k := 0) (by omega) (by omega)
        (by rw [plan_four (by omega)]; rfl) (by rfl)
      exact ⟨i, h, by rw [ht, vt_four (by omega)]⟩
  admitMsg x i m := by
    rintro ⟨ℓ, hcall, h | ⟨-, hpre, hpost⟩⟩
    · obtain ⟨σ, h1, h2⟩ := facts_emit x i m ⟨ℓ, hcall, h⟩
      exact ⟨x, σ, h1, h2⟩
    · change m ∉ (run.state x i).ac.pool m.slot at hpre
      change m ∈ (run.post i).ac.pool m.slot at hpost
      obtain ⟨z, hm, hle⟩ := post_pool_sub i m.slot (by rw [hcall.2]; exact Option.some_ne_none _)
        hpost
      refine ⟨z, m.slot, hm, le_antisymm ?_ hle⟩
      refine not_lt.1 fun hlt => hpre ?_
      have h := pool_full x z i m.slot hlt
      rwa [← hm] at h
  block y i B := by
    rintro ⟨acc, hn, hl⟩
    obtain ⟨t, ht, rfl, s, hs, rfl, h4⟩ := cut_ok hl
    exact ⟨s, hs, rfl, by rw [ht, h4]; change ((4 * s : Nat) : Int) = 4 * (s : Int); omega, hn, hl⟩
  accept_exists y s hs := by
    rcases eq_w0_or_w1 y with rfl | rfl
    · obtain ⟨i, h, ht⟩ := fg_at (t := 4 * s) (j := 0) (k := 2) (by omega) (by omega)
        (by rw [plan_four hs]; rfl) (by rfl)
      exact ⟨i, h, by rw [ht]; change ((4 * s : Nat) : Int) = 4 * (s : Int); omega⟩
    · obtain ⟨i, h, ht⟩ := fg_at (t := 4 * s) (j := 2) (k := 0) (by omega) (by omega)
        (by rw [plan_four hs]; rfl) (by rfl)
      exact ⟨i, h, by rw [ht]; change ((4 * s : Nat) : Int) = 4 * (s : Int); omega⟩
  sign := facts_sign
  admitAtt x i a := by
    rintro (h | ⟨ℓ, hcall, hpre, hpost⟩)
    · obtain ⟨q, hq, h1, h2⟩ := facts_sign x i a h
      exact ⟨x, q, hq, h1, by rw [h2, rowRecv_self]⟩
    · obtain ⟨z, q, hq, ha, hle⟩ := post_atts_sub i
        (by rw [hcall.2]; exact Option.some_ne_none _) hpost
      rw [hcall.1] at hle
      refine ⟨z, q, hq, ha, le_antisymm ?_ hle⟩
      refine not_lt.1 fun hlt => hpre ?_
      rw [ha]
      exact atts_full x z q i hq hlt
  processAtt z y q hq := by
    have h1 : 1 ≤ 10 * (q - 1) + 1 := by omega
    have h10 : (10 * (q - 1) + 1) % 10 = 1 := by omega
    rcases eq_w0_or_w1 z with rfl | rfl <;> rcases eq_w0_or_w1 y with rfl | rfl
    · obtain ⟨i, h, ht⟩ := fg_at (t := 4 * (10 * (q - 1) + 1) + 1) (j := 0) (k := 3)
        (by omega) (by omega) (by rw [plan_four1_row h1 h10]; rfl) (by rfl)
      rw [hgt_rt q hq] at h
      exact ⟨i, h, by rw [ht, rowRecv_self, rt]; congr 1; omega⟩
    · obtain ⟨i, h, ht⟩ := fg_at (t := 4 * (10 * q)) (j := 5) (k := 0) (by omega) (by omega)
        (by rw [plan_four (by omega), ite_eq_left (by omega : 10 * q % 10 = 0)]; rfl) (by rfl)
      rw [show 10 * q / 10 = q by omega] at h
      refine ⟨i, h, ?_⟩
      rw [ht, rowRecv, ite_eq_left ⟨rfl, rfl⟩, rt]
      congr 1
      omega
    · obtain ⟨i, h, ht⟩ := fg_at (t := 4 * (10 * (q - 1) + 1) + 1) (j := 2) (k := 0)
        (by omega) (by omega) (by rw [plan_four1_row h1 h10]; rfl) (by rfl)
      rw [hgt_rt q hq] at h
      refine ⟨i, h, ?_⟩
      rw [ht, rowRecv, ite_eq_right (fun h => w1_ne h.1), rt]
      congr 1
      omega
    · obtain ⟨i, h, ht⟩ := fg_at (t := 4 * (10 * (q - 1) + 1) + 1) (j := 1) (k := 3)
        (by omega) (by omega) (by rw [plan_four1_row h1 h10]; rfl) (by rfl)
      rw [hgt_rt q hq] at h
      exact ⟨i, h, by rw [ht, rowRecv_self, rt]; congr 1; omega⟩

end Consensus.Goldilocks.Witness.TwoRun

end
