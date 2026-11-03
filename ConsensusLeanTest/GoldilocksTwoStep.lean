module
public import ConsensusLeanTest.GoldilocksTwoAC
public import ConsensusLeanTest.GoldilocksTwoFacts
@[expose] public section

/-! # The healthy two-validator run: the node's events

The state of a node of the run (`NS`: the FG store with the chain up to a tip, its pool, its
record, and the shape of its SA state `ACShape`), the state before each time (`Good`), and each
top-level event of the run computed from it: its cuts (up to frames and emission records) and the
state after it. -/

namespace Consensus.Goldilocks.Witness.TwoRun

open SA Node ChainFrame

/-! ## The node state -/

/-- The shape of an SA state: no restart, the voted slot `vs`, the pools `pl` (stamped at their
vote times), the blocks up to `τ` stamped at their slots, the first `us` slots saved with their
blocks, locks on chain blocks up to `lk`, the fast lock of slot `tl` on its block (from `1`), the
record on the block of slot `lc`, the block of slot `rp` reported. -/
structure ACShape (A : SAState sp.n) (vs : Int) (τ : Nat) (pl : Nat → List (Vote sp.n))
    (lk tl lc rp us : Nat) : Prop where
  restart : A.restartTime = ⊥
  voted : A.votedSlot = vs
  pool : A.pool = pl
  vstamp : ∀ σ, ∀ x ∈ pl σ, A.voteStamp x = ETime.of ((vt σ : Nat) : Int)
  bstamp : ∀ m, 1 ≤ m → m ≤ τ → A.blockStamp (blk m).root = ETime.of ((4 * m : Nat) : Int)
  bstamp0 : A.blockStamp 0 = ⊥
  saved : ∀ j : Int, A.saved j = if 0 ≤ j ∧ j < us then some (blk j.toNat).root else none
  locks : LocksLe A.locks lk
  tipLock : 1 ≤ tl → (⟨(blk tl).root, tl, true, tl + 2⟩ : Lock) ∈ A.locks
  latest : A.latestConfirmed = (blk lc).root
  reported : A.fgReported = (blk rp).root

/-- The state of node `y`: the chain accepted up to `τ`, the first `k` attestations of its pool,
its rows of heights `1, …, nr` signed, and the SA state of that shape. -/
structure NS (st : St) (y : Fin sp.n) (τ k nr : Nat) (vs : Int) (pl : Nat → List (Vote sp.n))
    (lk tl lc rp us : Nat) : Prop where
  fg : FGGood st.fg τ
  atts : st.fg.atts = poolOf y k
  record : RecGood st.record nr
  ac : ACShape st.ac vs τ pl lk tl lc rp us

/-- The latest slot whose block is accepted before time `t`. -/
def tip (t : Nat) : Nat := (t + 3) / 4 - 1

/-- The latest slot whose block is reported before time `t`. -/
def rep (t : Nat) : Nat := (t - 2) / 4

/-- The number of slots saved before time `t`. -/
def nsv (t : Nat) : Nat := (t + 1) / 4 - 1

/-- The number of heights whose rows are signed before time `t`. -/
def nrw (t : Nat) : Nat := if t ≤ 5 then 0 else (t - 6) / 40 + 1

/-- The number of rows of `v1` that `v0` holds before time `t`. -/
def nrv (t : Nat) : Nat := if t ≤ 40 then 0 else (t - 41) / 40 + 1

/-- The size of `y`'s pool before time `t`. -/
def cnt (y : Fin sp.n) (t : Nat) : Nat := if y = w0 then nrw t + nrv t else 2 * nrw t

/-- The pools of `y` before time `t`: both votes of each slot up to the tip. -/
noncomputable def poolT (y : Fin sp.n) (t : Nat) : Nat → List (Vote sp.n) := fun σ =>
  if 2 ≤ t ∧ σ ≤ tip t then [vote y σ, vote (other y) σ] else []

/-- The voted slot before time `t`. -/
def vsT (t : Nat) : Int := if t ≤ 1 then -1 else tip t

/-- **The state of `y` before time `t`.** -/
def Good (st : St) (y : Fin sp.n) (t : Nat) : Prop :=
  NS st y (tip t) (cnt y t) (nrw t) (vsT t) (poolT y t) (tip t) (tip t) (tip t) (rep t) (nsv t)

theorem good_init (y : Fin sp.n) : Good (Node.init N) y 0 := by
  refine ⟨fgGood_init, by
    rw [show cnt y 0 = 0 by unfold cnt nrw nrv; split_ifs <;> omega]; rfl, recGood_empty,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩⟩
  · funext σ; simp [poolT, Node.init, SAState.initial]
  · intro σ x hx; simp [poolT] at hx
  · intro m h1 h2; simp [tip] at h2; omega
  · rfl
  · intro j; simp [Node.init, SAState.initial, nsv]
  · intro l hl; exact absurd hl (Set.notMem_empty _)
  · intro h; simp [tip] at h

theorem ns_frame {st : St} {y : Fin sp.n} {τ k nr : Nat} {vs : Int}
    {pl : Nat → List (Vote sp.n)} {lk tl lc rp us : Nat}
    (h : NS st y τ k nr vs pl lk tl lc rp us) : ∃ f, ChainFrame (Node.frame st) f (jx τ) τ :=
  fgGood_frame h.fg

/-! ## Ticks, generically -/

theorem onTick_eq' (y : Fin sp.n) (st : St) (t : Time) (x : Nat) :
    Node.onTick prop dg y st t x =
      ((tickStep prop dg y (tickStep prop dg y
        (tickStep prop dg y st t x .acTick).1 t x .proposal).1 t x
        .fgUpdate).1,
       (tickStep prop dg y st t x .acTick).2 ++
        (tickStep prop dg y
          (tickStep prop dg y st t x .acTick).1 t x .proposal).2 ++
        (tickStep prop dg y (tickStep prop dg y
          (tickStep prop dg y st t x .acTick).1 t x .proposal).1 t x
          .fgUpdate).2) := by
  simp [Node.onTick, runSteps, tickSteps]

theorem proposes_iff (y : Fin sp.n) (n : Nat) :
    Node.Proposes prop y (n : Int) ↔ y = w0 ∧ n % 4 = 0 ∧ 4 ≤ n := by
  unfold Node.Proposes
  rw [show sp.toParams.slotOf (n : Int) = n / 4 from slotOf_nat n]
  change 0 < n / 4 ∧ (n : Int) = 4 * ((n / 4 : Nat) : Int) ∧ w0 = y ↔ _
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3.symm, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h1.symm⟩

theorem tickStep_proposal_no {y : Fin sp.n} {st : St} {n : Nat}
    (h : ¬ (y = w0 ∧ n % 4 = 0 ∧ 4 ≤ n)) (x : Nat) :
    tickStep prop dg y st (n : Int) x .proposal = (st, []) := by
  simp only [tickStep]
  rw [ite_eq_right (fun hp => h ((proposes_iff y n).1 hp))]

theorem tickStep_acTick (y : Fin sp.n) (st : St) (t : Time) (x : Nat) :
    tickStep prop dg y st t x .acTick =
      ({ st with ac := (acOnTick sp y st.ac (Node.frame st) t).1 },
      [.ac ⟨.tick, Node.frame st, (acOnTick sp y st.ac (Node.frame st) t).2⟩]) := rfl

theorem tickStep_fgUpdate_none {y : Fin sp.n} {st : St} {f j τ : Nat}
    (hf : ChainFrame (Node.frame st) f j τ) {b : Nat} (hL : LocksLe st.ac.locks b)
    (hb : f ≤ b) (hbτ : b ≤ τ) (hrep : st.ac.fgReported = (blk b).root) (n x : Nat) :
    tickStep prop dg y st (n : Int) x .fgUpdate =
      (st, [.ac ⟨.toFG, Node.frame st, []⟩]) := by
  obtain ⟨h1, h2⟩ := acToFG_none hf hL hb hbτ hrep (n : Int)
  simp only [tickStep, Node.acToFG]
  split
  · change ({ st with ac := (SA.acToFG sp st.ac (Node.frame st) n).1 }, _) = _
    rw [h1]
  · rename_i C heq
    exact absurd (heq.symm.trans h2) (by simp)

theorem jx_le_pred (τ : Nat) : jx τ ≤ τ - 1 ∨ jx τ = 0 := by
  rcases τ with _ | τ
  · exact Or.inr rfl
  · exact Or.inl (by have := jx_succ_le τ; omega)

/-- **A tick with nothing to do**: its SA tick changes nothing, it does not propose, and
`ac_to_fg` returns nothing (every lock at or below the reported block, which is the tip or its
parent). -/
theorem tick_noop {st : St} {y : Fin sp.n} {τ k nr : Nat} {vs : Int}
    {pl : Nat → List (Vote sp.n)} {lk tl lc rp us : Nat}
    (h : NS st y τ k nr vs pl lk tl lc rp us) {n : Nat}
    (hnp : ¬ (y = w0 ∧ n % 4 = 0 ∧ 4 ≤ n))
    (hac : acOnTick sp y st.ac (Node.frame st) n = (st.ac, []))
    (hlk : lk ≤ rp) (hrp : rp ≤ τ) (hrp' : τ ≤ rp + 1) :
    Node.onTick prop dg y st (n : Int) 0 =
      (st, [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.toFG, Node.frame st, []⟩]) := by
  obtain ⟨f, hf⟩ := ns_frame h
  have hfr : f ≤ rp := by
    have h1 := hf.fj; have h2 := jx_le_pred τ; omega
  rw [onTick_eq', tickStep_acTick, hac]
  dsimp only
  rw [show ({ fg := st.fg, ac := st.ac, record := st.record } : St) = st from rfl,
    tickStep_proposal_no hnp,
    tickStep_fgUpdate_none hf (fun l hl => (h.ac.locks l hl).imp fun _ hm => ⟨by omega, hm.2⟩)
      hfr hrp h.ac.reported]
  rfl

/-! ## The parameters along time -/

theorem tip_four (s : Nat) : tip (4 * s) = s - 1 := by unfold tip; omega
theorem tip_four1 (s : Nat) : tip (4 * s + 1) = s := by unfold tip; omega
theorem tip_four2 (s : Nat) : tip (4 * s + 2) = s := by unfold tip; omega
theorem tip_four3 (s : Nat) : tip (4 * s + 3) = s := by unfold tip; omega
theorem rep_four (s : Nat) : rep (4 * s) = s - 1 := by unfold rep; omega
theorem rep_four1 (s : Nat) : rep (4 * s + 1) = s - 1 := by unfold rep; omega
theorem rep_four2 (s : Nat) : rep (4 * s + 2) = s := by unfold rep; omega
theorem rep_four3 (s : Nat) : rep (4 * s + 3) = s := by unfold rep; omega
theorem nsv_four (s : Nat) : nsv (4 * s) = s - 1 := by unfold nsv; omega
theorem nsv_four1 (s : Nat) : nsv (4 * s + 1) = s - 1 := by unfold nsv; omega
theorem nsv_four2 (s : Nat) : nsv (4 * s + 2) = s - 1 := by unfold nsv; omega
theorem nsv_four3 (s : Nat) : nsv (4 * s + 3) = s := by unfold nsv; omega

/-- Rows are signed only at times `1 mod 4`. -/
theorem nrw_succ_of {t : Nat} (h : t % 4 ≠ 1) : nrw (t + 1) = nrw t := by
  unfold nrw; split_ifs <;> omega

/-- The rows of `v1` reach `v0` only at times `0 mod 4`. -/
theorem nrv_succ_of {t : Nat} (h : t % 4 ≠ 0) : nrv (t + 1) = nrv t := by
  unfold nrv; split_ifs <;> omega

theorem nrw_row {s : Nat} (hs : 1 ≤ s) : nrw (4 * s + 1) =
    if s % 10 = 1 then hgt s - 1 else hgt s := by
  unfold nrw hgt; split_ifs <;> omega

theorem nrw_row_succ {s : Nat} (hs : 1 ≤ s) : nrw (4 * s + 2) = hgt s := by
  unfold nrw hgt; split_ifs <;> omega

theorem nrv_four {s : Nat} : nrv (4 * s + 1) = if s % 10 = 0 ∧ 10 ≤ s then nrv (4 * s) + 1
    else nrv (4 * s) := by
  unfold nrv; split_ifs <;> omega

theorem vt_le (σ : Nat) : vt σ ≤ 4 * σ + 1 := by unfold vt; split_ifs <;> omega

theorem saved_succ {S : Int → Option Nat} {u : Nat}
    (h : ∀ j : Int, S j = if 0 ≤ j ∧ j < u then some (blk j.toNat).root else none) (j : Int) :
    Function.update S ((u : Nat) : Int) (some (blk u).root) j =
      if 0 ≤ j ∧ j < (u + 1 : Nat) then some (blk j.toNat).root else none := by
  by_cases hj : j = ((u : Nat) : Int)
  · subst hj; rw [Function.update_self, ite_eq_left ⟨by omega, by omega⟩, Int.toNat_natCast]
  · rw [Function.update_of_ne hj, h j]
    split_ifs with h1 h2 h2 <;> first | rfl | omega

/-! ## The ticks -/

/-- **The tick of `t_s + 2Δ`**: the confirmation update of slot `s − 1`. -/
theorem tick_update {st : St} {y : Fin sp.n} {s : Nat} (hs : 1 ≤ s)
    (h : Good st y (4 * s + 2)) :
    ∃ A', Node.onTick prop dg y st ((4 * s + 2 : Nat) : Int) 0 =
      ({ st with ac := A' }, [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.toFG, Node.frame st, []⟩]) ∧
      Good { st with ac := A' } y (4 * s + 3) := by
  have ht := tip_four2 s
  obtain ⟨hfg, hatts, hrec, hac⟩ := h
  rw [ht] at hfg
  rw [ht, rep_four2, nsv_four2] at hac
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  change ChainFrame (Node.frame st) f (jx s) s at hf
  have hfs : f ≤ s - 1 := by have h1 := hf.fj; have h2 := jx_le_pred s; omega
  have hp : st.ac.pool (s - 1) = [vote y (s - 1), vote (other y) (s - 1)] := by
    rw [hac.pool]; unfold poolT; rw [ht, ite_eq_left ⟨by omega, by omega⟩]
  have hres : ∀ x ∈ st.ac.pool (s - 1), resolutionTime st.ac (Node.frame st) x <
      ETime.of (sp.ts ((s - 1 : Nat) : Int) + 2 * sp.Δ) := by
    intro x hx
    rw [hp] at hx
    have hx' : x = vote y (s - 1) ∨ x = vote (other y) (s - 1) := by simpa using hx
    have hb : st.ac.blockStamp (blk (s - 1)).root < ETime.of (4 * ((s - 1 : Nat) : Int) + 2) := by
      rcases Nat.lt_or_ge (s - 1) 1 with h1 | h1
      · rw [show s - 1 = 0 by omega, blk_root_zero, hac.bstamp0]; exact WithBot.bot_lt_coe _
      · rw [hac.bstamp _ h1 (by omega)]
        refine WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 ?_)
        change ((4 * (s - 1) : Nat) : Int) < 4 * ((s - 1 : Nat) : Int) + 2
        omega
    rw [ts_nat, delta1]
    rcases hx' with rfl | rfl <;>
    · rw [resolutionTime_vote hf hfs (by omega)]
      refine max_lt ?_ hb
      rw [hac.vstamp (s - 1) _ (by rw [← hac.pool, hp]; simp)]
      have := vt_le (s - 1)
      refine WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 ?_)
      change ((vt (s - 1) : Nat) : Int) < 4 * ((s - 1 : Nat) : Int) + 2 * 1
      omega
  have hC := getConfirmation_tick hf hfs (by omega) hp hres
  obtain ⟨hsame, hsv, hlat, N', hN, hlk⟩ := updateConfirmation_tick (t := ((4 * s + 2 : Nat) : Int))
    hf hC (b := s) (by omega) le_rfl hfs hac.latest
  set A' := updateConfirmation sp st.ac (Node.frame st) ((4 * s + 2 : Nat) : Int) (s - 1)
  have hstep : acOnTick sp y st.ac (Node.frame st) ((4 * s + 2 : Nat) : Int) = (A', []) := by
    rw [acOnTick_eq _ _ _ _ hac.restart, ite_eq_left ⟨by omega, by omega⟩]
    rw [show (4 * s + 2) / 4 - 1 = s - 1 by omega]
  have hL : LocksLe A'.locks s := by
    rw [hlk]; exact addLocks_le hf hac.locks le_rfl _ _ hN
  have htip : 1 ≤ s → (⟨(blk s).root, s, true, s + 2⟩ : Lock) ∈ A'.locks := fun h1 => by
    rw [hlk]
    exact hf.mem_liveLocks (Or.inl (hac.tipLock h1)) (by omega) le_rfl rfl
      (by rw [slot_nat]; dsimp only; omega)
  have hac' : ACShape A' (vsT (4 * s + 3)) s (poolT y (4 * s + 3)) s s s s s := by
    refine ⟨hsame.restartTime.trans hac.restart, ?_, ?_, ?_, fun m h1 h2 => ?_, ?_, fun j => ?_,
      hL, htip, hlat.trans hac.latest, hsame.fgReported.trans hac.reported⟩
    · rw [hsame.votedSlot, hac.voted]; unfold vsT; rw [tip_four2, tip_four3]
      split_ifs <;> first | rfl | omega
    · rw [hsame.pool, hac.pool]; funext σ; unfold poolT; rw [tip_four2, tip_four3]
      split_ifs <;> first | rfl | omega
    · intro σ x hx
      rw [hsame.voteStamp]
      refine hac.vstamp σ x ?_
      unfold poolT at hx ⊢; rw [tip_four2]; rw [tip_four3] at hx
      split_ifs at hx ⊢ <;> first | exact hx | omega
    · rw [hsame.blockStamp]; exact hac.bstamp m h1 h2
    · rw [hsame.blockStamp]; exact hac.bstamp0
    · rw [hsv, show s = (s - 1) + 1 by omega]
      exact saved_succ hac.saved j
  have hrep : A'.fgReported = (blk s).root := hsame.fgReported.trans hac.reported
  refine ⟨A', ?_, ?_⟩
  · rw [onTick_eq', tickStep_acTick, hstep]
    dsimp only
    rw [tickStep_proposal_no (by omega),
      tickStep_fgUpdate_none (st := { st with ac := A' }) hf hL (by omega) le_rfl hrep]
    · rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [tip_four3]; exact hfg
    · rw [show cnt y (4 * s + 3) = cnt y (4 * s + 2) by
        unfold cnt; rw [nrw_succ_of (by omega), nrv_succ_of (by omega)]]; exact hatts
    · rw [nrw_succ_of (by omega)]; exact hrec
    · rw [tip_four3, rep_four3, nsv_four3]; exact hac'

theorem frame_zero {st : St} {f : Nat} (hf : ChainFrame (Node.frame st) f (jx 0) 0) :
    ChainFrame (Node.frame st) 0 0 0 := by
  have h1 := hf.fj
  have : f = 0 := by change f ≤ 0 at h1; omega
  subst this; exact hf

theorem vstamp_update {A : SAState sp.n} {pl : Nat → List (Vote sp.n)}
    (h : ∀ σ, ∀ x ∈ pl σ, A.voteStamp x = ETime.of ((vt σ : Nat) : Int)) {σ : Nat}
    {v : Vote sp.n} (hv : v.slot = σ) (hnot : ∀ σ', v ∉ pl σ') :
    ∀ σ', ∀ x ∈ Function.update pl σ (pl σ ++ [v]) σ',
      Function.update A.voteStamp v (ETime.of ((vt σ : Nat) : Int)) x =
        ETime.of ((vt σ' : Nat) : Int) := by
  intro σ' x hx
  by_cases hs : σ' = σ
  · subst hs
    rw [Function.update_self] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [Function.update_of_ne (fun he => hnot σ' (by rw [← he]; exact hx)), h σ' x hx]
    · rw [List.mem_singleton] at hx; subst hx; rw [Function.update_self]
  · rw [Function.update_of_ne hs] at hx
    rw [Function.update_of_ne (fun he => hnot σ' (by rw [← he]; exact hx)), h σ' x hx]

/-- **The tick of time `1`**: the vote of slot `0`. -/
theorem tick_vote0 {st : St} {y : Fin sp.n} (h : Good st y 1) :
    ∃ A' e, Node.onTick prop dg y st ((1 : Nat) : Int) 0 =
      ({ st with ac := A' }, [.ac ⟨.tick, Node.frame st, [e]⟩, .ac ⟨.toFG, Node.frame st, []⟩]) ∧
      e.msg = vote y 0 ∧
      NS { st with ac := A' } y 0 (cnt y 1) (nrw 1) 0
        (Function.update (poolT y 1) 0 [vote y 0]) 0 0 0 0 0 := by
  obtain ⟨hfg, hatts, hrec, hac⟩ := h
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  have hf0 := frame_zero hf
  have hp0 : poolT y 1 = fun _ => [] := by funext σ; unfold poolT; rw [ite_eq_right (by omega)]
  obtain ⟨d, hd⟩ := tryVote_zero (y := y) hf0 hac.restart hac.voted hac.locks
  have hpool : st.ac.pool 0 = [] := by rw [hac.pool, hp0]
  have hadm := admitVote_fresh (A := { st.ac with votedSlot := 0 }) (t := 1) (v := vote y 0)
    (slot_nat 1) (by change _ ∉ st.ac.pool 0; rw [hpool]; simp)
    (by change ∀ x ∈ st.ac.pool 0, _; rw [hpool]; simp)
  set A' := admitVote sp { st.ac with votedSlot := 0 } 1 (vote y 0)
  have hstep : acOnTick sp y st.ac (Node.frame st) ((1 : Nat) : Int) =
      (A', [⟨vote y 0, { st.ac with votedSlot := 0 }, some d⟩]) := by
    rw [acOnTick_eq _ _ _ _ hac.restart, ite_eq_right (by omega), ite_eq_left (by omega)]
    exact hd
  have hac' : ACShape A' 0 0 (Function.update (poolT y 1) 0 [vote y 0]) 0 0 0 0 0 := by
    rw [hadm]
    refine ⟨hac.restart, rfl, ?_, ?_, hac.bstamp, hac.bstamp0, hac.saved, hac.locks, hac.tipLock,
      hac.latest, hac.reported⟩
    · change Function.update st.ac.pool 0 (st.ac.pool 0 ++ [vote y 0]) = _
      rw [hpool, hac.pool]; rfl
    · have := vstamp_update (A := st.ac) (pl := poolT y 1) hac.vstamp (σ := 0) (v := vote y 0) rfl
        (fun σ' => by rw [hp0]; simp)
      rw [hp0] at this ⊢
      exact this
  refine ⟨A', ⟨vote y 0, { st.ac with votedSlot := 0 }, some d⟩, ?_, rfl, hfg, hatts, hrec, hac'⟩
  rw [onTick_eq', tickStep_acTick, hstep]
  dsimp only
  rw [tickStep_proposal_no (by omega),
    tickStep_fgUpdate_none (st := { st with ac := A' }) hf0 hac'.locks le_rfl le_rfl hac'.reported]
  rfl

/-- The SA's receipt of the other validator's vote of the slot, the own vote already held. -/
theorem acOnMessage_other {y : Fin sp.n} {A : SAState sp.n} {Φ : N.Frm} {t : Time} {σ : Nat}
    (hst : sp.slot t = σ) (hpool : A.pool σ = [vote y σ]) (hvs : A.votedSlot = σ) :
    acOnMessage sp y A Φ t (vote (other y) σ) =
      (optimisticConfirmation sp
        { A with pool := Function.update A.pool σ [vote y σ, vote (other y) σ],
                 voteStamp := Function.update A.voteStamp (vote (other y) σ) (ETime.of t) } Φ t,
        []) := by
  unfold acOnMessage
  have hne := other_ne y
  rw [admitVote_fresh (by rw [hst]; rfl)
    (by change _ ∉ A.pool σ; rw [hpool]; simp only [List.mem_singleton]
        intro he; exact hne (vote_inj he).1)
    (by change ∀ x ∈ A.pool σ, _; rw [hpool]; simp only [List.mem_singleton, forall_eq]
        intro he; exact hne (he.symm.trans rfl))]
  change tryVote sp y (optimisticConfirmation sp
    { A with pool := Function.update A.pool σ (A.pool σ ++ [vote (other y) σ]),
             voteStamp := Function.update A.voteStamp (vote (other y) σ) (ETime.of t) } Φ t) Φ t = _
  rw [hpool]
  exact tryVote_voted (by
    obtain ⟨hs, -⟩ := optimisticConfirmation_cases
      { A with pool := Function.update A.pool σ ([vote y σ] ++ [vote (other y) σ]),
               voteStamp := Function.update A.voteStamp (vote (other y) σ) (ETime.of t) } Φ t
    rw [hs.votedSlot, hst]; exact hvs)

theorem onMessage_eq (y : Fin sp.n) (st : St) (t : Time) (m : Vote sp.n) :
    Node.onMessage y st t m =
      ({ st with ac := (acOnMessage sp y st.ac (Node.frame st) t m).1 },
        [.ac ⟨.message m, Node.frame st, (acOnMessage sp y st.ac (Node.frame st) t m).2⟩]) := rfl

/-- **The other validator's vote of slot `0`**, at time `1`. -/
theorem deliver_vote0 {st : St} {y : Fin sp.n}
    (h : NS st y 0 (cnt y 1) (nrw 1) 0 (Function.update (poolT y 1) 0 [vote y 0]) 0 0 0 0 0) :
    ∃ A', Node.onMessage y st ((1 : Nat) : Int) (vote (other y) 0) =
      ({ st with ac := A' }, [.ac ⟨.message (vote (other y) 0), Node.frame st, []⟩]) ∧
      Good { st with ac := A' } y 2 := by
  obtain ⟨hfg, hatts, hrec, hac⟩ := h
  have hpool : st.ac.pool 0 = [vote y 0] := by rw [hac.pool, Function.update_self]
  have hs1 : sp.slot ((1 : Nat) : Int) = 0 := slot_nat 1
  rw [onMessage_eq, acOnMessage_other hs1 hpool (by rw [hac.voted]; rfl),
    optimisticConfirmation_of_none (optimisticSelect_slot_zero hs1)]
  refine ⟨_, rfl, ?_⟩
  have hp2 : poolT y 2 = Function.update (poolT y 1) 0 [vote y 0, vote (other y) 0] := by
    funext σ; unfold poolT; rw [Function.update_apply]
    simp only [show tip 2 = 0 from rfl, show tip 1 = 0 from rfl]
    split_ifs <;> first | rfl | omega | (subst_vars; rfl)
  refine ⟨hfg, hatts, hrec, ⟨hac.restart, hac.voted, ?_, ?_, hac.bstamp, hac.bstamp0, hac.saved,
    hac.locks, hac.tipLock, hac.latest, hac.reported⟩⟩
  · change Function.update st.ac.pool 0 _ = _
    rw [hp2, hac.pool, Function.update_idem]
  · intro σ x hx
    rw [hp2, Function.update_apply] at hx
    split_ifs at hx with h0
    · subst h0
      have hne := other_ne y
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      change Function.update st.ac.voteStamp (vote (other y) 0) (ETime.of ((1 : Nat) : Int)) x = _
      rcases hx with rfl | rfl
      · rw [Function.update_of_ne (fun he => hne (vote_inj he).1.symm)]
        exact hac.vstamp 0 _ (by rw [Function.update_self]; exact List.mem_singleton_self _)
      · rw [Function.update_self]; rfl
    · unfold poolT at hx; rw [ite_eq_right (by omega)] at hx; cases hx

theorem onAttestation_eq (st : St) (a : FG.Att sp.n) :
    Node.onAttestation st a = ({ st with fg := st.fg.onAttestation a }, [.fg (.attestation a)]) :=
  rfl

theorem poolAt_not_mem (y : Fin sp.n) (k : Nat) : poolAt y k ∉ poolOf y k := by
  rw [mem_poolOf]; rintro ⟨i, hi, he⟩; have := poolAt_inj y he; omega

/-- **An attestation delivery**: the next attestation of the pool's order. -/
theorem deliver_att {st : St} {y : Fin sp.n} {τ k nr : Nat} {vs : Int}
    {pl : Nat → List (Vote sp.n)} {lk tl lc rp us : Nat}
    (h : NS st y τ k nr vs pl lk tl lc rp us) :
    Node.onAttestation st (poolAt y k) =
      ({ st with fg := { st.fg with atts := st.fg.atts ++ [poolAt y k] } },
        [.fg (.attestation (poolAt y k))]) ∧
      NS { st with fg := { st.fg with atts := st.fg.atts ++ [poolAt y k] } } y τ (k + 1) nr vs pl
        lk tl lc rp us := by
  rw [onAttestation_eq, onAttestation_new (by rw [h.atts]; exact poolAt_not_mem y k)]
  refine ⟨rfl, ⟨?_, ?_, h.record, h.ac⟩⟩
  · obtain ⟨hb, hs, hJ, hj, hm, hF⟩ := h.fg
    exact ⟨hb, hs, hJ, hj, hm, hF⟩
  · change st.fg.atts ++ [poolAt y k] = _; rw [h.atts, poolOf_succ]

theorem ac_report {A : SAState sp.n} {Φ : N.Frm} {f s : Nat} (hf : ChainFrame Φ f (jx s) s)
    (hs : 1 ≤ s) {vs : Int} {pl : Nat → List (Vote sp.n)} {lc us : Nat}
    (hac : ACShape A vs s pl s s lc (s - 1) us) :
    (SA.acToFG sp A Φ ((4 * s + 1 : Nat) : Int)).1 = { A with fgReported := (blk s).root } ∧
      (SA.acToFG sp A Φ ((4 * s + 1 : Nat) : Int)).2 = some (blk s) :=
  acToFG_tick hf hac.restart (by rw [slot_nat]; omega) (hac.tipLock hs) (by omega) hac.reported

theorem tickStep_report {y : Fin sp.n} {st : St} {f s : Nat}
    (hf : ChainFrame (Node.frame st) f (jx s) s) (hs : 1 ≤ s) {vs : Int}
    {pl : Nat → List (Vote sp.n)} {lc us : Nat} (hac : ACShape st.ac vs s pl s s lc (s - 1) us) :
    tickStep prop dg y st ((4 * s + 1 : Nat) : Int) 0 .fgUpdate =
      let st' : St := { st with ac := { st.ac with fgReported := (blk s).root } }
      ((Node.attest y st' (blk s)).1,
        .ac ⟨.toFG, Node.frame st, []⟩ :: (Node.attest y st' (blk s)).2) := by
  obtain ⟨h1, h2⟩ := ac_report hf hs hac
  simp only [tickStep, Node.acToFG]
  rw [h2]
  dsimp only
  rw [h1]

theorem tick_report_ac {y : Fin sp.n} {st : St} {s : Nat} (hs : 1 ≤ s)
    (hac : ACShape st.ac (vsT (4 * s + 1)) s (poolT y (4 * s + 1)) s s s (s - 1)
      (nsv (4 * s + 1))) :
    acOnTick sp y st.ac (Node.frame st) ((4 * s + 1 : Nat) : Int) = (st.ac, []) := by
  rw [acOnTick_eq _ _ _ _ hac.restart, ite_eq_right (by omega), ite_eq_left (by omega)]
  exact tryVote_voted (by rw [hac.voted, slot_nat]; unfold vsT; rw [tip_four1,
    ite_eq_right (by omega)]; congr 1; omega)

theorem ac_reported {A : SAState sp.n} {vs : Int} {τ : Nat} {pl : Nat → List (Vote sp.n)}
    {lk tl lc rp us : Nat} (h : ACShape A vs τ pl lk tl lc rp us) (r : Nat) :
    ACShape { A with fgReported := (blk r).root } vs τ pl lk tl lc r us :=
  ⟨h.restart, h.voted, h.pool, h.vstamp, h.bstamp, h.bstamp0, h.saved, h.locks, h.tipLock,
    h.latest, rfl⟩

/-- **The tick of `t_s + Δ` at a row slot** (`s ≡ 1 mod 10`): `ac_to_fg` returns the block of
slot `s`, the entry of its height (or genesis's height for `s = 1`), and the node signs and
processes its row of that height. -/
theorem tick_report_new {st : St} {y : Fin sp.n} {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 = 1)
    (h : Good st y (4 * s + 1)) :
    ∃ st', Node.onTick prop dg y st ((4 * s + 1 : Nat) : Int) 0 =
      (st', [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.toFG, Node.frame st, []⟩,
        .fg (.attest (blk s) (some (row y (hgt s)))), .fg (.attestation (row y (hgt s)))]) ∧
      NS st' y s (cnt y (4 * s + 1) + 1) (hgt s) (vsT (4 * s + 1)) (poolT y (4 * s + 1)) s s s s
        (nsv (4 * s + 1)) := by
  obtain ⟨hfg, hatts, hrec, hac⟩ := h
  rw [tip_four1] at hfg hac
  rw [rep_four1] at hac
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  change ChainFrame (Node.frame st) f (jx s) s at hf
  rw [nrw_row hs, ite_eq_left h10] at hrec
  obtain ⟨Λ', hatt, hrec'⟩ := attest_new hfg le_rfl y hrec
  have hk : poolAt y (cnt y (4 * s + 1)) = row y (hgt s) := by
    unfold poolAt cnt
    have hq := hgt_pos s
    have hn1 : nrw (4 * s + 1) = hgt s - 1 := by rw [nrw_row hs, ite_eq_left h10]
    have hn2 : nrv (4 * s + 1) = hgt s - 1 := by unfold nrv hgt; split_ifs <;> omega
    split_ifs with h1 h2 h3 <;> (try subst h1) <;> first
      | omega | (congr 1; omega)
  set st' : St := { st with ac := { st.ac with fgReported := (blk s).root } }
  have hatt' : st'.fg.attest st'.record y (blk s) = some (row y (hgt s), Λ') := hatt
  have hns : NS { st' with record := Λ' } y s (cnt y (4 * s + 1)) (hgt s) (vsT (4 * s + 1))
      (poolT y (4 * s + 1)) s s s s (nsv (4 * s + 1)) :=
    ⟨hfg, hatts, hrec', ac_reported hac s⟩
  obtain ⟨hda, hns'⟩ := deliver_att hns
  rw [hk] at hda hns'
  refine ⟨_, ?_, hns'⟩
  rw [onTick_eq', tickStep_acTick, tick_report_ac hs hac]
  dsimp only
  rw [show ({ fg := st.fg, ac := st.ac, record := st.record } : St) = st from rfl,
    tickStep_proposal_no (by omega), tickStep_report hf hs hac]
  dsimp only
  unfold Node.attest
  rw [hatt']
  dsimp only
  rw [hda]
  rfl

/-- **The tick of `t_s + Δ` at another slot**: `ac_to_fg` returns the block of slot `s`, whose
height's row the node has signed already. -/
theorem tick_report_old {st : St} {y : Fin sp.n} {s : Nat} (hs : 1 ≤ s) (h10 : s % 10 ≠ 1)
    (h : Good st y (4 * s + 1)) :
    Node.onTick prop dg y st ((4 * s + 1 : Nat) : Int) 0 =
      ({ st with ac := { st.ac with fgReported := (blk s).root } },
        [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.toFG, Node.frame st, []⟩,
          .fg (.attest (blk s) none)]) ∧
      Good { st with ac := { st.ac with fgReported := (blk s).root } } y (4 * s + 2) := by
  obtain ⟨hfg, hatts, hrec, hac⟩ := h
  rw [tip_four1] at hfg hac
  rw [rep_four1] at hac
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  change ChainFrame (Node.frame st) f (jx s) s at hf
  have hrec2 := hrec
  rw [nrw_row hs, ite_eq_right h10] at hrec2
  have hatt := attest_old hfg le_rfl y hrec2
  refine ⟨?_, ?_⟩
  · rw [onTick_eq', tickStep_acTick, tick_report_ac hs hac]
    dsimp only
    rw [show ({ fg := st.fg, ac := st.ac, record := st.record } : St) = st from rfl,
      tickStep_proposal_no (by omega), tickStep_report hf hs hac]
    dsimp only
    unfold Node.attest
    rw [show st.fg.attest st.record y (blk s) = none from hatt]
    rfl
  · refine ⟨by rw [tip_four2]; exact hfg, ?_, ?_, ?_⟩
    · rw [show cnt y (4 * s + 2) = cnt y (4 * s + 1) by
        unfold cnt; rw [nrw_row_succ hs, nrw_row hs, ite_eq_right h10, nrv_succ_of (by omega)]]
      exact hatts
    · rw [nrw_row_succ hs]; exact hrec2
    · have hv : vsT (4 * s + 2) = vsT (4 * s + 1) := by
        unfold vsT; rw [tip_four1, tip_four2, ite_eq_right (by omega), ite_eq_right (by omega)]
      have hp : poolT y (4 * s + 2) = poolT y (4 * s + 1) := by
        funext σ; unfold poolT; rw [tip_four1, tip_four2]
        split_ifs <;> first | rfl | omega
      have hn : nsv (4 * s + 2) = nsv (4 * s + 1) := by rw [nsv_four1, nsv_four2]
      rw [tip_four2, rep_four2, hv, hp, hn]
      exact ac_reported hac s

/-! ## The blocks of the chain -/

theorem blockReceipt_blk {A : SAState sp.n} {t : Time} {k : Nat}
    (h0 : vote w0 k ∈ A.pool k) (h1 : vote w1 k ∈ A.pool k) :
    blockReceipt sp A t (blk (k + 1)) =
      { A with blockStamp := Function.update A.blockStamp (blk (k + 1)).root (ETime.of t) } := by
  unfold blockReceipt
  rw [blockVotes_blk, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  generalize Function.update A.blockStamp (blk (k + 1)).root (ETime.of t) = bs
  rw [admitVote_old (A := { A with blockStamp := bs }) h0,
    admitVote_old (A := { A with blockStamp := bs }) h1]

/-- **`ac_on_block` of the block of slot `k + 1`** at `t_{k+1}`: its stamp, and the vote of slot
`k + 1` on it. -/
theorem acOnBlock_blk {y : Fin sp.n} {A : SAState sp.n} {Φ : N.Frm} {f k : Nat}
    (h : ChainFrame Φ f (jx (k + 1)) (k + 1)) (hj : A.restartTime = ⊥)
    (hvs : A.votedSlot = (k : Int)) (hpool : A.pool (k + 1) = [])
    (h0 : vote w0 k ∈ A.pool k) (h1 : vote w1 k ∈ A.pool k) (hL : LocksLe A.locks k)
    (htip : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ A.locks) :
    ∃ L₁ e, acOnBlock sp y A Φ ((4 * (k + 1) : Nat) : Int) (blk (k + 1)) =
      ({ A with pool := Function.update A.pool (k + 1) [vote y (k + 1)],
                voteStamp := Function.update A.voteStamp (vote y (k + 1))
                  (ETime.of ((4 * (k + 1) : Nat) : Int)),
                blockStamp := Function.update A.blockStamp (blk (k + 1)).root
                  (ETime.of ((4 * (k + 1) : Nat) : Int)),
                locks := L₁, votedSlot := ((k + 1 : Nat) : Int) }, [e]) ∧
      e.msg = vote y (k + 1) ∧ LocksLe L₁ k ∧
      (1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁) := by
  have hs := slot4 k
  unfold acOnBlock
  rw [blockReceipt_blk h0 h1,
    optimisticConfirmation_of_none (optimisticSelect_of_pool_nil (by rw [hs]; exact hpool))]
  obtain ⟨L₁, d, he, hL₁, htip₁⟩ := tryVote_blk (y := y)
    (A := { A with blockStamp := Function.update A.blockStamp (blk (k + 1)).root
                    (ETime.of ((4 * (k + 1) : Nat) : Int)) }) h hj hvs hpool hL htip
  rw [he, admitVote_fresh (by rw [hs]; rfl) (by change _ ∉ A.pool (k + 1); rw [hpool]; simp)
      (by change ∀ x ∈ A.pool (k + 1), _; rw [hpool]; simp)]
  generalize Function.update A.blockStamp (blk (k + 1)).root
    (ETime.of ((4 * (k + 1) : Nat) : Int)) = bs
  refine ⟨L₁,
    ⟨vote y (k + 1), { A with blockStamp := bs, locks := L₁, votedSlot := ((k + 1 : Nat) : Int) },
      some d⟩, ?_, rfl, hL₁, htip₁⟩
  congr 2
  change Function.update A.pool (k + 1) (A.pool (k + 1) ++ [vote y (k + 1)]) = _
  rw [hpool]; rfl

theorem onBlock_eq_accept {y : Fin sp.n} {st : St} {t : Time} {B : N.Blk}
    (hslot : ¬ sp.toParams.slotOf t < B.slot) {fg' : Store sp.toParams N.Payload}
    (hfg : st.fg.onBlock B = some fg') :
    Node.onBlock y st t B =
      ({ st with fg := fg', ac := (acOnBlock sp y st.ac (Node.frame { st with fg := fg' }) t B).1 },
        [.fg (.block B true), .ac ⟨.block B, Node.frame { st with fg := fg' },
          (acOnBlock sp y st.ac (Node.frame { st with fg := fg' }) t B).2⟩]) := by
  unfold Node.onBlock
  rw [ite_eq_right hslot, hfg]
  rfl

/-- The rows of the block of slot `s` are in the pool of `y` before time `t_s`. -/
theorem payload_in_pool {y : Fin sp.n} {s : Nat} (hs : 1 ≤ s) :
    ∀ a ∈ (blk s).fgPayload, a ∈ poolOf y (cnt y (4 * s)) := by
  intro a ha
  rw [mem_poolOf]
  have hc0 : cnt w0 (4 * s) = nrw (4 * s) + nrv (4 * s) := by unfold cnt; rw [ite_eq_left rfl]
  have hc1 : cnt w1 (4 * s) = 2 * nrw (4 * s) := by unfold cnt; rw [ite_eq_right w1_ne]
  rcases mem_blk_fgPayload.1 ha with ⟨q, hq, hm, rfl⟩ | ⟨q, hq, hm, rfl⟩
  · -- the row of `v0` for height `q`, signed at `t_{10(q−1)+1} + Δ`
    unfold car0 at hm
    rcases eq_w0_or_w1 y with rfl | rfl
    · refine ⟨2 * (q - 1), ?_, ?_⟩
      · rw [hc0]; unfold nrw nrv; split_ifs <;> omega
      · unfold poolAt; rw [ite_eq_left (by omega)]; congr 1; omega
    · refine ⟨2 * (q - 1) + 1, ?_, ?_⟩
      · rw [hc1]; unfold nrw; split_ifs <;> omega
      · unfold poolAt other; rw [ite_eq_right (by omega), ite_eq_right (by decide)]
        congr 1; omega
  · -- the row of `v1` for height `q`
    unfold car1 at hm
    rcases eq_w0_or_w1 y with rfl | rfl
    · refine ⟨2 * (q - 1) + 1, ?_, ?_⟩
      · rw [hc0]; unfold nrw nrv; split_ifs <;> omega
      · unfold poolAt other; rw [ite_eq_right (by omega), ite_eq_left rfl]; congr 1; omega
    · refine ⟨2 * (q - 1), ?_, ?_⟩
      · rw [hc1]; unfold nrw; split_ifs <;> omega
      · unfold poolAt; rw [ite_eq_left (by omega)]; congr 1; omega

theorem pool_both {y : Fin sp.n} {σ : Nat} {l : List (Vote sp.n)}
    (h : l = [vote y σ, vote (other y) σ]) : vote w0 σ ∈ l ∧ vote w1 σ ∈ l := by
  subst h
  rcases eq_w0_or_w1 y with rfl | rfl
  · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩
  · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_self ..), List.mem_cons_self ..⟩

/-- The state of `y` at `t_s` after accepting the block of slot `s` and voting for it. -/
abbrev Voted (st : St) (y : Fin sp.n) (s : Nat) : Prop :=
  NS st y s (cnt y (4 * s)) (nrw (4 * s)) s
    (Function.update (poolT y (4 * s)) s [vote y s]) (s - 1) (s - 1) (s - 1) (s - 1)
    (nsv (4 * s))

/-- **The acceptance of the block of slot `s ≥ 1`** at `t_s`, and the vote for it. -/
theorem onBlock_blk {st : St} {y : Fin sp.n} {s : Nat} (hs : 1 ≤ s)
    (h : NS st y (s - 1) (cnt y (4 * s)) (nrw (4 * s)) (vsT (4 * s)) (poolT y (4 * s)) (s - 1)
      (s - 1) (s - 1) (s - 1) (nsv (4 * s))) :
    ∃ st' e, Node.onBlock y st ((4 * s : Nat) : Int) (blk s) =
      (st', [.fg (.block (blk s) true), .ac ⟨.block (blk s), Node.frame st', [e]⟩]) ∧
      e.msg = vote y s ∧ Voted st' y s := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  obtain ⟨hfg, hatts, hrec, hac⟩ := h
  rw [Nat.add_sub_cancel] at hfg hac
  obtain ⟨fg', hob, hfg', hatts'⟩ := fgGood_onBlock hfg
    (fun a ha => by rw [hatts]; exact payload_in_pool (by omega) a ha)
  obtain ⟨f, hf⟩ := fgGood_frame hfg'
  change ChainFrame (Node.frame { st with fg := fg' }) f (jx (k + 1)) (k + 1) at hf
  have hvt : vsT (4 * (k + 1)) = (k : Int) := by
    unfold vsT; rw [tip_four, ite_eq_right (by omega)]; rfl
  have hpk : st.ac.pool k = [vote y k, vote (other y) k] := by
    rw [hac.pool]; unfold poolT; rw [tip_four, ite_eq_left ⟨by omega, by omega⟩]
  have hp1 : st.ac.pool (k + 1) = [] := by
    rw [hac.pool]; unfold poolT; rw [tip_four, ite_eq_right (by omega)]
  obtain ⟨L₁, e, he, hem, hL₁, htip₁⟩ := acOnBlock_blk (y := y) hf hac.restart
    (by rw [hac.voted, hvt]) hp1 (pool_both hpk).1 (pool_both hpk).2 hac.locks hac.tipLock
  refine ⟨{ st with fg := fg', ac := (acOnBlock sp y st.ac (Node.frame { st with fg := fg' })
    ((4 * (k + 1) : Nat) : Int) (blk (k + 1))).1 }, e, ?_, hem, ?_⟩
  · rw [onBlock_eq_accept (by rw [slotOf_nat, blk_slot]; omega) hob, he]; rfl
  · rw [he]
    refine ⟨hfg', by rw [hatts', hatts], hrec, ⟨hac.restart, rfl, ?_, ?_, ?_, ?_, hac.saved,
      by rw [Nat.add_sub_cancel]; exact hL₁, by rw [Nat.add_sub_cancel]; exact htip₁,
      by rw [Nat.add_sub_cancel]; exact hac.latest, by rw [Nat.add_sub_cancel]; exact hac.reported⟩⟩
    · change Function.update st.ac.pool (k + 1) [vote y (k + 1)] = _
      rw [hac.pool]
    · intro σ x hx
      change Function.update st.ac.voteStamp (vote y (k + 1)) _ x = _
      rw [Function.update_apply] at hx
      split_ifs at hx with hσ
      · subst hσ
        rw [List.mem_singleton] at hx; subst hx
        rw [Function.update_self]; unfold vt; rw [ite_eq_right (by omega)]
      · have hxp := hx
        unfold poolT at hx
        split_ifs at hx with h2
        · rw [Function.update_of_ne (fun he' => by
            subst he'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with he' | he' <;> have := (vote_inj he').2 <;> rw [tip_four] at h2 <;>
              omega)]
          exact hac.vstamp σ x hxp
        · cases hx
    · intro m h1 h2
      change Function.update st.ac.blockStamp (blk (k + 1)).root _ (blk m).root = _
      rcases Nat.lt_or_ge m (k + 1) with hm | hm
      · rw [Function.update_of_ne (fun he' => by have := blk_root_inj he'; omega)]
        exact hac.bstamp m h1 (by omega)
      · rw [show m = k + 1 by omega, Function.update_self]
    · change Function.update st.ac.blockStamp (blk (k + 1)).root _ 0 = _
      rw [Function.update_of_ne (fun he' => blk_root_succ_ne k he'.symm), hac.bstamp0]

/-! ## The proposal -/

theorem mkBlock_blk {fg : Store sp.toParams N.Payload} {k : Nat}
    (hpa : fg.proposalAttestations (blk k) = (blk (k + 1)).fgPayload) :
    mkBlock dg w0 fg ((4 * (k + 1) : Nat) : Int) 0 (blk k)
      ([vote w0 k, vote w1 k], [vote w0 k, vote w1 k]) = blk (k + 1) := by
  unfold mkBlock
  rw [hpa, slotOf_nat, show 4 * (k + 1) / 4 = k + 1 by omega, ← blk_acPayload]
  have e1 := blk_root_succ k
  have e2 := blk_parent_succ k
  have e3 := blk_slot (k + 1)
  have e4 := blk_proposer (k + 1)
  have e5 := blk_input (k + 1)
  generalize blk (k + 1) = B at *
  cases B
  simp only at e1 e2 e3 e4 e5
  subst e1 e2 e3 e4 e5
  rfl

theorem cnt_w0_four (k : Nat) : cnt w0 (4 * (k + 1)) = (k + 9) / 10 + k / 10 := by
  unfold cnt nrw nrv; rw [ite_eq_left rfl]; split_ifs <;> omega

theorem acOnTick_four {y : Fin sp.n} {A : SAState sp.n} {Φ : N.Frm} {s : Nat}
    (hj : A.restartTime = ⊥) : acOnTick sp y A Φ ((4 * s : Nat) : Int) = (A, []) := by
  rw [acOnTick_eq _ _ _ _ hj, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem other_w0 : other w0 = w1 := rfl

/-- **The rows an own block carries**: those of `v0`'s pool valid on its parent's chain state
and not yet on its chain. -/
theorem proposalAttestations_blk {fg : Store sp.toParams N.Payload} {k : Nat} (h : FGGood fg k)
    (ha : fg.atts = poolOf w0 ((k + 9) / 10 + k / 10)) :
    fg.proposalAttestations (blk k) = (blk (k + 1)).fgPayload := by
  classical
  unfold Store.proposalAttestations
  rw [ha, h.sigma k le_rfl, csN_eq]
  apply filter_eq_of_mem_iff (poolOf_nodup _ _)
  · rw [blk_fgPayload]; split_ifs <;> simp
  intro a
  simp only [decide_eq_true_eq]
  have hq := hgt_pos k
  rw [mem_poolOf, blk_fgPayload]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hv, hnc⟩
    unfold poolAt at hv hnc ⊢
    replace hv := (row_valid_iff (m := k) _ (by omega)).1 hv
    by_cases hpar : i % 2 = 0
    · rw [ite_eq_left hpar] at hnc ⊢
      rw [onChain_row0 h, not_and] at hnc
      have hc := hnc (by omega)
      unfold car0 at hc
      have hk1 : (k + 1) % 10 = 2 := by unfold hgt at hv; split_ifs at hv <;> omega
      rw [ite_eq_left hk1, hv]; exact List.mem_singleton_self _
    · rw [ite_eq_right hpar, other_w0] at hnc ⊢
      rw [onChain_row1 h, not_and] at hnc
      have hk1 : (k + 1) % 10 = 1 ∧ 11 ≤ k + 1 := by unfold hgt at hv; split_ifs at hv <;> omega
      rw [ite_eq_right (by omega), ite_eq_left hk1, hv]; exact List.mem_singleton_self _
  · intro hm
    split_ifs at hm with h1 h2
    · rw [List.mem_singleton] at hm; subst hm
      refine ⟨⟨2 * (hgt k - 1), ?_, ?_⟩, (row_valid_iff _ hq).2 rfl, ?_⟩
      · unfold hgt; split_ifs <;> omega
      · unfold poolAt; rw [ite_eq_left (by omega)]; congr 1; omega
      · rw [onChain_row0 h]; unfold car0 hgt; split_ifs <;> omega
    · rw [List.mem_singleton] at hm; subst hm
      refine ⟨⟨2 * (hgt k - 1) + 1, ?_, ?_⟩, (row_valid_iff _ hq).2 rfl, ?_⟩
      · unfold hgt; split_ifs <;> omega
      · unfold poolAt; rw [ite_eq_right (by omega), other_w0]; congr 1; omega
      · rw [onChain_row1 h]; unfold car1 hgt; split_ifs <;> omega
    · cases hm

/-- **`v0`'s tick at `t_s`**: the proposal of the block of slot `s` on the tip, its acceptance
and the vote for it. -/
theorem tick_propose {st : St} {s : Nat} (hs : 1 ≤ s) (h : Good st w0 (4 * s)) :
    ∃ st' e, Node.onTick prop dg w0 st ((4 * s : Nat) : Int) 0 =
      (st', [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.proposal, Node.frame st, []⟩,
        .fg (.block (blk s) true), .ac ⟨.block (blk s), Node.frame st', [e]⟩,
        .ac ⟨.toFG, Node.frame st', []⟩]) ∧
      e.msg = vote w0 s ∧ Voted st' w0 s := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hgood := h
  obtain ⟨hfg, hatts, hrec, hac⟩ := h
  rw [tip_four, Nat.add_sub_cancel] at hfg hac
  rw [rep_four, Nat.add_sub_cancel] at hac
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  change ChainFrame (Node.frame st) f (jx k) k at hf
  have hpk : st.ac.pool k = [vote w0 k, vote w1 k] := by
    rw [hac.pool]; unfold poolT; rw [tip_four, ite_eq_left ⟨by omega, by omega⟩]; rfl
  have hvst : ∀ y, st.ac.voteStamp (vote y k) < ⊤ := fun y => by
    rcases eq_w0_or_w1 y with rfl | rfl
    · rw [hac.vstamp k _ (by rw [← hac.pool, hpk]; exact List.mem_cons_self ..)]
      exact etime_of_lt_top _
    · have hm : vote w1 k ∈ poolT w0 (4 * (k + 1)) k := by
        rw [← hac.pool, hpk]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      rw [hac.vstamp k _ hm]
      exact etime_of_lt_top _
  have hbst : st.ac.blockStamp (blk k).root < ⊤ := by
    rcases Nat.lt_or_ge k 1 with h1 | h1
    · rw [show k = 0 by omega, blk_root_zero, hac.bstamp0]; exact WithBot.bot_lt_coe _
    · rw [hac.bstamp k h1 le_rfl]; exact etime_of_lt_top _
  obtain ⟨L₁, d, hprop, hd, hL₁, htip₁⟩ :=
    acProposal_tick hf hac.restart hpk hvst hbst hac.locks hac.tipLock
  set st₁ : St := { st with ac := { st.ac with locks := L₁ } }
  have hpa : st₁.fg.proposalAttestations (blk k) = (blk (k + 1)).fgPayload :=
    proposalAttestations_blk hfg (by rw [hatts, cnt_w0_four])
  have hns₁ : NS st₁ w0 k (cnt w0 (4 * (k + 1))) (nrw (4 * (k + 1))) (vsT (4 * (k + 1)))
      (poolT w0 (4 * (k + 1))) k k k k (nsv (4 * (k + 1))) :=
    ⟨hfg, hatts, hrec, ⟨hac.restart, hac.voted, hac.pool, hac.vstamp, hac.bstamp, hac.bstamp0,
      hac.saved, hL₁, htip₁, hac.latest, hac.reported⟩⟩
  obtain ⟨st₂, e, hob, hem, hv⟩ := onBlock_blk (y := w0) (s := k + 1) (by omega)
    (by rw [Nat.add_sub_cancel]; exact hns₁)
  obtain ⟨f₂, hf₂⟩ := fgGood_frame hv.fg
  change ChainFrame (Node.frame st₂) f₂ (jx (k + 1)) (k + 1) at hf₂
  have hfu := tickStep_fgUpdate_none (y := w0) (st := st₂) hf₂ hv.ac.locks
    (by have := hf₂.fj; have := jx_succ_le k; omega) (by omega) hv.ac.reported (4 * (k + 1)) 0
  have hP : tickStep prop dg w0 st ((4 * (k + 1) : Nat) : Int) 0 .proposal =
      (st₂, .ac ⟨.proposal, Node.frame st, []⟩ ::
        [.fg (.block (blk (k + 1)) true), .ac ⟨.block (blk (k + 1)), Node.frame st₂, [e]⟩]) := by
    simp only [tickStep]
    rw [ite_eq_left ((proposes_iff w0 _).2 ⟨rfl, by omega, by omega⟩)]
    simp only [Node.acProposal]
    rw [hprop]
    dsimp only
    rw [hd]
    unfold proposeBlock
    rw [mkBlock_blk hpa]
    exact congrArg (fun r => (r.1, _ :: r.2)) hob |>.trans rfl
  refine ⟨st₂, e, ?_, hem, hv⟩
  rw [onTick_eq', tickStep_acTick, acOnTick_four hac.restart]
  dsimp only
  rw [show ({ fg := st.fg, ac := st.ac, record := st.record } : St) = st from rfl, hP]
  dsimp only
  rw [hfu]
  rfl

/-! ## The other vote of a slot -/

theorem addLocks_tip {Φ : N.Frm} {f s : Nat} (h : ChainFrame Φ f (jx s) s) {L : Set Lock}
    (hL : LocksLe L (s - 1)) {t : Time} (hst : sp.slot t = s) :
    LocksLe (addLocks sp L Φ t s {((blk s).root, true, s + 2)}) s ∧
      (⟨(blk s).root, s, true, s + 2⟩ : Lock) ∈
        addLocks sp L Φ t s {((blk s).root, true, s + 2)} := by
  have hf : f ≤ s := le_trans h.fj (jx_le _)
  refine ⟨addLocks_le h (fun l hl => (hL l hl).imp fun _ hm => ⟨by omega, hm.2⟩) le_rfl _ _ ?_, ?_⟩
  · rintro p hp; rw [Set.mem_singleton_iff] at hp
    exact ⟨blk s, h.mem hf le_rfl, by rw [hp]⟩
  · exact h.mem_liveLocks (Or.inr ⟨_, rfl, rfl⟩) hf le_rfl rfl (by rw [hst]; dsimp only; omega)

/-- **The other validator's vote of slot `s ≥ 1`** at `t_s`: both votes are held, and the
optimistic check locks the block of slot `s` and records it as confirmed. -/
theorem deliver_vote {st : St} {y : Fin sp.n} {s : Nat} (hs : 1 ≤ s) (h : Voted st y s) :
    ∃ A', Node.onMessage y st ((4 * s : Nat) : Int) (vote (other y) s) =
      ({ st with ac := A' }, [.ac ⟨.message (vote (other y) s), Node.frame st, []⟩]) ∧
      NS { st with ac := A' } y s (cnt y (4 * s)) (nrw (4 * s + 1)) (vsT (4 * s + 1))
        (poolT y (4 * s + 1)) s s s (rep (4 * s + 1)) (nsv (4 * s + 1)) := by
  obtain ⟨hfg, hatts, hrec, hac⟩ := h
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  change ChainFrame (Node.frame st) f (jx s) s at hf
  have hst : sp.slot ((4 * s : Nat) : Int) = s := by rw [slot_nat]; omega
  have hpool : st.ac.pool s = [vote y s] := by rw [hac.pool, Function.update_self]
  rw [onMessage_eq, acOnMessage_other hst hpool (by rw [hac.voted])]
  have hsel := optimisticSelect_two hf hs hst
    (by rw [ts_nat, delta1]; change ((4 * s : Nat) : Int) < 4 * (s : Int) + 2 * 1; omega)
    (joined_of_bot hac.restart _) (y := y)
    (A := { st.ac with
      pool := Function.update st.ac.pool s [vote y s, vote (other y) s],
      voteStamp := Function.update st.ac.voteStamp (vote (other y) s)
        (ETime.of ((4 * s : Nat) : Int)) }) (Function.update_self _ _ _)
  rw [optimisticConfirmation_of_some hsel, hst]
  refine ⟨_, rfl, ?_⟩
  obtain ⟨hLk, htipk⟩ := addLocks_tip hf hac.locks hst
  have hnot : ¬ AncR (Node.frame st) (blk s) st.ac.latestConfirmed := by
    rintro ⟨R, hR, hr, ha⟩
    rw [hac.latest] at hr
    obtain ⟨rfl, -, -⟩ := hf.eq_of_root hR hr
    have := hf.le_of_anc ha; omega
  unfold updateLatestConfirmed
  rw [ite_eq_right hnot]
  have hp1 : poolT y (4 * s + 1) = Function.update (poolT y (4 * s)) s
      [vote y s, vote (other y) s] := by
    funext σ; unfold poolT; rw [Function.update_apply, tip_four1, tip_four]
    split_ifs <;> first | rfl | omega | (subst_vars; rfl)
  have hne := other_ne y
  refine ⟨hfg, hatts, ?_, ⟨hac.restart, ?_, ?_, ?_, ?_, hac.bstamp0, ?_,
    hLk, fun _ => htipk, rfl, by rw [rep_four1]; exact hac.reported⟩⟩
  · rw [nrw_succ_of (by omega)]; exact hrec
  · dsimp only; rw [hac.voted]; unfold vsT; rw [tip_four1, ite_eq_right (by omega)]
  · change Function.update st.ac.pool s _ = _
    rw [hp1, hac.pool, Function.update_idem]
  · intro σ x hx
    change Function.update st.ac.voteStamp (vote (other y) s) _ x = _
    rw [hp1, Function.update_apply] at hx
    split_ifs at hx with hσ
    · subst hσ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [Function.update_of_ne (fun he => hne (vote_inj he).1.symm)]
        exact hac.vstamp σ _ (by rw [Function.update_self]; exact List.mem_singleton_self _)
      · rw [Function.update_self]; unfold vt; rw [ite_eq_right (by omega)]
    · rw [Function.update_of_ne (fun he => by
        subst he; unfold poolT at hx; rw [tip_four] at hx
        split_ifs at hx with h2
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with he | he <;> have := (vote_inj he).2 <;> omega
        · cases hx)]
      exact hac.vstamp σ x (by rw [Function.update_of_ne hσ]; exact hx)
  · intro m h1 h2; exact hac.bstamp m h1 h2
  · intro j; dsimp only; rw [hac.saved, nsv_four, nsv_four1]

/-- After the other vote, the state before `t_s + Δ`, except for the row of `v1` that `v0`
receives later at `t_s` when `s ≡ 0 mod 10`. -/
theorem good_of_voted {st : St} {y : Fin sp.n} {s : Nat}
    (h : NS st y s (cnt y (4 * s)) (nrw (4 * s + 1)) (vsT (4 * s + 1)) (poolT y (4 * s + 1)) s s s
      (rep (4 * s + 1)) (nsv (4 * s + 1))) (hc : cnt y (4 * s + 1) = cnt y (4 * s)) :
    Good st y (4 * s + 1) := by
  unfold Good; rw [tip_four1, hc]; exact h

theorem cnt_four1 (y : Fin sp.n) (s : Nat) :
    cnt y (4 * s + 1) =
      if y = w0 ∧ s % 10 = 0 ∧ 10 ≤ s then cnt y (4 * s) + 1 else cnt y (4 * s) := by
  unfold cnt; rw [nrw_succ_of (by omega), nrv_four]
  split_ifs <;> first | rfl | omega

end Consensus.Goldilocks.Witness.TwoRun

end
