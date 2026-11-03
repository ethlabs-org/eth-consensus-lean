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

end Consensus.Goldilocks.Witness.TwoRun

end
