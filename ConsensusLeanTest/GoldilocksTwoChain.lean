module
public import ConsensusLeanTest.GoldilocksTwoRun
@[expose] public section

/-! # The healthy two-validator run: its chain

The chain that `v0` builds in the run of `GoldilocksTwoRun` (`n = 2`, `q = 2`, `k = c = 2`), with
its FG side:

* **The chain** (`blk`): genesis, then the own proposal of every slot `s + 1` on the block of slot
  `s`, carrying both slot-`s` votes (`vote`) as votes and support, and the rows (`row`): the
  first row of `v0` for the height of its parent's chain state when the parent's slot is
  `1 mod 10`, the row of `v1` for it when the parent's slot is `0 mod 10` (it reaches `v0`
  thirty-five time units after its signing).
* **Heights** (`hgt`): the chain state of the block of slot `m ≥ 1` is at height
  `(m − 1)/10 + 1`; height `q ≥ 2` is entered by the block of slot `ent q = 10(q − 1) + 1`,
  which justifies the entry of height `q − 1` and finalizes that of `q − 2` (the rows of a height
  carry the finality pair of the previous one). Height `1` is genesis's.
* **Chain states** (`cs`): explicit, and `cs_trans`: the state transition of each block of the
  chain on its parent's state. -/

namespace Consensus.Goldilocks.Witness.TwoRun

open SA Node

/-! ## The chain -/

/-- The index of the entry block of height `q`: genesis for `q ≤ 1`, else `10(q − 1) + 1`. -/
def ent (q : Nat) : Nat := if q ≤ 1 then 0 else 10 * (q - 1) + 1

/-- The height of the chain state of the block of slot `m`. -/
def hgt (m : Nat) : Nat := if m = 0 then 1 else (m - 1) / 10 + 1

/-- The row of `y` for height `q`, read off the blocks `f`: the target is the entry of height
`q`, the finality pair the entry of height `q − 1` (none at height `1`). -/
def rowF (f : Nat → N.Blk) (y : Fin sp.n) (q : Nat) : FG.Att sp.n :=
  ⟨y, q, (f (ent q)).root, false, if q ≤ 1 then none else some (q - 1, (f (ent (q - 1))).root)⟩

/-- The rows the block of slot `s + 1` carries. -/
def attsF (f : Nat → N.Blk) (s : Nat) : List (FG.Att sp.n) :=
  if (s + 1) % 10 = 2 then [rowF f w0 (hgt s)]
  else if (s + 1) % 10 = 1 ∧ 11 ≤ s + 1 then [rowF f w1 (hgt s)] else []

/-- The two votes of slot `s` on the block `B`. -/
def votesOn (s : Nat) (B : N.Blk) : List (Vote sp.n) := [⟨w0, s, B.root⟩, ⟨w1, s, B.root⟩]

/-- The block of slot `s + 1` on the block `f s`. -/
noncomputable def mkF (f : Nat → N.Blk) (s : Nat) : N.Blk :=
  ⟨dg (some (f s).root) (s + 1) 0 (attsF f s) (votesOn s (f s), votesOn s (f s)),
    some (f s).root, s + 1, w0, 0, attsF f s, (votesOn s (f s), votesOn s (f s))⟩

/-- The blocks up to slot `m` (the rest junk). -/
noncomputable def blks : Nat → Nat → N.Blk
  | 0 => fun _ => sp.toParams.genesisBlock N.genesisPayload
  | m + 1 => Function.update (blks m) (m + 1) (mkF (blks m) m)

/-- **The block of slot `m`.** -/
noncomputable def blk (m : Nat) : N.Blk := blks m m

theorem blks_eq : ∀ m i, i ≤ m → blks m i = blk i
  | 0, i, h => by rw [Nat.le_zero.1 h]; rfl
  | m + 1, i, h => by
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · change Function.update (blks m) (m + 1) _ i = _
      rw [Function.update_of_ne (by omega), blks_eq m i (by omega)]
    · rw [show i = m + 1 by omega]; rfl

theorem ent_le_of {q s : Nat} (hq : q ≤ hgt s) (hs : 1 ≤ s) : ent q ≤ s := by
  unfold ent hgt at *; split_ifs at * <;> omega

theorem blk_zero : blk 0 = sp.toParams.genesisBlock N.genesisPayload := rfl

theorem blk_succ (s : Nat) : blk (s + 1) = mkF blk s := by
  change Function.update (blks s) (s + 1) (mkF (blks s) s) (s + 1) = _
  rw [Function.update_self]
  have hf : ∀ i ≤ s, blks s i = blk i := blks_eq s
  unfold mkF attsF rowF
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rfl
  · have h1 := hf _ (ent_le_of le_rfl hs)
    have h2 := hf _ (ent_le_of (Nat.sub_le (hgt s) 1) hs)
    rw [hf s le_rfl, h1, h2]

/-- The row of `y` for height `q`. -/
noncomputable def row (y : Fin sp.n) (q : Nat) : FG.Att sp.n := rowF blk y q

/-- The vote of `y` in slot `σ`: on the block of slot `σ`. -/
noncomputable def vote (y : Fin sp.n) (σ : Nat) : Vote sp.n := ⟨y, σ, (blk σ).root⟩

theorem blk_slot : ∀ m, (blk m).slot = m
  | 0 => rfl
  | _ + 1 => by rw [blk_succ]; rfl

theorem blk_parent_succ (s : Nat) : (blk (s + 1)).parent = some (blk s).root := by
  rw [blk_succ]; rfl

theorem blk_parent_zero : (blk 0).parent = none := rfl

theorem blk_root_zero : (blk 0).root = 0 := rfl

theorem blk_proposer : ∀ m, (blk m).proposer = w0
  | 0 => rfl
  | _ + 1 => by rw [blk_succ]; rfl

theorem blk_input : ∀ m, (blk m).input = 0
  | 0 => rfl
  | _ + 1 => by rw [blk_succ]; rfl

theorem blk_fgPayload (s : Nat) : (blk (s + 1)).fgPayload =
    if (s + 1) % 10 = 2 then [row w0 (hgt s)]
    else if (s + 1) % 10 = 1 ∧ 11 ≤ s + 1 then [row w1 (hgt s)] else [] := by
  rw [blk_succ]; rfl

theorem blk_fgPayload_zero : (blk 0).fgPayload = [] := rfl

theorem blk_acPayload (s : Nat) :
    (blk (s + 1)).acPayload = ([vote w0 s, vote w1 s], [vote w0 s, vote w1 s]) := by
  rw [blk_succ]; rfl

theorem blk_root_succ (s : Nat) : (blk (s + 1)).root =
    dg (some (blk s).root) (s + 1) 0 (blk (s + 1)).fgPayload (blk (s + 1)).acPayload := by
  rw [blk_succ]; rfl

theorem blk_root_succ_ne (s : Nat) : (blk (s + 1)).root ≠ 0 := by
  rw [blk_root_succ]
  unfold dg
  rw [ite_eq_right (by simp [genContent])]
  omega

theorem blk_root_inj : ∀ {m m' : Nat}, (blk m).root = (blk m').root → m = m'
  | 0, 0, _ => rfl
  | 0, m' + 1, h => absurd h.symm (blk_root_succ_ne m')
  | m + 1, 0, h => absurd h (blk_root_succ_ne m)
  | m + 1, m' + 1, h => by
    rw [blk_root_succ, blk_root_succ] at h
    have := dg_injective h
    simp only [Prod.mk.injEq] at this
    omega

theorem blk_inj {m m' : Nat} (h : blk m = blk m') : m = m' := blk_root_inj (by rw [h])

theorem blk_injective : Function.Injective blk := fun _ _ h => blk_inj h

theorem row_h (y : Fin sp.n) (q : Nat) : (row y q).h = q := rfl

theorem row_T (y : Fin sp.n) (q : Nat) : (row y q).T = (blk (ent q)).root := rfl

theorem row_val (y : Fin sp.n) (q : Nat) : (row y q).val = y := rfl

theorem row_timeout (y : Fin sp.n) (q : Nat) : (row y q).timeout = false := rfl

theorem row_fin (y : Fin sp.n) (q : Nat) : (row y q).fin =
    if q ≤ 1 then none else some (q - 1, (blk (ent (q - 1))).root) := rfl

theorem row_inj {y y' : Fin sp.n} {q q' : Nat} (h : row y q = row y' q') : y = y' ∧ q = q' :=
  ⟨by rw [← row_val y q, h, row_val], by rw [← row_h y q, h, row_h]⟩

theorem row_wellFormed (y : Fin sp.n) {q : Nat} (hq : 1 ≤ q) : (row y q).WellFormed := by
  refine ⟨hq, fun p hp => ?_⟩
  rw [row_fin] at hp
  split_ifs at hp with h
  · simp at hp
  · simp only [Option.toList_some, List.mem_singleton] at hp; subst hp; change q - 1 < q; omega

theorem vote_val (y : Fin sp.n) (σ : Nat) : (vote y σ).val = y := rfl

theorem vote_slot (y : Fin sp.n) (σ : Nat) : (vote y σ).slot = σ := rfl

theorem vote_head (y : Fin sp.n) (σ : Nat) : (vote y σ).head = (blk σ).root := rfl

theorem vote_inj {y y' : Fin sp.n} {σ σ' : Nat} (h : vote y σ = vote y' σ') : y = y' ∧ σ = σ' :=
  ⟨by rw [← vote_val y σ, h, vote_val], by rw [← vote_slot y σ, h, vote_slot]⟩

/-! ## Heights -/

theorem hgt_pos (m : Nat) : 1 ≤ hgt m := by unfold hgt; split_ifs <;> omega

theorem hgt_succ_of {m : Nat} (h : ¬ ((m + 1) % 10 = 1 ∧ 11 ≤ m + 1)) : hgt (m + 1) = hgt m := by
  rw [not_and_or] at h
  unfold hgt; split_ifs <;> first | omega | simp_all

theorem hgt_succ_entry {m : Nat} (h : (m + 1) % 10 = 1 ∧ 11 ≤ m + 1) :
    hgt (m + 1) = hgt m + 1 := by
  obtain ⟨h1, h2⟩ := h
  unfold hgt; split_ifs <;> first | omega | simp_all

theorem ent_hgt_le (m : Nat) : ent (hgt m) ≤ m := by unfold ent hgt; split_ifs <;> omega

theorem ent_mono {q q' : Nat} (h : q ≤ q') : ent q ≤ ent q' := by unfold ent; split_ifs <;> omega

theorem hgt_ent {q : Nat} (hq : 1 ≤ q) : hgt (ent q) = q := by
  unfold hgt ent; split_ifs <;> first | omega | simp_all

theorem hgt_mono {m m' : Nat} (h : m ≤ m') : hgt m ≤ hgt m' := by unfold hgt; split_ifs <;> omega

theorem ent_hgt_succ_entry {m : Nat} (h : (m + 1) % 10 = 1 ∧ 11 ≤ m + 1) :
    ent (hgt (m + 1)) = m + 1 := by
  unfold ent hgt; split_ifs <;> omega

/-! ## Chain states -/

/-- The finality bits of the chain state of the block of slot `m`. -/
def finOf (m : Nat) : Nat → Finset (Fin sp.toParams.fg.n) := fun i =>
  if 1 ≤ i ∧ i + 1 < hgt m then {w0, w1}
  else if i + 1 = hgt m ∧ 2 ≤ hgt m ∧ m % 10 ≠ 1 then {w0} else ∅

/-- **The chain state of the block of slot `m`.** -/
noncomputable def cs (m : Nat) : FG.ChainState sp.toParams.fg.n :=
  if m = 0 then FG.ChainState.init sp.toParams.fg else
  { L := (blk m).root
    s := m
    h := hgt m
    Th := (blk (ent (hgt m))).root
    ThSlot := ent (hgt m)
    target := if m % 10 = 1 then ∅ else {w0}
    prog := if m % 10 = 1 then ∅ else {w0}
    pending := if hgt m ≤ 1 then [] else [(hgt m - 1, (blk (ent (hgt m - 1))).root)]
    fin := finOf m
    J := (blk (ent (hgt m - 1))).root
    hj := hgt m - 1
    F := (blk (ent (hgt m - 2))).root
    hF := hgt m - 2 }

theorem cs_zero : cs 0 = FG.ChainState.init sp.toParams.fg := rfl

theorem cs_pos {m : Nat} (hm : m ≠ 0) : cs m =
  { L := (blk m).root
    s := m
    h := hgt m
    Th := (blk (ent (hgt m))).root
    ThSlot := ent (hgt m)
    target := if m % 10 = 1 then ∅ else {w0}
    prog := if m % 10 = 1 then ∅ else {w0}
    pending := if hgt m ≤ 1 then [] else [(hgt m - 1, (blk (ent (hgt m - 1))).root)]
    fin := finOf m
    J := (blk (ent (hgt m - 1))).root
    hj := hgt m - 1
    F := (blk (ent (hgt m - 2))).root
    hF := hgt m - 2 } := by
  unfold cs; exact ite_eq_right hm

theorem cs_s (m : Nat) : (cs m).s = m := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_h (m : Nat) : (cs m).h = hgt m := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_Th (m : Nat) : (cs m).Th = (blk (ent (hgt m))).root := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_J (m : Nat) : (cs m).J = (blk (ent (hgt m - 1))).root := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_hj (m : Nat) : (cs m).hj = hgt m - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_F (m : Nat) : (cs m).F = (blk (ent (hgt m - 2))).root := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_pending (m : Nat) : (cs m).pending =
    if hgt m ≤ 1 then [] else [(hgt m - 1, (blk (ent (hgt m - 1))).root)] := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_target (m : Nat) : (cs m).target = if m % 10 = 1 ∨ m = 0 then ∅ else {w0} := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]; simp only [show m ≠ 0 by omega, or_false]


theorem cs_L (m : Nat) : (cs m).L = (blk m).root := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_ThSlot (m : Nat) : (cs m).ThSlot = ent (hgt m) := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_prog (m : Nat) : (cs m).prog = if m % 10 = 1 ∨ m = 0 then ∅ else {w0} := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]; simp only [show m ≠ 0 by omega, or_false]

theorem cs_fin (m : Nat) : (cs m).fin = finOf m := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · funext i; simp [cs_zero, FG.ChainState.init, finOf, hgt]
  · rw [cs_pos (by omega)]

theorem cs_hF (m : Nat) : (cs m).hF = hgt m - 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · rfl
  · rw [cs_pos (by omega)]

theorem cs_ext {X Y : FG.ChainState sp.toParams.fg.n} (h1 : X.L = Y.L) (h2 : X.s = Y.s)
    (h3 : X.h = Y.h)
    (h4 : X.Th = Y.Th) (h5 : X.ThSlot = Y.ThSlot) (h6 : X.target = Y.target)
    (h7 : X.prog = Y.prog) (h8 : X.pending = Y.pending) (h9 : X.fin = Y.fin) (h10 : X.J = Y.J)
    (h11 : X.hj = Y.hj) (h12 : X.F = Y.F) (h13 : X.hF = Y.hF) : X = Y := by
  cases X; cases Y; dsimp only at *; subst_vars; rfl

/-! ## The state transition, generically -/

section Generic

variable (gp : FG.FGParams)

theorem stateTransition_eq {σ : FG.ChainState gp.n} {B : FG.FGBlock gp.n} (hs : σ.s < B.slot)
    (ha : ∀ a ∈ B.atts, a.WellFormed ∧ σ.validAtt a) :
    gp.stateTransition σ B =
      some (gp.heightEvents { B.atts.foldl FG.ChainState.processAtt { σ with s := B.slot } with
        L := B.root }) := by
  unfold FG.FGParams.stateTransition; exact ite_eq_left ⟨hs, ha⟩

theorem heightEvents_stay {σ : FG.ChainState gp.n} (h1 : ¬ gp.justifies (gp.finalizePrune σ))
    (h2 : ¬ gp.timesOut (gp.finalizePrune σ)) : gp.heightEvents σ = gp.finalizePrune σ := by
  unfold FG.FGParams.heightEvents; dsimp only; rw [ite_eq_right h1, ite_eq_right h2]

theorem heightEvents_just {σ : FG.ChainState gp.n} (h1 : gp.justifies (gp.finalizePrune σ)) :
    gp.heightEvents σ = let σ₁ := gp.finalizePrune σ
      let ps := σ₁.pending ++ [(σ₁.h, σ₁.Th)]
      FG.ChainState.advance
        { σ₁ with J := σ₁.Th, hj := σ₁.h, pending := ps.drop (ps.length - 2),
                  fin := Function.update σ₁.fin σ₁.h ∅ } := by
  unfold FG.FGParams.heightEvents; dsimp only; rw [ite_eq_left h1]; rfl

theorem finalizePrune_none {σ : FG.ChainState gp.n} (h : gp.bestFinal σ = none) :
    gp.finalizePrune σ = { σ with pending := σ.pending.filter (fun p => σ.hF < p.1) } := by
  unfold FG.FGParams.finalizePrune; rw [h]

theorem finalizePrune_some {σ : FG.ChainState gp.n} {p : Nat × Nat} (h : gp.bestFinal σ = some p) :
    gp.finalizePrune σ =
      { σ with F := p.2, hF := p.1, pending := σ.pending.filter (fun p' => p.1 < p'.1) } := by
  unfold FG.FGParams.finalizePrune; rw [h]

theorem bestFinal_nil {σ : FG.ChainState gp.n} (h : σ.pending = []) : gp.bestFinal σ = none := by
  unfold FG.FGParams.bestFinal; rw [h]; rfl

theorem bestFinal_one_lt {σ : FG.ChainState gp.n} {p : Nat × Nat} (h : σ.pending = [p])
    (hc : (σ.fin p.1).card < gp.q) : gp.bestFinal σ = none := by
  unfold FG.FGParams.bestFinal; rw [h]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [ite_eq_right (by omega)]

theorem bestFinal_one_ge {σ : FG.ChainState gp.n} {p : Nat × Nat} (h : σ.pending = [p])
    (hc : gp.q ≤ (σ.fin p.1).card) : gp.bestFinal σ = some p := by
  unfold FG.FGParams.bestFinal; rw [h]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [ite_eq_left hc]

/-- An attestation for the chain's own entry, its finality pair pending or absent. -/
theorem processAtt_own {σ : FG.ChainState gp.n} {a : FG.Att gp.n} (hh : a.h = σ.h)
    (hT : a.T = σ.Th) (hto : a.timeout = false) (hf : ∀ p ∈ a.fin, p ∈ σ.pending) :
    σ.processAtt a =
      { σ with prog := insert a.val σ.prog, target := insert a.val σ.target,
               fin := match a.fin with
                 | some p => Function.update σ.fin p.1 (insert a.val (σ.fin p.1))
                 | none => σ.fin } := by
  unfold FG.ChainState.processAtt
  rcases hfa : a.fin with _ | p
  · dsimp only; rw [ite_eq_left ⟨hh, hT⟩, hto]; rfl
  · dsimp only
    rw [ite_eq_left (hf p (by rw [hfa]; rfl))]
    dsimp only
    rw [ite_eq_left ⟨hh, hT⟩, hto]; rfl

theorem heightEvents_quiet {σ : FG.ChainState gp.n}
    (hpend : σ.pending = [] ∨ ∃ p, σ.pending = [p] ∧ (σ.fin p.1).card < gp.q ∧ σ.hF < p.1)
    (ht : σ.target.card < gp.q) (hpr : σ.prog.card < gp.q) : gp.heightEvents σ = σ := by
  have hfp : gp.finalizePrune σ = σ := by
    rcases hpend with h | ⟨p, h, hc, hl⟩
    · rw [finalizePrune_none gp (bestFinal_nil gp h)]; simp only [h, List.filter_nil]; rw [← h]
    · rw [finalizePrune_none gp (bestFinal_one_lt gp h hc), h]
      simp only [List.filter_cons, hl, decide_true, ite_true, List.filter_nil]
      rw [← h]
  rw [heightEvents_stay gp (by rw [hfp]; unfold FG.FGParams.justifies; omega)
    (by rw [hfp]; unfold FG.FGParams.timesOut; omega), hfp]

theorem st_nil {σ : FG.ChainState gp.n} {B : FG.FGBlock gp.n} (hs : σ.s < B.slot)
    (hb : B.atts = []) :
    gp.stateTransition σ B = some (gp.heightEvents { σ with s := B.slot, L := B.root }) := by
  rw [stateTransition_eq gp hs (by rw [hb]; intro a ha; cases ha), hb]; rfl

theorem st_own {σ : FG.ChainState gp.n} {B : FG.FGBlock gp.n} {a : FG.Att gp.n}
    (hs : σ.s < B.slot) (hb : B.atts = [a]) (hwf : a.WellFormed) (hh : a.h = σ.h)
    (hT : a.T = σ.Th) (hto : a.timeout = false) (hf : ∀ p ∈ a.fin, p ∈ σ.pending) :
    gp.stateTransition σ B = some (gp.heightEvents
      { σ with s := B.slot, L := B.root, prog := insert a.val σ.prog,
               target := insert a.val σ.target,
               fin := match a.fin with
                 | some p => Function.update σ.fin p.1 (insert a.val (σ.fin p.1))
                 | none => σ.fin }) := by
  rw [stateTransition_eq gp hs (by
    rw [hb]; intro a' ha
    cases ha with
    | head => exact ⟨hwf, Or.inl ⟨hh, hT⟩⟩
    | tail _ h => cases h), hb, List.foldl_cons, List.foldl_nil,
    processAtt_own gp (σ := { σ with s := B.slot }) hh hT hto hf]


theorem st_own_none {σ : FG.ChainState gp.n} {B : FG.FGBlock gp.n} {a : FG.Att gp.n}
    (hs : σ.s < B.slot) (hb : B.atts = [a]) (hwf : a.WellFormed) (hh : a.h = σ.h)
    (hT : a.T = σ.Th) (hto : a.timeout = false) (hfa : a.fin = none) :
    gp.stateTransition σ B = some (gp.heightEvents
      { σ with s := B.slot, L := B.root, prog := insert a.val σ.prog,
               target := insert a.val σ.target }) := by
  rw [st_own gp hs hb hwf hh hT hto (by rw [hfa]; intro p hp; cases hp)]
  simp only [hfa]

theorem st_own_some {σ : FG.ChainState gp.n} {B : FG.FGBlock gp.n} {a : FG.Att gp.n}
    {p : Nat × Nat} (hs : σ.s < B.slot) (hb : B.atts = [a]) (hwf : a.WellFormed)
    (hh : a.h = σ.h) (hT : a.T = σ.Th) (hto : a.timeout = false) (hfa : a.fin = some p)
    (hp : p ∈ σ.pending) :
    gp.stateTransition σ B = some (gp.heightEvents
      { σ with s := B.slot, L := B.root, prog := insert a.val σ.prog,
               target := insert a.val σ.target,
               fin := Function.update σ.fin p.1 (insert a.val (σ.fin p.1)) }) := by
  rw [st_own gp hs hb hwf hh hT hto (by rw [hfa]; intro p' hp'; cases hp'; exact hp)]
  simp only [hfa]

end Generic

theorem card_w0 : ({w0} : Finset (Fin sp.n)).card = 1 := rfl

theorem card_w01 : ({w0, w1} : Finset (Fin sp.n)).card = 2 := by decide

theorem finOf_card_lt (m : Nat) : (finOf m (hgt m - 1)).card < 2 := by
  unfold finOf
  rw [ite_eq_right (by unfold hgt; split_ifs <;> omega)]
  split_ifs
  · exact Nat.lt_of_le_of_lt (le_of_eq card_w0) (by omega)
  · simp

theorem gp_q : sp.toParams.fg.q = 2 := rfl

/-- The transition of a block that carries no row. -/
theorem cs_trans_plain {m : Nat} (hm : ¬ (m + 1) % 10 = 2)
    (hm' : ¬ ((m + 1) % 10 = 1 ∧ 11 ≤ m + 1)) :
    sp.toParams.fg.stateTransition (cs m) (blk (m + 1)).fgView = some (cs (m + 1)) := by
  have hp : (blk (m + 1)).fgPayload = [] := by
    rw [blk_fgPayload, ite_eq_right hm, ite_eq_right hm']
  have hh := hgt_succ_of hm'
  have hm'' := hm'
  rw [not_and_or] at hm''
  rw [st_nil sp.toParams.fg (σ := cs m) (B := (blk (m + 1)).fgView)
    (by change (cs m).s < (blk (m + 1)).slot; rw [cs_s, blk_slot]; omega) hp,
    heightEvents_quiet]
  · congr 1
    apply cs_ext <;> dsimp only
    · rw [cs_L]; try rfl
    · rw [cs_s]; exact blk_slot _
    · rw [cs_h, cs_h, hh]
    · rw [cs_Th, cs_Th, hh]
    · rw [cs_ThSlot, cs_ThSlot, hh]
    · rw [cs_target, cs_target]
      split_ifs <;> first | rfl | (simp only [or_false, not_or] at *; omega)
    · rw [cs_prog, cs_prog]
      split_ifs <;> first | rfl | (simp only [or_false, not_or] at *; omega)
    · rw [cs_pending, cs_pending, hh]
    · rw [cs_fin, cs_fin]; funext i; unfold finOf; rw [hh]
      have hg0 : m = 0 → hgt m = 1 := by rintro rfl; rfl
      split_ifs <;> first | rfl | (simp only [not_and_or] at *; omega)
    · rw [cs_J, cs_J, hh]
    · rw [cs_hj, cs_hj, hh]
    · rw [cs_F, cs_F, hh]
    · rw [cs_hF, cs_hF, hh]
  · dsimp only
    rw [cs_pending]
    split_ifs with h1
    · exact Or.inl rfl
    · refine Or.inr ⟨_, rfl, ?_, ?_⟩
      · rw [cs_fin]; exact finOf_card_lt m
      · rw [cs_hF]; omega
  · dsimp only; rw [cs_target]; split_ifs <;> decide
  · dsimp only; rw [cs_prog]; split_ifs <;> decide

theorem row_fin_mem {m : Nat} (y : Fin sp.n) :
    ∀ p ∈ (row y (hgt m)).fin, p ∈ (cs m).pending := by
  intro p hpm
  rw [row_fin] at hpm
  rw [cs_pending]
  split_ifs at hpm ⊢ with h1
  · cases hpm
  · cases hpm; exact List.mem_singleton_self _

/-- The transition of the block that carries the first row of `v0` for a height. -/
theorem cs_trans_row0 {m : Nat} (hm : (m + 1) % 10 = 2) :
    sp.toParams.fg.stateTransition (cs m) (blk (m + 1)).fgView = some (cs (m + 1)) := by
  have hp : (blk (m + 1)).fgPayload = [row w0 (hgt m)] := by
    rw [blk_fgPayload, ite_eq_left hm]
  have hm' : ¬ ((m + 1) % 10 = 1 ∧ 11 ≤ m + 1) := by omega
  have hh := hgt_succ_of hm'
  have hm0 : m ≠ 0 := by omega
  have hq := hgt_pos m
  have hs : (cs m).s < (blk (m + 1)).fgView.slot := by
    change (cs m).s < (blk (m + 1)).slot; rw [cs_s, blk_slot]; omega
  have hf1 : finOf m (hgt m - 1) = ∅ := by
    unfold finOf; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have htg : (cs m).target = ∅ := by rw [cs_target, ite_eq_left (Or.inl (by omega))]
  have hpg : (cs m).prog = ∅ := by rw [cs_prog, ite_eq_left (Or.inl (by omega))]
  have hcommon : ∀ (fin' : Nat → Finset (Fin sp.toParams.fg.n)), fin' = finOf (m + 1) →
      sp.toParams.fg.heightEvents
        { cs m with s := (blk (m + 1)).fgView.slot, L := (blk (m + 1)).fgView.root,
                    prog := insert w0 (cs m).prog, target := insert w0 (cs m).target,
                    fin := fin' } = cs (m + 1) := by
    rintro fin' rfl
    rw [heightEvents_quiet]
    · apply cs_ext <;> dsimp only
      · rw [cs_L]; try rfl
      · rw [cs_s]; exact blk_slot _
      · rw [cs_h, cs_h, hh]
      · rw [cs_Th, cs_Th, hh]
      · rw [cs_ThSlot, cs_ThSlot, hh]
      · rw [cs_target (m + 1), htg, ite_eq_right (by omega)]; rfl
      · rw [cs_prog (m + 1), hpg, ite_eq_right (by omega)]; rfl
      · rw [cs_pending, cs_pending, hh]
      · rw [cs_fin]
      · rw [cs_J, cs_J, hh]
      · rw [cs_hj, cs_hj, hh]
      · rw [cs_F, cs_F, hh]
      · rw [cs_hF, cs_hF, hh]
    · dsimp only
      rw [cs_pending]
      split_ifs with h1
      · exact Or.inl rfl
      · refine Or.inr ⟨_, rfl, ?_, ?_⟩
        · unfold finOf; rw [hh]
          rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega, by omega⟩]; decide
        · rw [cs_hF]; omega
    · dsimp only; rw [htg]; decide
    · dsimp only; rw [hpg]; decide
  rcases Nat.lt_or_ge (hgt m) 2 with h2 | h2
  · rw [st_own_none sp.toParams.fg (σ := cs m) (B := (blk (m + 1)).fgView) (a := row w0 (hgt m))
      hs hp (row_wellFormed w0 hq) (by rw [row_h, cs_h]) (by rw [row_T, cs_Th]) rfl
      (by rw [row_fin, ite_eq_left (by omega)])]
    congr 1
    refine hcommon (cs m).fin ?_
    rw [cs_fin]; funext i; unfold finOf; rw [hh]; split_ifs <;> first | rfl | omega
  · rw [st_own_some sp.toParams.fg (σ := cs m) (B := (blk (m + 1)).fgView) (a := row w0 (hgt m))
      hs hp (row_wellFormed w0 hq) (by rw [row_h, cs_h]) (by rw [row_T, cs_Th]) rfl
      (by rw [row_fin, ite_eq_right (by omega)])
      (by rw [cs_pending, ite_eq_right (by omega)]; exact List.mem_singleton_self _)]
    congr 1
    apply hcommon
    rw [cs_fin]; funext i
    rw [Function.update_apply]
    dsimp only
    rw [hf1]
    unfold finOf; rw [hh]
    split_ifs <;> first | rfl | omega

theorem pair_comm' : ({w1, w0} : Finset (Fin sp.toParams.fg.n)) = {w0, w1} := by decide

/-- The transition of the block that carries the row of `v1` for a height: it justifies the
height's entry (and finalizes the previous entry) and enters the next height. -/
theorem cs_trans_entry {m : Nat} (hm : (m + 1) % 10 = 1 ∧ 11 ≤ m + 1) :
    sp.toParams.fg.stateTransition (cs m) (blk (m + 1)).fgView = some (cs (m + 1)) := by
  have hp : (blk (m + 1)).fgPayload = [row w1 (hgt m)] := by
    rw [blk_fgPayload, ite_eq_right (by omega), ite_eq_left hm]
  have hh := hgt_succ_entry hm
  have he := ent_hgt_succ_entry hm
  have hm0 : m ≠ 0 := by omega
  have hq := hgt_pos m
  have hs : (cs m).s < (blk (m + 1)).fgView.slot := by
    change (cs m).s < (blk (m + 1)).slot; rw [cs_s, blk_slot]; omega
  have htg : (cs m).target = {w0} := by rw [cs_target, ite_eq_right (by omega)]
  have hpg : (cs m).prog = {w0} := by rw [cs_prog, ite_eq_right (by omega)]
  have htg2 : (insert w1 (cs m).target).card = 2 := by rw [htg]; decide
  rcases Nat.lt_or_ge (hgt m) 2 with h2 | h2
  · -- height `1`: no finality pair
    have hq' : hgt m = 1 := by omega
    rw [st_own_none sp.toParams.fg (σ := cs m) (B := (blk (m + 1)).fgView) (a := row w1 (hgt m))
      hs hp (row_wellFormed w1 hq) (by rw [row_h, cs_h]) (by rw [row_T, cs_Th]) rfl
      (by rw [row_fin, ite_eq_left (by omega)])]
    have hb : ∀ σ : FG.ChainState sp.toParams.fg.n, σ.pending = (cs m).pending →
        sp.toParams.fg.bestFinal σ = none := fun σ h =>
      bestFinal_nil _ (by rw [h, cs_pending, ite_eq_left (by omega)])
    rw [heightEvents_just _ (by
      rw [finalizePrune_none]
      · refine ⟨by dsimp only; rw [gp_q]; exact le_of_eq htg2.symm, Or.inl ?_⟩
        dsimp only; unfold FG.ChainState.previousHeightJustified; rw [cs_hj]; omega
      · exact hb _ rfl), finalizePrune_none]
    swap; · exact hb _ rfl
    congr 1
    apply cs_ext <;> dsimp only [FG.ChainState.advance]
    · rw [cs_L]; rfl
    · rw [cs_s]; exact blk_slot _
    · rw [cs_h, cs_h, hh]
    · rw [cs_Th, he]; rfl
    · rw [cs_ThSlot, he]; exact blk_slot _
    · rw [cs_target, ite_eq_left (Or.inl hm.1)]
    · rw [cs_prog, ite_eq_left (Or.inl hm.1)]
    · rw [cs_pending, cs_pending, ite_eq_left (by omega), ite_eq_right (by omega), cs_h,
        cs_Th, hh, Nat.add_sub_cancel]; rfl
    · rw [cs_fin, cs_fin, cs_h]; funext i
      rw [Function.update_apply]; unfold finOf; rw [hh]
      split_ifs <;> first | rfl | omega
    · rw [cs_Th, cs_J, hh, Nat.add_sub_cancel]
    · rw [cs_h, cs_hj, hh, Nat.add_sub_cancel]
    · rw [cs_F, cs_F, hh, hq']
    · rw [cs_hF, cs_hF, hh, hq']
  · -- height `q ≥ 2`: the finality pair of the previous entry completes
    have hpd : (cs m).pending = [(hgt m - 1, (blk (ent (hgt m - 1))).root)] := by
      rw [cs_pending, ite_eq_right (by omega)]
    have hf1 : finOf m (hgt m - 1) = {w0} := by
      unfold finOf; rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, h2, by omega⟩]
    rw [st_own_some sp.toParams.fg (σ := cs m) (B := (blk (m + 1)).fgView) (a := row w1 (hgt m))
      (p := (hgt m - 1, (blk (ent (hgt m - 1))).root))
      hs hp (row_wellFormed w1 hq) (by rw [row_h, cs_h]) (by rw [row_T, cs_Th]) rfl
      (by rw [row_fin, ite_eq_right (by omega)])
      (by rw [hpd]; exact List.mem_singleton_self _)]
    have hb : ∀ σ : FG.ChainState sp.toParams.fg.n, σ.pending = (cs m).pending →
        σ.fin (hgt m - 1) = {w0, w1} →
        sp.toParams.fg.bestFinal σ = some (hgt m - 1, (blk (ent (hgt m - 1))).root) :=
      fun σ h hf => bestFinal_one_ge _ (by rw [h, hpd]) (by rw [hf, gp_q]; decide)
    have hfu : Function.update (cs m).fin (hgt m - 1, (blk (ent (hgt m - 1))).root).1
        (insert (row w1 (hgt m)).val ((cs m).fin (hgt m - 1, (blk (ent (hgt m - 1))).root).1))
        (hgt m - 1) = {w0, w1} := by
      simp only [Function.update_self]; rw [cs_fin, hf1]; exact pair_comm'
    rw [heightEvents_just _ (by
      rw [finalizePrune_some]
      case h => exact hb _ (by rfl) (by exact hfu)
      refine ⟨by dsimp only; rw [gp_q]; exact le_of_eq htg2.symm, Or.inr ?_⟩
      dsimp only; rw [cs_hj]), finalizePrune_some]
    case h => exact hb _ (by rfl) (by exact hfu)
    congr 1
    apply cs_ext <;> dsimp only [FG.ChainState.advance]
    · rw [cs_L]; rfl
    · rw [cs_s]; exact blk_slot _
    · rw [cs_h, cs_h, hh]
    · rw [cs_Th, he]; rfl
    · rw [cs_ThSlot, he]; exact blk_slot _
    · rw [cs_target, ite_eq_left (Or.inl hm.1)]
    · rw [cs_prog, ite_eq_left (Or.inl hm.1)]
    · rw [hpd, cs_pending, ite_eq_right (by omega), cs_h, cs_Th, hh, Nat.add_sub_cancel]
      simp
    · rw [cs_fin, cs_fin, cs_h]; funext i
      rw [Function.update_apply, Function.update_apply, hf1]
      change _ = finOf (m + 1) i
      unfold finOf; rw [hh]
      split_ifs <;> first | rfl | omega | exact pair_comm'
    · rw [cs_Th, cs_J, hh, Nat.add_sub_cancel]
    · rw [cs_h, cs_hj, hh, Nat.add_sub_cancel]
    · rw [cs_F, hh]; congr 3
    · rw [cs_hF, hh]; omega

/-- **The chain states along the chain.** -/
theorem cs_trans (m : Nat) :
    sp.toParams.fg.stateTransition (cs m) (blk (m + 1)).fgView = some (cs (m + 1)) := by
  by_cases h1 : (m + 1) % 10 = 2
  · exact cs_trans_row0 h1
  · by_cases h2 : (m + 1) % 10 = 1 ∧ 11 ≤ m + 1
    · exact cs_trans_entry h2
    · exact cs_trans_plain h1 h2

/-! ## Ancestry along the chain -/

/-- `S` holds chain blocks only. -/
def OnChain (S : Set N.Blk) : Prop := ∀ B ∈ S, ∃ m, B = blk m

theorem anc_blk {S : Set N.Blk} {a b : Nat} (hab : a ≤ b)
    (hS : ∀ k, a ≤ k → k ≤ b → blk k ∈ S) : Anc S (blk a) (blk b) := by
  induction b, hab using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ b hab ih =>
    exact Relation.ReflTransGen.tail (ih fun k h1 h2 => hS k h1 (by omega))
      ⟨hS b hab (by omega), hS (b + 1) (by omega) le_rfl, blk_parent_succ b⟩

theorem anc_blk_inv {S : Set N.Blk} (hS : OnChain S) {A : N.Blk} {b : Nat}
    (h : Anc S A (blk b)) : ∃ a ≤ b, A = blk a ∧ (a = b ∨ A ∈ S) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨b, le_rfl, rfl, Or.inl rfl⟩
  | head h' _ ih =>
    obtain ⟨c, hc, rfl, -⟩ := ih
    obtain ⟨hA, -, hpar⟩ := h'
    obtain ⟨a, rfl⟩ := hS _ hA
    rcases c with _ | c
    · rw [blk_parent_zero] at hpar; cases hpar
    · rw [blk_parent_succ] at hpar
      have := blk_root_inj (Option.some.inj hpar)
      subst this
      exact ⟨_, by omega, rfl, Or.inr hA⟩

theorem le_of_anc_blk {S : Set N.Blk} (hS : OnChain S) {a b : Nat}
    (h : Anc S (blk a) (blk b)) : a ≤ b := by
  obtain ⟨a', h', he, -⟩ := anc_blk_inv hS h
  rw [blk_inj he]; exact h'

/-! ## The FG store along the chain -/

/-- The accepted blocks by root when the chain is accepted up to slot `τ`. -/
noncomputable def chainBlocks : Nat → Nat → Option N.Blk
  | 0 => fun r => if r = 0 then some (blk 0) else none
  | s + 1 => Function.update (chainBlocks s) (blk (s + 1)).root (some (blk (s + 1)))

theorem chainBlocks_eq_some : ∀ {τ r : Nat} {B : N.Blk},
    chainBlocks τ r = some B ↔ ∃ m ≤ τ, B = blk m ∧ r = (blk m).root
  | 0, r, B => by
    simp only [chainBlocks]
    split_ifs with h
    · subst h
      constructor
      · rintro ⟨⟩; exact ⟨0, le_rfl, rfl, rfl⟩
      · rintro ⟨m, hm, rfl, -⟩; rw [Nat.le_zero.1 hm]
    · simp only [false_iff, not_exists, not_and]
      intro m hm _ hr; rw [Nat.le_zero.1 hm] at hr; exact h hr
  | τ + 1, r, B => by
    simp only [chainBlocks, Function.update_apply]
    split_ifs with h
    · subst h
      constructor
      · rintro ⟨⟩; exact ⟨τ + 1, le_rfl, rfl, rfl⟩
      · rintro ⟨m, hm, rfl, hr⟩; rw [blk_root_inj hr.symm]
    · rw [chainBlocks_eq_some]
      constructor
      · rintro ⟨m, hm, h1, h2⟩; exact ⟨m, by omega, h1, h2⟩
      · rintro ⟨m, hm, h1, h2⟩
        refine ⟨m, ?_, h1, h2⟩
        by_contra hc
        exact h (by rw [h2, show m = τ + 1 by omega])

/-- The index of the justified block when the chain is accepted up to slot `τ`. -/
def jx (τ : Nat) : Nat := ent (hgt τ - 1)

theorem jx_le (τ : Nat) : jx τ ≤ τ := by
  unfold jx ent hgt; split_ifs <;> omega

theorem jx_mono {τ τ' : Nat} (h : τ ≤ τ') : jx τ ≤ jx τ' := ent_mono (by have := hgt_mono h; omega)

/-- The chain state of the block of slot `m`, typed as the store keeps it. -/
noncomputable def csN (m : Nat) : FG.ChainState sp.n := cs m

theorem csN_eq (m : Nat) : csN m = cs m := rfl

/-- The FG store when the chain is accepted up to slot `τ` (the pool apart). -/
structure FGGood (fg : Store sp.toParams N.Payload) (τ : Nat) : Prop where
  blocks : fg.blocks = chainBlocks τ
  sigma : ∀ m ≤ τ, fg.σ (blk m).root = csN m
  J : fg.J = blk (jx τ)
  hj : fg.hj = hgt τ - 1
  hmax : fg.hmax = hgt τ
  F : ∃ f ≤ jx τ, fg.F = blk f

theorem mem_tree_iff {fg : Store sp.toParams N.Payload} {τ : Nat}
    (h : fg.blocks = chainBlocks τ) {B : N.Blk} : B ∈ fg.tree ↔ ∃ m ≤ τ, B = blk m := by
  change fg.blocks B.root = some B ↔ _
  rw [h, chainBlocks_eq_some]
  constructor
  · rintro ⟨m, hm, rfl, -⟩; exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl, rfl⟩

theorem onChain_tree {fg : Store sp.toParams N.Payload} {τ : Nat}
    (h : fg.blocks = chainBlocks τ) : OnChain fg.tree := fun _ hB => by
  obtain ⟨m, -, rfl⟩ := (mem_tree_iff h).1 hB; exact ⟨m, rfl⟩

theorem anc_tree {fg : Store sp.toParams N.Payload} {τ : Nat}
    (h : fg.blocks = chainBlocks τ) {a b : Nat} (hab : a ≤ b) (hb : b ≤ τ) :
    fg.Anc (blk a) (blk b) :=
  anc_blk hab fun k _ hk => (mem_tree_iff h).2 ⟨k, by omega, rfl⟩

theorem blocks_blk {fg : Store sp.toParams N.Payload} {τ : Nat}
    (h : fg.blocks = chainBlocks τ) {m : Nat} (hm : m ≤ τ) :
    fg.blocks (blk m).root = some (blk m) := by
  rw [h]; exact chainBlocks_eq_some.2 ⟨m, hm, rfl, rfl⟩

/-- What `update_finality` can change: `h_max`, the justification cache (to a held block),
and `Σ.F` (to a held block). -/
theorem updateFinality_cases {ACP : Type} (st : Store sp.toParams ACP)
    (σ : FG.ChainState sp.n) :
    ∃ J hj F, st.updateFinality σ = { st with hmax := max st.hmax σ.h, J := J, hj := hj, F := F } ∧
    ((J = st.J ∧ hj = st.hj ∧
        ¬ (∃ X, st.blocks σ.J = some X ∧ st.Anc st.F X ∧
          Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J))) ∨
      ∃ X, st.blocks σ.J = some X ∧ J = X ∧ hj = σ.hj) ∧
    (F = st.F ∨ ∃ X, st.blocks σ.F = some X ∧ F = X) := by
  unfold Store.updateFinality
  dsimp only
  classical
  rcases hX : st.blocks σ.J with _ | X
  · dsimp only
    have hn : ¬ (∃ X, (none : Option (NodeBlock sp.toParams ACP)) = some X ∧ st.Anc st.F X ∧
        Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J)) := by
      rintro ⟨X', h1, -⟩; cases h1
    split
    · rename_i Y hY
      split
      · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inr ⟨Y, hY, rfl⟩⟩
      · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inl rfl⟩
    · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inl rfl⟩
  · dsimp only
    by_cases hc : ({ st with hmax := max st.hmax σ.h } : Store sp.toParams ACP).Anc st.F X ∧
        Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J)
    · simp only [hc, and_self, ↓reduceIte]
      split
      · rename_i Y hY
        split
        · exact ⟨_, _, _, rfl, Or.inr ⟨X, rfl, rfl, rfl⟩, Or.inr ⟨Y, hY, rfl⟩⟩
        · exact ⟨_, _, _, rfl, Or.inr ⟨X, rfl, rfl, rfl⟩, Or.inl rfl⟩
      · exact ⟨_, _, _, rfl, Or.inr ⟨X, rfl, rfl, rfl⟩, Or.inl rfl⟩
    · simp only [hc, ↓reduceIte]
      have hn : ¬ (∃ X', some X = some X' ∧ st.Anc st.F X' ∧
          Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J)) := by
        rintro ⟨X', h1, h2⟩; cases h1; exact hc h2
      split
      · rename_i Y hY
        split
        · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inr ⟨Y, hY, rfl⟩⟩
        · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inl rfl⟩
      · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inl rfl⟩

/-- `update_finality` on the chain state of the newest block. -/
theorem updateFinality_chain {st : Store sp.toParams N.Payload} {τ : Nat}
    (hb : st.blocks = chainBlocks (τ + 1))
    (hJ : st.J = blk (jx τ)) (hhj : st.hj = hgt τ - 1) (hmax : st.hmax = hgt τ)
    (hF : ∃ f ≤ jx τ, st.F = blk f) :
    ∃ J hj F, st.updateFinality (cs (τ + 1)) =
      { st with hmax := hgt (τ + 1), J := J, hj := hj, F := F } ∧
      J = blk (jx (τ + 1)) ∧ hj = hgt (τ + 1) - 1 ∧ ∃ f ≤ jx (τ + 1), F = blk f := by
  obtain ⟨f, hf, hFe⟩ := hF
  have hmx : max st.hmax (cs (τ + 1)).h = hgt (τ + 1) := by
    rw [hmax, cs_h]; exact max_eq_right (hgt_mono (by omega))
  obtain ⟨J, hj, F, he, hj2, hf2⟩ := updateFinality_cases st (cs (τ + 1))
  refine ⟨J, hj, F, by rw [he, hmx], ?_⟩
  have hJ2 : J = blk (jx (τ + 1)) ∧ hj = hgt (τ + 1) - 1 := by
    rcases hj2 with ⟨h1, h2, h3⟩ | ⟨X, h1, h2, h3⟩
    · by_cases he : (τ + 1) % 10 = 1 ∧ 11 ≤ τ + 1
      · exfalso
        refine h3 ⟨blk (jx (τ + 1)), by rw [cs_J]; exact blocks_blk hb (jx_le _), ?_, ?_⟩
        · rw [hFe]
          exact anc_tree hb (le_trans hf (jx_mono (by omega))) (jx_le _)
        · rw [hhj, cs_hj, hgt_succ_entry he]
          exact Or.inl (by have := hgt_pos τ; omega)
      · rw [h1, h2, hJ, hhj]; unfold jx; rw [hgt_succ_of he]; exact ⟨rfl, rfl⟩
    · rw [cs_J, show (blk (ent (hgt (τ + 1) - 1))).root = (blk (jx (τ + 1))).root from rfl,
        blocks_blk hb (jx_le _)] at h1
      cases h1
      exact ⟨h2, by rw [h3, cs_hj]⟩
  refine ⟨hJ2.1, hJ2.2, ?_⟩
  rcases hf2 with h | ⟨X, h1, h2⟩
  · rw [h]; exact ⟨f, le_trans hf (jx_mono (by omega)), hFe⟩
  · have hle : ent (hgt (τ + 1) - 2) ≤ jx (τ + 1) := ent_mono (by omega)
    rw [cs_F, blocks_blk hb (le_trans hle (jx_le _))] at h1
    cases h1
    exact ⟨_, hle, h2⟩

theorem addAtts_present {ACP : Type} :
    ∀ (l : List (FG.Att sp.n)) (st : Store sp.toParams ACP), (∀ a ∈ l, a ∈ st.atts) →
      st.addAtts l = st
  | [], _, _ => rfl
  | a :: l, st, h => by
    change (st.onAttestation a).addAtts l = st
    have ha : st.onAttestation a = st := by
      unfold Store.onAttestation; rw [ite_eq_left (h a (List.mem_cons_self ..))]
    rw [ha]
    exact addAtts_present l st fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem fgGood_init : FGGood (Store.init N.genesisPayload) 0 :=
  ⟨rfl, fun m hm => by rw [Nat.le_zero.1 hm]; rfl, rfl, rfl, rfl, 0, le_rfl, rfl⟩

theorem sigma_update {τ : Nat} (σf : Nat → FG.ChainState sp.n)
    (h : ∀ m ≤ τ, σf (blk m).root = csN m) :
    ∀ m ≤ τ + 1, Function.update σf (blk (τ + 1)).root (csN (τ + 1)) (blk m).root = csN m := by
  intro m hm
  rcases Nat.lt_or_ge m (τ + 1) with hm' | hm'
  · rw [Function.update_of_ne (fun he => by have := blk_root_inj he; omega)]
    exact h m (by omega)
  · rw [show m = τ + 1 by omega, Function.update_self]

theorem cs_trans' {m : Nat} (σ : FG.ChainState sp.n) (h : σ = csN m) :
    sp.toParams.fg.stateTransition σ (blk (m + 1)).fgView = some (cs (m + 1)) := by
  subst h; exact cs_trans m

/-- **The FG accepts the next block of the chain**, whose rows it holds. -/
theorem fgGood_onBlock {fg : Store sp.toParams N.Payload} {τ : Nat} (h : FGGood fg τ)
    (hatts : ∀ a ∈ (blk (τ + 1)).fgPayload, a ∈ fg.atts) :
    ∃ fg', fg.onBlock (blk (τ + 1)) = some fg' ∧ FGGood fg' (τ + 1) ∧ fg'.atts = fg.atts := by
  have hσ' := cs_trans' (fg.σ (blk τ).root) (h.sigma τ le_rfl)
  have hnew : fg.blocks (blk (τ + 1)).root = none := by
    rw [h.blocks]
    rcases hc : chainBlocks τ (blk (τ + 1)).root with _ | B
    · rfl
    · obtain ⟨m, hm, -, hr⟩ := chainBlocks_eq_some.1 hc
      have := blk_root_inj hr; omega
  have hpar : fg.blocks (blk τ).root = some (blk τ) := blocks_blk h.blocks le_rfl
  obtain ⟨f, hf, hFe⟩ := h.F
  have hanc : Goldilocks.Anc (insert (blk (τ + 1)) fg.tree) fg.F (blk (τ + 1)) := by
    rw [hFe]
    refine anc_blk (by have := jx_le τ; omega) fun k _ hk => ?_
    rcases Nat.lt_or_ge k (τ + 1) with hk' | hk'
    · exact Or.inr ((mem_tree_iff h.blocks).2 ⟨k, by omega, rfl⟩)
    · exact Or.inl (by rw [show k = τ + 1 by omega])
  unfold Store.onBlock
  rw [blk_parent_succ]
  dsimp only
  split_ifs with hc
  · exfalso
    simp only [hnew, hpar, Option.isSome_none, Option.isNone_some] at hc
    simp at hc
    exact hc hanc
  split
  · rename_i hn; rw [hσ'] at hn; cases hn
  rename_i σ'' hn
  rw [hσ'] at hn; cases hn
  set st₁ : Store sp.toParams N.Payload :=
    { fg with blocks := Function.update fg.blocks (blk (τ + 1)).root (some (blk (τ + 1))),
              σ := Function.update fg.σ (blk (τ + 1)).root (cs (τ + 1)) } with hst₁
  have hb₁ : st₁.blocks = chainBlocks (τ + 1) := by rw [hst₁]; dsimp only; rw [h.blocks]; rfl
  obtain ⟨J, hj, F, he, hJ, hhj, hF⟩ :=
    updateFinality_chain hb₁ h.J h.hj h.hmax ⟨f, hf, hFe⟩
  have hatts' : ∀ a ∈ (blk (τ + 1)).fgPayload,
      a ∈ ({ st₁ with hmax := hgt (τ + 1), J := J, hj := hj, F := F } : Store _ _).atts := hatts
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [he, addAtts_present _ _ hatts']
    exact ⟨hb₁, sigma_update fg.σ h.sigma, hJ, hhj, rfl, hF⟩
  · rw [he, addAtts_present _ _ hatts']

/-! ## The frames -/

/-- A frame over the chain: the tree is the blocks of slots `f … τ`, `Φ.F` the block of slot
`f`, the fork-choice root the block of slot `j`, and the viable heads the blocks of slots
`j … τ`. -/
structure ChainFrame (Φ : N.Frm) (f j τ : Nat) : Prop where
  tree : ∀ B, B ∈ Φ.tree ↔ ∃ m, f ≤ m ∧ m ≤ τ ∧ B = blk m
  F : Φ.F = blk f
  fcRoot : Φ.fcRoot = blk j
  heads : ∀ B, B ∈ Φ.viableHeads ↔ ∃ m, j ≤ m ∧ m ≤ τ ∧ B = blk m
  fj : f ≤ j
  jτ : j ≤ τ

namespace ChainFrame

variable {Φ : N.Frm} {f j τ : Nat}

theorem onChain (h : ChainFrame Φ f j τ) : OnChain Φ.tree := fun B hB => by
  obtain ⟨m, -, -, rfl⟩ := (h.tree B).1 hB; exact ⟨m, rfl⟩

theorem mem (h : ChainFrame Φ f j τ) {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) : blk m ∈ Φ.tree :=
  (h.tree _).2 ⟨m, h1, h2, rfl⟩

theorem mem_iff (h : ChainFrame Φ f j τ) {m : Nat} : blk m ∈ Φ.tree ↔ f ≤ m ∧ m ≤ τ := by
  rw [h.tree]
  constructor
  · rintro ⟨m', h1, h2, he⟩; rw [blk_inj he]; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨m, h1, h2, rfl⟩

theorem anc (h : ChainFrame Φ f j τ) {a b : Nat} (ha : f ≤ a) (hab : a ≤ b) (hb : b ≤ τ) :
    Φ.Anc (blk a) (blk b) :=
  anc_blk hab fun k h1 h2 => h.mem (by omega) (by omega)

theorem le_of_anc (h : ChainFrame Φ f j τ) {a b : Nat} (hab : Φ.Anc (blk a) (blk b)) : a ≤ b :=
  le_of_anc_blk h.onChain hab

theorem head_mem (h : ChainFrame Φ f j τ) {m : Nat} (h1 : j ≤ m) (h2 : m ≤ τ) :
    blk m ∈ Φ.viableHeads :=
  (h.heads _).2 ⟨m, h1, h2, rfl⟩

/-- The viable tree of a domain holding the tip and inside the tree: the blocks from the
fork-choice root to the tip. -/
theorem mem_viableTree (h : ChainFrame Φ f j τ) {S : Set N.Blk} (hS : blk τ ∈ S)
    {m : Nat} (h1 : j ≤ m) (h2 : m ≤ τ) (hm : blk m ∈ S) : blk m ∈ Φ.viableTree S :=
  ⟨hm, by rw [h.fcRoot]; exact h.anc h.fj h1 h2, blk τ, hS, h.head_mem h.jτ le_rfl,
    h.anc (by have := h.fj; omega) h2 le_rfl⟩

theorem viableTree_sub (h : ChainFrame Φ f j τ) {S : Set N.Blk} (hS : S ⊆ Φ.tree) {B : N.Blk}
    (hB : B ∈ Φ.viableTree S) : ∃ m, j ≤ m ∧ m ≤ τ ∧ B = blk m := by
  obtain ⟨hBS, hanc, -⟩ := hB
  obtain ⟨m, -, hm, rfl⟩ := (h.tree B).1 (hS hBS)
  rw [h.fcRoot] at hanc
  exact ⟨m, h.le_of_anc hanc, hm, rfl⟩

end ChainFrame

theorem ent_pred_le (m : Nat) : ent (hgt m - 1) ≤ m := by
  unfold ent hgt; split_ifs <;> omega

theorem jx_le_of_hgt {τ m : Nat} (h : hgt τ ≤ hgt m) : jx τ ≤ m :=
  le_trans (ent_mono (by omega)) (ent_pred_le m)

theorem hgt_ge_of_jx {τ m : Nat} (h : jx τ ≤ m) : hgt τ - 1 ≤ hgt m := by
  rcases Nat.lt_or_ge (hgt τ - 1) 1 with h1 | h1
  · have := hgt_pos m; omega
  · have := hgt_mono h
    unfold jx at this; rw [hgt_ent h1] at this; exact this

/-- **The frame of an FG store** with the chain accepted up to slot `τ`. -/
theorem fgGood_frame {fg : Store sp.toParams N.Payload} {τ : Nat} (h : FGGood fg τ) :
    ∃ f, ChainFrame fg.toFrame f (jx τ) τ := by
  classical
  obtain ⟨f, hf, hFe⟩ := h.F
  have hmem : ∀ B : N.Blk, B ∈ fg.tree ↔ ∃ m ≤ τ, B = blk m := fun B => mem_tree_iff h.blocks
  have htree : ∀ B, B ∈ fg.toFrame.tree ↔ ∃ m, f ≤ m ∧ m ≤ τ ∧ B = blk m := by
    intro B
    change B ∈ fg.tree ∧ fg.Anc fg.F B ↔ _
    rw [hmem B, hFe]
    constructor
    · rintro ⟨⟨m, hm, rfl⟩, ha⟩
      exact ⟨m, le_of_anc_blk (onChain_tree h.blocks) ha, hm, rfl⟩
    · rintro ⟨m, h1, h2, rfl⟩
      exact ⟨⟨m, h2, rfl⟩, anc_tree h.blocks h1 h2⟩
  have hjm : ∀ m ≤ τ, hgt τ ≤ hgt m → jx τ ≤ m := fun m _ hh => jx_le_of_hgt hh
  have hnc : ¬ fg.Contest := by
    rintro ⟨-, B, hB, -, hh, hna⟩
    obtain ⟨m, hm, rfl⟩ := (hmem _).1 hB
    rw [h.sigma m hm, csN_eq, cs_h, h.hmax] at hh
    apply hna
    rw [h.J]
    exact anc_tree h.blocks (hjm m hm hh.ge) hm
  have hfc : fg.fcRoot = blk (jx τ) := by
    unfold Store.fcRoot
    rw [ite_eq_left ⟨by rw [h.hmax, h.hj]; have := hgt_pos τ; omega, hnc⟩, h.J]
  have hfloor : fg.headHeightFloor = hgt τ - 1 := by
    unfold Store.headHeightFloor; rw [ite_eq_right hnc, h.hmax]
  refine ⟨f, ⟨htree, hFe, hfc, fun B => ?_, hf, jx_le τ⟩⟩
  change (B ∈ fg.tree ∧ fg.Anc fg.F B ∧ fg.Anc fg.fcRoot B ∧ fg.IsViable B) ↔ _
  rw [hfc, hFe]
  constructor
  · rintro ⟨hB, -, ha, -⟩
    obtain ⟨m, hm, rfl⟩ := (hmem _).1 hB
    exact ⟨m, le_of_anc_blk (onChain_tree h.blocks) ha, hm, rfl⟩
  · rintro ⟨m, h1, h2, rfl⟩
    refine ⟨(hmem _).2 ⟨m, h2, rfl⟩, anc_tree h.blocks (by omega) h2, anc_tree h.blocks h1 h2, ?_⟩
    unfold Store.IsViable
    rw [hfloor, h.sigma m h2, csN_eq, cs_h]
    exact hgt_ge_of_jx h1

/-! ## The rows on the chain -/

/-- The block that carries the row of `v0` for height `q`. -/
def car0 (q : Nat) : Nat := 10 * (q - 1) + 2

/-- The block that carries the row of `v1` for height `q`. -/
def car1 (q : Nat) : Nat := 10 * q + 1

theorem mem_blk_fgPayload {m : Nat} {a : FG.Att sp.n} : a ∈ (blk m).fgPayload ↔
    (∃ q, 1 ≤ q ∧ m = car0 q ∧ a = row w0 q) ∨ (∃ q, 1 ≤ q ∧ m = car1 q ∧ a = row w1 q) := by
  rcases m with _ | s
  · rw [blk_fgPayload_zero]; simp only [List.not_mem_nil, false_iff, not_or, not_exists, not_and]
    exact ⟨fun q _ h => by unfold car0 at h; omega, fun q _ h => by unfold car1 at h; omega⟩
  · rw [blk_fgPayload]
    have hq := hgt_pos s
    split_ifs with h1 h2
    · rw [List.mem_singleton]
      constructor
      · rintro rfl; exact Or.inl ⟨_, hq, by unfold car0 hgt; split_ifs <;> omega, rfl⟩
      · rintro (⟨q, hq1, hm, rfl⟩ | ⟨q, -, hm, -⟩)
        · unfold car0 at hm; congr 1; unfold hgt; split_ifs <;> omega
        · unfold car1 at hm; omega
    · rw [List.mem_singleton]
      constructor
      · rintro rfl; exact Or.inr ⟨_, hq, by unfold car1 hgt; split_ifs <;> omega, rfl⟩
      · rintro (⟨q, -, hm, -⟩ | ⟨q, hq1, hm, rfl⟩)
        · unfold car0 at hm; omega
        · unfold car1 at hm; congr 1; unfold hgt; split_ifs <;> omega
    · simp only [List.not_mem_nil, false_iff, not_or, not_exists, not_and]
      exact ⟨fun q hq1 h => by unfold car0 at h; omega,
        fun q hq1 h => by unfold car1 at h; omega⟩

theorem row_valid_iff {m q : Nat} (y : Fin sp.n) (hq : 1 ≤ q) :
    (cs m).validAtt (row y q) ↔ q = hgt m := by
  constructor
  · rintro (⟨hh, -⟩ | ⟨p, hp, hpp, hlt, hlt'⟩)
    · rw [row_h, cs_h] at hh; exact hh
    · rw [row_fin] at hp
      split_ifs at hp with h1
      · cases hp
      · simp only [Option.toList_some, List.mem_singleton] at hp
        subst hp
        rw [cs_pending] at hpp
        rw [row_h, cs_h] at hlt'
        split_ifs at hpp
        · cases hpp
        · simp only [List.mem_singleton, Prod.mk.injEq] at hpp; omega
  · rintro rfl; exact Or.inl ⟨by rw [row_h, cs_h], by rw [row_T, cs_Th]⟩

/-- The other validator. -/
def other (y : Fin sp.n) : Fin sp.n := if y = w0 then w1 else w0

/-- The `i`-th attestation of `y`'s pool: its own row of each height, then the other's. -/
noncomputable def poolAt (y : Fin sp.n) (i : Nat) : FG.Att sp.n :=
  row (if i % 2 = 0 then y else other y) (i / 2 + 1)

/-- The first `k` attestations of `y`'s pool. -/
noncomputable def poolOf (y : Fin sp.n) (k : Nat) : List (FG.Att sp.n) :=
  (List.range k).map (poolAt y)

theorem poolOf_succ (y : Fin sp.n) (k : Nat) :
    poolOf y (k + 1) = poolOf y k ++ [poolAt y k] := by
  simp [poolOf, List.range_succ]

theorem other_ne (y : Fin sp.n) : other y ≠ y := by
  unfold other; rcases eq_w0_or_w1 y with rfl | rfl <;> decide

theorem poolAt_inj (y : Fin sp.n) {i i' : Nat} (h : poolAt y i = poolAt y i') : i = i' := by
  obtain ⟨h1, h2⟩ := row_inj h
  have := other_ne y
  split_ifs at h1 <;> omega

theorem mem_poolOf {y : Fin sp.n} {k : Nat} {a : FG.Att sp.n} :
    a ∈ poolOf y k ↔ ∃ i < k, a = poolAt y i := by
  simp only [poolOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem poolOf_nodup (y : Fin sp.n) (k : Nat) : (poolOf y k).Nodup :=
  (List.nodup_range).map (fun _ _ h => poolAt_inj y h)

theorem onAttestation_new {ACP : Type} {st : Store sp.toParams ACP} {a : FG.Att sp.n}
    (h : a ∉ st.atts) : st.onAttestation a = { st with atts := st.atts ++ [a] } := by
  unfold Store.onAttestation; rw [ite_eq_right h]

theorem onAttestation_old {ACP : Type} {st : Store sp.toParams ACP} {a : FG.Att sp.n}
    (h : a ∈ st.atts) : st.onAttestation a = st := by
  unfold Store.onAttestation; rw [ite_eq_left h]

/-- A filter of a duplicate-free list with the members of a list of at most one element. -/
theorem filter_eq_of_mem_iff {α : Type} {l r : List α} {p : α → Bool}
    (hl : l.Nodup) (hr : r.length ≤ 1) (h : ∀ a, (a ∈ l ∧ p a = true) ↔ a ∈ r) :
    l.filter p = r := by
  rcases r with _ | ⟨x, _ | ⟨y, r⟩⟩
  · rw [List.filter_eq_nil_iff]
    intro a ha hp; exact List.not_mem_nil ((h a).1 ⟨ha, hp⟩)
  · have hnd : (l.filter p).Nodup := hl.filter p
    have hall : ∀ a ∈ l.filter p, a = x := fun a ha => by
      rw [List.mem_filter] at ha; exact List.mem_singleton.1 ((h a).1 ha)
    have hx : x ∈ l.filter p := List.mem_filter.2 ((h x).2 (List.mem_singleton_self x))
    rcases hf : l.filter p with _ | ⟨z, _ | ⟨z', rest⟩⟩
    · rw [hf] at hx; cases hx
    · rw [hall z (by rw [hf]; exact List.mem_singleton_self z)]
    · exfalso
      rw [hf] at hnd hall
      have h1 := hall z (List.mem_cons_self ..)
      have h2 := hall z' (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      exact (List.nodup_cons.1 hnd).1 (by rw [h1, ← h2]; exact List.mem_cons_self ..)
  · simp at hr

theorem onChain_row0 {fg : Store sp.toParams N.Payload} {τ : Nat} (h : FGGood fg τ) (q : Nat) :
    fg.OnChain (blk τ) (row w0 q) ↔ 1 ≤ q ∧ car0 q ≤ τ := by
  constructor
  · rintro ⟨X, hX, hXa, hm⟩
    obtain ⟨m, hm', rfl⟩ := (mem_tree_iff h.blocks).1 hX
    have hle := le_of_anc_blk (onChain_tree h.blocks) hXa
    rcases mem_blk_fgPayload.1 hm with ⟨q', hq', h1, h2⟩ | ⟨q', hq', h1, h2⟩
    · obtain ⟨-, rfl⟩ := row_inj h2; exact ⟨hq', by omega⟩
    · exact absurd (row_inj h2).1 (by decide)
  · rintro ⟨hq, hc⟩
    exact ⟨blk (car0 q), (mem_tree_iff h.blocks).2 ⟨_, hc, rfl⟩, anc_tree h.blocks hc le_rfl,
      mem_blk_fgPayload.2 (Or.inl ⟨q, hq, rfl, rfl⟩)⟩

theorem onChain_row1 {fg : Store sp.toParams N.Payload} {τ : Nat} (h : FGGood fg τ) (q : Nat) :
    fg.OnChain (blk τ) (row w1 q) ↔ 1 ≤ q ∧ car1 q ≤ τ := by
  constructor
  · rintro ⟨X, hX, hXa, hm⟩
    obtain ⟨m, hm', rfl⟩ := (mem_tree_iff h.blocks).1 hX
    have hle := le_of_anc_blk (onChain_tree h.blocks) hXa
    rcases mem_blk_fgPayload.1 hm with ⟨q', hq', h1, h2⟩ | ⟨q', hq', h1, h2⟩
    · exact absurd (row_inj h2).1 (by decide)
    · obtain ⟨-, rfl⟩ := row_inj h2; exact ⟨hq', by omega⟩
  · rintro ⟨hq, hc⟩
    exact ⟨blk (car1 q), (mem_tree_iff h.blocks).2 ⟨_, hc, rfl⟩, anc_tree h.blocks hc le_rfl,
      mem_blk_fgPayload.2 (Or.inr ⟨q, hq, rfl, rfl⟩)⟩

end Consensus.Goldilocks.Witness.TwoRun

end
