module
public import ConsensusLeanTest.GoldilocksWitness
@[expose] public section

/-! # The one-validator tick run: its chain

The tick run of `GoldilocksWitness` (`n = 1`, `Δ = 1`, `t_s = 4s`, `k = 2`, `δ_t = 2`) builds one
chain (consensus-lean#69, W3). This file describes it and the FG side of each step:

* **The chain** (`blk`): genesis, then the own proposal of every slot `s + 1` on the block of slot
  `s`, carrying the slot-`s` attestation (`att`, from slot `1` on) and the slot-`s` vote (`cv`) as
  its votes and support. The attestation of slot `s ≥ 2` is the target of the entry `blk s` at
  height `s` with the finality pair of the previous entry; of slot `1`, height `1` on genesis.
* **The FG store** (`FGGood fg τ`): the chain up to slot `τ` is accepted (`chainBlocks`), every
  chain state has the `Shape` of its slot (each block justifies its parent's entry and enters the
  next height, from slot `3` on also finalizing two slots back), `Σ.J`, `Σ.h_j`, `Σ.h_max` follow,
  and `Σ.F` is at or below the justification. `fgGood_onBlock`: the FG accepts the next block.
* **The record** (`RecGood Λ n`) after the attestations of slots `1, …, n`, and `attest_blk`: the
  attestation of slot `s` is signed on `blk s`; `proposalAttestations_blk`: the own block carries
  the previous slot's attestation alone.
* **The frames** (`ChainFrame`): the frame of an FG store with the chain up to `τ` is the chain from
  `Σ.F` to `τ`, with `fc_root` the block of slot `jexp τ` (the parent of the tip, from slot `3` on)
  and the viable heads from there to the tip (`fgGood_frame`). -/

namespace Consensus.Goldilocks.Witness.One

open SA Node

theorem ite_pos {α : Sort*} {c : Prop} {_ : Decidable c} (h : c) {a b : α} : ite c a b = a := by
  simp [h]

theorem ite_neg {α : Sort*} {c : Prop} {_ : Decidable c} (h : ¬ c) {a b : α} : ite c a b = b := by
  simp [h]

theorem dite_pos' {α : Sort*} {c : Prop} {_ : Decidable c} (h : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a h := by
  simp [h]

theorem dite_neg' {α : Sort*} {c : Prop} {_ : Decidable c} (h : ¬ c) {a : c → α} {b : ¬ c → α} :
    dite c a b = b h := by
  simp [h]

/-! ## The chain -/

/-- The validator. -/
abbrev w0 : Fin sp1.n := v0

/-- The attestation signed at slot `s`, read off the block `B` of slot `s`: height `1` on
genesis at slot `1`; from slot `2` on, the target `B` at height `s` with the finality pair of
the previous entry (genesis at height `1`, `B`'s parent above). -/
def attOf (s : Nat) (B : N1.Blk) : FG.Att sp1.n :=
  if s ≤ 1 then ⟨w0, 1, 0, false, none⟩
  else ⟨w0, s, B.root, false, some (s - 1, if s = 2 then 0 else B.parent.getD 0)⟩

/-- The block of slot `s`: genesis, then the own proposal of each slot on the previous one,
carrying the previous slot's attestation and vote. -/
noncomputable def blk : Nat → N1.Blk
  | 0 => sp1.toParams.genesisBlock N1.genesisPayload
  | s + 1 =>
    let B := blk s
    let atts : List (FG.Att sp1.n) := if s = 0 then [] else [attOf s B]
    let pay : Payload sp1.n := ([⟨w0, s, B.root⟩], [⟨w0, s, B.root⟩])
    ⟨dg1 (some B.root) (s + 1) 0 atts pay, some B.root, s + 1, w0, 0, atts, pay⟩

/-- The attestation of slot `s`. -/
noncomputable def att (s : Nat) : FG.Att sp1.n := attOf s (blk s)

/-- The vote of slot `σ`. -/
noncomputable def cv (σ : Nat) : Vote sp1.n := ⟨w0, σ, (blk σ).root⟩

/-- The index of the entry block of height `h`. -/
def ent (h : Nat) : Nat := if h ≤ 1 then 0 else h

/-- The root of the entry of height `h`. -/
noncomputable def eroot (h : Nat) : Nat := (blk (ent h)).root

theorem blk_slot : ∀ m, (blk m).slot = m
  | 0 => rfl
  | _ + 1 => rfl

theorem blk_parent_succ (s : Nat) : (blk (s + 1)).parent = some (blk s).root := rfl

theorem blk_parent_zero : (blk 0).parent = none := rfl

theorem blk_root_zero : (blk 0).root = 0 := rfl

theorem blk_proposer : ∀ m, (blk m).proposer = w0
  | 0 => rfl
  | _ + 1 => rfl

theorem blk_fgPayload (s : Nat) :
    (blk (s + 1)).fgPayload = if s = 0 then [] else [att s] := rfl

theorem blk_acPayload (s : Nat) : (blk (s + 1)).acPayload = ([cv s], [cv s]) := rfl

theorem blk_root_succ (s : Nat) : (blk (s + 1)).root =
    dg1 (some (blk s).root) (s + 1) 0 (if s = 0 then [] else [att s]) ([cv s], [cv s]) := rfl

theorem blk_root_succ_ne (s : Nat) : (blk (s + 1)).root ≠ 0 := by
  rw [blk_root_succ]
  unfold dg1
  rw [ite_neg (by simp [genContent])]
  omega

theorem blk_root_inj : ∀ {m m' : Nat}, (blk m).root = (blk m').root → m = m'
  | 0, 0, _ => rfl
  | 0, m' + 1, h => absurd h.symm (blk_root_succ_ne m')
  | m + 1, 0, h => absurd h (blk_root_succ_ne m)
  | m + 1, m' + 1, h => by
    rw [blk_root_succ, blk_root_succ] at h
    have := dg1_injective h
    simp only [Prod.mk.injEq] at this
    omega

theorem blk_inj {m m' : Nat} (h : blk m = blk m') : m = m' := blk_root_inj (by rw [h])

theorem att_one : att 1 = ⟨w0, 1, 0, false, none⟩ := rfl

theorem att_eq {s : Nat} (hs : 2 ≤ s) :
    att s = ⟨w0, s, (blk s).root, false, some (s - 1, eroot (s - 1))⟩ := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  unfold att attOf eroot ent
  rw [ite_neg (by omega)]
  by_cases h2 : s + 1 = 2
  · rw [ite_pos h2, ite_pos (by omega)]; rfl
  · rw [ite_neg h2, ite_neg (by omega), blk_parent_succ]; rfl

theorem att_h : ∀ s, 1 ≤ s → (att s).h = s
  | 1, _ => rfl
  | s + 2, _ => by rw [att_eq (by omega)]

theorem slotOf_nat (t : Nat) : sp1.toParams.slotOf (t : Int) = t / 4 := by
  unfold Params.slotOf
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by simp; omega, fun _ => ?_, fun n hn _ h => ?_⟩
  · change 4 * ((t / 4 : Nat) : Int) ≤ t; omega
  · change 4 * (n : Int) ≤ t at h; omega

/-! ## Ancestry along the chain -/

/-- `S` holds chain blocks only. -/
def OnChain (S : Set N1.Blk) : Prop := ∀ B ∈ S, ∃ m, B = blk m

theorem anc_blk {S : Set N1.Blk} {a b : Nat} (hab : a ≤ b)
    (hS : ∀ k, a ≤ k → k ≤ b → blk k ∈ S) : Anc S (blk a) (blk b) := by
  induction b, hab using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ b hab ih =>
    exact Relation.ReflTransGen.tail (ih fun k h1 h2 => hS k h1 (by omega))
      ⟨hS b hab (by omega), hS (b + 1) (by omega) le_rfl, blk_parent_succ b⟩

theorem anc_blk_inv {S : Set N1.Blk} (hS : OnChain S) {A : N1.Blk} {b : Nat}
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

theorem le_of_anc_blk {S : Set N1.Blk} (hS : OnChain S) {a b : Nat}
    (h : Anc S (blk a) (blk b)) : a ≤ b := by
  obtain ⟨a', h', he, -⟩ := anc_blk_inv hS h
  rw [blk_inj he]; exact h'

/-! ## The FG store along the chain -/

/-- The accepted blocks by root when the chain is accepted up to slot `τ`. -/
noncomputable def chainBlocks : Nat → Nat → Option N1.Blk
  | 0 => fun r => if r = 0 then some (blk 0) else none
  | s + 1 => Function.update (chainBlocks s) (blk (s + 1)).root (some (blk (s + 1)))

theorem chainBlocks_eq_some : ∀ {τ r : Nat} {B : N1.Blk},
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

/-! ## Chain states along the chain -/

section Transition

variable (gp : FG.FGParams) (hq : gp.q = 1)

include hq in
/-- The transition of a block of slot `m + 1 ≥ 3` carrying the target of the entry `R` at the
height `m` with the finality pair `(m - 1, J)`: it finalizes `J`, justifies `R`, and enters
height `m + 1` with the block. -/
theorem trans_gen {m : Nat} (hm : 2 ≤ m) (σ : FG.ChainState gp.n) (B : FG.FGBlock gp.n) (R J : Nat)
    (v : Fin gp.n) (hs : σ.s = m) (hh : σ.h = m) (hTh : σ.Th = R) (htg : σ.target = ∅)
    (hpg : σ.prog = ∅) (hpd : σ.pending = [(m - 1, J)]) (hhj : σ.hj = m - 1)
    (hsl : B.slot = m + 1)
    (hatts : B.atts = [⟨v, m, R, false, some (m - 1, J)⟩]) :
    ∃ σ', gp.stateTransition σ B = some σ' ∧ σ'.L = B.root ∧ σ'.s = m + 1 ∧ σ'.h = m + 1 ∧
      σ'.Th = B.root ∧ σ'.ThSlot = m + 1 ∧ σ'.target = ∅ ∧ σ'.prog = ∅ ∧
      σ'.pending = [(m, R)] ∧ σ'.J = R ∧ σ'.hj = m ∧ σ'.F = J ∧ σ'.hF = m - 1 := by
  unfold FG.FGParams.stateTransition
  rw [ite_pos ⟨by rw [hs, hsl]; omega, by
    rw [hatts]; intro a ha
    rw [List.mem_singleton] at ha; subst ha
    exact ⟨by simp [FG.Att.WellFormed]; omega, Or.inl ⟨hh.symm, hTh.symm⟩⟩⟩]
  refine ⟨_, rfl, ?_⟩
  simp [hatts, FG.ChainState.processAtt, FG.FGParams.heightEvents, FG.FGParams.finalizePrune,
    FG.FGParams.bestFinal, FG.FGParams.justifies, FG.ChainState.advance,
    FG.ChainState.previousHeightJustified,
    FG.FGParams.KW, hq, hh, hTh, htg, hpg, hpd, hhj, hsl]

include hq in
/-- The transition of the slot-`1` block on genesis, with no attestation. -/
theorem trans_zero (σ : FG.ChainState gp.n) (B : FG.FGBlock gp.n) (hs : σ.s = 0)
    (hpg : σ.prog = ∅) (htg : σ.target = ∅) (hpd : σ.pending = [])
    (hsl : B.slot = 1) (hatts : B.atts = []) :
    gp.stateTransition σ B = some { σ with s := 1, L := B.root } := by
  unfold FG.FGParams.stateTransition
  rw [ite_pos ⟨by rw [hs, hsl]; omega, by simp [hatts]⟩]
  simp [hatts, FG.FGParams.heightEvents, FG.FGParams.finalizePrune, FG.FGParams.bestFinal,
    FG.FGParams.justifies, FG.FGParams.timesOut, hq, htg, hpg, hpd, hsl]

include hq in
/-- The transition of the slot-`2` block, carrying the target of genesis at height `1`: it
justifies genesis and enters height `2` with the block. -/
theorem trans_one (σ : FG.ChainState gp.n) (B : FG.FGBlock gp.n) (v : Fin gp.n) (hs : σ.s = 1)
    (hh : σ.h = 1) (hTh : σ.Th = 0) (htg : σ.target = ∅) (hpg : σ.prog = ∅)
    (hpd : σ.pending = []) (hhj : σ.hj = 0) (hF : σ.F = 0) (hhF : σ.hF = 0)
    (hsl : B.slot = 2)
    (hatts : B.atts = [⟨v, 1, 0, false, none⟩]) :
    ∃ σ', gp.stateTransition σ B = some σ' ∧ σ'.L = B.root ∧ σ'.s = 2 ∧ σ'.h = 2 ∧
      σ'.Th = B.root ∧ σ'.ThSlot = 2 ∧ σ'.target = ∅ ∧ σ'.prog = ∅ ∧
      σ'.pending = [(1, 0)] ∧ σ'.J = 0 ∧ σ'.hj = 1 ∧ σ'.F = 0 ∧ σ'.hF = 0 := by
  unfold FG.FGParams.stateTransition
  rw [ite_pos ⟨by rw [hs, hsl]; omega, by
    rw [hatts]; intro a ha
    rw [List.mem_singleton] at ha; subst ha
    exact ⟨by simp [FG.Att.WellFormed], Or.inl ⟨hh.symm, hTh.symm⟩⟩⟩]
  refine ⟨_, rfl, ?_⟩
  simp [hatts, FG.ChainState.processAtt, FG.FGParams.heightEvents, FG.FGParams.finalizePrune,
    FG.FGParams.bestFinal, FG.FGParams.justifies, FG.ChainState.advance,
    FG.ChainState.previousHeightJustified,
    FG.FGParams.KW, hq, hh, hTh, htg, hpg, hpd, hhj, hsl, hF, hhF]

end Transition

/-- The height of the chain state of the slot-`m` block. -/
def hexp (m : Nat) : Nat := if m ≤ 1 then 1 else m

/-- The index of the justified block in the chain state of the slot-`m` block. -/
def jexp (m : Nat) : Nat := if m ≤ 2 then 0 else m - 1

/-- The index of the finalized block in the chain state of the slot-`m` block. -/
def fsig (m : Nat) : Nat := if m ≤ 3 then 0 else m - 2

/-- The chain state of the slot-`m` block (every field but the finality bits). -/
structure Shape (m : Nat) (σ : FG.ChainState sp1.n) : Prop where
  L : σ.L = (blk m).root
  s : σ.s = m
  h : σ.h = hexp m
  Th : σ.Th = (blk (ent m)).root
  ThSlot : σ.ThSlot = ent m
  target : σ.target = ∅
  prog : σ.prog = ∅
  pending : σ.pending = if m ≤ 1 then [] else [(m - 1, (blk (jexp m)).root)]
  J : σ.J = (blk (jexp m)).root
  hj : σ.hj = m - 1
  F : σ.F = (blk (fsig m)).root
  hF : σ.hF = m - 2

theorem shape_init : Shape 0 (FG.ChainState.init sp1.toParams.fg) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem eroot_pred {m : Nat} (hm : 2 ≤ m) : eroot (m - 1) = (blk (jexp m)).root := by
  unfold eroot ent jexp
  congr 2
  split_ifs <;> omega

/-- The chain state of the next block on the chain. -/
theorem shape_trans {m : Nat} {σ : FG.ChainState sp1.n} (hS : Shape m σ) :
    ∃ σ', sp1.toParams.fg.stateTransition σ (blk (m + 1)).fgView = some σ' ∧ Shape (m + 1) σ' := by
  rcases m with _ | _ | m
  · refine ⟨_, trans_zero sp1.toParams.fg rfl σ (blk 1).fgView hS.s hS.prog hS.target hS.pending
      rfl rfl, ?_⟩
    exact ⟨rfl, rfl, hS.h, hS.Th, hS.ThSlot, hS.target, hS.prog, hS.pending, hS.J, hS.hj, hS.F,
      hS.hF⟩
  · obtain ⟨σ', hσ', hL, hs, hh, hTh, hThS, htg, hpg, hpd, hJ, hhj, hF, hhF⟩ :=
      trans_one sp1.toParams.fg rfl σ (blk 2).fgView w0 hS.s hS.h hS.Th hS.target hS.prog hS.pending
        hS.hj
        hS.F hS.hF rfl rfl
    exact ⟨σ', hσ', hL, hs, hh, hTh, hThS, htg, hpg, hpd, hJ, hhj, hF, hhF⟩
  · obtain ⟨σ', hσ', hL, hs, hh, hTh, hThS, htg, hpg, hpd, hJ, hhj, hF, hhF⟩ :=
      trans_gen sp1.toParams.fg rfl (m := m + 2) (by omega) σ (blk (m + 3)).fgView
        (blk (m + 2)).root
        (blk (jexp (m + 2))).root w0 hS.s (by rw [hS.h]; simp [hexp]) (by rw [hS.Th]; simp [ent])
        hS.target hS.prog (by rw [hS.pending]; simp) hS.hj rfl
        (by
          change (blk (m + 3)).fgPayload = _
          rw [blk_fgPayload, ite_neg (by omega), att_eq (by omega), eroot_pred (by omega)]; rfl)
    refine ⟨σ', hσ', hL, hs, by rw [hh]; simp [hexp], by rw [hTh]; simp [ent]; rfl, by
      rw [hThS]; simp [ent], htg, hpg, by rw [hpd]; simp [jexp], by rw [hJ]; simp [jexp], hhj,
      by rw [hF]; congr 2; simp only [jexp, fsig]; split_ifs <;> omega, by rw [hhF]; omega⟩

/-! ## The FG store -/

/-- The FG store when the chain is accepted up to slot `τ` (the pool apart). -/
structure FGGood (fg : Store sp1.toParams N1.Payload) (τ : Nat) : Prop where
  blocks : fg.blocks = chainBlocks τ
  sigma : ∀ m ≤ τ, Shape m (fg.σ (blk m).root)
  J : fg.J = blk (jexp τ)
  hj : fg.hj = τ - 1
  hmax : fg.hmax = hexp τ
  F : ∃ f ≤ jexp τ, fg.F = blk f

theorem jexp_le (m : Nat) : jexp m ≤ m := by unfold jexp; split_ifs <;> omega

theorem jexp_mono {m m' : Nat} (h : m ≤ m') : jexp m ≤ jexp m' := by
  unfold jexp; split_ifs <;> omega

theorem fsig_le_jexp (m : Nat) : fsig m ≤ jexp m := by unfold fsig jexp; split_ifs <;> omega

theorem hexp_mono {m m' : Nat} (h : m ≤ m') : hexp m ≤ hexp m' := by
  unfold hexp; split_ifs <;> omega

theorem mem_tree_iff {fg : Store sp1.toParams N1.Payload} {τ : Nat}
    (h : fg.blocks = chainBlocks τ) {B : N1.Blk} : B ∈ fg.tree ↔ ∃ m ≤ τ, B = blk m := by
  change fg.blocks B.root = some B ↔ _
  rw [h, chainBlocks_eq_some]
  constructor
  · rintro ⟨m, hm, rfl, -⟩; exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl, rfl⟩

theorem onChain_tree {fg : Store sp1.toParams N1.Payload} {τ : Nat}
    (h : fg.blocks = chainBlocks τ) : OnChain fg.tree := fun _ hB => by
  obtain ⟨m, -, rfl⟩ := (mem_tree_iff h).1 hB; exact ⟨m, rfl⟩

theorem anc_tree {fg : Store sp1.toParams N1.Payload} {τ : Nat}
    (h : fg.blocks = chainBlocks τ) {a b : Nat} (hab : a ≤ b) (hb : b ≤ τ) :
    fg.Anc (blk a) (blk b) :=
  anc_blk hab fun k _ hk => (mem_tree_iff h).2 ⟨k, by omega, rfl⟩

theorem blocks_blk {fg : Store sp1.toParams N1.Payload} {τ : Nat}
    (h : fg.blocks = chainBlocks τ) {m : Nat} (hm : m ≤ τ) :
    fg.blocks (blk m).root = some (blk m) := by
  rw [h]; exact chainBlocks_eq_some.2 ⟨m, hm, rfl, rfl⟩

theorem addAtts_eq {ACP : Type} (st : Store sp1.toParams ACP) (l : List (FG.Att sp1.n)) :
    ∃ l', st.addAtts l = { st with atts := l' } := by
  induction l generalizing st with
  | nil => exact ⟨st.atts, rfl⟩
  | cons a l ih =>
    obtain ⟨l', h⟩ := ih (st.onAttestation a)
    refine ⟨l', ?_⟩
    change (st.onAttestation a).addAtts l = _
    rw [h]; unfold Store.onAttestation; split_ifs <;> rfl

/-- What `update_finality` can change: `h_max`, the justification cache (to a held block),
and `Σ.F` (to a held block). -/
theorem updateFinality_cases {ACP : Type} (st : Store sp1.toParams ACP) (σ : FG.ChainState sp1.n) :
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
    have hn : ¬ (∃ X, (none : Option (NodeBlock sp1.toParams ACP)) = some X ∧ st.Anc st.F X ∧
        Store.LexLt (st.hj, st.J.root) (σ.hj, σ.J)) := by
      rintro ⟨X', h1, -⟩; cases h1
    split
    · rename_i Y hY
      split
      · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inr ⟨Y, hY, rfl⟩⟩
      · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inl rfl⟩
    · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, hn⟩, Or.inl rfl⟩
  · dsimp only
    by_cases hc : ({ st with hmax := max st.hmax σ.h } : Store sp1.toParams ACP).Anc st.F X ∧
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
theorem updateFinality_chain {st : Store sp1.toParams N1.Payload} {τ : Nat}
    (hb : st.blocks = chainBlocks (τ + 1)) {σ' : FG.ChainState sp1.n} (hS : Shape (τ + 1) σ')
    (hJ : st.J = blk (jexp τ)) (hhj : st.hj = τ - 1) (hmax : st.hmax = hexp τ)
    (hF : ∃ f ≤ jexp τ, st.F = blk f) :
    ∃ J hj F, st.updateFinality σ' = { st with hmax := hexp (τ + 1), J := J, hj := hj, F := F } ∧
      J = blk (jexp (τ + 1)) ∧ hj = τ ∧ ∃ f ≤ jexp (τ + 1), F = blk f := by
  obtain ⟨f, hf, hFe⟩ := hF
  have hmx : max st.hmax σ'.h = hexp (τ + 1) := by
    rw [hmax, hS.h]; exact max_eq_right (hexp_mono (by omega))
  obtain ⟨J, hj, F, he, hj2, hf2⟩ := updateFinality_cases st σ'
  refine ⟨J, hj, F, by rw [he, hmx], ?_⟩
  have hJ2 : J = blk (jexp (τ + 1)) ∧ hj = τ := by
    rcases hj2 with ⟨h1, h2, h3⟩ | ⟨X, h1, h2, h3⟩
    · rcases τ with _ | τ
      · exact ⟨h1.trans hJ, h2.trans hhj⟩
      · exfalso
        refine h3 ⟨blk (jexp (τ + 2)), by rw [hS.J]; exact blocks_blk hb (jexp_le _), ?_, ?_⟩
        · rw [hFe]
          exact anc_tree hb (le_trans hf (jexp_mono (by omega))) (jexp_le _)
        · rw [hhj, hS.hj]
          exact Or.inl (by omega)
    · rw [hS.J, blocks_blk hb (jexp_le _)] at h1
      cases h1
      exact ⟨h2, by rw [h3, hS.hj]; omega⟩
  refine ⟨hJ2.1, hJ2.2, ?_⟩
  rcases hf2 with h | ⟨X, h1, h2⟩
  · rw [h]; exact ⟨f, le_trans hf (jexp_mono (by omega)), hFe⟩
  · rw [hS.F, blocks_blk hb (le_trans (fsig_le_jexp _) (jexp_le _))] at h1
    cases h1
    exact ⟨_, fsig_le_jexp _, h2⟩

theorem addAtts_present {ACP : Type} :
    ∀ (l : List (FG.Att sp1.n)) (st : Store sp1.toParams ACP), (∀ a ∈ l, a ∈ st.atts) →
      st.addAtts l = st
  | [], _, _ => rfl
  | a :: l, st, h => by
    change (st.onAttestation a).addAtts l = st
    have ha : st.onAttestation a = st := by
      unfold Store.onAttestation; rw [ite_pos (h a (List.mem_cons_self ..))]
    rw [ha]
    exact addAtts_present l st fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem fgGood_init : FGGood (Store.init N1.genesisPayload) 0 :=
  ⟨rfl, fun m hm => by rw [Nat.le_zero.1 hm]; exact shape_init, rfl, rfl, rfl, 0, le_rfl, rfl⟩

theorem shape_update {τ : Nat} (σf : Nat → FG.ChainState sp1.n) (σ0 : FG.ChainState sp1.n)
    (h : ∀ m ≤ τ, Shape m (σf (blk m).root)) (h0 : Shape (τ + 1) σ0) :
    ∀ m ≤ τ + 1, Shape m (Function.update σf (blk (τ + 1)).root σ0 (blk m).root) := by
  intro m hm
  rcases Nat.lt_or_ge m (τ + 1) with hm' | hm'
  · rw [Function.update_of_ne (fun he => by have := blk_root_inj he; omega)]
    exact h m (by omega)
  · rw [show m = τ + 1 by omega, Function.update_self]; exact h0

/-- **The FG accepts the next block of the chain.** -/
theorem fgGood_onBlock {fg : Store sp1.toParams N1.Payload} {τ : Nat} (h : FGGood fg τ)
    (hatts : ∀ a ∈ (blk (τ + 1)).fgPayload, a ∈ fg.atts) :
    ∃ fg', fg.onBlock (blk (τ + 1)) = some fg' ∧ FGGood fg' (τ + 1) ∧ fg'.atts = fg.atts := by
  obtain ⟨σ', hσ', hS'⟩ := shape_trans (h.sigma τ le_rfl)
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
    refine anc_blk (by have := jexp_le τ; omega) fun k _ hk => ?_
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
  set st₁ : Store sp1.toParams N1.Payload :=
    { fg with blocks := Function.update fg.blocks (blk (τ + 1)).root (some (blk (τ + 1))),
              σ := Function.update fg.σ (blk (τ + 1)).root σ' } with hst₁
  have hb₁ : st₁.blocks = chainBlocks (τ + 1) := by rw [hst₁]; dsimp only; rw [h.blocks]; rfl
  obtain ⟨J, hj, F, he, hJ, hhj, hF⟩ :=
    updateFinality_chain hb₁ hS' h.J h.hj h.hmax ⟨f, hf, hFe⟩
  have hatts' : ∀ a ∈ (blk (τ + 1)).fgPayload,
      a ∈ ({ st₁ with hmax := hexp (τ + 1), J := J, hj := hj, F := F } : Store _ _).atts := hatts
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [he, addAtts_present _ _ hatts']
    refine ⟨hb₁, fun m hm => ?_, hJ, hhj, rfl, hF⟩
    exact shape_update fg.σ σ' h.sigma hS' m hm
  · rw [he, addAtts_present _ _ hatts']

/-! ## The attestation pool and the record -/

/-- The attestations of slots `1, …, n`. -/
noncomputable def attList (n : Nat) : List (FG.Att sp1.n) := (List.range n).map fun k => att (k + 1)

theorem attList_succ (n : Nat) : attList (n + 1) = attList n ++ [att (n + 1)] := by
  simp [attList, List.range_succ]

theorem mem_attList {n : Nat} {a : FG.Att sp1.n} :
    a ∈ attList n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ a = att k := by
  simp only [attList, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k + 1, by omega, by omega, rfl⟩
  · rintro ⟨k, hk1, hk2, rfl⟩; exact ⟨k - 1, by omega, by rw [Nat.sub_add_cancel hk1]⟩

theorem att_inj {k k' : Nat} (hk : 1 ≤ k) (hk' : 1 ≤ k') (h : att k = att k') : k = k' := by
  rw [← att_h k hk, ← att_h k' hk', h]

theorem ent_ent (h : Nat) : ent (ent h) = ent h := by unfold ent; split_ifs <;> omega

theorem hexp_ent {s : Nat} (hs : 1 ≤ s) : hexp (ent s) = s := by
  unfold hexp ent; split_ifs <;> omega

theorem att_T {s : Nat} (hs : 1 ≤ s) : (att s).T = eroot s := by
  rcases Nat.lt_or_ge s 2 with h | h
  · rw [show s = 1 by omega]; rfl
  · rw [att_eq h]
    change (blk s).root = (blk (ent s)).root
    unfold ent; rw [ite_neg (show ¬ s ≤ 1 by omega)]

/-- The anti-slashing record after the attestations of slots `1, …, n`. -/
structure RecGood (Λ : FG.Record) (n : Nat) : Prop where
  target : ∀ h, Λ.target h = if 1 ≤ h ∧ h ≤ n then some (eroot h) else none
  timeout : ∀ h, Λ.timeout h = ∅
  lock : ∀ h, Λ.lock h = if 1 ≤ h ∧ h + 1 ≤ n then some (eroot h) else none
  sent : ∀ c ∈ Λ.sent, c.1 ≤ n

theorem recGood_empty : RecGood FG.Record.empty 0 :=
  ⟨fun _ => by simp [FG.Record.empty]; omega, fun _ => rfl,
    fun _ => by simp [FG.Record.empty], fun _ h => by simp [FG.Record.empty] at h⟩

/-- **The attestation of slot `s`**, signed on the block of slot `s`. -/
theorem attest_blk {fg : Store sp1.toParams N1.Payload} {s : Nat} (hs : 1 ≤ s) (h : FGGood fg s)
    {Λ : FG.Record} (hΛ : RecGood Λ (s - 1)) :
    ∃ Λ', fg.attest Λ w0 (blk s) = some (att s, Λ') ∧ RecGood Λ' s := by
  have hTh : (fg.σ (blk s).root).Th = (blk (ent s)).root := (h.sigma s le_rfl).Th
  have hSe : Shape (ent s) (fg.σ (blk (ent s)).root) :=
    h.sigma _ (by unfold ent; split_ifs <;> omega)
  have he_h : (fg.σ (blk (ent s)).root).h = s := by rw [hSe.h, hexp_ent hs]
  have he_Th : (fg.σ (blk (ent s)).root).Th = eroot s := by rw [hSe.Th, ent_ent]; rfl
  have hfin : Λ.finalityPair (fg.σ (blk (ent s)).root) = (att s).fin := by
    unfold FG.Record.finalityPair
    rcases Nat.lt_or_ge s 2 with h2 | h2
    · obtain rfl : s = 1 := by omega
      have hb : ¬ (fg.σ (blk (ent 1)).root).previousHeightJustified := by
        unfold FG.ChainState.previousHeightJustified; rw [hSe.hj]; simp [ent]
      rw [ite_neg hb, hSe.pending]
      rfl
    · have hb : (fg.σ (blk (ent s)).root).previousHeightJustified := by
        unfold FG.ChainState.previousHeightJustified; rw [hSe.hj, he_h]
        unfold ent; split_ifs <;> omega
      have hperm : Λ.permits (fg.σ (blk (ent s)).root).hj (fg.σ (blk (ent s)).root).J := by
        rw [hSe.hj, hSe.J]
        refine ⟨Or.inr ?_, by rw [hΛ.timeout]; simp, Or.inl ?_⟩
        · rw [hΛ.target, ite_pos (by unfold ent; split_ifs <;> omega)]
          unfold ent; rw [ite_neg (by omega), ← eroot_pred h2]
        · rw [hΛ.lock, ite_neg (by unfold ent; split_ifs <;> omega)]
      rw [ite_pos hb, ite_pos hperm, att_eq h2, hSe.hj, hSe.J]
      unfold ent; rw [ite_neg (by omega), ← eroot_pred h2]
  have hhp : Λ.heightPair s (eroot s) = some (s, eroot s, false) := by
    unfold FG.Record.heightPair
    rw [ite_neg (by rw [hΛ.lock, ite_neg (by omega)]; simp), ite_neg (by rw [hΛ.timeout]; simp),
      ite_pos (Or.inl (by rw [hΛ.target, ite_neg (by omega)]))]
  have hsent : ¬ (Λ.sent.any fun b => decide (b.1 = s ∧ ((!false) = true ∨ b.2.1 = eroot s))) =
      true := by
    rw [List.any_eq_true]
    rintro ⟨b, hb, hb'⟩
    have := hΛ.sent b hb
    simp at hb'; omega
  refine ⟨Λ.recordAtt (att s), ?_, ?_⟩
  · unfold Store.attest FG.Record.createAtt
    rw [hTh, he_h, he_Th, hhp]
    dsimp only
    rw [ite_neg hsent]
    simp only [Option.some.injEq, Prod.mk.injEq]
    rw [hfin]
    have ha : (⟨w0, s, eroot s, false, (att s).fin⟩ : FG.Att sp1.n) = att s := by
      rcases Nat.lt_or_ge s 2 with h2 | h2
      · obtain rfl : s = 1 := by omega
        rfl
      · rw [att_eq h2]
        dsimp only
        unfold eroot ent; rw [ite_neg (show ¬ s ≤ 1 by omega)]
    rw [ha]; exact ⟨rfl, rfl⟩
  · have hah : (att s).h = s := att_h s hs
    have haT : (att s).T = eroot s := att_T hs
    have hato : (att s).timeout = false := by
      rcases Nat.lt_or_ge s 2 with h2 | h2
      · obtain rfl : s = 1 := by omega
        rfl
      · rw [att_eq h2]
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun c hc => ?_⟩
    · unfold FG.Record.recordAtt
      dsimp only
      rw [ite_pos ⟨by simp [hato], by rw [hah, hΛ.target, ite_neg (by omega)]⟩,
        Function.update_apply, hah, haT, hΛ.target]
      split_ifs with h1 h2 h3 <;> (try subst h1) <;> first | rfl | omega
    · unfold FG.Record.recordAtt
      dsimp only
      rw [hato]
      exact hΛ.timeout h'
    · unfold FG.Record.recordAtt
      dsimp only
      rcases Nat.lt_or_ge s 2 with h2 | h2
      · obtain rfl : s = 1 := by omega
        change Λ.lock h' = _
        rw [hΛ.lock]
        split_ifs <;> first | rfl | omega
      · rw [att_eq h2]
        dsimp only
        rw [Function.update_apply, hΛ.lock]
        split_ifs with h1 h3 h4 <;> (try subst h1) <;> first | rfl | omega
    · unfold FG.Record.recordAtt at hc
      dsimp only at hc
      rcases List.mem_append.1 hc with hc | hc
      · have := hΛ.sent c hc; omega
      · rw [List.mem_singleton] at hc; subst hc
        change (att s).h ≤ s
        omega

theorem hexp_succ (k : Nat) : hexp (k + 1) = k + 1 := by unfold hexp; split_ifs <;> omega

/-- The attestations an own block carries: those of the pool valid on its parent's chain state
and not yet on its chain, the previous slot's attestation alone. -/
theorem proposalAttestations_blk {fg : Store sp1.toParams N1.Payload} {τ : Nat} (h : FGGood fg τ)
    (ha : fg.atts = attList τ) : fg.proposalAttestations (blk τ) = (blk (τ + 1)).fgPayload := by
  classical
  unfold Store.proposalAttestations
  rw [ha, blk_fgPayload]
  rcases τ with _ | k
  · rfl
  rw [ite_neg (by omega), attList_succ, List.filter_append]
  have hS := h.sigma (k + 1) le_rfl
  have hnone : (attList k).filter (fun a => decide ((fg.σ (blk (k + 1)).root).validAtt a ∧
      ¬ fg.OnChain (blk (k + 1)) a)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a hmem hdec
    obtain ⟨j, hj1, hjk, rfl⟩ := mem_attList.1 hmem
    have hv := (of_decide_eq_true hdec).1
    rcases hv with ⟨hh, -⟩ | ⟨p, hp, hpp, -⟩
    · rw [att_h j hj1, hS.h, hexp_succ] at hh; omega
    · rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · rw [show j = 1 by omega, att_one] at hp; simp at hp
      · rw [att_eq hj2] at hp
        simp only [Option.toList_some, List.mem_singleton] at hp
        subst hp
        rw [hS.pending, ite_neg (by omega)] at hpp
        simp only [List.mem_singleton, Prod.mk.injEq] at hpp
        omega
  rw [hnone, List.nil_append, List.filter_singleton]
  have hval : (fg.σ (blk (k + 1)).root).validAtt (att (k + 1)) :=
    Or.inl ⟨by rw [att_h _ (by omega), hS.h, hexp_succ], by rw [att_T (by omega), hS.Th]; rfl⟩
  have hnot : ¬ fg.OnChain (blk (k + 1)) (att (k + 1)) := by
    rintro ⟨X, hX, -, hmem⟩
    obtain ⟨m, hm, rfl⟩ := (mem_tree_iff h.blocks).1 hX
    rcases m with _ | m
    · exact List.not_mem_nil hmem
    · rw [blk_fgPayload] at hmem
      split_ifs at hmem with hm0
      · simp at hmem
      · rw [List.mem_singleton] at hmem
        have := att_inj (by omega) (by omega) hmem
        omega
  rw [show decide ((fg.σ (blk (k + 1)).root).validAtt (att (k + 1)) ∧
    ¬ fg.OnChain (blk (k + 1)) (att (k + 1))) = true from decide_eq_true ⟨hval, hnot⟩]
  rfl

theorem onAttestation_att {fg : Store sp1.toParams N1.Payload} {s : Nat} (hs : 1 ≤ s)
    (ha : fg.atts = attList (s - 1)) :
    fg.onAttestation (att s) = { fg with atts := attList s } := by
  unfold Store.onAttestation
  rw [ite_neg, ha, show s = (s - 1) + 1 by omega, attList_succ, Nat.add_sub_cancel]
  rw [ha]
  intro hm
  obtain ⟨k, hk1, hk2, he⟩ := mem_attList.1 hm
  have := att_inj hs hk1 he
  omega

theorem payload_mem_attList (τ : Nat) : ∀ a ∈ (blk (τ + 1)).fgPayload, a ∈ attList τ := by
  intro a ha
  rw [blk_fgPayload] at ha
  split_ifs at ha with h0
  · simp at ha
  · rw [List.mem_singleton] at ha
    exact mem_attList.2 ⟨τ, by omega, le_rfl, ha⟩

/-! ## The frames -/

/-- A frame over the chain: the tree is the blocks of slots `f … τ`, `Φ.F` the block of slot
`f`, the fork-choice root the block of slot `j`, and the viable heads the blocks of slots
`j … τ`. -/
structure ChainFrame (Φ : N1.Frm) (f j τ : Nat) : Prop where
  tree : ∀ B, B ∈ Φ.tree ↔ ∃ m, f ≤ m ∧ m ≤ τ ∧ B = blk m
  F : Φ.F = blk f
  fcRoot : Φ.fcRoot = blk j
  heads : ∀ B, B ∈ Φ.viableHeads ↔ ∃ m, j ≤ m ∧ m ≤ τ ∧ B = blk m
  fj : f ≤ j
  jτ : j ≤ τ

namespace ChainFrame

variable {Φ : N1.Frm} {f j τ : Nat}

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
theorem mem_viableTree (h : ChainFrame Φ f j τ) {S : Set N1.Blk} (hS : blk τ ∈ S)
    {m : Nat} (h1 : j ≤ m) (h2 : m ≤ τ) (hm : blk m ∈ S) : blk m ∈ Φ.viableTree S :=
  ⟨hm, by rw [h.fcRoot]; exact h.anc h.fj h1 h2, blk τ, hS, h.head_mem h.jτ le_rfl,
    h.anc (by have := h.fj; omega) h2 le_rfl⟩

theorem viableTree_sub (h : ChainFrame Φ f j τ) {S : Set N1.Blk} (hS : S ⊆ Φ.tree) {B : N1.Blk}
    (hB : B ∈ Φ.viableTree S) : ∃ m, j ≤ m ∧ m ≤ τ ∧ B = blk m := by
  obtain ⟨hBS, hanc, -⟩ := hB
  obtain ⟨m, -, hm, rfl⟩ := (h.tree B).1 (hS hBS)
  rw [h.fcRoot] at hanc
  exact ⟨m, h.le_of_anc hanc, hm, rfl⟩

end ChainFrame

/-- The frame of an FG store with the chain accepted up to slot `τ`. -/
theorem fgGood_frame {fg : Store sp1.toParams N1.Payload} {τ : Nat} (h : FGGood fg τ) :
    ∃ f, ChainFrame fg.toFrame f (jexp τ) τ := by
  classical
  obtain ⟨f, hf, hFe⟩ := h.F
  have hmem : ∀ B : N1.Blk, B ∈ fg.tree ↔ ∃ m ≤ τ, B = blk m := fun B => mem_tree_iff h.blocks
  have htree : ∀ B, B ∈ fg.toFrame.tree ↔ ∃ m, f ≤ m ∧ m ≤ τ ∧ B = blk m := by
    intro B
    change B ∈ fg.tree ∧ fg.Anc fg.F B ↔ _
    rw [hmem B, hFe]
    constructor
    · rintro ⟨⟨m, hm, rfl⟩, ha⟩
      exact ⟨m, le_of_anc_blk (onChain_tree h.blocks) ha, hm, rfl⟩
    · rintro ⟨m, h1, h2, rfl⟩
      exact ⟨⟨m, h2, rfl⟩, anc_tree h.blocks h1 h2⟩
  have hnc : ¬ fg.Contest := by
    rintro ⟨-, B, hB, -, hh, hna⟩
    obtain ⟨m, hm, rfl⟩ := (hmem _).1 hB
    rw [(h.sigma m hm).h, h.hmax] at hh
    apply hna
    rw [h.J]
    refine anc_tree h.blocks ?_ hm
    unfold hexp at hh; unfold jexp; split_ifs at hh ⊢ <;> omega
  have hfc : fg.fcRoot = blk (jexp τ) := by
    unfold Store.fcRoot
    rw [ite_pos ⟨by rw [h.hmax, h.hj]; unfold hexp; split_ifs <;> omega, hnc⟩, h.J]
  have hfloor : fg.headHeightFloor = hexp τ - 1 := by
    unfold Store.headHeightFloor; rw [ite_neg hnc, h.hmax]
  refine ⟨f, ⟨htree, hFe, hfc, fun B => ?_, hf, jexp_le τ⟩⟩
  change (B ∈ fg.tree ∧ fg.Anc fg.F B ∧ fg.Anc fg.fcRoot B ∧ fg.IsViable B) ↔ _
  rw [hfc, hFe]
  constructor
  · rintro ⟨hB, -, ha, -⟩
    obtain ⟨m, hm, rfl⟩ := (hmem _).1 hB
    exact ⟨m, le_of_anc_blk (onChain_tree h.blocks) ha, hm, rfl⟩
  · rintro ⟨m, h1, h2, rfl⟩
    refine ⟨(hmem _).2 ⟨m, h2, rfl⟩, anc_tree h.blocks (by omega) h2, anc_tree h.blocks h1 h2, ?_⟩
    unfold Store.IsViable
    rw [hfloor, (h.sigma m h2).h]
    unfold hexp; unfold jexp at h1; split_ifs at h1 ⊢ <;> omega

end Consensus.Goldilocks.Witness.One

end
