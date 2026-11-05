module
public import ConsensusLeanTest.Goldilocks.Mirror.Setup
@[expose] public section

/-! # A computable mirror of the Goldilocks node: the FG store

The FG part of the mirror (`Goldilocks/Mirror/Setup`). In the fragment every accepted block
is a table block with no attestations, so the FG never counts a vote: each chain state has height
`1` and entry genesis, nothing is justified or finalized, `F = J = genesis`, `h_j = 0` and
`h_max = 1`. The FG state is then given by `FGD`: the list of accepted roots (`tree`, genesis
included) and the attestation pool. `FGD.interp` is the `Store`.

* `toFrame_interp`: the frame of the store is `frameOf tree` (no contest, `fc_root = genesis`,
  every block viable);
* `onBlock_interp`: `fg_on_block` of a table block refuses a held root or a missing parent and
  otherwise adds the root (`FGD.onBlock`);
* `attest_interp`: `fg_attest` signs `(v, 1, genesis, target, no finality pair)` once, then
  nothing (`attestD`, the record being `recI signed`);
* the frame facts of `frameOf`: `lookup`, `InTree`, `AncR`, `Compatible`, the viable tree and
  the viable ancestor. -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA

namespace Fix

variable (X : Fix)

/-- The store of the node. -/
abbrev St := Store X.sp.toParams (Payload X.sp.n)

/-- The chain state of an accepted table block: latest block `r` at its slot, height `1`, entry
genesis, nothing pending, justified or finalized. -/
def σOf (r : Nat) : FG.ChainState X.sp.n :=
  ⟨r, X.slotR r, 1, X.g, 0, ∅, ∅, [], fun _ => ∅, X.g, 0, X.g, 0⟩

/-- The FG data: the accepted roots (genesis included) and the attestation pool. -/
structure FGD where
  /-- The accepted roots. -/
  tree : List Nat
  /-- The attestation pool, in the order of first acceptance. -/
  atts : List (FG.Att X.sp.n)

variable {X}

/-- The store of the FG data. -/
def FGD.interp (d : X.FGD) : X.St where
  blocks r := if r ∈ d.tree then some (X.blk r) else none
  σ r := if r ∈ d.tree then X.σOf r else FG.ChainState.init X.sp.toParams.fg
  F := X.gBlk
  J := X.gBlk
  hj := 0
  hmax := 1
  atts := d.atts

variable (X)

/-- The initial FG data. -/
def FGD.init : X.FGD := ⟨[X.g], []⟩

variable {X}

/-- `fg_on_block` of the table block with root `r`: refused at a held root or a missing parent. -/
def FGD.onBlock (d : X.FGD) (r : Nat) : Option X.FGD :=
  if r ∈ d.tree ∨ X.par r ∉ d.tree then none else some ⟨r :: d.tree, d.atts⟩

/-- `fg_on_attestation`. -/
def FGD.onAtt (d : X.FGD) (a : FG.Att X.sp.n) : X.FGD :=
  if a ∈ d.atts then d else ⟨d.tree, d.atts ++ [a]⟩

/-- The attestation of the fragment: `(v, 1, genesis, target, none)`. -/
def attG (v : Fin X.sp.n) : FG.Att X.sp.n := ⟨v, 1, X.g, false, none⟩

/-- The record after the attestation of the fragment. -/
def recSigned : FG.Record :=
  ⟨Function.update (fun _ => none) 1 (some X.g), fun _ => ∅, fun _ => none, [(1, X.g, false, none)]⟩

variable (X) in
/-- The record of the fragment: empty, or after its one attestation. -/
def recI (signed : Bool) : FG.Record := if signed then X.recSigned else FG.Record.empty

variable (X) in
/-- What `fg_attest` signs with the record `recI signed`. -/
def attestD (signed : Bool) (v : Fin X.sp.n) : Option (FG.Att X.sp.n) :=
  if signed then none else some (X.attG v)

/-! ## The store -/

theorem σOf_g (hX : X.OK) : X.σOf X.g = FG.ChainState.init X.sp.toParams.fg := by
  simp only [σOf, slotR_g hX]; rfl

@[simp] theorem gBlk_root : X.gBlk.root = X.g := rfl

theorem gBlk_eq : X.gBlk = X.sp.toParams.genesisBlock (([], []) : Payload X.sp.n) := rfl

theorem interp_init (hX : X.OK) :
    (FGD.init X).interp = Store.init (P := X.sp.toParams) (([], []) : Payload X.sp.n) := by
  simp only [FGD.interp, FGD.init, Store.init, List.mem_singleton]
  congr 1
  · funext r; by_cases h : r = X.g <;> simp [h, blk_g hX, gBlk]
  · funext r; by_cases h : r = X.g <;> simp [h, σOf_g hX] <;> rfl

theorem σ_interp_Th (d : X.FGD) (r : Nat) : (d.interp.σ r).Th = X.g := by
  by_cases h : r ∈ d.tree <;> simp [FGD.interp, h, σOf, FG.ChainState.init, Params.fg]

theorem σ_interp_g (hX : X.OK) (d : X.FGD) :
    d.interp.σ X.g = FG.ChainState.init X.sp.toParams.fg := by
  by_cases h : X.g ∈ d.tree <;> simp [FGD.interp, h, σOf_g hX] <;> rfl

theorem tree_interp {d : X.FGD} (hM : X.Closed d.tree) : d.interp.tree = X.T d.tree := by
  ext B
  change d.interp.blocks B.root = some B ↔ _
  by_cases hr : B.root ∈ d.tree
  · simp only [FGD.interp, hr, ↓reduceIte, Option.some.injEq]
    exact ⟨fun h => ⟨B.root, hr, h.symm⟩, fun h => (root_mem_of_T hM h).2.symm⟩
  · simp only [FGD.interp, hr, ↓reduceIte, reduceCtorEq, false_iff]
    exact fun h => hr (root_mem_of_T hM h).1

theorem not_contest (d : X.FGD) : ¬ d.interp.Contest := by
  rintro ⟨-, B, -, hFB, -, hJB⟩
  exact hJB hFB

theorem fcRoot_interp (d : X.FGD) : d.interp.fcRoot = X.gBlk := by
  have h : d.interp.hmax = d.interp.hj + 1 ∧ ¬ d.interp.Contest := ⟨rfl, not_contest d⟩
  unfold Store.fcRoot
  simp only [h, not_false_eq_true, and_self, ↓reduceIte]; rfl

theorem isViable_interp (d : X.FGD) (B : X.Blk) : d.interp.IsViable B := by
  unfold Store.IsViable Store.headHeightFloor
  simp only [not_contest d, ↓reduceIte]
  exact Nat.zero_le _

/-- The frame of the store is `frameOf tree`. -/
theorem toFrame_interp (hX : X.OK) {d : X.FGD} (hM : X.Closed d.tree) :
    d.interp.toFrame = X.frameOf d.tree := by
  have hT := tree_interp hM
  have hF : d.interp.F = X.gBlk := rfl
  have hanc : ∀ B ∈ X.T d.tree, Anc (X.T d.tree) X.gBlk B := fun B hB => gBlk_anc hX hM hB
  simp only [Store.toFrame, frameOf, fcRoot_interp, Store.Anc, hT, hF]
  congr 1
  · ext B; exact ⟨fun h => h.1, fun h => ⟨h, hanc B h⟩⟩
  · ext B
    exact ⟨fun h => h.1, fun h => ⟨h, hanc B h, hanc B h, isViable_interp d B⟩⟩

theorem q_pos : 1 ≤ X.sp.toParams.fg.q := by
  have := X.sp.toParams.hn
  simp only [FG.FGParams.q, Params.fg]; omega

theorem fgView_blk {r : Nat} (hr : r ∈ X.roots) : (X.blk r).fgView = ⟨r, X.slotR r, X.f, []⟩ := by
  obtain ⟨b, hb⟩ := exists_row hr
  obtain ⟨-, hroot⟩ := row_some hb
  simp [Block.fgView, blk, slotR, hb, mkBlk, hroot]

theorem stateTransition_σOf (hX : X.OK) {r : Nat} (hr : r ∈ X.roots) :
    X.sp.toParams.fg.stateTransition (X.σOf (X.par r)) (X.blk r).fgView = some (X.σOf r) := by
  have hlt := slotR_par_lt hX hr
  have hq : X.sp.toParams.fg.q ≠ 0 := by have := q_pos (X := X); omega
  rw [fgView_blk hr]
  unfold FG.FGParams.stateTransition
  dsimp only [Params.fg] at hq ⊢
  simp [σOf, hlt, FG.FGParams.heightEvents, FG.FGParams.finalizePrune, FG.FGParams.bestFinal,
    FG.FGParams.justifies, FG.FGParams.timesOut, hq]
  exact ite_eq_left ⟨hlt, fun a ha => absurd ha List.not_mem_nil⟩

/-- `update_finality` with genesis as `F` and `J` at `h_j = 0`, and a chain state that names
genesis as its justification and finalization at height `0`: only `h_max` moves. -/
theorem updateFinality_frag (st : X.St) (σ' : FG.ChainState X.sp.n)
    (hg : st.blocks X.g = some X.gBlk) (hF : st.F = X.gBlk) (hJ : st.J = X.gBlk)
    (hj : st.hj = 0) (hσJ : σ'.J = X.g) (hσhj : σ'.hj = 0) (hσF : σ'.F = X.g) :
    st.updateFinality σ' = { st with hmax := max st.hmax σ'.h } := by
  obtain ⟨blocks, σ, F, J, hj', hmax, atts⟩ := st
  obtain ⟨L, s, h, Th, ThSlot, target, prog, pending, fin, J', hjσ, F', hF'⟩ := σ'
  dsimp only at hg hF hJ hj hσJ hσhj hσF
  subst hF hJ hj hσJ hσhj hσF
  simp [Store.updateFinality, hg, Store.LexLt]

theorem closed_cons {M : List Nat} (hM : X.Closed M) {r : Nat} (hr : r ∈ X.roots)
    (hp : X.par r ∈ M) : X.Closed (r :: M) := by
  refine ⟨List.mem_cons_of_mem _ hM.g_mem, fun a ha => ?_, fun a ha hag => ?_⟩
  · rcases List.mem_cons.1 ha with rfl | ha
    · exact Or.inr hr
    · exact hM.valid a ha
  · rcases List.mem_cons.1 ha with rfl | ha
    · exact List.mem_cons_of_mem _ hp
    · exact List.mem_cons_of_mem _ (hM.par_mem a ha hag)

/-- `fg_on_block` of a table block. -/
theorem onBlock_interp (hX : X.OK) {d : X.FGD} (hM : X.Closed d.tree) {r : Nat}
    (hr : r ∈ X.roots) : d.interp.onBlock (X.blk r) = (d.onBlock r).map FGD.interp := by
  have hpar := blk_parent_of_mem hr
  have hroot := blk_root (X := X) (Or.inr hr)
  have hrg : r ≠ X.g := fun e => hX.g_not (e ▸ hr)
  by_cases h1 : r ∈ d.tree
  · have e : d.onBlock r = none := by simp [FGD.onBlock, h1]
    rw [e]; unfold Store.onBlock; rw [hpar]; dsimp only
    rw [ite_eq_left (Or.inl (by simp [FGD.interp, hroot, h1]))]; rfl
  by_cases h2 : X.par r ∈ d.tree
  swap
  · have e : d.onBlock r = none := by simp [FGD.onBlock, h2]
    rw [e]; unfold Store.onBlock; rw [hpar]; dsimp only
    rw [ite_eq_left (Or.inr (Or.inl (by simp [FGD.interp, h2])))]; rfl
  have hM' := closed_cons hM hr h2
  have hanc : Goldilocks.Anc (insert (X.blk r) d.interp.tree) d.interp.F (X.blk r) := by
    have e : insert (X.blk r) d.interp.tree = X.T (r :: d.tree) := by
      rw [tree_interp hM]; ext B; simp [T]
    rw [e]; exact gBlk_anc hX hM' (blk_mem_T List.mem_cons_self)
  have hσ : d.interp.σ (X.par r) = X.σOf (X.par r) := by simp [FGD.interp, h2]
  have e : d.onBlock r = some ⟨r :: d.tree, d.atts⟩ := by simp [FGD.onBlock, h1, h2]
  rw [e, Option.map_some]
  unfold Store.onBlock; rw [hpar]; dsimp only
  rw [ite_eq_right (not_or.2 ⟨by simp [FGD.interp, hroot, h1], not_or.2
    ⟨by simp [FGD.interp, h2], not_not.2 hanc⟩⟩), hσ, stateTransition_σOf hX hr]
  dsimp only
  simp only [hroot]
  have hgm : (Function.update d.interp.blocks r (some (X.blk r))) X.g = some X.gBlk := by
    rw [Function.update_of_ne (Ne.symm hrg)]
    simp [FGD.interp, hM.g_mem, blk_g hX]
  rw [updateFinality_frag _ _ hgm rfl rfl rfl rfl rfl rfl]
  simp only [Store.addAtts, blk_fgPayload, List.foldl_nil, FGD.interp]
  have hb : Function.update (fun a => if a ∈ d.tree then some (X.blk a) else none) r
      (some (X.blk r)) = fun a => if a ∈ r :: d.tree then some (X.blk a) else none := by
    funext a
    by_cases ha : a = r
    · subst ha; simp
    · simp [ha]
  have hs : Function.update (fun a => if a ∈ d.tree then X.σOf a
      else FG.ChainState.init X.sp.toParams.fg) r (X.σOf r) =
      fun a => if a ∈ r :: d.tree then X.σOf a else FG.ChainState.init X.sp.toParams.fg := by
    funext a
    by_cases ha : a = r
    · subst ha; simp
    · simp [ha]
  rw [hb, hs]; rfl

theorem onAtt_interp (d : X.FGD) (a : FG.Att X.sp.n) :
    d.interp.onAttestation a = (d.onAtt a).interp := by
  unfold Store.onAttestation FGD.onAtt
  by_cases h : a ∈ d.atts <;> simp [h, FGD.interp]

theorem recI_false : X.recI false = FG.Record.empty := rfl

/-- `fg_attest` of the fragment: the first call signs `attG v`, every later one nothing. -/
theorem attest_interp (hX : X.OK) (d : X.FGD) (signed : Bool) (v : Fin X.sp.n) (C : X.Blk) :
    d.interp.attest (X.recI signed) v C =
      (X.attestD signed v).map (fun a => (a, X.recI true)) := by
  unfold Store.attest
  rw [σ_interp_Th, σ_interp_g hX]
  cases signed <;>
    simp [recI, attestD, FG.Record.createAtt, FG.ChainState.init, Params.fg,
      FG.Record.heightPair, FG.Record.empty, recSigned, FG.Record.finalityPair,
      FG.ChainState.previousHeightJustified, FG.Record.recordAtt, attG, FG.Att.content]

/-! ## The frame `frameOf M` -/

variable {M : List Nat}

theorem inTree_frameOf (hM : X.Closed M) {r : Nat} : InTree (X.frameOf M) r ↔ r ∈ M := by
  constructor
  · rintro ⟨B, hB, rfl⟩; exact (root_mem_of_T hM hB).1
  · intro hr; exact ⟨X.blk r, blk_mem_T hr, blk_root (hM.valid r hr)⟩

theorem lookup_frameOf (hM : X.Closed M) (r : Nat) :
    lookup (X.frameOf M) r = if r ∈ M then some (X.blk r) else none := by
  split_ifs with hr
  · cases h : lookup (X.frameOf M) r with
    | none => exact absurd ((inTree_frameOf hM).2 hr) (lookup_eq_none h)
    | some H =>
      obtain ⟨hH, hroot⟩ := lookup_eq_some h
      rw [(root_mem_of_T hM hH).2, hroot]
  · cases h : lookup (X.frameOf M) r with
    | none => rfl
    | some H =>
      obtain ⟨hH, hroot⟩ := lookup_eq_some h
      exact absurd (hroot ▸ (root_mem_of_T hM hH).1) hr

theorem anc_frameOf (hX : X.OK) (hM : X.Closed M) {a b : Nat} (ha : X.Valid a) (hb : b ∈ M) :
    (X.frameOf M).Anc (X.blk a) (X.blk b) ↔ a ∈ X.chain b := anc_T_blk hX hM ha hb

theorem ancR_frameOf (hX : X.OK) (hM : X.Closed M) {a : Nat} (ha : X.Valid a) (r : Nat) :
    AncR (X.frameOf M) (X.blk a) r ↔ r ∈ M ∧ a ∈ X.chain r := by
  constructor
  · rintro ⟨R, hR, rfl, h⟩
    obtain ⟨hm, e⟩ := root_mem_of_T hM hR
    rw [e] at h
    exact ⟨hm, (anc_frameOf hX hM ha hm).1 h⟩
  · rintro ⟨hr, h⟩
    exact ⟨X.blk r, blk_mem_T hr, blk_root (hM.valid r hr), (anc_frameOf hX hM ha hr).2 h⟩

theorem compatible_frameOf (hX : X.OK) (hM : X.Closed M) {a b : Nat} (ha : a ∈ M) (hb : b ∈ M) :
    Compatible (X.frameOf M).tree (X.blk a) (X.blk b) ↔ a ∈ X.chain b ∨ b ∈ X.chain a :=
  or_congr (anc_frameOf hX hM (hM.valid a ha) hb) (anc_frameOf hX hM (hM.valid b hb) ha)

theorem viableTree_frameOf (hX : X.OK) (hM : X.Closed M) {S : Set X.Blk}
    (hS : S ⊆ X.T M) : (X.frameOf M).viableTree S = S := by
  ext B
  refine ⟨fun h => h.1, fun h => ⟨h, gBlk_anc hX hM (hS h), B, h, hS h, .refl⟩⟩

theorem viableAncestor_frameOf (hX : X.OK) (hM : X.Closed M) {B : X.Blk} (hB : B ∈ X.T M) :
    (X.frameOf M).viableAncestor B = B :=
  viableAncestor_self (frameOK hX hM) hB
    (Or.inl ((viableTree_frameOf hX hM le_rfl).symm ▸ hB))

end Fix

end Consensus.Goldilocks.Test.HalfCommittee

end
