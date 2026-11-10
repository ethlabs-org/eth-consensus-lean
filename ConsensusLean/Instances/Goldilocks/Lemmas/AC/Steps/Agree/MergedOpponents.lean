module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import Mathlib.Tactic.Ring

public section

/-! # Goldilocks SA: the proposal's view and a merged view give the same opponents

The view step of A1.1, over two frames and two states. The proposal's view is the slot-`s` pool
of a state `A` (every vote stamped, `hpool`), with its resolved votes as support; the merged view
of slot `s + 1` at a read point `R` is `R`'s slot-`s` votes held before the freeze `t_s + 3Δ`
and the votes of the only slot-`(s+1)` block `P` of the voter's tree (`hblk`), whose payload is
the proposal's view. What the run provides enters as premises: every early vote of `R` is in
`A`'s pool or makes its validator an equivocator there (`hstar`), a pooled vote whose head is a
block of the proposer's tree of slot at most the vote's is resolved there (`hres`), and the two
trees hold the same blocks of slot at most `s`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- Ancestry below a block of slot at most `s` only reads the blocks of slot at most `s`. -/
private theorem anc_of_slot_le {S S' : Set (Blk sp.n FGP)} (hS : Coherent S) {s : Nat}
    (heq : {X | X ∈ S ∧ X.slot ≤ s} = {X | X ∈ S' ∧ X.slot ≤ s}) {X Y : Blk sp.n FGP}
    (h : Anc S X Y) (hY : Y.slot ≤ s) : Anc S' X Y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail Z Y _ hZY ih =>
    have hlt := hS.2 _ hZY.1 _ hZY.2.1 hZY.2.2
    have hZ : Z ∈ {X | X ∈ S' ∧ X.slot ≤ s} := by rw [← heq]; exact ⟨hZY.1, by omega⟩
    have hY' : Y ∈ {X | X ∈ S' ∧ X.slot ≤ s} := by rw [← heq]; exact ⟨hZY.2.1, hY⟩
    exact (ih (by omega)).tail ⟨hZ.1, hY'.1, hZY.2.2⟩

private theorem compatible_of_slot_le {S S' : Set (Blk sp.n FGP)} (hS : Coherent S) {s : Nat}
    (heq : {X | X ∈ S ∧ X.slot ≤ s} = {X | X ∈ S' ∧ X.slot ≤ s}) {X Y : Blk sp.n FGP}
    (hX : X.slot ≤ s) (hY : Y.slot ≤ s) (h : Compatible S X Y) : Compatible S' X Y :=
  h.imp (fun h => anc_of_slot_le hS heq h hY) fun h => anc_of_slot_le hS heq h hX

/-- A resolved vote has its head in the tree, of slot at most the vote's. -/
private theorem resolved_head {A : SAState sp.n} {Φ : Frm sp.n FGP} {v : Vote sp.n}
    (h : resolutionTime A Φ v ≠ ⊤) : ∃ Hd ∈ Φ.tree, Hd.root = v.head ∧ Hd.slot ≤ v.slot := by
  unfold resolutionTime at h
  split at h
  · exact absurd rfl h
  · rename_i Hd hl
    obtain ⟨hHd, hr⟩ := lookup_eq_some hl
    split_ifs at h with hlt
    · exact absurd rfl h
    · exact ⟨Hd, hHd, hr, by omega⟩

private theorem mem_fst {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat} {c : ETime}
    {v : Vote sp.n} : v ∈ (voteViewList A Φ (s : Int) c).1 ↔ v ∈ A.pool s ∧ A.voteStamp v < c := by
  simp [voteViewList, SAState.poolAt]

private theorem mem_snd {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat} {c : ETime}
    {v : Vote sp.n} : v ∈ (voteViewList A Φ (s : Int) c).2 ↔
      (v ∈ A.pool s ∧ A.voteStamp v < c) ∧ resolutionTime A Φ v < c := by
  simp [voteViewList, SAState.poolAt]
  tauto

/-- **The votes of the merged view are the pool's, or make their validator an equivocator
there**: the early votes of the read point `R` are by `hstar`, and the votes of the only
slot-`(s+1)` block `P` of the tree are the slot-`s` votes of `A`'s pool. -/
theorem merged_votes_of_early {A R : SAState sp.n} {Φp Φy : Frm sp.n FGP} {s : Nat}
    {P : Blk sp.n FGP} (hPv : blockVotes P = (voteViewList A Φp (s : Int) ⊤).1)
    (hblk : ∀ X ∈ Φy.tree, X.slot = s + 1 → X = P)
    (hstar : ∀ x ∈ R.pool s, R.voteStamp x < ETime.of (sp.ts s + 3 * sp.Δ) →
      x ∈ A.pool s ∨ x.val ∈ equivocators {w | w ∈ A.pool s}) :
    ∀ v ∈ (mergedVoteView sp R Φy (s + 1)).votes,
      v ∈ A.pool s ∨ v.val ∈ equivocators {w | w ∈ A.pool s} := by
  have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rintro v (hv | ⟨X, hX, hXs, hv⟩)
  · change v ∈ (voteViewList _ _ _ _).1 at hv
    rw [hcast, mem_fst] at hv
    exact hstar v hv.1 (by simpa [freeze, hcast] using hv.2)
  · rw [hblk X hX hXs] at hv
    exact Or.inl (mem_fst.1 (hPv ▸ hv)).1

/-- **The proposal's view and the merged view give the same opponents** to every block `B` of
slot at most `s`, when the proposer's tree (of `Φp`) and the voter's tree (of `Φy`) hold the
same blocks of slot at most `s`, `P ∈ Φy.tree` (slot `s + 1`, the only one there) carries the
proposal's view as its payload, and the premises `hpool`, `hres`, `hstar` hold. -/
theorem opponents_eq_of_merged {A R : SAState sp.n} {Φp Φy : Frm sp.n FGP} {s : Nat}
    {P B : Blk sp.n FGP} (hΦp : FrameOK Φp) (hΦy : FrameOK Φy)
    (heq : {X | X ∈ Φp.tree ∧ X.slot ≤ s} = {X | X ∈ Φy.tree ∧ X.slot ≤ s})
    (hP : P ∈ Φy.tree) (hPs : P.slot = s + 1)
    (hPv : blockVotes P = (voteViewList A Φp (s : Int) ⊤).1)
    (hPsup : blockSupport P = (voteViewList A Φp (s : Int) ⊤).2)
    (hblk : ∀ X ∈ Φy.tree, X.slot = s + 1 → X = P)
    (hpool : ∀ w ∈ A.pool s, A.voteStamp w < ⊤)
    (hres : ∀ x ∈ A.pool s, ∀ Hd ∈ Φp.tree, Hd.root = x.head → Hd.slot ≤ x.slot →
      resolutionTime A Φp x ≠ ⊤)
    (hstar : ∀ x ∈ R.pool s, R.voteStamp x < ETime.of (sp.ts s + 3 * sp.Δ) →
      x ∈ A.pool s ∨ x.val ∈ equivocators {w | w ∈ A.pool s})
    (hBs : B.slot ≤ s) :
    opponents sp Φp (View.ofLists (voteViewList A Φp (s : Int) ⊤)) s B =
      opponents sp Φy (mergedVoteView sp R Φy (s + 1)) s B := by
  have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  have hset : {w | w ∈ (voteViewList A Φp (s : Int) ⊤).1} = {w | w ∈ A.pool s} :=
    Set.ext fun w => mem_fst.trans ⟨And.left, fun h => ⟨h, hpool w h⟩⟩
  have hvotes := merged_votes_of_early hPv hblk hstar
  have hmem : ∀ X : Blk sp.n FGP, X.slot ≤ s → (X ∈ Φp.tree ↔ X ∈ Φy.tree) := by
    intro X hX
    have hh := Set.ext_iff.1 heq X
    exact ⟨fun h => (hh.mp ⟨h, hX⟩).1, fun h => (hh.mpr ⟨h, hX⟩).1⟩
  have hcomp : ∀ Hd : Blk sp.n FGP, Hd.slot ≤ s →
      (Compatible Φp.tree Hd B ↔ Compatible Φy.tree Hd B) := fun Hd hHd =>
    ⟨compatible_of_slot_le hΦp.coherent heq hHd hBs,
      compatible_of_slot_le hΦy.coherent heq.symm hHd hBs⟩
  change opponents sp Φp ⟨{w | w ∈ (voteViewList _ _ _ _).1}, _⟩ s B = _
  rw [hset]
  ext w
  constructor
  · rintro (⟨a, ha, b, hb, hab, rfl, hbv⟩ | ⟨x, hx, rfl, hxs, Hd, hHd, hHdr, hnc⟩)
    · have hm : ∀ v ∈ A.pool s, v ∈ (mergedVoteView sp R Φy (s + 1)).votes := fun v hv =>
        Or.inr ⟨P, hP, hPs, hPv ▸ mem_fst.2 ⟨hv, hpool v hv⟩⟩
      exact Or.inl ⟨a, hm a ha, b, hm b hb, hab, rfl, hbv⟩
    · obtain ⟨-, hrt⟩ := mem_snd.1 hx
      obtain ⟨Hd', hHd', hHd'r, hHd's⟩ := resolved_head hrt.ne
      have hh : Hd' = Hd := hΦp.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
      subst hh
      have hHds : Hd'.slot ≤ s := by omega
      exact Or.inr ⟨x, Or.inr ⟨P, hP, hPs, hPsup ▸ hx, by omega, Hd', (hmem _ hHds).1 hHd,
        hHdr, by omega⟩, rfl, hxs, Hd', (hmem _ hHds).1 hHd, hHdr,
        fun h => hnc ((hcomp _ hHds).2 h)⟩
  · rintro (⟨a, ha, b, hb, hab, rfl, hbv⟩ | ⟨x, hx, rfl, hxs, Hd, hHd, hHdr, hnc⟩)
    · rcases hvotes a ha with ha' | ha'
      · rcases hvotes b hb with hb' | hb'
        · exact Or.inl ⟨a, ha', b, hb', hab, rfl, hbv⟩
        · exact Or.inl (hbv ▸ hb')
      · exact Or.inl ha'
    · rcases hx with hx | ⟨X, hX, hXs, hx, -, Hd', hHd', hHd'r, hHd's⟩
      · -- an early support vote of the voter
        change x ∈ (voteViewList _ _ _ _).2 at hx
        rw [hcast, mem_snd] at hx
        obtain ⟨⟨hxp, hxt⟩, hrt⟩ := hx
        obtain ⟨Hd', hHd', hHd'r, hHd's⟩ :=
          resolved_head (hrt.trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))).ne
        have hh : Hd' = Hd := hΦy.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
        subst hh
        have hHds : Hd'.slot ≤ s := by omega
        have hHdp := (hmem _ hHds).2 hHd
        rcases hstar x hxp (by simpa [freeze, hcast] using hxt) with hxP | hxP
        · -- the proposer holds it, resolved
          exact Or.inr ⟨x, mem_snd.2 ⟨⟨hxP, hpool x hxP⟩,
            lt_top_iff_ne_top.2 (hres x hxP Hd' hHdp hHdr hHd's)⟩,
            rfl, hxs, Hd', hHdp, hHdr, fun h => hnc ((hcomp _ hHds).1 h)⟩
        · exact Or.inl hxP
      · -- a support entry of the proposal
        rw [hblk X hX hXs] at hx
        have hh : Hd' = Hd := hΦy.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
        subst hh
        have hHds : Hd'.slot ≤ s := by omega
        exact Or.inr ⟨x, hPsup ▸ hx, rfl, hxs, Hd', (hmem _ hHds).2 hHd, hHdr,
          fun h => hnc ((hcomp _ hHds).1 h)⟩

end Consensus.Goldilocks.SA

end
