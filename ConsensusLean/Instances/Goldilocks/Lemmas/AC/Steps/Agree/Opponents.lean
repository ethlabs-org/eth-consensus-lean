module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.MergedOpponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks AC: proposer and voters agree on unlocking (A1.1)

The proposal's view and an honest voter's merged view give the same opponents to every block of
slot at most `s`, under `Sync[t_s, t_{s+1}]`, when both frames hold the same blocks of slot at
most `s`. The same synchrony window ensures that the voter's read point backs each declared vote
of the honest proposer.

The merged view is the voter's slot-`s` votes held before the freeze `t_s + 3Δ` and the votes of
the slot-`(s+1)` proposals of its tree; the proposer is honest, so its proposal is the only one
(`HonestObjects.one_block`), and the proposal view is the proposer's slot-`s` pool. Each early
vote of the voter was admitted at a time in `[t_s, t_s + 3Δ)`; under `Sync` the proposer,
joined at `t_{s+1}`, processed it before `t_{s+1}`: it holds the vote, or two other votes of its
validator. Heads of slot at most `s` are in both trees, ancestry below slot `s` is the same, and the
proposer has stamped the blocks of its tree, so a resolved vote at the voter is resolved at the
proposer. -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → ACState sp.n}

/-- `frameIn_of_callU` with the unlock given. -/
theorem frameIn_of_callU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

/-- Every block of an honest node's frame is genesis or was accepted by the node. With the unlock
given. -/
theorem frame_acceptedU
    {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ {ℓ : ACLabel (goldilocksAC sp FGP ro)}, tr.CallAt y i ℓ → ∀ X ∈ ℓ.frame.tree,
      X.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k X := by
  have step : ∀ (Φ Φ' : Frm sp.n FGP) (t : Time) (c : (goldilocksAC sp FGP ro).Call),
      (goldilocksAC sp FGP ro).CallOK U Φ t c Φ' → ∀ X ∈ Φ'.tree, X ∈ Φ.tree ∨ c = .block X := by
    intro Φ Φ' t c hok X hX
    obtain ⟨-, hc⟩ := hok
    cases c with
    | block B =>
      obtain ⟨hs, -, -⟩ := hc
      rw [hs.tree_eq] at hX
      rcases hX.1 with rfl | hX
      · exact Or.inr rfl
      · exact Or.inl hX
    | message m => exact Or.inl (hc.1 ▸ hX)
    | tick => exact Or.inl (hc ▸ hX)
    | proposal => exact Or.inl (hc ▸ hX)
    | toFG => exact Or.inl (hc ▸ hX)
    | restart => exact Or.inl (hc ▸ hX)
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc X hX
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, -⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · rcases step _ _ _ _ hok X hX with h | h
      · rw [htree, Set.mem_singleton_iff] at h
        exact Or.inl (h ▸ hroot)
      · exact Or.inr ⟨i, le_rfl, ℓ, hc, h⟩
    · rcases step _ _ _ _ hok X hX with h | h
      · exact (ih j hj hc' X h).imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans hj.le, h⟩
      · exact Or.inr ⟨i, le_rfl, ℓ, hc, h⟩

/-- The genesis block of an honest node's initial frame is in `U`, with slot `0`. -/
private theorem genesis_memU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ {ℓ : ACLabel (goldilocksAC sp FGP ro)}, tr.CallAt y i ℓ →
      ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.slot = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, hslot, -⟩, ⟨-, hsub⟩, -⟩ | ⟨j, ℓ', hj, hc', -⟩
    · exact ⟨Φ₀.F, hsub (htree ▸ rfl), hroot, hslot⟩
    · exact ih j hj hc'

/-- An honest proposer of a slot `σ > 0` has at most one block of slot `σ` in the honest frames.
With the unlock given. -/
theorem frameBlock_uniqueU
    {ini} {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U ini) {σ : Nat} (hσ : σ ≠ 0)
    (hp : proposer σ ∈ H) {B B' : Blk sp.n FGP} (hB : HonestFrameBlock tr H B)
    (hB' : HonestFrameBlock tr H B') (hs : B.slot = σ) (hs' : B'.slot = σ) : B = B' := by
  have hr := hrun.localRun
  have hprop : ∀ X, HonestFrameBlock tr H X → X.slot = σ → X.proposer = proposer σ := by
    rintro X ⟨y, hy, i, ℓ, hc, hX⟩ hXs
    obtain ⟨G, hG, hGr, hGs⟩ := genesis_memU hr hy i hc
    refine hXs ▸ hrun.honest.proposer X ⟨y, hy, i, ℓ, hc, hX⟩ fun hXr => hσ ?_
    rw [← hXs, hr.coherent.1 ((frameIn_of_callU hr hy hc).2 hX) hG (hXr.trans hGr.symm), hGs]
  exact hrun.honest.one_block B B' hB hB' (hprop B hB hs ▸ hp)
    ((hprop B hB hs).trans (hprop B' hB' hs').symm) (hs.trans hs'.symm)

/-- A vote with a finite stamp whose head is a stamped block of the tree of slot at most the
vote's is resolved. -/
theorem resolutionTime_ne_top {A : ACState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {v : Vote sp.n} {Hd : Blk sp.n FGP} (hHd : Hd ∈ Φ.tree) (hr : Hd.root = v.head)
    (hs : Hd.slot ≤ v.slot) (hv : A.voteStamp v ≠ ⊤) (hb : A.blockStamp v.head ≠ ⊤) :
    resolutionTime A Φ v ≠ ⊤ := by
  unfold resolutionTime
  split
  · rename_i hl
    exact absurd ⟨Hd, hHd, hr⟩ (lookup_eq_none hl)
  · rename_i Hd' hl
    obtain ⟨hHd', hr'⟩ := lookup_eq_some hl
    have : Hd' = Hd := hΦ.coherent.1 hHd' hHd (hr'.trans hr.symm)
    subst this
    split_ifs with hlt
    · omega
    · exact (max_lt (lt_top_iff_ne_top.2 hv) (lt_top_iff_ne_top.2 hb)).ne

theorem mem_voteViewList_fst {A : ACState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {c : ETime} {v : Vote sp.n} :
    v ∈ (voteViewList A Φ (s : Int) c).1 ↔ v ∈ A.pool s ∧ A.voteStamp v < c := by
  simp [voteViewList, ACState.poolAt]

theorem mem_voteViewList_snd {A : ACState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {c : ETime} {v : Vote sp.n} :
    v ∈ (voteViewList A Φ (s : Int) c).2 ↔
      (v ∈ A.pool s ∧ A.voteStamp v < c) ∧ resolutionTime A Φ v < c := by
  simp [voteViewList, ACState.poolAt]
  tauto

theorem etime_of_lt_top (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top t)

/-- `proposal_payload` with the unlock given. -/
theorem proposal_payloadWith
    {L : Set Lock} {A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposalWith sp L A Φ t).2 = some (d, pay)) :
    joined sp A t ∧ pay = voteViewList A Φ ((sp.slot t : Int) - 1) ⊤ ∧
      (acProposalWith sp L A Φ t).1.restartTime = A.restartTime := by
  unfold acProposalWith at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hj
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hj, h.2.symm, rfl⟩

/-- The payload of a proposal is the proposer's view of the previous slot's pool, and the
proposer is joined. -/
theorem proposal_payload {A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposal sp A Φ t).2 = some (d, pay)) :
    joined sp A t ∧ pay = voteViewList A Φ ((sp.slot t : Int) - 1) ⊤ ∧
      (acProposal sp A Φ t).1.restartTime = A.restartTime :=
  proposal_payloadWith (A := A) (Φ := Φ) (t := t) (d := d) (pay := pay) (h := h)

end Consensus.Goldilocks.AC

end
