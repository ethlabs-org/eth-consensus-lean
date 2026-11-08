module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Outage.Delivery
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The outage over AC traces, the restored side: the gate count and read majority

The gate rows of the outage census (`Compose/Regimes/OutageGate`), stated over an AC trace of the
SA with the unlock given at a write mode (`ACRunU wm u`), with the receiver-scoped service after
`g` (`Compose.ReceiverServiceAfter`) as hypothesis and the frames of the calls in place of node
frames:

* the extending majority at a label (`ExtendingCastersAC`, `OpponentsAC`, `ExtendingMajorityAC`:
  `Compose.ExtendingCasters`, `Compose.Opponents`, `Compose.ExtendingMajority` read on the AC
  trace, with ancestry inside `U`);
* L1 (`vote_held_before_earlyAC`): an honest slot-`q` vote whose head extends the call's `Φ.F`
  is pooled, its head is in the call's frame, and the vote is resolved before `t_q + 2Δ`, at
  every honest call from `t_q + 2Δ` without a restart after `t_q` (D3 with the voter's head facts,
  `honest_head_frameU`, `Compose.frame_anc_acceptedU`);
* L-gate (`gate_result_extendsAC`): at an honest joined update of a label from GST, with its
  call's frame below `B` and an extending majority for `B`, the update returns a result, and
  every result extends `B`;
* L3 (`read_majority_of_extendingAC`): the latest view of the state after an honest call, with
  that call's frame, has fewer voters than twice the supporters of `B` when the extending casters
  of its label outnumber the opponents and every extending vote is delivered. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {g : Time}

/-! ### The extending majority at a label -/

/-- The honest slot-`q` casters whose vote extends `B` inside `U`. -/
def ExtendingCastersAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (B : Blk sp.n FGP) (q : Nat) : Set (Fin sp.n) :=
  {x | x ∈ H ∧ ∃ k e, VoteAt tr x k e ∧ e.msg.slot = q ∧ VoteExtends U e.msg B}

/-- The faulty validators and the honest slot-`q` casters whose vote does not extend `B`. -/
def OpponentsAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (B : Blk sp.n FGP) (q : Nat) : Set (Fin sp.n) :=
  Hᶜ ∪ {x | x ∈ H ∧ ∃ k e, VoteAt tr x k e ∧ e.msg.slot = q ∧ ¬ VoteExtends U e.msg B}

/-- The extending majority: the extending casters of label `q` outnumber its opponents. -/
def ExtendingMajorityAC (tr : SATrace sp FGP ro) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (B : Blk sp.n FGP) (q : Nat) : Prop :=
  (OpponentsAC tr H U B q).ncard < (ExtendingCastersAC tr H U B q).ncard

theorem extendingCastersAC_iff {B : Blk sp.n FGP} {q : Nat} {x : Fin sp.n} :
    x ∈ ExtendingCastersAC tr H U B q ↔
      x ∈ H ∧ ∃ k e, VoteAt tr x k e ∧ e.msg.slot = q ∧ VoteExtends U e.msg B :=
  Iff.rfl

theorem opponentsAC_iff {B : Blk sp.n FGP} {q : Nat} {x : Fin sp.n} :
    x ∈ OpponentsAC tr H U B q ↔ x ∈ Hᶜ ∨
      (x ∈ H ∧ ∃ k e, VoteAt tr x k e ∧ e.msg.slot = q ∧ ¬ VoteExtends U e.msg B) :=
  Iff.rfl

theorem extendingMajorityAC_iff {B : Blk sp.n FGP} {q : Nat} :
    ExtendingMajorityAC tr H U B q ↔
      (OpponentsAC tr H U B q).ncard < (ExtendingCastersAC tr H U B q).ncard :=
  Iff.rfl

/-! ### Helpers -/

/-- A block between `Φ.F` and a block of a well-formed frame is in the frame. -/
private theorem mem_tree_between (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {B C : Blk sp.n FGP} (hFB : Anc U Φ.F B) (h : Anc U B C) :
    C ∈ Φ.tree → B ∈ Φ.tree := by
  induction h with
  | refl => exact id
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = Φ.F
    · subst hdF
      obtain rfl := Anc.antisymm hU hFB (hBc.tail e)
      exact hΦ.rooted.1
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    have hpc : p = c := hU.1 (hΦU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    subst hpc
    exact ih hp.1

/-- The votes and the support of the latest view, of slot `L` (`Compose.latestView_mem` for every
payload type). -/
private theorem latestView_memAC {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time} {L : Nat}
    (hL : (L : Int) = (latestView sp A Φ t).2) (v : Vote sp.n) :
    (v ∈ (latestView sp A Φ t).1.votes ↔ v ∈ A.pool L ∧ A.voteStamp v < ⊤) ∧
      (v ∈ (latestView sp A Φ t).1.support ↔
        (v ∈ A.pool L ∧ A.voteStamp v < ⊤) ∧ resolutionTime A Φ v < ⊤) := by
  simp only [latestView] at hL ⊢
  rw [← hL]
  simp only [voteView, voteViewList, View.ofLists, SAState.poolAt, Set.mem_ofPred_eq,
    List.mem_filter, decide_eq_true_eq, Int.natCast_nonneg, not_lt.2, ↓reduceIte,
    Int.toNat_natCast, and_assoc, true_and]

/-- An honest validator's slot-`s` pool votes of an honest validator `x` at cut `c` are its one
slot-`s` vote. -/
private theorem pool_vote_eq (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e)
    (hs : e.msg.slot = s) {v : Vote sp.n} (hvp : v ∈ (tr.state y c).pool s) (hvx : v.val = x) :
    v = e.msg := by
  have hr := hrun.localRun
  obtain ⟨j', -, e', hv', rfl⟩ := hrun.honest.pool_vote y hy c s v hvp (hvx ▸ hx)
  have hs' := state_pool_slotU sp hr hy c s _ hvp
  rw [hvx] at hv'
  exact congrArg (fun e : Em sp FGP => e.msg)
    (one_vote_per_slotU sp FGP ro H U tr hr x hx j' j e' e hv' hv (hs'.trans hs.symm)).2

/-- The voters of the slot-`s` pool of an honest validator are extending casters or opponents. -/
private theorem pool_voters_sub (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n} (hy : y ∈ H)
    {c s : Nat} (B : Blk sp.n FGP) {S : Set (Vote sp.n)} (hS : ∀ v ∈ S, v ∈ (tr.state y c).pool s) :
    voters S ⊆ ExtendingCastersAC tr H U B s ∪ OpponentsAC tr H U B s := by
  rintro w ⟨v, hv, rfl⟩
  by_cases hw : v.val ∈ H
  · obtain ⟨j, -, e, he, rfl⟩ := hrun.honest.pool_vote y hy c s _ (hS v hv) hw
    have hs := state_pool_slotU sp hrun.localRun hy c s _ (hS _ hv)
    by_cases hext : VoteExtends U e.msg B
    · exact Or.inl (extendingCastersAC_iff.2 ⟨hw, j, e, he, hs, hext⟩)
    · exact Or.inr (opponentsAC_iff.2 (Or.inr ⟨hw, j, e, he, hs, hext⟩))
  · exact Or.inr (opponentsAC_iff.2 (Or.inl hw))

/-! ### L1, L-gate, L3 -/

/-- **L1** (`Compose.vote_held_before_early` with the unlock given). An honest slot-`q` vote
whose head extends the call's `Φ.F` is held, its head in the call's frame, and resolved strictly
before `t_q + 2Δ`, at every honest call from `t_q + 2Δ` with no restart after `t_q`, under the
service from `g ≤ t_q + Δ`. -/
theorem vote_held_before_earlyAC (hrun : ACRunU wm u proposer tr H U)
    (hS : ∀ y ∈ H, Compose.ReceiverServiceAfter H U g y tr)
    {y : Fin sp.n} (hy : y ∈ H) {q c : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hc : tr.CallAt y c ℓ) (hct : sp.ts q + 2 * sp.Δ ≤ tr.time c) (hg : g ≤ sp.ts q + sp.Δ)
    (hres : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ sp.ts q)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP} (hv : VoteAt tr x i e)
    (hes : e.msg.slot = q) {Hd : Blk sp.n FGP} (hHd : Hd ∈ U) (hHdr : Hd.root = e.msg.head)
    (hF : Anc U ℓ.frame.F Hd) :
    e.msg ∈ (tr.state y c).pool q ∧ Hd ∈ ℓ.frame.tree ∧
      resolutionTime (tr.state y c) ℓ.frame e.msg < ETime.of (sp.ts q + 2 * sp.Δ) := by
  have hr := hrun.localRun
  obtain ⟨ℓv, hcv, hev⟩ := hv
  obtain ⟨Hd₀, hHd₀, hHd₀r, hHd₀s⟩ := honest_head_frameU hr hx ⟨hcv, hev⟩
  obtain ⟨-, hΦvU⟩ := frameIn_of_callAtU hr hx hcv
  obtain rfl : Hd₀ = Hd := hr.coherent.1 (hΦvU hHd₀) hHd (hHd₀r.trans hHdr.symm)
  have hsig := vote_signer_slotAC hr hx ⟨ℓv, hcv, hev⟩
  have htj : tr.time i ≤ sp.ts q + sp.Δ := by
    have h := vote_time_leU hr hx ⟨ℓv, hcv, hev⟩
    rw [← hsig.2, hes] at h
    exact h
  have hacc : Hd₀.root = sp.genesisRoot ∨
      ∃ k, tr.AcceptAt x k Hd₀ ∧ tr.time k ≤ sp.ts q + sp.Δ := by
    rcases Compose.frame_anc_acceptedU hr hx i ℓv hcv Hd₀ hHd₀ Hd₀ .refl with
      hgen | ⟨k, hk, hak⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨k, hak, (hr.time_mono hk).trans htj⟩
  exact vote_resolved_before_earlyAC hrun hS hy hc hct hg hres hx ⟨ℓv, hcv, hev⟩ hes hHd hHdr
    (by rw [← hes]; exact hHd₀s) hacc hF

/-- **L-gate** (`Compose.gate_result_extends` with the unlock given). A joined honest update of a
label `s` from GST (`g ≤ t_s + Δ`) whose call's frame is below `B` returns a result, and every
result of it extends `B`, when the extending casters of the label outnumber its opponents. -/
theorem gate_result_extendsAC (hrun : ACRunU wm u proposer tr H U)
    (hS : ∀ y ∈ H, Compose.ReceiverServiceAfter H U g y tr)
    {y : Fin sp.n} (hy : y ∈ H) {c s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hu : UpdateAt tr y c s ℓ) (hg : g ≤ sp.ts s + sp.Δ) {B : Blk sp.n FGP}
    (hmaj : ExtendingMajorityAC tr H U B s) (hFB : Anc U ℓ.frame.F B) :
    (∃ C CV, ResultAt tr y c s C CV) ∧ ∀ C CV, ResultAt tr y c s C CV → Anc U B C := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hres := update_restartsAC hr hy hu
  have hct : sp.ts s + 2 * sp.Δ ≤ tr.time c := by
    have : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
    linarith
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hu.1
  set A := tr.state y c
  -- every extending caster is delivered: pooled, its head framed, resolved early
  have hdel : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = s →
      ∀ Hd ∈ U, Hd.root = e.msg.head → Anc U B Hd →
      e.msg ∈ A.pool s ∧ Hd ∈ ℓ.frame.tree ∧
        resolutionTime A ℓ.frame e.msg < ETime.of (sp.ts s + 2 * sp.Δ) :=
    fun x hx k e hv hes Hd hHd hHdr hBHd =>
      vote_held_before_earlyAC hrun hS hy hu.1 hct hg hres hx hv hes hHd hHdr (hFB.trans hBHd)
  -- `B` is in the frame: an extending caster exists, and its head is framed above `B`
  have hBt : B ∈ ℓ.frame.tree := by
    have hpos : 0 < (ExtendingCastersAC tr H U B s).ncard :=
      lt_of_le_of_lt (Nat.zero_le _) (extendingMajorityAC_iff.1 hmaj)
    obtain ⟨x, hxE⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    obtain ⟨hx, k, e, hv, hes, Hd, hHd, hHdr, hBHd⟩ := extendingCastersAC_iff.1 hxE
    exact mem_tree_between hU hΦ hΦU hFB hBHd (hdel x hx k e hv hes Hd hHd hHdr hBHd).2.1
  set V : View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    resolutionTime A ℓ.frame v < ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hsupp : ExtendingCastersAC tr H U B s ⊆ supporters ℓ.frame V s B := by
    intro x hxE
    obtain ⟨hx, k, e, hv, hes, Hd, hHd, hHdr, hBHd⟩ := extendingCastersAC_iff.1 hxE
    obtain ⟨hvp, hHdt, hrs⟩ := hdel x hx k e hv hes Hd hHd hHdr hBHd
    refine ⟨?_, e.msg, ⟨hvp, hrs⟩, (vote_signer_slotAC hr hx hv).1, by exact_mod_cast hes,
      Hd, hHdt, hHdr, anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHdt⟩
    rintro ⟨v, hv1, v', hv2, hne, hvx, hv'x⟩
    exact hne ((pool_vote_eq hrun hy hx hv hes hv1 hvx).trans
      (pool_vote_eq hrun hy hx hv hes hv2 hv'x).symm)
  have hvot := pool_voters_sub hrun hy (c := c) (s := s) B (S := {v | v ∈ A.pool s})
    fun _ h => h
  have hmaj' : (voters {v | v ∈ A.pool s}).ncard <
      2 * confirmationScore sp A ℓ.frame s B := by
    have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
    have h2 := Set.ncard_union_le (ExtendingCastersAC tr H U B s) (OpponentsAC tr H U B s)
    have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
    have h4 := extendingMajorityAC_iff.1 hmaj
    change _ < 2 * (supporters ℓ.frame V s B).ncard
    omega
  -- the confirmation is the deepest majority block, which `B` is below
  set S := {X | X ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F X ∧
    (voters {v | v ∈ A.pool s}).ncard < 2 * confirmationScore sp A ℓ.frame s X}
  have hS' : S ⊆ ℓ.frame.tree := fun X hX => hX.1
  have hcs : ∀ X, confirmationScore sp A ℓ.frame s X = (supporters ℓ.frame V s X).ncard :=
    fun _ => rfl
  have hsub : V.support ⊆ V.votes := fun _ hv => hv.1
  have hch : ∀ X ∈ S, ∀ Y ∈ S, Compatible ℓ.frame.tree X Y := fun X hX Y hY =>
    majority_chain sp _ ℓ.frame V s X Y hΦ hsub hX.1 hY.1 (hcs X ▸ hX.2.2) (hcs Y ▸ hY.2.2)
  have hBS : B ∈ S := ⟨hBt, hΦ.rooted.2 B hBt, hmaj'⟩
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS' ⟨B, hBS⟩
  have hBD := anc_deepest hΦ hS' hch hD B hBS
  have hD' : getConfirmation sp A ℓ.frame s = some D := hD
  refine ⟨⟨D, _, ℓ, hu, hD', rfl⟩, ?_⟩
  rintro C CV ⟨ℓ', hu', hC, -⟩
  obtain rfl : ℓ' = ℓ := Option.some.inj (hu'.1.2.symm.trans hu.1.2)
  have hCD : C = D := Option.some.inj (hC.symm.trans hD')
  subst hCD
  exact hBD.mono hΦU

/-- **L3** (`Compose.read_majority_of_extending` with the unlock given, read at a call). The latest
view of the state after an honest call, with that call's frame, has fewer voters than twice the
supporters of `B`, when the extending casters of the view's label outnumber its opponents and
every extending vote is delivered (pooled after the call, its head in the call's frame with a
finite stamp). -/
theorem read_majority_of_extendingAC (hrun : ACRunU wm u proposer tr H U) {w : Fin sp.n}
    (hw : w ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt w j ℓ)
    {t : Time} {B : Blk sp.n FGP} {s : Nat}
    (hs : (latestView sp (tr.post j) ℓ.frame t).2 = s)
    (hmaj : ExtendingMajorityAC tr H U B s) (hBt : B ∈ ℓ.frame.tree)
    (hdeliv : ∀ x ∈ H, ∀ k e, VoteAt tr x k e → e.msg.slot = s → VoteExtends U e.msg B →
      e.msg ∈ (tr.post j).pool s ∧
      ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ (tr.post j).blockStamp Hd.root < ⊤) :
    (voters (latestView sp (tr.post j) ℓ.frame t).1.votes).ncard <
      2 * (supporters ℓ.frame (latestView sp (tr.post j) ℓ.frame t).1
        (latestView sp (tr.post j) ℓ.frame t).2 B).ncard := by
  have hr := hrun.localRun
  have hU := hr.coherent
  have hst : tr.state w (j + 1) = tr.post j := state_succ_of_call hc
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hw hc
  set A := tr.post j
  set Φ := ℓ.frame
  set LV := latestView sp A Φ t
  have hL : ((s : Nat) : Int) = LV.2 := hs.symm
  -- the latest view's votes are slot-`s` pool votes after the call
  have hpool : ∀ v ∈ LV.1.votes, v ∈ (tr.state w (j + 1)).pool s := by
    intro v hv
    rw [hst]
    exact ((latestView_memAC hL v).1.1 hv).1
  have hsupp : ExtendingCastersAC tr H U B s ⊆ supporters Φ LV.1 LV.2 B := by
    intro x hxE
    obtain ⟨hx, k, e, hv, hes, Hd, hHdU, hHdr, hBHd⟩ := extendingCastersAC_iff.1 hxE
    obtain ⟨hvp, Hd', hHd't, hHd'r, hbst⟩ := hdeliv x hx k e hv hes ⟨Hd, hHdU, hHdr, hBHd⟩
    obtain rfl : Hd' = Hd := hU.1 (hΦU hHd't) hHdU (hHd'r.trans hHdr.symm)
    obtain ⟨Hd₂, hHd₂, hHd₂r, hHd₂s⟩ := honest_headU hrun hx hv
    obtain rfl : Hd' = Hd₂ := hU.1 hHdU hHd₂ (hHdr.trans hHd₂r.symm)
    have hvp' : e.msg ∈ (tr.state w (j + 1)).pool s := by rw [hst]; exact hvp
    -- the vote has a finite stamp, so it is a vote of the latest view
    have hvst : A.voteStamp e.msg < ⊤ := by
      have hus : e.msg.slot = s := hes
      rcases pool_originU hr hw (j + 1) e.msg (by rw [hus]; exact hvp') with
        ⟨k, -, -, h, -⟩ | ⟨k, -, -, -, -, h, -⟩ <;>
        rw [← hst, h] <;> exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
    have hres : resolutionTime A Φ e.msg < ⊤ := by
      unfold resolutionTime
      rw [← hHdr, lookup_of_mem hΦ hHd't]
      dsimp only
      simp only [not_lt.2 hHd₂s, ↓reduceIte]
      exact max_lt hvst hbst
    refine ⟨?_, e.msg, (latestView_memAC hL e.msg).2.2 ⟨⟨hvp, hvst⟩, hres⟩,
      (vote_signer_slotAC hr hx hv).1, by rw [← hL, hes], Hd', hHd't, hHdr,
      anc_tree_of_anc_U hU hΦ hΦU hBt hBHd hHd't⟩
    rintro ⟨a, ha, b, hb, hab, hav, hbv⟩
    exact hab ((pool_vote_eq hrun hw hx hv hes (hpool a ha) hav).trans
      (pool_vote_eq hrun hw hx hv hes (hpool b hb) hbv).symm)
  have hvot := pool_voters_sub hrun hw (c := j + 1) (s := s) B hpool
  have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
  have h2 := Set.ncard_union_le (ExtendingCastersAC tr H U B s) (OpponentsAC tr H U B s)
  have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
  have h4 := extendingMajorityAC_iff.1 hmaj
  omega

end Consensus.Goldilocks.SA

end
