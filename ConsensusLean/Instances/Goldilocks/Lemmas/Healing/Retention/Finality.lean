module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Crossing

public section

/-! # Goldilocks Healing, HR.4: a low `Σ.F` is below every high origin

G1.2 at strict height (`hr4-cut-scope.md` §3, "For low finalized height `d ≤ H`"): the cut
step's conclusion for `Σ.F` when `Σ.J` is low. The finalized pair of a state names the entry of
its height (`fin_pair_entry`: a pending pair is a past justification, whose block is the entry of
the justified height), so a store's `Σ.F ⪯ Σ.J` is finalized at a height `≤ Σ.h_j`
(`low_finalized_below_origin`); G1.2 over the run (`finalized_anc_of_height_lt`) puts it below
every honest block of greater state height. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- Along one block, the finalized pair and the pending pairs of the new state are old ones
(pending, or the old finalized pair) or the old height's entry pair. -/
private theorem step_pairs {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') (Q : Nat × Nat → Prop)
    (hp : ∀ p ∈ σ.pending, Q p) (hF : Q (σ.hF, σ.F)) (hE : Q (σ.h, σ.Th)) :
    (∀ p ∈ σ'.pending, Q p) ∧ Q (σ'.hF, σ'.F) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF', σ₁, rfl, hFc, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hpend : ∀ r ∈ σ.pending.filter (fun p => hF' < p.1), Q r :=
    fun r hr => hp r (List.mem_of_mem_filter hr)
  have hF₁ : Q (hF', F) := by
    rcases hFc with ⟨rfl, rfl⟩ | ⟨hm, -⟩
    · exact hF
    · exact hp _ hm
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · refine ⟨fun r hr => ?_, hF₁⟩
    simp only [FG.ChainState.advance] at hr
    rcases List.mem_append.1 (List.mem_of_mem_drop hr) with hr | hr
    · exact hpend r hr
    · rw [List.mem_singleton] at hr
      subst hr
      exact hE
  · exact ⟨hpend, hF₁⟩
  · exact ⟨hpend, hF₁⟩

/-- **The finalized pair of a held block's state names the entry of its height** (or genesis):
the finalized pair is the old one or a pending pair, and every pending pair was appended at a
justification of the entry of the parent's height (G0.2 (d), (g) at the store). -/
theorem fin_pair_entry (hr : st.Reachable acp₀) {X : NodeBlock P ACP} (hX : X ∈ st.tree) :
    (st.σ X.root).F = P.genesisRoot ∨
      ∃ W ∈ st.tree, W.root = (st.σ X.root).F ∧ (st.σ W.root).h = (st.σ X.root).hF := by
  let Q : Nat × Nat → Prop := fun p =>
    p.2 = P.genesisRoot ∨ ∃ W ∈ st.tree, W.root = p.2 ∧ (st.σ W.root).h = p.1
  suffices key : (∀ p ∈ (st.σ X.root).pending, Q p) ∧ Q ((st.σ X.root).hF, (st.σ X.root).F) from
    key.2
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 X hX
  clear hX
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr]
    exact ⟨fun p hp => by simp [FG.ChainState.init] at hp, Or.inl rfl⟩
  | tail _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := step_σ hr hYW.2.1 hYW.2.2
    obtain ⟨⟨E, hE, hEr, -, hEh, -⟩, -⟩ :=
      Goldilocks.Store.entry_state_of_source P ACP acp₀ _ hr _ hYW.1
    exact step_pairs ht Q ih.1 ih.2 (Or.inr ⟨E, hE, hEr, hEh⟩)

end Store

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
  {proposer : Nat → Fin sp.n}

/-- **G1.2 over the run** (claims G1.2, G1.3, G0.5; `hr4-cut-scope.md` §3; the same statement as
Boot's `finalized_anc_of_lt`). A block `F` finalized by the state of a held `X` in an honest
store is an ancestor of every honest block `W` whose state height exceeds the finalized height:
otherwise the finality quorum of `(h_F, F)` on `X`'s chain and the crossing quorum of `h_F` on
`W`'s chain (whose roots do not contain `F`) share `2q − n > f` validators with an E1 pair
(`FG.finalization_meets_crossing`), an honest one of which signed both attestations
(unforgeability) in one client run (`Store.signed_run`), against client safety (G0.5). -/
theorem finalized_anc_of_height_lt (hp : ResetPremises tr H proposer dg g ΔF a) {y z : Fin sp.n}
    (hy : y ∈ H) (hz : z ∈ H) {k m : Nat} {X F W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hF : F ∈ (tr.state y k).fg.tree)
    (hFr : F.root = ((tr.state y k).fg.σ X.root).F) (hW : W ∈ (tr.state z m).fg.tree)
    (hlt : ((tr.state y k).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h) :
    Anc (tr.HonestBlocks H) F W := by
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have hfg := Compose.fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hp.run.genesis_root_ok hp.run.toLocalRun hp.noColl
  have hst : ∀ {w : Fin sp.n}, w ∈ H → ∀ i, tr.projFG.store w i = (tr.state w i).fg :=
    fun hw i => by simp only [FGTrace.store, Compose.projFG_state hp.run.toLocalRun hw i]
  have hH : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
    have h3 := hp.healthy.2.2
    have hn := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    omega
  have h := finalized_anc_of_lt_fg hfg hH hy hz (k := k) (m := m) (X := X) (F := F) (W := W)
  rw [hst hy, hst hz] at h
  exact h hX hF hFr hW hlt

/-- **G1.2 at strict height: a low `Σ.F` is below an honest-held high block**
(`hr4-cut-scope.md` §3, "For low finalized height `d ≤ H`, `B`'s accepted chain has height `> d`";
claims G1.2;
`producer-reset-continuation.md` §11 "Historical finality and acceptance"). When an honest
node's `Σ.h_j ≤ H_z`, its `Σ.F ⪯ Σ.J` is genesis or finalized at a height
`d = σ[Σ.F].h ≤ σ[Σ.J].h = Σ.h_j ≤ H_z < σ[B].h` (`fin_pair_entry`; a genesis `Σ.J` makes `Σ.F`
genesis), so `Σ.F ⪯ B` by G1.2 (`finalized_anc_of_height_lt`). -/
theorem low_finalized_below_high_block (hp : ResetPremises tr H proposer dg g ΔF a)
    {y x : Fin sp.n} (hy : y ∈ H) (hx : x ∈ H) {m i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBt : B ∈ (tr.state x i).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ ((tr.state x i).fg.σ B.root).h)
    (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) :
    Anc (tr.HonestBlocks H) (tr.state y m).fg.F B := by
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy m
  have hU := Compose.honest_blocks_coherent hp.run.toLocalRun hp.noColl
  have hsub : (tr.state y m).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, m, hX⟩
  have hcoh : Coherent (tr.state y m).fg.tree := hU.mono hsub
  have hg := Store.genesis_mem hreach
  have hgB : Anc (tr.HonestBlocks H)
      (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B :=
    ((Goldilocks.Store.accepted_tree _ _ _ _
      (Compose.fg_reachable hp.run.toLocalRun hx i)).2.2.2 B hBt).mono
        (fun X hX => (⟨x, hx, i, hX⟩ : X ∈ tr.HonestBlocks H))
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hreach
  have hgF : (tr.state y m).fg.Anc (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)
      (tr.state y m).fg.F := (Goldilocks.Store.accepted_tree _ _ _ _ hreach).2.2.2 _ hFm
  -- a genesis `Σ.F` is below `B`
  have hgen : (tr.state y m).fg.F.root = sp.toParams.genesisRoot →
      Anc (tr.HonestBlocks H) (tr.state y m).fg.F B := fun he => by
    rw [hcoh.1 hFm hg he]
    exact hgB
  rcases Store.fin_pair_entry hreach hBf with he | ⟨W, hW, hWr, hWh⟩
  · exact hgen (hBfF.symm.trans he)
  obtain rfl : W = (tr.state y m).fg.F := hcoh.1 hW hFm (hWr.trans hBfF)
  obtain ⟨E, hE, hEr, -, hcase⟩ := Store.J_entry_of_reachable hreach hBj
  obtain rfl : E = (tr.state y m).fg.J := hcoh.1 hE hJm (hEr.trans hBjJ)
  rcases hcase with hEg | ⟨hEh, -⟩
  · -- `Σ.J` is genesis, so is `Σ.F ⪯ Σ.J`
    rw [hEg] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have h₁ := h_le_of_store_anc hreach hFJ
  refine finalized_anc_of_height_lt hp hy hx hBf hFm hBfF.symm hBt ?_
  omega

/-- The origin-specialized form of strict-height finalized ancestry. -/
theorem low_finalized_below_origin (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n}
    (hy : y ∈ H) (m : Nat) (hlow : (tr.state y m).fg.hj ≤ HZ tr H g) {x : Fin sp.n}
    {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    Anc (tr.HonestBlocks H) (tr.state y m).fg.F B := by
  obtain ⟨CV, hst⟩ := ho.2.2.1
  exact low_finalized_below_high_block hp hy ho.1
    (storedFastLock_mem hp.run hp.noColl ho.1 hst).1 ho.2.2.2 hlow

end Consensus.Goldilocks.Healing

end
