module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Service

public section

/-! # Goldilocks Healing: C1.2, AC outcome service for honest entries (assembly)

C1.2 (`Compose.OutcomeService`, claims C1.2 at goldilocks `6703bf05`) from the post-reset duty
supplier (`Outcome/Supplier`) and two C1.2-specific steps, following
fradamt-agent/workbench `producer-reset-continuation.md` §17, §18 (BA) and §26:

* **Entry rows** (`entry_rows`, §17 corrected, §18 BA): for a served entry `E = (h, T, u)` (an
  honest ready proposal `T` of slot `u ≥` the drain, at height `h ≥ H_z + 1`, with a high
  predecessor when bound), by `t_u + 6Δ` either honest validators of weight `q` have signed a
  target row for `E`, carrying the predecessor `(h − 1, J)` at a bound entry, or an honest
  accepted block has justified `E` (and finalized the predecessor at a bound entry) — the
  retained justified crossing. From `ready_unanimous`, `ready_update`, HR.4 (R1), (R4), G0.10
  and `δ_t ≥ 2` (no timeout through `t_u + 6Δ`).
* **The outcome** (`outcome_of_rows`, §26): with the window's honest ready proposal `W` whose
  parent extends `T` (retained ready inclusion), the rows reach `W`'s proposer before `t_{W.slot}`
  (`6Δ + Δ_F ≤ 4Δ·𝓕`) and give the literal `GW(E, 0, k_F)` at its acceptance of `W` (C0.3), unless
  a retained chain justified `E` first (branch (ii)); the carrier is relayed within `Δ`; at an
  unbound entry `E` is justified by the window's end in both branches (G1.7 in branch (i)).

Interface: `entry_rows` is open. `outcome_of_rows` is proved from two open private steps, one per
branch, on the relay of the carrier: acceptance relay reaches only the honest nodes whose `Σ.F`
the carrier extends, so each step says that at the relay deadline every honest node holds the
carrier or has its `Σ.F` below it (`window_carrier_below`, `early_carrier_below`; the T3 paper
orb's flag on branch (ii)). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The rows of a served entry by its deadline**: the entry `T` of height `h` (bound when
`bound`, with predecessor justification `Jr` at `hj`) has, by `d`, a quorum of honest target rows
signed by `d`, carrying the predecessor at a bound entry; or an honest node has accepted by `d` a
block `X` that justifies `T` at `h` and, at a bound entry, has finalized the predecessor. -/
def EntryRows (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (T : SA.Blk sp.n (List (FG.Att sp.n))) (h hj : Nat) (bound : Bool) (Jr : Nat) (d : Time) :
    Prop :=
  (∃ R : Finset (FG.Att sp.n), sp.toParams.fg.q ≤ (R.image FG.Att.val).card ∧
    ∀ r ∈ R, r.val ∈ H ∧ (∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ d) ∧
      r.h = h ∧ r.T = T.root ∧ r.timeout = false ∧ (bound = true → r.fin = some (hj, Jr))) ∨
  ∃ y ∈ H, ∃ k X, tr.AcceptAt y k X ∧ tr.time k ≤ d ∧
    Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T h X ∧
    (bound = true → ((tr.post k).fg.σ X.root).hF + 1 = h ∧ ((tr.post k).fg.σ X.root).F = Jr)

theorem entryRows_iff {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {h hj : Nat} {bound : Bool} {Jr : Nat} {d : Time} :
    EntryRows tr H T h hj bound Jr d ↔
      ((∃ R : Finset (FG.Att sp.n), sp.toParams.fg.q ≤ (R.image FG.Att.val).card ∧
        ∀ r ∈ R, r.val ∈ H ∧ (∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ d) ∧
          r.h = h ∧ r.T = T.root ∧ r.timeout = false ∧
          (bound = true → r.fin = some (hj, Jr))) ∨
      ∃ y ∈ H, ∃ k X, tr.AcceptAt y k X ∧ tr.time k ≤ d ∧
        Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T h X ∧
        (bound = true →
          ((tr.post k).fg.σ X.root).hF + 1 = h ∧ ((tr.post k).fg.σ X.root).F = Jr)) :=
  Iff.rfl

/-! ## FG traces: pools, ancestry and justifications across honest stores -/

section FGTraces

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

private theorem mem_onAttestation {st : Store P ACP} {a b : FG.Att P.n}
    (h : a ∈ st.atts ∨ a = b) : a ∈ (st.onAttestation b).atts := by
  unfold Store.onAttestation
  split_ifs with hb
  · rcases h with h | rfl
    exacts [h, hb]
  · rcases h with h | rfl
    · simp [h]
    · simp

private theorem mem_addAtts {a : FG.Att P.n} :
    ∀ (l : List (FG.Att P.n)) (st : Store P ACP), a ∈ st.atts ∨ a ∈ l → a ∈ (st.addAtts l).atts
  | [], _, h => h.resolve_right List.not_mem_nil
  | b :: l, st, h => by
    rw [Store.addAtts, List.foldl_cons, ← Store.addAtts]
    refine mem_addAtts l _ ?_
    rcases h with h | h
    · exact Or.inl (mem_onAttestation (Or.inl h))
    · rcases List.mem_cons.1 h with rfl | h
      exacts [Or.inl (mem_onAttestation (Or.inr rfl)), Or.inr h]

/-- The pool of an honest node only grows. -/
private theorem pool_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {k m : Nat}
    (hkm : k ≤ m) : (tr.store y k).atts ⊆ (tr.store y m).atts := by
  induction m, hkm using Nat.le_induction with
  | base => exact fun _ h => h
  | succ m _ ih =>
    intro a ha
    have ha := ih ha
    rcases Store.store_step hr hy m with he | ⟨B, -, hB⟩ | ⟨b, -, he⟩
    · rwa [he]
    · obtain ⟨pr, σ', -, -, -, -, -, he⟩ := Store.onBlock_eq_some hB
      rw [he]
      refine mem_addAtts _ _ (Or.inl ?_)
      rw [(Store.updateFinality_spec _ _).2.2.1]
      exact ha
    · rw [he]
      exact mem_onAttestation (Or.inl ha)

/-- An attestation that an honest node processes is in its pool after the cut. -/
private theorem pool_of_process (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {k : Nat} {a : FG.Att P.n} (h : tr.ProcessAt y k a) : a ∈ (tr.store y (k + 1)).atts := by
  obtain ⟨ℓ, hc, ha⟩ := h
  cases ℓ with
  | block B acc =>
    cases acc with
    | false => cases ha
    | true =>
      obtain ⟨pr, σ', -, -, -, -, -, he⟩ :=
        Store.onBlock_eq_some (Store.accept_onBlock hr hy hc)
      rw [he]
      exact mem_addAtts _ _ (Or.inr ha)
  | attestation b =>
    obtain rfl : a = b := List.mem_singleton.1 ha
    obtain ⟨rfl, hl⟩ := hc
    have hs := hr.exec k _ hl hy
    have he : tr.store (tr.node k) (k + 1) = (tr.store (tr.node k) k).onAttestation a := by
      simpa [FGTrace.store, Trace.state, hl] using congrArg Prod.fst hs
    rw [he]
    exact mem_onAttestation (Or.inr rfl)
  | attest src signed => cases ha

/-- A block of `U` whose root an honest held block names as its parent is held. -/
private theorem parent_mem (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B Y : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) (hY : Y ∈ U)
    (hp : B.parent = some Y.root) : Y ∈ (tr.store y i).tree := by
  rcases ((Store.accepted_tree P ACP acp₀ _ (Store.store_reachable hr hy i)).2.2.2 B
    hB).cases_tail with rfl | ⟨Z, -, hZ, -, hZp⟩
  · exact absurd hp (by simp [Params.genesisBlock])
  · obtain rfl : Z = Y := hr.coherent.1 (hr.tree_subset y hy i hZ) hY
      (Option.some.inj (hZp.symm.trans hp))
    exact hZ

/-- Ancestry inside `U` ending at an honest held block is ancestry in that store. -/
private theorem store_anc (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A B : NodeBlock P ACP} (h : Anc U A B) (hB : B ∈ (tr.store y i).tree) :
    (tr.store y i).Anc A B := by
  induction h with
  | refl => exact .refl
  | tail _ hYB ih =>
    have hY := parent_mem hr hy hB hYB.1 hYB.2.2
    exact (ih hY).tail ⟨hY, hB, hYB.2.2⟩

/-- Ancestors of a held block are held. -/
private theorem mem_of_anc {st : Store P ACP} {A B : NodeBlock P ACP} (h : st.Anc A B)
    (hB : B ∈ st.tree) : A ∈ st.tree := by
  induction h with
  | refl => exact hB
  | tail _ hp ih => exact ih hp.1

/-- Ancestry at one honest store holds at another that holds the descendant. -/
private theorem anc_transfer (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n} (hy : y ∈ H)
    (hz : z ∈ H) {i j : Nat} {A B : NodeBlock P ACP} (h : (tr.store y i).Anc A B)
    (hB : B ∈ (tr.store z j).tree) : (tr.store z j).Anc A B :=
  store_anc hr hz (h.mono (hr.tree_subset y hy i)) hB

/-- A justification of an entry at one honest store holds at every honest store that holds the
justifying block (it reads only that block's ancestors and their states). -/
private theorem justifies_transfer (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n} (hy : y ∈ H)
    (hz : z ∈ H) {i j h : Nat} {T X : NodeBlock P ACP}
    (hJ : Store.JustifiesEntry P ACP (tr.store y i) T h X) (hX : X ∈ (tr.store z j).tree) :
    Store.JustifiesEntry P ACP (tr.store z j) T h X := by
  obtain ⟨hXy, hTX, hhj, hJX, hall⟩ := hJ
  have hσ := Store.σ_eq_of_held hr hz hy hX hXy
  refine ⟨hX, anc_transfer hr hy hz hTX hX, by rw [hσ]; exact hhj, by rw [hσ]; exact hJX,
    fun Y hY hTY hYX hne => ?_⟩
  have hYXy := anc_transfer hr hz hy hYX hXy
  have hYy := mem_of_anc hYXy hXy
  rw [Store.σ_eq_of_held hr hz hy hY hYy]
  exact hall Y hYy (anc_transfer hr hz hy hTY hYy) hYXy hne

/-- A block justifying an entry held by an honest node is not genesis (the entry's height is at
least `1`, genesis justifies height `0`). -/
private theorem justifier_ne_genesis (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n} (hy : y ∈ H)
    (hz : z ∈ H) {i j : Nat} {T X : NodeBlock P ACP} (hT : T ∈ (tr.store y i).tree)
    (hJ : Store.JustifiesEntry P ACP (tr.store z j) T ((tr.store y i).σ T.root).h X) :
    X ≠ P.genesisBlock acp₀ := by
  rintro rfl
  have h0 := hJ.2.2.1
  rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl,
    Store.σ_genesis (Store.store_reachable hr hz j)] at h0
  obtain ⟨c, -, -, -, hc⟩ :=
    Store.chain_state_of_chain P ACP acp₀ _ (Store.store_reachable hr hy i) T hT
  have h1 := (FG.chain_invariants P.fg _ _ hc).1
  simp only [FG.ChainState.init] at h0
  omega

/-- A block an honest node accepts is held after the cut. -/
private theorem accepted_mem (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {k : Nat}
    {B : NodeBlock P ACP} (h : tr.AcceptAt y k B) : B ∈ (tr.store y (k + 1)).tree := by
  rw [(Store.tree_grows P ACP acp₀ _ (Store.store_reachable hr hy k)).1 B _
    (Store.accept_onBlock hr hy h)]
  exact Set.mem_insert _ _

end FGTraces

/-! ## Runs: deadlines and the relay of a carrier -/

section Runs

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}

private theorem lastWake_coe {y : Fin P.n} {w : Time} :
    ∀ {c : Nat}, tr.lastWake y c = (w : WithBot Time) → ∃ k ≤ c, tr.RestartAt y k ∧ tr.time k = w
  | 0, h => by
    unfold RunTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨0, le_rfl, hr, WithBot.coe_injective h⟩
    · simp at h
  | c + 1, h => by
    unfold RunTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨c + 1, le_rfl, hr, WithBot.coe_injective h⟩
    · obtain ⟨k, hk, h'⟩ := lastWake_coe h
      exact ⟨k, hk.trans (Nat.le_succ c), h'⟩

/-- With every restart of `y` at or before `a`, the deadline of `τ` is at most `max(τ, a) + Δ'`. -/
private theorem deadline_le {y : Fin P.n} {c : Nat} {a : Time}
    (h : ∀ k, tr.RestartAt y k → tr.time k ≤ a) (τ Δ' : Time) :
    tr.deadline y c τ Δ' ≤ max τ a + Δ' := by
  unfold RunTrace.deadline
  rcases hw : tr.lastWake y c with _ | w
  · change τ + Δ' ≤ max τ a + Δ'
    linarith [le_max_left τ a]
  · obtain ⟨k, -, hrk, rfl⟩ := lastWake_coe hw
    change max τ (tr.time k) + Δ' ≤ max τ a + Δ'
    linarith [max_le_max (le_refl τ) (h k hrk)]

end Runs

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp a : Time} {cF kF : Nat}

/-- **Entry rows** (§17 corrected, §18 BA): under C1.2's premises, a served entry has its rows,
or a retained justified crossing, by `t_u + 6Δ`. -/
theorem entry_rows (hrun : GoldilocksRun dg H tr) (hsh : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hcF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time))
    (hδ : cF + kF ≤ sp.toParams.δt) (ha : IsReset tr H g a) {p y : Fin sp.n} {k i u : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u T)
    (hE : Compose.RunEntry tr H y i T) (hR : drainTime sp a ≤ sp.ts u)
    (hh : HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).h)
    (hhj : 0 < ((tr.post i).fg.σ T.root).hj →
      ((tr.post i).fg.σ T.root).hj + 1 = ((tr.post i).fg.σ T.root).h →
      HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).hj) :
    EntryRows tr H T ((tr.post i).fg.σ T.root).h ((tr.post i).fg.σ T.root).hj
      (decide ((tr.post i).fg.σ T.root).bound) ((tr.post i).fg.σ T.root).J
      (sp.ts u + 6 * sp.Δ) := by
  sorry

/-! ## The carriers -/

/-- **C0.3 at an honest proposal**: the own block of an honest proposal is accepted at its cut,
and it includes every row of the proposer's pool that is valid against its parent's state and not
on its parent's chain (`proposal_attestations`). -/
private theorem proposal_accepted (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {w : Fin sp.n} (hw : w ∈ H) {kw : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt w kw W) :
    tr.AcceptAt w kw W ∧ ∀ Pr ∈ (tr.state w kw).fg.tree, W.parent = some Pr.root →
      ∀ r ∈ (tr.state w kw).fg.atts, ((tr.state w kw).fg.σ Pr.root).validAtt r →
        ¬ (tr.state w kw).fg.OnChain Pr r → r ∈ W.fgPayload := by
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hP
  rcases Compose.blockCall_cases hrun.toLocalRun hw hc with hg |
    ⟨j, x, rfl, hg, hpr, d, p, hdp, rfl, -, -, -, hfg⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  obtain ⟨hacc, -⟩ :=
    own_block_accepted hrun.toLocalRun hreq hrun.genesis_root_ok hnc hw hg hpr hdp
  have he := hc.2.symm.trans hacc.2
  simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at he
  obtain rfl := he.2
  refine ⟨hc, fun Pr hPr hpar r hr hv hn => ?_⟩
  rw [hfg] at hPr hr hv hn
  have hroot : d.head.root = Pr.root := Option.some.inj hpar
  change r ∈ (tr.state w j).fg.proposalAttestations d.head
  simp only [Store.proposalAttestations, List.mem_filter, decide_eq_true_eq]
  refine ⟨hr, by rw [hroot]; exact hv, fun ⟨X, hX, hXd, hrX⟩ => hn ⟨X, hX, ?_, hrX⟩⟩
  have hd : d.head ∈ (tr.state w j).fg.tree := by
    rcases eq_or_ne X d.head with rfl | hne
    exacts [hX, (hXd.mem hne).2]
  have e : (tr.state w j).fg.blocks d.head.root = some Pr := by rw [hroot]; exact hPr
  obtain rfl : d.head = Pr := Option.some.inj (hd.symm.trans e)
  exact hXd

/-- The first cut from a time `t ≥ ḡ` exists under `Healthy(g)`. -/
private theorem firstCutFrom_exists (hrun : GoldilocksRun dg H tr) (hh : tr.HealthyRun H ΔF g)
    {z : Fin sp.n} (hz : z ∈ H) {t : Time} (ht : SA.gbar g ≤ t) : ∃ j, tr.FirstCutFrom j t := by
  classical
  obtain ⟨i, -, hi⟩ := hrun.awake_in_horizon z hz t (hh.2.1 z hz t ht)
  have hex : ∃ k, t ≤ tr.time k := ⟨i, hi⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩

/-- **The relay of a carrier**: a block (not genesis) that an honest node accepted by `t − Δ`,
`t ≥ ḡ + 2Δ`, which every honest node at the state at `t` holds or has above its `Σ.F`, is
accepted by every honest node before `t` (`Catch(2Δ)` or acceptance relay, `relay_held`). -/
private theorem relayed (hrun : GoldilocksRun dg H tr) (hsh : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x z : Fin sp.n} (hx : x ∈ H) (hz : z ∈ H) {k₀ : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hacc : tr.AcceptAt x k₀ B)
    (hB : B ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) {t : Time}
    (hκ : SA.gbar g + 2 * sp.Δ ≤ t) (hk₀ : tr.time k₀ + sp.Δ ≤ t)
    (hF : ∀ j, tr.FirstCutFrom j t →
      B ∈ (tr.state z j).fg.tree ∨ Anc (tr.HonestBlocks H) (tr.state z j).fg.F B) :
    ∃ k', tr.AcceptAt z k' B ∧ tr.time k' < t := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨j, hj⟩ := firstCutFrom_exists hrun hsh.healthy hz (t := t) (by linarith)
  have hBj : B ∈ (tr.state z j).fg.tree := (hF j hj).elim id
    (relay_held hrun.toLocalRun hsh.healthy hsh.noRestart hc hx hz hacc hκ hk₀ hj)
  rcases tree_accepted hrun.toLocalRun hz hBj with h | ⟨k', hk', hA⟩
  · exact absurd h hB
  · exact ⟨k', hA, hj.2 k' hk'⟩

/-- **The window's carrier is not below a conflicting honest `Σ.F`** (open; §26, "the carrier is
relayed within `Δ`"): in the rows branch, at the state at `t_{W.slot} + Δ` every honest node holds
the window's honest ready proposal `W` or has its `Σ.F` below `W`, so acceptance relay reaches it.
The acceptance relay (`Sync`) only promises acceptance to nodes whose `Σ.F` the block extends;
the run premises of C1.2 do not by themselves exclude an honest `Σ.F` that conflicts with `W`
(a finalization on another branch through `T` between `t_u` and `t_{W.slot} + Δ`). -/
private theorem window_carrier_below (hrun : GoldilocksRun dg H tr)
    (hsh : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (hpp : PropPlus tr H g Gp)
    (hcF₁ : 4 * sp.Δ * ((cF : Time) - 1) < 6 * sp.Δ + ΔF)
    (hcF₂ : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time)) (hδ : cF + kF ≤ sp.toParams.δt)
    (ha : IsReset tr H g a) {p y : Fin sp.n} {k i u : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u T)
    (hE : Compose.RunEntry tr H y i T) (hR : drainTime sp a ≤ sp.ts u)
    {w : Fin sp.n} {kw : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hWP : ReadyProposal tr H w kw W.slot W) (hWs₁ : u + cF ≤ W.slot)
    (hWs₂ : W.slot ≤ u + cF + kF) {Pr : SA.Blk sp.n (List (FG.Att sp.n))}
    (hWpar : W.parent = some Pr.root) (hTPr : Anc (tr.HonestBlocks H) T Pr)
    {R : Finset (FG.Att sp.n)} (hRq : sp.toParams.fg.q ≤ (R.image FG.Att.val).card)
    (hRr : ∀ r ∈ R, r.val ∈ H ∧ (∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ sp.ts u + 6 * sp.Δ) ∧
      r.h = ((tr.post i).fg.σ T.root).h ∧ r.T = T.root ∧ r.timeout = false ∧
      (decide ((tr.post i).fg.σ T.root).bound = true →
        r.fin = some (((tr.post i).fg.σ T.root).hj, ((tr.post i).fg.σ T.root).J))) :
    ∀ z ∈ H, ∀ j, tr.FirstCutFrom j (sp.ts W.slot + sp.Δ) →
      W ∈ (tr.state z j).fg.tree ∨ Anc (tr.HonestBlocks H) (tr.state z j).fg.F W := by
  sorry

/-- **The early carrier is not below a conflicting honest `Σ.F`** (open; §26 branch (ii), the
T3 paper orb's flag): at the state at `t_u + 7Δ` every honest node holds the retained crossing `X`
(an honest accepted block, by `t_u + 6Δ`, that justifies `T` and at a bound entry has finalized
the predecessor) or has its `Σ.F` below `X`, so acceptance relay reaches it. A receiver may have
finalized a descendant of `X` (then it holds `X`), or a different branch through `T`; the latter
is what this excludes. -/
private theorem early_carrier_below (hrun : GoldilocksRun dg H tr)
    (hsh : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (hpp : PropPlus tr H g Gp)
    (hcF₁ : 4 * sp.Δ * ((cF : Time) - 1) < 6 * sp.Δ + ΔF)
    (hcF₂ : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time)) (hδ : cF + kF ≤ sp.toParams.δt)
    (ha : IsReset tr H g a) {p y : Fin sp.n} {k i u : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u T)
    (hE : Compose.RunEntry tr H y i T) (hR : drainTime sp a ≤ sp.ts u)
    (hW : ∃ (w : Fin sp.n) (kw : Nat) (W : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H w kw W.slot W ∧ u + cF ≤ W.slot ∧ W.slot ≤ u + cF + kF ∧
      ∃ Pr, W.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) T Pr)
    {x : Fin sp.n} (hx : x ∈ H) {kx : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXacc : tr.AcceptAt x kx X) (hXt : tr.time kx ≤ sp.ts u + 6 * sp.Δ)
    (hXJ : Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post kx).fg T
      ((tr.post i).fg.σ T.root).h X)
    (hXb : decide ((tr.post i).fg.σ T.root).bound = true →
      ((tr.post kx).fg.σ X.root).hF + 1 = ((tr.post i).fg.σ T.root).h ∧
        ((tr.post kx).fg.σ X.root).F = ((tr.post i).fg.σ T.root).J) :
    ∀ z ∈ H, ∀ j, tr.FirstCutFrom j (sp.ts u + 7 * sp.Δ) →
      X ∈ (tr.state z j).fg.tree ∨ Anc (tr.HonestBlocks H) (tr.state z j).fg.F X := by
  sorry

/-- **The outcome from the rows** (§26): with the window's honest ready proposal whose parent
extends `T`, the rows (or the retained crossing) give C1.2's conclusion: the literal good window
or the early outcome, with the carrier relayed, and at an unbound entry a justification by the
window's end. -/
theorem outcome_of_rows (hrun : GoldilocksRun dg H tr) (hsh : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hpp : PropPlus tr H g Gp)
    (hcF₁ : 4 * sp.Δ * ((cF : Time) - 1) < 6 * sp.Δ + ΔF)
    (hcF₂ : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time)) (hδ : cF + kF ≤ sp.toParams.δt)
    (ha : IsReset tr H g a) {p y : Fin sp.n} {k i u : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H p k u T)
    (hE : Compose.RunEntry tr H y i T) (hR : drainTime sp a ≤ sp.ts u)
    (hW : ∃ (w : Fin sp.n) (kw : Nat) (W : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H w kw W.slot W ∧ u + cF ≤ W.slot ∧ W.slot ≤ u + cF + kF ∧
      ∃ Pr, W.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) T Pr)
    (hrows : EntryRows tr H T ((tr.post i).fg.σ T.root).h ((tr.post i).fg.σ T.root).hj
      (decide ((tr.post i).fg.σ T.root).bound) ((tr.post i).fg.σ T.root).J
      (sp.ts u + 6 * sp.Δ)) :
    let h := ((tr.post i).fg.σ T.root).h
    let bound := decide ((tr.post i).fg.σ T.root).bound
    let T₁ := sp.ts (u + cF + kF + 1 : Nat)
    ((∃ (q : Fin sp.n) (j : Nat) (Bs Pr : SA.Blk sp.n (List (FG.Att sp.n)))
        (R : Finset (FG.Att sp.n)),
        tr.projFG.time j < T₁ ∧
        Store.GoodWindow sp.toParams (Payload sp.n) H tr.projFG cF T 0 kF q j Bs Pr R ∧
        ∀ z ∈ H, ∃ k', tr.AcceptAt z k' Bs ∧ tr.time k' < T₁ + sp.Δ) ∨
      Compose.EarlyOutcome tr H T h bound ((tr.post i).fg.σ T.root).J T₁) ∧
    (bound = false → ∃ y ∈ H, ∃ k' X, tr.AcceptAt y k' X ∧ tr.time k' < T₁ ∧
      Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k').fg T h X) := by
  dsimp only
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hΔF : sp.Δ ≤ ΔF := hsh.healthy.1.deltaF
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  have hfg := Compose.fg_projection _ _ dg H _ tr hreq hsh.genesisRoot hrun.toLocalRun hsh.noColl
  have hst : ∀ z ∈ H, ∀ k, tr.projFG.store z k = (tr.state z k).fg := fun z hz k => by
    simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hz k]
  have hpost : ∀ z ∈ H, ∀ k B, tr.AcceptAt z k B → (tr.post k).fg = tr.projFG.store z (k + 1) :=
    fun z hz k B hB => by rw [hst z hz, tr.state_succ_of_call hB]
  have hE' := hE
  obtain ⟨hy, hTacc, hTh⟩ := hE'
  have hTy : T ∈ (tr.projFG.store y (i + 1)).tree :=
    accepted_mem hfg hy (Compose.projFG_callAt.2 hTacc)
  have hpi := hpost y hy i T hTacc
  have hTu : T.slot = u := hP.2.2.2.2.1
  -- times: `ḡ + 8Δ < t_u` (the drain is after the reset, which is after `c_z`), `c_F ≥ 2`
  have hgu : SA.gbar g + 8 * sp.Δ < sp.ts u := by
    have h1 := cutZ_lt_reset hrun hsh.healthy ha
    have h2 := lt_cutZ sp g
    have ha0 : 0 ≤ a := by linarith [gbar_nonneg g]
    have h3 : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have h4 : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts u :=
      le_trans ((SA.ts_le_iff sp).2 (by push_cast; omega)) (drainTime_eq (sp := sp) a ▸ hR)
    linarith
  have hcF : (2 : Int) ≤ cF := by
    by_contra hlt
    have : (cF : Int) ≤ 1 := by omega
    nlinarith
  have hT₁ : sp.ts ((u + cF + kF + 1 : Nat) : Int) =
      sp.ts u + 4 * sp.Δ * cF + 4 * sp.Δ * kF + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hc2 : 4 * sp.Δ * 2 ≤ 4 * sp.Δ * cF := mul_le_mul_of_nonneg_left hcF (by linarith)
  have hk0 : 0 ≤ 4 * sp.Δ * kF := by positivity
  rcases hrows with ⟨R, hRq, hRr⟩ | ⟨x, hx, kx, X, hXacc, hXt, hXJ, hXb⟩
  swap
  · -- the retained crossing: the early outcome, relayed
    have hXt' : tr.time kx < sp.ts ((u + cF + kF + 1 : Nat) : Int) := by rw [hT₁]; linarith
    have hXJ' := hXJ
    rw [hpost x hx kx X hXacc, hpi] at hXJ'
    have hXne := justifier_ne_genesis hfg hy hx hTy hXJ'
    have hrel : ∀ z ∈ H, ∃ k', tr.AcceptAt z k' X ∧
        tr.time k' < sp.ts ((u + cF + kF + 1 : Nat) : Int) + sp.Δ := by
      intro z hz
      obtain ⟨k', hA, hk'⟩ := relayed hrun hsh hc hx hz hXacc hXne (t := sp.ts u + 7 * sp.Δ)
        (by linarith) (by linarith)
        (early_carrier_below hrun hsh hc hpp hcF₁ hcF₂ hδ ha hP hE hR hW hx hXacc hXt hXJ hXb
          z hz)
      exact ⟨k', hA, by rw [hT₁]; linarith⟩
    exact ⟨Or.inr ⟨x, hx, kx, X, hXacc, hXt', hXJ, hXb, hrel⟩,
      fun _ => ⟨x, hx, kx, X, hXacc, hXt', hXJ⟩⟩
  -- the rows: the literal good window at the window's honest ready proposal
  obtain ⟨w, kw, W, hWP, hWs₁, hWs₂, Pr, hWpar, hTPr⟩ := hW
  have hwH := hWP.1
  have hprop := hWP.2.2.2.1
  obtain ⟨hacc, hincl⟩ := proposal_accepted hrun hsh.noColl hwH hprop
  have hkw : tr.time kw = sp.ts W.slot := hprop.2.2.trans (sp.slotTime_eq _)
  have hWt₁ : sp.ts u + 4 * sp.Δ * cF ≤ sp.ts W.slot := by
    have := (SA.ts_le_iff sp).2 (show ((u + cF : Nat) : Int) ≤ W.slot by exact_mod_cast hWs₁)
    simp only [SA.SAParams.ts] at this ⊢; push_cast at this; linarith
  have hWt₂ : sp.ts W.slot ≤ sp.ts u + 4 * sp.Δ * cF + 4 * sp.Δ * kF := by
    have := (SA.ts_le_iff sp).2 (show (W.slot : Int) ≤ ((u + cF + kF : Nat) : Int) by
      exact_mod_cast hWs₂)
    simp only [SA.SAParams.ts] at this ⊢; push_cast at this; linarith
  have hWa : tr.projFG.AcceptAt w kw W := Compose.projFG_callAt.2 hacc
  have hW1 := accepted_mem hfg hwH hWa
  have hPrU : Pr ∈ tr.HonestBlocks H := by
    rcases eq_or_ne T Pr with rfl | hne
    · exact ⟨y, hy, i + 1, by rw [← hst y hy]; exact hTy⟩
    · exact (hTPr.mem hne).2
  have hPr : Pr ∈ (tr.projFG.store w kw).tree := by
    have h1 := parent_mem hfg hwH hW1 hPrU hWpar
    rw [(Store.tree_grows _ _ _ _ (Store.store_reachable hfg hwH kw)).1 W _
      (Store.accept_onBlock hfg hwH hWa)] at h1
    rcases Set.mem_insert_iff.1 h1 with rfl | h
    · have hU := hfg.tree_subset w hwH (kw + 1) hW1
      exact absurd (hfg.coherent.2 _ hU _ hU hWpar) (lt_irrefl _)
    · exact h
  have hTw : (tr.projFG.store w kw).Anc T Pr := store_anc hfg hwH hTPr hPr
  have hTmem := mem_of_anc hTw hPr
  have hσT : (tr.projFG.store w kw).σ T.root = (tr.post i).fg.σ T.root := by
    rw [hpi]; exact Store.σ_eq_of_held hfg hwH hy hTmem hTy
  -- every row reaches the proposer's pool before its proposal (`6Δ + Δ_F ≤ 4Δ𝓕`)
  have hpool : ∀ r ∈ R, r ∈ (tr.projFG.store w kw).atts := by
    intro r hr
    obtain ⟨hrH, ⟨js, hsign, hjs⟩, -⟩ := hRr r hr
    have hdl : ∀ c, tr.deadline w c (max (tr.time js) g) ΔF ≤ tr.time kw := fun c => by
      have h1 := deadline_le (c := c) (hsh.noRestart w hwH) (max (tr.time js) g) ΔF
      have h2 : max (max (tr.time js) g) (SA.gbar g) ≤ sp.ts u + 6 * sp.Δ :=
        max_le (max_le hjs (by linarith [le_gbar g])) (by linarith)
      rw [hkw]
      linarith
    obtain ⟨k', hk', -, hproc, hlt⟩ := hsh.healthy.1.attestation r.val hrH js r (Or.inl hsign)
      trivial w hwH kw ⟨_, hacc⟩ (hdl kw)
    have hk'lt : k' < kw := lt_of_le_of_ne hk' fun e => by
      have := hdl k'
      rw [e] at hlt this
      linarith
    have hp : tr.projFG.ProcessAt w k' r := by
      rcases hproc with hcall | ⟨B, hB, hrB⟩
      · exact ⟨.attestation r, Compose.projFG_callAt.2 hcall, List.mem_singleton_self _⟩
      · exact ⟨.block B true, Compose.projFG_callAt.2 hB, hrB⟩
    exact pool_mono hfg hwH hk'lt (pool_of_process hfg hwH hp)
  have hgw : Store.GoodWindow sp.toParams (Payload sp.n) H tr.projFG cF T 0 kF w kw W Pr R := by
    refine ⟨⟨hwH, hWa, hprop.2.1, hprop.2.2.symm, hPr, hWpar, ?_⟩, ⟨hTmem, by rw [hσT]; exact hTh⟩,
      hTw, by omega, hRq, fun r hr => ?_, fun r hr => Or.inr fun _ => ?_,
      fun r hr => Or.inr (hpool r hr), by omega, by decide⟩
    · rw [hst w hwH kw]
      exact hincl Pr (by rw [← hst w hwH kw]; exact hPr) hWpar
    · obtain ⟨-, -, hh, hT, hto, hfin⟩ := hRr r hr
      exact ⟨by rw [hσT]; exact hh, hT, hto, fun hb => by
        rw [hσT] at hb ⊢; exact hfin (decide_eq_true hb)⟩
    · obtain ⟨-, ⟨js, ⟨src, hs⟩, hjs⟩, -⟩ := hRr r hr
      refine ⟨js, ⟨src, Compose.projFG_callAt.2 hs⟩, ?_⟩
      rw [hTu, Nat.add_zero, sp.slotTime_eq]
      exact hjs
  -- the carrier `W` is relayed within `Δ`
  have hWne : W ≠ sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := fun h => by
    rw [h] at hWpar
    simp [Params.genesisBlock] at hWpar
  have hrel : ∀ z ∈ H, ∃ k', tr.AcceptAt z k' W ∧
      tr.time k' < sp.ts ((u + cF + kF + 1 : Nat) : Int) + sp.Δ := by
    intro z hz
    obtain ⟨k', hA, hk'⟩ := relayed hrun hsh hc hwH hz hacc hWne (t := sp.ts W.slot + sp.Δ)
      (by linarith) (by rw [hkw])
      (window_carrier_below hrun hsh hc hpp hcF₁ hcF₂ hδ ha hP hE hR hWP hWs₁ hWs₂ hWpar hTPr
        hRq hRr z hz)
    exact ⟨k', hA, by rw [hT₁]; linarith⟩
  -- the unbound clause: the window's chain justifies `T` (G1.7's first half)
  obtain ⟨X, hXJ, -⟩ := Store.window_justifies hfg hgw
  have hXJ' := hXJ
  rw [hσT, hpi] at hXJ'
  have hXne := justifier_ne_genesis hfg hy hwH hTy hXJ'
  rcases Store.tree_accepted hfg hwH hXJ.1 with h | ⟨k', hk', hA⟩
  · exact absurd h hXne
  have hA' : tr.AcceptAt w k' X := Compose.projFG_callAt.1 hA
  have hk't : tr.time k' ≤ tr.time kw := hrun.time_mono (by omega)
  refine ⟨Or.inl ⟨w, kw, W, Pr, R, ?_, hgw, hrel⟩, fun _ => ⟨w, hwH, k', X, hA', ?_, ?_⟩⟩
  · change tr.time kw < _
    rw [hkw, hT₁]
    linarith
  · rw [hT₁]
    linarith
  · rw [hpost w hwH k' X hA', ← hσT]
    exact justifies_transfer hfg hwH hwH hXJ (accepted_mem hfg hwH hA)

/-- **C1.2, AC outcome service for honest entries.** -/
theorem outcome_service : Compose.OutcomeService := by
  intro sp ro dg H tr g ΔF Gp a cF kF hrun hsh hc hpp hcF₁ hcF₂ hδ ha p k i T u hP hE hu hh hhj
    hW
  have hR : drainTime sp a ≤ sp.ts u := by rw [drainTime_eq]; exact hu
  exact outcome_of_rows hrun hsh hc hpp hcF₁ hcF₂ hδ ha hP hE hR hW
    (entry_rows hrun hsh hc hcF₂ hδ ha hP hE hR hh hhj)

end Consensus.Goldilocks.Healing

end
