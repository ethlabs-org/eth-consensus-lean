module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Outcome
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion

-- Keep the finite reset service adapter with the outcome-service assembly it supplies.
set_option linter.style.longFile 2000

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
  retained justified crossing. From `report_cover` (workbench#30 `entry-rows-exact.md`), HR.4
  (R1), the honest client records (no high timeout) and `δ_t ≥ 2` (no timeout by `t_u + 6Δ`).
* **The outcome** (`outcome_of_rows`, §26): with the window's honest ready proposal `W` whose
  parent extends `T` (retained ready inclusion), the rows reach `W`'s proposer before `t_{W.slot}`
  (`6Δ + Δ_F ≤ 4Δ·𝓕`) and give the literal `GW(E, 0, k_F)` at its acceptance of `W` (C0.3), unless
  a retained chain justified `E` first (branch (ii)); the carrier is relayed within `Δ`; at an
  unbound entry `E` is justified by the window's end in both branches (G1.7 in branch (i)).

Acceptance relay reaches only the honest nodes whose `Σ.F` the carrier extends, so each branch
needs that at the relay deadline every honest node holds the carrier or has its `Σ.F` below it.
Both are `carrier_below_origin`: a carrier below a high origin is held or above every honest
`Σ.F`, since HR.4 (R2) makes every honest `Σ.F` compatible with the origin. In branch (ii)
(`early_carrier_below`) the crossing lies below a high origin by `EntryRows`; in branch (i)
(`window_carrier_below`) `W` lies below one by `window_origin`: the update of slot `W.slot`
(`ready_update`) writes a fast lock stored on `W`, high because `W` is above the reset's origin
(`reset_origin_below`, (R3) and `ready_unanimous`), or an actual higher report above `W` lies
below a high origin (`higher_report_window_origin`, through `high_report_origin`).

Interface: `entry_rows` uses the open `report_cover`; `outcome_of_rows` the open private step
`update_window_kept` (at that update `W` stays a viable-ancestor candidate, or a higher source
intervened, below a high origin above `W`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The rows of a served entry by its deadline**: the entry `T` of height `h` (bound when
`bound`, with predecessor justification `Jr` at `hj`) has, by `d`, a quorum of honest target rows
signed by `d`, carrying the predecessor at a bound entry; or an honest node has accepted by `d` a
block `X` that justifies `T` at `h`, at a bound entry has finalized the predecessor, and lies below
a high origin (HR.4) written by `d` (the crossing is extracted from an actual higher returned
source, below its stored origin). -/
def EntryRows (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time)
    (T : SA.Blk sp.n (List (FG.Att sp.n))) (h hj : Nat) (bound : Bool) (Jr : Nat) (d : Time) :
    Prop :=
  (∃ R : Finset (FG.Att sp.n), sp.toParams.fg.q ≤ (R.image FG.Att.val).card ∧
    ∀ r ∈ R, r.val ∈ H ∧ (∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ d) ∧
      r.h = h ∧ r.T = T.root ∧ r.timeout = false ∧ (bound = true → r.fin = some (hj, Jr))) ∨
  ∃ y ∈ H, ∃ k X, tr.AcceptAt y k X ∧ tr.time k ≤ d ∧
    Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T h X ∧
    (bound = true → ((tr.post k).fg.σ X.root).hF + 1 = h ∧ ((tr.post k).fg.σ X.root).F = Jr) ∧
    ∃ xo io jo B, HighOrigin tr H g xo io jo B ∧ tr.time io ≤ d ∧ Anc (tr.HonestBlocks H) X B

theorem entryRows_iff {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {g : Time}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {h hj : Nat} {bound : Bool} {Jr : Nat} {d : Time} :
    EntryRows tr H g T h hj bound Jr d ↔
      ((∃ R : Finset (FG.Att sp.n), sp.toParams.fg.q ≤ (R.image FG.Att.val).card ∧
        ∀ r ∈ R, r.val ∈ H ∧ (∃ j, tr.SignAt r.val j r ∧ tr.time j ≤ d) ∧
          r.h = h ∧ r.T = T.root ∧ r.timeout = false ∧
          (bound = true → r.fin = some (hj, Jr))) ∨
      ∃ y ∈ H, ∃ k X, tr.AcceptAt y k X ∧ tr.time k ≤ d ∧
        Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T h X ∧
        (bound = true →
          ((tr.post k).fg.σ X.root).hF + 1 = h ∧ ((tr.post k).fg.σ X.root).F = Jr) ∧
        ∃ xo io jo B, HighOrigin tr H g xo io jo B ∧ tr.time io ≤ d ∧
          Anc (tr.HonestBlocks H) X B) :=
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

/-! ## The first crossing of an entry before its timeout (workbench#30 §5)

As `Lemmas/FGStore/Window.lean` (`events_current`, `entry_facts`), at a reachable store. -/

section Walk

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- One block keeps the height and entry (and its slot), or enters the next height itself. -/
private theorem step_entry_slot {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    (σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ σ'.ThSlot = σ.ThSlot) ∨
      (σ'.h = σ.h + 1 ∧ σ'.Th = B.root ∧ σ'.ThSlot = B.slot) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩

/-- Before the entry `(h₀, Tr)` of slot `u` is `δ_t` old, the height events keep it, its
justification `(j, Jr)` and (bound) `(j, Jr)` pending or finalized, or justify it having
finalized `(j, Jr)` at a bound height (`Window.lean`'s `events_current`, first half). -/
private theorem events_keep {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    (he : gp.heightEvents σ = σ') {h₀ Tr u j Jr : Nat}
    (hh : σ.h = h₀) (hT : σ.Th = Tr) (hu : σ.ThSlot = u) (hj : σ.hj = j) (hJ : σ.J = Jr)
    (hpw : σ.pending.Pairwise (fun p r => p.1 < r.1))
    (hmem : ∀ p ∈ σ.pending, σ.hF < p.1 ∧ p.1 ≤ σ.hj)
    (hP : 0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ.pending ∨ σ.hF = j ∧ σ.F = Jr)
    (hs : σ.s < u + gp.δt) :
    (σ'.h = h₀ ∧ σ'.Th = Tr ∧ σ'.ThSlot = u ∧ σ'.hj = j ∧ σ'.J = Jr ∧
        (0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ'.pending ∨ σ'.hF = j ∧ σ'.F = Jr)) ∨
      (σ'.h = h₀ + 1 ∧ σ'.hj = h₀ ∧ σ'.J = Tr ∧ (0 < j ∧ j + 1 = h₀ → σ'.F = Jr ∧ σ'.hF = j)) := by
  subst he hh hT hu hj hJ
  obtain ⟨F, hF, hfp, hc⟩ := gp.finalizePrune_eq σ
  have hP₁ : 0 < σ.hj ∧ σ.hj + 1 = σ.h →
      (σ.hj, σ.J) ∈ σ.pending.filter (fun p => hF < p.1) ∨ hF = σ.hj ∧ F = σ.J := by
    intro hb
    simp only [List.mem_filter, decide_eq_true_eq]
    rcases hP hb with hm | ⟨e1, e2⟩ <;> rcases hc with ⟨rfl, rfl⟩ | ⟨hm', -⟩
    · exact Or.inl ⟨hm, (hmem _ hm).1⟩
    · by_cases hlt : hF < σ.hj
      · exact Or.inl ⟨hm, hlt⟩
      · have he : hF = σ.hj := le_antisymm (hmem _ hm').2 (not_lt.1 hlt)
        have := FG.eq_of_pairwise_fst_lt hpw hm' hm he
        exact Or.inr ⟨he, (Prod.ext_iff.1 this).2⟩
    · exact Or.inr ⟨e1, e2⟩
    · have := hmem _ hm'
      omega
  by_cases hJ' : gp.justifies (gp.finalizePrune σ)
  · -- justifying: the next height, with the predecessor finalized at a bound height
    unfold FG.FGParams.heightEvents
    simp only [hJ', ↓reduceIte]
    rw [hfp] at hJ' ⊢
    dsimp only [FG.ChainState.advance]
    obtain ⟨-, hJ'⟩ := hJ'
    refine Or.inr ⟨rfl, rfl, rfl, fun hb => ?_⟩
    have he := hJ'.resolve_left (· hb)
    dsimp only at he
    rcases hP₁ hb with hm | ⟨-, hF'⟩
    · have := (List.mem_filter.1 hm).2
      simp only [decide_eq_true_eq] at this
      omega
    · exact ⟨hF', he⟩
  have hTO : ¬ gp.timesOut (gp.finalizePrune σ) := by
    rw [hfp]; rintro ⟨-, h⟩; dsimp only at h; omega
  have e : gp.heightEvents σ = gp.finalizePrune σ := by
    unfold FG.FGParams.heightEvents; simp only [hJ', hTO, ↓reduceIte]
  rw [e, hfp]
  exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hP₁⟩

/-- `events_keep` for one accepted block of a slot before `u + δ_t`. -/
private theorem step_keep {gp : FG.FGParams} {c : List (FG.FGBlock gp.n)}
    {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n} (hc : gp.chainState c = some σ)
    (hB : gp.stateTransition σ B = some σ') {h₀ Tr u j Jr : Nat}
    (hh : σ.h = h₀) (hT : σ.Th = Tr) (hu : σ.ThSlot = u) (hj : σ.hj = j) (hJ : σ.J = Jr)
    (hP : 0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ.pending ∨ σ.hF = j ∧ σ.F = Jr)
    (hs : B.slot < u + gp.δt) :
    (σ'.h = h₀ ∧ σ'.Th = Tr ∧ σ'.ThSlot = u ∧ σ'.hj = j ∧ σ'.J = Jr ∧
        (0 < j ∧ j + 1 = h₀ → (j, Jr) ∈ σ'.pending ∨ σ'.hF = j ∧ σ'.F = Jr)) ∨
      (σ'.h = h₀ + 1 ∧ σ'.hj = h₀ ∧ σ'.J = Tr ∧ (0 < j ∧ j + 1 = h₀ → σ'.F = Jr ∧ σ'.hF = j)) := by
  obtain ⟨-, -, -, -, -, -, hpw, hmem, -, -⟩ := FG.chain_invariants gp c σ hc
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 hB
  obtain ⟨f, p, t, hf⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he
  exact events_keep he hh hT hu hj hJ hpw hmem hP hs

/-- An entry block entered its height at its slot, with (bound) its predecessor pending. -/
private theorem entry_slot_pending {st : Store P ACP} (hr : st.Reachable acp₀)
    {T : NodeBlock P ACP} (hT : T ∈ st.tree) (hTe : (st.σ T.root).Th = T.root) :
    (st.σ T.root).ThSlot = T.slot ∧
      ((st.σ T.root).bound → ((st.σ T.root).hj, (st.σ T.root).J) ∈ (st.σ T.root).pending) := by
  obtain ⟨-, hcoh, -, hg⟩ := Store.accepted_tree P ACP acp₀ _ hr
  rcases Relation.ReflTransGen.cases_tail (hg T hT) with rfl | ⟨Z, -, hZ, -, hp⟩
  · rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]
    exact ⟨rfl, fun h => absurd h.1 (lt_irrefl 0)⟩
  obtain ⟨-, -, -, hst⟩ := Store.step_σ hr hT hp
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain P ACP acp₀ _ hr Z hZ
  rcases step_entry_slot hst with ⟨-, hTh, -⟩ | ⟨hh, -, hs⟩
  · exfalso
    obtain ⟨⟨E, hE, hEr, hEZ, -⟩, -⟩ := Store.entry_state_of_source P ACP acp₀ _ hr Z hZ
    obtain rfl : E = T := hcoh.1 hE hT (hEr.trans (hTh.symm.trans hTe))
    have := (hEZ.slot_le hcoh).1
    have := hcoh.2 Z hZ E hT hp
    omega
  · refine ⟨hs, fun hb => ?_⟩
    obtain ⟨-, -, -, -, h5⟩ := FG.height_step P.fg _ _ _ _ hc hst
    exact List.mem_of_getLast? ((h5 hh).2.2 hb).2

/-- **The first crossing of an entry before its timeout** (workbench#30 §5): from an entry `T` to
`C`, all slots before `T.slot + δ_t`, each block keeps `T`'s height, entry and justification (all
blocks from `T` to it too), or some `X` on the way justifies `T` and (bound) finalized `P_E`. -/
private theorem crossing_walk {st : Store P ACP} (hr : st.Reachable acp₀) {T C : NodeBlock P ACP}
    (hT : T ∈ st.tree) (hTe : (st.σ T.root).Th = T.root)
    (hslot : ∀ W, st.Anc W C → W.slot < T.slot + P.fg.δt) :
    ∀ W, st.Anc T W → st.Anc W C →
      (((st.σ W.root).h = (st.σ T.root).h ∧ (st.σ W.root).Th = T.root ∧
          (st.σ W.root).ThSlot = T.slot ∧ (st.σ W.root).hj = (st.σ T.root).hj ∧
          (st.σ W.root).J = (st.σ T.root).J ∧
          (0 < (st.σ T.root).hj ∧ (st.σ T.root).hj + 1 = (st.σ T.root).h →
            ((st.σ T.root).hj, (st.σ T.root).J) ∈ (st.σ W.root).pending ∨
            (st.σ W.root).hF = (st.σ T.root).hj ∧ (st.σ W.root).F = (st.σ T.root).J)) ∧
        ∀ Y ∈ st.tree, st.Anc T Y → st.Anc Y W →
          (st.σ Y.root).h = (st.σ T.root).h ∧ (st.σ Y.root).Th = T.root) ∨
      ∃ X, Store.JustifiesEntry P ACP st T (st.σ T.root).h X ∧ st.Anc X W ∧
        ((st.σ T.root).bound →
          (st.σ X.root).F = (st.σ T.root).J ∧ (st.σ X.root).hF = (st.σ T.root).hj) := by
  obtain ⟨-, hcoh, -, -⟩ := Store.accepted_tree P ACP acp₀ _ hr
  obtain ⟨hTs, hPE⟩ := entry_slot_pending hr hT hTe
  intro W hTW
  induction hTW with
  | refl =>
    refine fun _ => Or.inl ⟨⟨rfl, hTe, hTs, rfl, rfl, fun hb => Or.inl (hPE hb)⟩,
      fun Y _ hTY hYT => ?_⟩
    obtain rfl := hTY.antisymm hcoh hYT
    exact ⟨rfl, hTe⟩
  | @tail W' W hTW' hpW ih =>
    intro hWC
    obtain ⟨h1, h2, hp'⟩ := hpW
    rcases ih (Relation.ReflTransGen.head ⟨h1, h2, hp'⟩ hWC) with
      ⟨⟨hh, hTh, hu, hj, hJ, hP⟩, hkeep⟩ | ⟨X, hX, hXW', hfin⟩
    swap
    · exact Or.inr ⟨X, hX, hXW'.tail ⟨h1, h2, hp'⟩, hfin⟩
    obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain P ACP acp₀ _ hr W' h1
    obtain ⟨-, -, -, hst⟩ := Store.step_σ hr h2 hp'
    have hkeep' : ∀ Y ∈ st.tree, st.Anc T Y → st.Anc Y W → Y ≠ W →
        (st.σ Y.root).h = (st.σ T.root).h ∧ (st.σ Y.root).Th = T.root := by
      intro Y hY hTY hYW hne
      rcases Relation.ReflTransGen.cases_tail hYW with rfl | ⟨Z, hYZ, hZ, -, hZp⟩
      · exact absurd rfl hne
      · obtain rfl : Z = W' := hcoh.1 hZ h1 (Option.some.inj (hZp.symm.trans hp'))
        exact hkeep Y hY hTY hYZ
    rcases step_keep hc hst hh hTh hu hj hJ hP (hslot W hWC) with
      hcur | ⟨-, hj', hJ', hfin⟩
    · refine Or.inl ⟨hcur, fun Y hY hTY hYW => ?_⟩
      by_cases hne : Y = W
      · subst hne
        exact ⟨hcur.1, hcur.2.1⟩
      · exact hkeep' Y hY hTY hYW hne
    · exact Or.inr ⟨W, ⟨h2, hTW'.tail ⟨h1, h2, hp'⟩, hj', hJ', hkeep'⟩, .refl, hfin⟩

/-- The block named by a source's `T_h` is held and is the entry of its own state. -/
private theorem source_entry {st : Store P ACP} (hr : st.Reachable acp₀) (src : NodeBlock P ACP) :
    ∃ E ∈ st.tree, E.root = (st.σ src.root).Th ∧ (st.σ E.root).Th = E.root := by
  rcases hs : st.blocks src.root with _ | X
  · have hg : (st.σ src.root).Th = P.genesisRoot := by rw [Store.σ_of_blocks_none hr hs]; rfl
    refine ⟨_, Store.genesis_mem hr, hg.symm, ?_⟩
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]; rfl
  · have hXr : X.root = src.root := Goldilocks.Store.Reachable.blocks_root hr hs
    have hX : X ∈ st.tree := by change st.blocks X.root = some X; rw [hXr]; exact hs
    obtain ⟨⟨E, hE, hEr, -, -, hET⟩, -⟩ := Store.entry_state_of_source P ACP acp₀ _ hr X hX
    rw [← hXr]
    exact ⟨E, hE, hEr, hET.trans hEr.symm⟩

end Walk

/-! ## The honest client's records (workbench#30 §4) -/

section Client

/-- `create_attestation` signs `(h, T_h)` of its input with the record's finality pair and
records it; a timeout only on a recorded timeout or another target at that height. -/
private theorem createAtt_spec {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    a.val = v ∧ a.h = σe.h ∧ a.T = σe.Th ∧ a.fin = Λ.finalityPair σe ∧ Λ' = Λ.recordAtt a ∧
      (a.timeout = true → Λ.timeout σe.h ≠ ∅ ∨ ∃ T', Λ.target σe.h = some T' ∧ T' ≠ σe.Th) := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · cases h
  dsimp only at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := Store.heightPair_eq hp
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun hτ => ?_⟩
  unfold FG.Record.heightPair at hp
  split_ifs at hp with h1 h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp
  · exact Or.inl h2
  · simp_all
  · push Not at h3
    obtain ⟨T'', hT''⟩ := Option.ne_none_iff_exists'.1 h3.1
    exact Or.inr ⟨T'', hT'', fun e => h3.2 (hT''.trans (by rw [e]))⟩

/-- `create_attestation` signs nothing only on a lock of another root at the input's height, or
a content of that height already sent. -/
private theorem createAtt_none {n : Nat} {Λ : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    (h : Λ.createAtt v σe = none) :
    (Λ.lock σe.h ≠ none ∧ Λ.lock σe.h ≠ some σe.Th) ∨ ∃ b ∈ Λ.sent, b.1 = σe.h := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · unfold FG.Record.heightPair at hp
    split_ifs at hp with h1
    exact Or.inl h1
  · obtain ⟨rfl, -⟩ := Store.heightPair_eq hp
    dsimp only at h
    split_ifs at h with hany
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.1 hany
    exact Or.inr ⟨b, hb, (of_decide_eq_true hb').1⟩

end Client

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
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp a : Time} {cF kF : Nat}

/-! ## The actual reports (workbench#30 §3) -/

/-- A block that `ac_to_fg` returns is a candidate (as in `Retention/Rows`). -/
private theorem mem_toFGCandidates {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {C : SA.Blk sp.n FGP} (h : (SA.acToFG sp A Φ t).2.1 = some C) :
    C ∈ SA.toFGCandidates sp A Φ t := by
  unfold SA.acToFG at h
  dsimp only at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (SA.deepest_mem hC').1

/-- The selection of a fast-lock write is in the frame of its call (as in `Retention/Rows`). -/
private theorem fastLockAt_frame_mem {x : Fin sp.n} {i s : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (h : SA.FastLockAt tr.projAC x i s D CV) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x i ℓ) : D ∈ ℓ.frame.tree := by
  rcases h with ⟨ℓ', C, ⟨hc', -⟩, -, -, hD, -⟩ | ⟨ℓ', A, ⟨hc', -⟩, -, hsel, -⟩
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    exact (SA.deepest_mem hD).1.1.1
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (SA.deepest_mem hsel).1.1

/-- The block of an actual report is in the reporter's FG tree. -/
private theorem report_mem (hrun : GoldilocksRun proposer dg H tr)
    {z : Fin sp.n} (hz : z ∈ H) {r : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.ToFGAt tr.projAC z r ℓ C) : C ∈ (tr.state z r).fg.tree :=
  mem_tree_of_frame hrun hz h.1 (mem_toFGCandidates h.2.2).1.1

/-- **An actual high report has a stored high origin written before it** (workbench#30 §3, the
prefix of `high_row_source`): `C` is the viable image of a live fast lock, below the stored block
`B` of an earlier fast-lock write (`stored_fast_lock_provenance`); `B` is high as `C ⪯ B` is. -/
theorem high_report_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ℓ C)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h) :
    ∃ io < r, ∃ jo B, HighOrigin tr H g z io jo B ∧ Anc (tr.HonestBlocks H) C B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := hr.coherent
  obtain ⟨hpc, -, hC'⟩ := hrep
  obtain ⟨hCv, l, hl, hlb, hlf, -⟩ := mem_toFGCandidates hC'
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨io, hio, CV, ℓw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    stored_fast_lock_provenance hr hz r l₀ hl₀ hlf
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hz hpc
  obtain ⟨hΦw, -⟩ := SA.frameIn_of_callAt hr hz hcw
  have hCt : C ∈ ℓ.frame.tree := hCv.1
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
  obtain rfl : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
  set O := ℓw.frame.viableAncestor D
  have hCO : Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor L) O := (hva.mono hΦU).trans hLO
  have hOt : O ∈ (tr.state z io).fg.tree :=
    mem_tree_of_frame hp.run hz hcw (SA.viableAncestor_anc hΦw (fastLockAt_frame_mem hfl hcw)).1
  have hOr : O ∈ (tr.state z r).fg.tree := Compose.tree_mono hp.run.toLocalRun hz hio.le hOt
  have hCOr := store_anc_of_honest_anc hp.run hp.noColl hz hCO hOr
  have hOh : HZ tr H g + 1 ≤ ((tr.state z io).fg.σ O.root).h := by
    rw [← σ_eq_honest hp.run hp.noColl hz hz hOr hOt]
    exact hhC.trans (h_le_of_store_anc (Compose.fg_reachable hp.run.toLocalRun hz r) hCOr)
  have hoO : HighOrigin tr H g z io l₀.slot O := by
    unfold HighOrigin Compose.StoredFastLockAt
    exact ⟨hz, joinedAt_of_fastLockAt hp.run hp.noColl hz hfl, ⟨CV, ℓw, D, hcw, hfl, rfl⟩, hOh⟩
  exact ⟨io, hio, l₀.slot, O, hoO, hCO⟩

/-- Bounded report provenance retains the raw fast-lock source, as well as
its stored viable image. Both cover the actual report. -/
theorem ResetPremisesUpTo.high_report_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h) :
    ∃ io < r, ∃ jo O D CV, HighOrigin tr H g z io jo O ∧ tr.time io ≤ b ∧
      SA.FastLockAt tr.projAC z io jo D CV ∧ Anc (tr.HonestBlocks H) C O ∧
      Anc (tr.HonestBlocks H) O D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hpc, _, hC'⟩ := hrep
  obtain ⟨hCv, l, hl, hlb, hlf, _⟩ := mem_toFGCandidates hC'
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, _, rfl⟩ := hl
  obtain ⟨io, hio, CV, ellw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    stored_fast_lock_provenance hr hz r l₀ hl₀ hlf
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hz hpc
  obtain ⟨hPhiw, hPhiwU⟩ := SA.frameIn_of_callAt hr hz hcw
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hPhi hB₀
  obtain rfl : C = ell.frame.viableAncestor B₀ :=
    hr.coherent.1 (hPhiU hCv.1) (hPhiU hvat) hlb.symm
  obtain rfl : L = B₀ := hr.coherent.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)
  let O := ellw.frame.viableAncestor D
  have hCO : Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) O :=
    (hva.mono hPhiU).trans hLO
  have hOD := SA.viableAncestor_anc hPhiw (fastLockAt_frame_mem hfl hcw)
  have hOt : O ∈ (tr.state z io).fg.tree := mem_tree_of_frame hp.run hz hcw hOD.1
  have hOr := Compose.tree_mono hp.run.toLocalRun hz hio.le hOt
  have hOh : HZ tr H g + 1 ≤ ((tr.state z io).fg.σ O.root).h := by
    rw [← σ_eq_honest hp.run hp.noColl hz hz hOr hOt]
    exact hhC.trans (h_le_of_store_anc (Compose.fg_reachable hp.run.toLocalRun hz r)
      (store_anc_of_honest_anc hp.run hp.noColl hz hCO hOr))
  refine ⟨io, hio, l₀.slot, O, D, CV, ?_, (hp.run.time_mono hio.le).trans hrb,
    hfl, hCO, hOD.2.mono hPhiwU⟩
  exact ⟨hz, joinedAt_of_fastLockAt hp.run hp.noColl hz hfl, ⟨CV, ellw, D, hcw, hfl, rfl⟩, hOh⟩

/-! ## High entries and the honest records (workbench#30 §4) -/

/-- Historical self-entries under bounded high origins agree at equal height. -/
theorem ResetPremisesUpTo.high_entry_eq {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (ho' : HighOrigin tr H g x' i' j' B') (hi'b : tr.time i' ≤ b)
    (h₁ : Anc (tr.HonestBlocks H) Z₁ B) (h₂ : Anc (tr.HonestBlocks H) Z₂ B')
    {y₁ y₂ : Fin sp.n} (hy₁ : y₁ ∈ H) (hy₂ : y₂ ∈ H) {m₁ m₂ : Nat}
    (hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have key : ∀ {w : Fin sp.n} {k : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}, w ∈ H →
      D ∈ (tr.state w k).fg.tree → Anc (tr.HonestBlocks H) Z₁ D →
      Anc (tr.HonestBlocks H) Z₂ D → Z₁.root = Z₂.root := by
    intro w k D hw hD hZ₁D hZ₂D
    have e₁ := σ_eq_honest hp.run hp.noColl hy₁ hw hZ₁ (hp.mem_tree_of_anc hw hZ₁D hD)
    have e₂ := σ_eq_honest hp.run hp.noColl hy₂ hw hZ₂ (hp.mem_tree_of_anc hw hZ₂D hD)
    exact hp.entry_root_eq hw hD hZ₁D hZ₂D (by rw [← e₁, ← e₂, hh])
      (by rw [← e₁, hT₁]) (by rw [← e₂, hT₂])
  obtain ⟨CV, hs⟩ := ho.2.2.1
  obtain ⟨CV', hs'⟩ := ho'.2.2.1
  rcases hp.origins_compatible ho hib ho' hi'b with hBB' | hB'B
  · exact key ho'.1 (storedFastLock_mem hp.run hp.noColl ho'.1 hs').1 (h₁.trans hBB') h₂
  · exact key ho.1 (storedFastLock_mem hp.run hp.noColl ho.1 hs).1 h₁ (h₂.trans hB'B)

/-- **Two high-chain entries of one height are one block**: below two high origins, comparable
(R1), they sit below the larger, held by its writer, where `entry_root_eq` applies. -/
private theorem high_entry_eq (hp : ResetPremises tr H proposer dg g ΔF a) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (ho' : HighOrigin tr H g x' i' j' B')
    (h₁ : Anc (tr.HonestBlocks H) Z₁ B) (h₂ : Anc (tr.HonestBlocks H) Z₂ B')
    {y₁ y₂ : Fin sp.n} (hy₁ : y₁ ∈ H) (hy₂ : y₂ ∈ H) {m₁ m₂ : Nat}
    (hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have key : ∀ {w : Fin sp.n} {k : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}, w ∈ H →
      D ∈ (tr.state w k).fg.tree → Anc (tr.HonestBlocks H) Z₁ D →
      Anc (tr.HonestBlocks H) Z₂ D → Z₁.root = Z₂.root := by
    intro w k D hw hD hZ₁D hZ₂D
    have e₁ := σ_eq_run hp hy₁ hw hZ₁ (mem_tree_of_anc hp hw hZ₁D hD)
    have e₂ := σ_eq_run hp hy₂ hw hZ₂ (mem_tree_of_anc hp hw hZ₂D hD)
    exact entry_root_eq hp hw hD hZ₁D hZ₂D (by rw [← e₁, ← e₂, hh]) (by rw [← e₁, hT₁])
      (by rw [← e₂, hT₂])
  obtain ⟨CV, hs⟩ := ho.2.2.1
  obtain ⟨CV', hs'⟩ := ho'.2.2.1
  rcases (height_scoped_retention sp ro proposer dg H tr g ΔF hp.run hp.healthy hp.noColl a
    hp.reset).comparable x i j B x' i' j' B' ho ho' with hBB' | hB'B
  · exact key ho'.1 (storedFastLock_mem hp.run hp.noColl ho'.1 hs').1 (h₁.trans hBB') h₂
  · exact key ho.1 (storedFastLock_mem hp.run hp.noColl ho.1 hs).1 h₁ (h₂.trans hB'B)

/-- **A high record entry is the high-chain entry of its height**: an honest record's target,
timeout or lock entry at `h ≥ H_z + 1` is the root of every entry at `h` below a high origin. -/
theorem ResetPremisesUpTo.record_entry_eq {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {i h r : Nat} (hib : tr.time i ≤ b)
    (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r)
    {xo : Fin sp.n} {io jo : Nat} {B E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hEB : Anc (tr.HonestBlocks H) E B) {z : Fin sp.n}
    (hz : z ∈ H) {m : Nat} (hE : E ∈ (tr.state z m).fg.tree)
    (hEh : ((tr.state z m).fg.σ E.root).h = h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) : r = E.root := by
  have target : ∀ k < i, ∀ att, tr.SignAt y k att → att.h = h → att.T = r → r = E.root := by
    intro k hki att hs hah har
    obtain ⟨q, hqk, l, O, hO, X, hX, hXO, hXr, hXh, hXT⟩ :=
      hp.high_row_source hy hs (hah ▸ hh)
    exact har.symm.trans (hXr.symm.trans (hp.high_entry_eq hO
      ((hp.run.time_mono (hqk.le.trans hki.le)).trans hib) ho hiob
      (hXO.mono fun D hD => ⟨y, hy, q, hD⟩) hEB hy hz hX hE
      (hXh.trans (hah.trans hEh.symm)) hXT hET))
  rcases hr with ht | ht | hl
  · obtain ⟨k, hki, att, hs, hah, har⟩ :=
      (client_record_origin_of_run hp.run hy h r i).1 (Or.inl ht)
    exact target k hki att hs hah har
  · obtain ⟨k, hki, att, hs, hah, har⟩ :=
      (client_record_origin_of_run hp.run hy h r i).1 (Or.inr ht)
    exact target k hki att hs hah har
  · obtain ⟨k, hki, att, hs, hfin⟩ := (client_record_origin_of_run hp.run hy h r i).2 hl
    obtain ⟨J, hJ, X, hX, hXr, hJX, hJr, hJh, hJT⟩ := signed_fin_pair_entry_of_run hp.run hy hs hfin
    obtain ⟨X', hX', hX'r, hX'h⟩ := signAt_entry hp.run hy hs
    obtain rfl : X' = X := hp.honest_coherent.1 ⟨y, hy, k, hX'⟩ ⟨y, hy, k, hX⟩
      (hX'r.trans hXr.symm)
    have hle := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k) hJX
    obtain ⟨q, hqk, l, O, hO, X'', hX'', hXO, hX''r, _, _⟩ := hp.high_row_source hy hs (by omega)
    obtain rfl : X'' = X' := hp.honest_coherent.1 ⟨y, hy, q, hX''⟩ ⟨y, hy, k, hX⟩
      (hX''r.trans hX'r.symm)
    have hJO : Anc (tr.HonestBlocks H) J O :=
      (hJX.mono (show (tr.state y k).fg.tree ⊆ tr.HonestBlocks H from
        fun D hD => ⟨y, hy, k, hD⟩)).trans
        (hXO.mono fun D hD => ⟨y, hy, q, hD⟩)
    exact hJr.symm.trans (hp.high_entry_eq hO
      ((hp.run.time_mono (hqk.le.trans hki.le)).trans hib) ho hiob
      hJO hEB hy hz hJ hE (hJh.trans hEh.symm) hJT hET)

private theorem record_entry_eq (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H)
    {i h r : Nat} (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r)
    {xo : Fin sp.n} {io jo : Nat} {B E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hEB : Anc (tr.HonestBlocks H) E B) {z : Fin sp.n}
    (hz : z ∈ H) {m : Nat} (hE : E ∈ (tr.state z m).fg.tree)
    (hEh : ((tr.state z m).fg.σ E.root).h = h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) : r = E.root := by
  obtain ⟨x, i', j, B', ho', Z, hZB', rfl, w, hw, k, hZ, hZh, hZT⟩ := high_record_entry hp
    (height_scoped_retention sp ro proposer dg H tr g ΔF
      hp.run hp.healthy hp.noColl a hp.reset).rows
    hy hh hr
  exact high_entry_eq hp ho' ho hZB' hEB hw hz hZ hE (hZh.trans hEh.symm) hZT hET

/-- An honest record changes only when the node signs, by recording the signed attestation. -/
private theorem record_step (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    (tr.state y (i + 1)).record = (tr.state y i).record ∨
      ∃ att, tr.SignAt y i att ∧
        (tr.state y (i + 1)).record = (tr.state y i).record.recordAtt att := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hlaw := hrun.cutLaw y hy i c hc
    have hsucc := tr.state_succ_of_call hc
    cases c with
    | ac ℓ => exact Or.inl (by rw [hsucc]; exact hlaw.2.2.2)
    | fg ℓ =>
      rcases ℓ with ⟨B, _ | _⟩ | a' | ⟨C, _ | a'⟩
      · exact Or.inl (by rw [hsucc, hlaw.2])
      · exact Or.inl (by rw [hsucc]; exact hlaw.2.2.2)
      · exact Or.inl (by rw [hsucc]; exact hlaw.2.2)
      · exact Or.inl (by rw [hsucc, hlaw.2])
      · exact Or.inr ⟨a', ⟨C, hc⟩, hsucc ▸ (createAtt_spec hlaw.1).2.2.2.2.1⟩
  · exact Or.inl (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

/-- **The sent contents of an honest record were signed earlier** (`record_attestation`). -/
private theorem sent_origin (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {b : FG.Content} : ∀ i, b ∈ (tr.state y i).record.sent →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b
  | 0, hb => by
    rw [Trace.state, hrun.init y hy] at hb
    simp [Node.init, FG.Record.empty] at hb
  | i + 1, hb => by
    rcases record_step hrun hy i with he | ⟨att, hs, he⟩ <;> rw [he] at hb
    · obtain ⟨k, hk, h⟩ := sent_origin hrun hy i hb
      exact ⟨k, by omega, h⟩
    · rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨k, hk, h⟩ := sent_origin hrun hy i hb
        exact ⟨k, by omega, h⟩
      · exact ⟨i, by omega, att, hs, (List.mem_singleton.1 hb).symm⟩

/-- **The first-timeout step**: with no timeout recorded at its height, an honest high row is a
target: another recorded target there is the high-chain entry, the row's own. -/
private theorem sign_target (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hh : HZ tr H g + 1 ≤ att.h)
    (he : (tr.state y k).record.timeout att.h = ∅) : att.timeout = false := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw y hy k _ hc).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨-, hah, haT, -, -, hτ⟩ := createAtt_spec hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · obtain ⟨_, -, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := high_row_source hp hy ⟨src, hc⟩ hh
    exact hne ((record_entry_eq hp hy hh (Or.inl hT') hO (hEO.mono fun X hX => ⟨y, hy, _, hX⟩)
      hy hE hEh hET).trans hEr)

/-- **No honest high timeout** (workbench#30 §4, first-timeout induction): the timeout sets of an
honest record at the heights `≥ H_z + 1` stay empty. -/
private theorem timeout_empty (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i h, HZ tr H g + 1 ≤ h → (tr.state y i).record.timeout h = ∅
  | 0, h, _ => by
    rw [Trace.state, hp.run.init y hy]
    rfl
  | i + 1, h, hh => by
    rcases record_step hp.run hy i with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact timeout_empty hp hy i h hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := sign_target hp hy hs hh (timeout_empty hp hy i _ hh)
          simp_all
        · exact timeout_empty hp hy i h hh
      · exact timeout_empty hp hy i h hh

/-- The target and timeout fields of a high entry's row do not require its
predecessor to be high. -/
private theorem sign_target_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) (hkb : tr.time k ≤ b) (hh : HZ tr H g + 1 ≤ att.h)
    (he : (tr.state y k).record.timeout att.h = ∅) : att.timeout = false := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw y hy k _ hc).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, hah, haT, _, _, hτ⟩ := createAtt_spec hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · obtain ⟨q, hqk, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := hp.high_row_source hy ⟨src, hc⟩ hh
    exact hne ((hp.record_entry_eq hy hkb hh (Or.inl hT') hO
      ((hp.run.time_mono hqk.le).trans hkb) (hEO.mono fun X hX => ⟨y, hy, q, hX⟩)
      hy hE hEh hET).trans hEr)

private theorem timeout_empty_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i, tr.time i ≤ b → ∀ h, HZ tr H g + 1 ≤ h → (tr.state y i).record.timeout h = ∅
  | 0, _, h, _ => by rw [Trace.state, hp.run.init y hy]; rfl
  | i + 1, hib, h, hh => by
    have hib' := (hp.run.time_mono (Nat.le_succ i)).trans hib
    rcases record_step hp.run hy i with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact timeout_empty_before hp hy i hib' h hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := sign_target_before hp hy hs hib' hh (timeout_empty_before hp hy i hib' _ hh)
          simp_all
        · exact timeout_empty_before hp hy i hib' h hh
      · exact timeout_empty_before hp hy i hib' h hh

/-- Finite normalization of a high signature's target and timeout fields. -/
theorem ResetPremisesUpTo.row_target_of_sign {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {j : Nat} {att : FG.Att sp.n} (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocks H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false := by
  subst hσ
  have hh : HZ tr H g + 1 ≤ att.h := hatt ▸ hhT
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z hz j _ hc).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hv, _, _, _, _, _⟩ := createAtt_spec hcl
  obtain ⟨q, hqj, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := hp.high_row_source hz ⟨src, hc⟩ hh
  have hTr : att.T = T.root := hEr.symm.trans (hp.high_entry_eq hO
    ((hp.run.time_mono hqj.le).trans hjb) ho hiob
    (hEO.mono fun X hX => ⟨z, hz, q, hX⟩) hTB hz hy hE hT (hEh.trans hatt) hET hTe)
  exact ⟨hv, hTr, sign_target_before hp hz ⟨src, hc⟩ hjb hh (timeout_empty_before hp hz j hjb _ hh)⟩

theorem row_target_of_sign (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H)
    {j : Nat} {att : FG.Att sp.n} (hs : tr.SignAt z j att) {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hTB : Anc (tr.HonestBlocks H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false := by
  subst hσ
  have hh : HZ tr H g + 1 ≤ att.h := hatt ▸ hhT
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z hz j _ hc).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hv, -, -, -, -, -⟩ := createAtt_spec hcl
  obtain ⟨_, -, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := high_row_source hp hz ⟨src, hc⟩ hh
  have hTr : att.T = T.root := hEr.symm.trans (high_entry_eq hp hO ho
    (hEO.mono fun X hX => ⟨z, hz, _, hX⟩) hTB hz hy hE hT (hEh.trans hatt) hET hTe)
  exact ⟨hv, hTr, sign_target hp hz ⟨src, hc⟩ hh (timeout_empty hp hz j _ hh)⟩

/-- Historical signatures carry the exact bound predecessor when that predecessor
is high; permission is proved at the original signing cut. -/
theorem ResetPremisesUpTo.row_of_sign {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {j : Nat} {att : FG.Att sp.n} (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.bound → HZ tr H g + 1 ≤ σT.hj)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocks H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.bound → att.fin = some (σT.hj, σT.J)) := by
  subst hσ
  obtain ⟨hv, hTr, htimeout⟩ := hp.row_target_of_sign hz hs hjb hy hT rfl hTe hhT ho hiob hTB hatt
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z hz j _ hc).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, _, haT, hfin, _, _⟩ := createAtt_spec hcl
  refine ⟨hv, hTr, htimeout, fun hb => ?_⟩
  obtain ⟨E', hE', hE'r, hE'T⟩ := source_entry (Compose.fg_reachable hp.run.toLocalRun hz j) src
  have hR : ((tr.state z j).fg.σ src.root).Th = T.root := by
    rw [← hTr, haT, ← hE'r, hE'T]
  have he : E' = T := hp.honest_coherent.1 ⟨z, hz, j, hE'⟩ ⟨y, hy, m, hT⟩ (hE'r.trans hR)
  rw [he] at hE'
  rw [hfin, hR, σ_eq_honest hp.run hp.noColl hz hy hE' hT]
  obtain ⟨J₀, hJ₀, hJ₀T, hJ₀r, hJ₀h, hJ₀T'⟩ :=
    (chain_pairs_entry (Compose.fg_reachable hp.run.toLocalRun hy m) hT).1 hb.1
  have hsub : (tr.state y m).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, m, hX⟩
  have heq := fun r hr => (hp.record_entry_eq hz hjb (hhj hb) (i := j) (r := r) hr ho hiob
    ((hJ₀T.mono hsub).trans hTB) hy hJ₀ hJ₀h hJ₀T').trans hJ₀r
  have hperm : (tr.state z j).record.permits ((tr.state y m).fg.σ T.root).hj
      ((tr.state y m).fg.σ T.root).J := by
    refine ⟨?_, fun r hr => Finset.mem_singleton.2 (heq r (Or.inr (Or.inl hr))), ?_⟩
    · rcases ht : (tr.state z j).record.target _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inl ht)])]
    · rcases hl : (tr.state z j).record.lock _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inr (Or.inr hl))])]
  unfold FG.Record.finalityPair
  simp only [hb, hperm, ↓reduceIte]

/-- **An honest row of a high entry's height is its target row, with the predecessor at a bound
entry** (workbench#30 §4): it names `T` (`high_entry_eq`), is no timeout (`timeout_empty`), and
its `finality_pair` of `σ[T]` is `(h_j, J)`, which the high records permit (`record_entry_eq`). -/
theorem row_of_sign (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H)
    {j : Nat} {att : FG.Att sp.n} (hs : tr.SignAt z j att) {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.bound → HZ tr H g + 1 ≤ σT.hj)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hTB : Anc (tr.HonestBlocks H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.bound → att.fin = some (σT.hj, σT.J)) := by
  subst hσ
  obtain ⟨hv, hTr, htimeout⟩ := row_target_of_sign hp hz hs hy hT rfl hTe hhT ho hTB hatt
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z hz j _ hc).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨-, -, haT, hfin, -, -⟩ := createAtt_spec hcl
  refine ⟨hv, hTr, htimeout, fun hb => ?_⟩
  obtain ⟨E', hE', hE'r, hE'T⟩ := source_entry (Compose.fg_reachable hp.run.toLocalRun hz j) src
  have hR : ((tr.state z j).fg.σ src.root).Th = T.root := by
    rw [← hTr, haT, ← hE'r, hE'T]
  have hE'eq : E' = T := (honest_coherent hp).1 ⟨z, hz, j, hE'⟩ ⟨y, hy, m, hT⟩ (hE'r.trans hR)
  rw [hE'eq] at hE'
  rw [hfin, hR, σ_eq_run hp hz hy hE' hT]
  -- the records permit the predecessor: each high record entry at `h_j` is `J`'s block
  obtain ⟨J₀, hJ₀, hJ₀T, hJ₀r, hJ₀h, hJ₀T'⟩ :=
    (chain_pairs_entry (Compose.fg_reachable hp.run.toLocalRun hy m) hT).1 hb.1
  have hsub : (tr.state y m).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, m, hX⟩
  have heq := fun r hr => (record_entry_eq hp hz (hhj hb) (i := j) (r := r) hr ho
    ((hJ₀T.mono hsub).trans hTB) hy hJ₀ hJ₀h hJ₀T').trans hJ₀r
  have hperm : (tr.state z j).record.permits ((tr.state y m).fg.σ T.root).hj
      ((tr.state y m).fg.σ T.root).J := by
    refine ⟨?_, fun r hr => Finset.mem_singleton.2 (heq r (Or.inr (Or.inl hr))), ?_⟩
    · rcases ht : (tr.state z j).record.target _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inl ht)])]
    · rcases hl : (tr.state z j).record.lock _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inr (Or.inr hl))])]
  unfold FG.Record.finalityPair
  simp only [hb, hperm, ↓reduceIte]

/-- **A same-height report gives a row of the entry's height by then** (workbench#30 §4): the
client call after it (`toFG_attest`) reads `σ[T]`; it signs, or (no foreign lock,
`record_entry_eq`) already sent a content of that height, signed earlier (`sent_origin`). -/
theorem sign_of_report (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ℓ C) {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hTC : Anc (tr.HonestBlocks H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hTB : Anc (tr.HonestBlocks H) T B) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.h = σT.h := by
  subst hσ
  have hCt := report_mem hp.run hz hrep
  obtain ⟨hpc, hcall, hC⟩ := hrep
  have hTt := mem_tree_of_anc hp hz hTC hCt
  have hσT := σ_eq_run hp hz hy hTt hT
  have hCTh : ((tr.state z r).fg.σ C.root).Th = T.root := by
    rw [Th_eq_of_anc (Compose.fg_reachable hp.run.toLocalRun hz r) (anc_tree_of_anc hp hz hTC hCt)
      (by rw [hCh, hσT]), hσT, hTe]
  rw [Compose.projAC_state hp.run.toLocalRun hz] at hC
  obtain ⟨s, hs, hts, hfg⟩ :=
    toFG_attest hp.run.toLocalRun hz (Compose.projAC_callAt.1 hpc) hcall hC
  -- the entry state of the client call is `σ[T]`
  have hσe : (tr.state z (r + 1)).fg.σ ((tr.state z (r + 1)).fg.σ C.root).Th =
      (tr.state y m).fg.σ T.root := by
    rw [hfg, hCTh, hσT]
  cases s with
  | some att =>
    have hcl := (hp.run.cutLaw z hz _ _ hs).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = some (att, _) at hcl
    exact ⟨r + 1, att, ⟨C, hs⟩, hts.le, by rw [(createAtt_spec hcl).2.1, hσe]⟩
  | none =>
    have hcl := (hp.run.cutLaw z hz _ _ hs).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases createAtt_none hcl with ⟨hl, hl'⟩ | ⟨b, hb, hb1⟩
    · obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 hl
      have := record_entry_eq hp hz hhT (Or.inr (Or.inr hr')) ho hTB hy hT rfl hTe
      exact absurd (by rw [hr', this, hTe]) hl'
    · obtain ⟨k, hk, att, hsk, rfl⟩ := sent_origin hp.run hz (r + 1) hb
      exact ⟨k, att, hsk, (hp.run.time_mono hk.le).trans hts.le, hb1⟩

/-! ## A higher report: the same first crossing and its origin (workbench#30 §5) -/

/-- A bounded same-height report supplies an actual signature by its timestamp,
including the case where a previously signed content suppresses the new call. -/
theorem ResetPremisesUpTo.sign_of_report {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hTC : Anc (tr.HonestBlocks H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocks H) T B) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.h = σT.h := by
  subst hσ
  have hCt := report_mem hp.run hz hrep
  obtain ⟨hpc, hcall, hC⟩ := hrep
  have hTt := hp.mem_tree_of_anc hz hTC hCt
  have hσT := σ_eq_honest hp.run hp.noColl hz hy hTt hT
  have hCTh : ((tr.state z r).fg.σ C.root).Th = T.root := by
    rw [Th_eq_of_anc (Compose.fg_reachable hp.run.toLocalRun hz r)
      (store_anc_of_honest_anc hp.run hp.noColl hz hTC hCt)
      (by rw [hCh, hσT]), hσT, hTe]
  rw [Compose.projAC_state hp.run.toLocalRun hz] at hC
  obtain ⟨s, hs, hts, hfg⟩ :=
    toFG_attest hp.run.toLocalRun hz (Compose.projAC_callAt.1 hpc) hcall hC
  have hσe : (tr.state z (r + 1)).fg.σ ((tr.state z (r + 1)).fg.σ C.root).Th =
      (tr.state y m).fg.σ T.root := by rw [hfg, hCTh, hσT]
  cases s with
  | some att =>
    have hcl := (hp.run.cutLaw z hz _ _ hs).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = some (att, _) at hcl
    exact ⟨r + 1, att, ⟨C, hs⟩, hts.le, by rw [(createAtt_spec hcl).2.1, hσe]⟩
  | none =>
    have hcl := (hp.run.cutLaw z hz _ _ hs).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases createAtt_none hcl with ⟨hl, hl'⟩ | ⟨c, hc, _⟩
    · obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 hl
      have := hp.record_entry_eq hz (hts.le.trans hrb) hhT (Or.inr (Or.inr hr'))
        ho hiob hTB hy hT rfl hTe
      exact absurd (by rw [hr', this, hTe]) hl'
    · obtain ⟨k, hk, att, hsk, rfl⟩ := sent_origin hp.run hz (r + 1) hc
      exact ⟨k, att, hsk, (hp.run.time_mono hk.le).trans hts.le, by assumption⟩

/-- **A higher report gives the retained crossing** (workbench#30 §5): the reported `C ⪰ T`,
accepted by `t_u + 6Δ`, has slot `≤ u + 1 < u + δ_t`; the first `X` leaving `T`'s height on the
chain justifies `T` (`crossing_walk`), and `X ⪯ C ⪯ B`, `B` the report's origin. -/
private theorem crossing_of_report (hp : ResetPremises tr H proposer dg g ΔF a)
    (hδ : 2 ≤ sp.toParams.δt) {z : Fin sp.n} (hz : z ∈ H) {r : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ℓ C) {u : Nat} (hrt : tr.time r ≤ sp.ts u + 6 * sp.Δ)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hTu : T.slot = u) {y : Fin sp.n} (hy : y ∈ H)
    {m : Nat} (hT : T ∈ (tr.state y m).fg.tree) {σT : FG.ChainState sp.n}
    (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root) (hhT : HZ tr H g + 1 ≤ σT.h)
    (hTC : Anc (tr.HonestBlocks H) T C) (hlt : σT.h < ((tr.state z r).fg.σ C.root).h) :
    ∃ w ∈ H, ∃ k X, tr.AcceptAt w k X ∧ tr.time k ≤ sp.ts u + 6 * sp.Δ ∧
      Store.JustifiesEntry sp.toParams (Payload sp.n) (tr.post k).fg T σT.h X ∧
      (decide σT.bound = true →
        ((tr.post k).fg.σ X.root).hF + 1 = σT.h ∧ ((tr.post k).fg.σ X.root).F = σT.J) ∧
      ∃ xo io jo B, HighOrigin tr H g xo io jo B ∧ tr.time io ≤ sp.ts u + 6 * sp.Δ ∧
        Anc (tr.HonestBlocks H) X B := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hCt := report_mem hp.run hz hrep
  have hreach := Compose.fg_reachable hp.run.toLocalRun hz r
  have hcoh := (Store.accepted_tree _ _ _ _ hreach).2.1
  have hTt := mem_tree_of_anc hp hz hTC hCt
  have hσT := (σ_eq_run hp hz hy hTt hT).trans hσ
  -- the report is high: below a stored high origin written before it
  obtain ⟨io, hio, jo, B, ho, hCB⟩ := high_report_origin hp hz hrep (by omega)
  -- the report was accepted by `t_u + 6Δ`, so its slot is at most `u + 1`
  have hCslot : C.slot ≤ u + 1 := by
    rcases tree_accepted hp.run.toLocalRun hz hCt with hg | ⟨k, hk, hacc⟩
    · exfalso
      have := genesis_not_high hp hz hCt (by rw [hg]; rfl)
      omega
    have hsl : C.slot ≤ sp.slot (tr.time k) := (hp.run.cutLaw z hz k _ hacc).1
    have h1 : sp.ts (C.slot : Int) ≤ tr.time k :=
      (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).2 (by exact_mod_cast hsl)
    have h2 := hp.run.time_mono hk.le
    have h3 : sp.ts ((u + 2 : Nat) : Int) = sp.ts u + 8 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    have := (SA.ts_lt_iff sp).1 (h1.trans_lt (by linarith : tr.time k < _))
    omega
  have hslot : ∀ W, (tr.state z r).fg.Anc W C → W.slot < T.slot + sp.toParams.fg.δt :=
    fun W hW => by have := (hW.slot_le hcoh).1; change W.slot < T.slot + sp.toParams.δt; omega
  rcases crossing_walk hreach hTt (by rw [hσT, hTe]) hslot C
    (anc_tree_of_anc hp hz hTC hCt) .refl with ⟨⟨hh, -⟩, -⟩ | ⟨X, hJ, hXC, hfin⟩
  · rw [hσT] at hh
    omega
  obtain ⟨hXt, hTX, hXhj, hXJ, hkeep⟩ := hJ
  rcases tree_accepted hp.run.toLocalRun hz hXt with hg | ⟨kX, hkX, hacc⟩
  · exfalso
    rw [hg, show (sp.toParams.genesisBlock _).root = sp.toParams.genesisRoot from rfl,
      Store.σ_genesis hreach, hσT] at hXhj
    change 0 = _ at hXhj
    omega
  have hpost : (tr.post kX).fg = (tr.state z (kX + 1)).fg := by rw [tr.state_succ_of_call hacc]
  have hXk : X ∈ (tr.state z (kX + 1)).fg.tree := by
    rw [tr.state_succ_of_call hacc, (Store.tree_grows _ _ _ _
      (Compose.fg_reachable hp.run.toLocalRun hz kX)).1 X _ (hp.run.cutLaw z hz kX _ hacc).2.1]
    exact Set.mem_insert _ _
  have hσX := σ_eq_run hp hz hz hXk hXt
  have hsub : ∀ k, (tr.state z k).fg.tree ⊆ tr.HonestBlocks H := fun k X hX => ⟨z, hz, k, hX⟩
  refine ⟨z, hz, kX, X, hacc, (hp.run.time_mono hkX.le).trans hrt, ?_, fun hb => ?_, z, io, jo,
    B, ho, (hp.run.time_mono hio.le).trans hrt, (hXC.mono (hsub r)).trans hCB⟩
  · -- the justification at the acceptance of `X`
    rw [hpost, ← hσT]
    refine ⟨hXk, anc_tree_of_anc hp hz (hTX.mono (hsub r)) hXk, by rw [hσX]; exact hXhj,
      by rw [hσX]; exact hXJ, fun Y hY hTY hYX hne => ?_⟩
    have hYX' := anc_tree_of_anc hp hz (hYX.mono (hsub _)) hXt
    have hYr := mem_tree_of_anc hp hz (hYX.mono (hsub _)) hXt
    rw [σ_eq_run hp hz hz hY hYr]
    exact hkeep Y hYr (anc_tree_of_anc hp hz (hTY.mono (hsub _)) hYr) hYX' hne
  · have hb' := of_decide_eq_true hb
    obtain ⟨hF, hhF⟩ := hfin (by rw [hσT]; exact hb')
    rw [hpost, hσX, hF, hhF, hσT]
    exact ⟨hb'.2, rfl⟩

/-- **Entry rows** (§17 corrected, §18 BA): under C1.2's premises, a served entry has its rows,
or a retained justified crossing, by `t_u + 6Δ`. -/
theorem entry_rows (hrun : GoldilocksRun proposer dg H tr) (hsh : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hcF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time))
    (hδ : cF + kF ≤ sp.toParams.δt) (ha : IsReset tr H g a) {p y : Fin sp.n} {k i u : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u T)
    (hE : Compose.RunEntry tr H y i T) (hR : drainTime sp a ≤ sp.ts u)
    (hh : HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).h)
    (hhj : 0 < ((tr.post i).fg.σ T.root).hj →
      ((tr.post i).fg.σ T.root).hj + 1 = ((tr.post i).fg.σ T.root).h →
      HZ tr H g + 1 ≤ ((tr.post i).fg.σ T.root).hj) :
    EntryRows tr H g T ((tr.post i).fg.σ T.root).h ((tr.post i).fg.σ T.root).hj
      (decide ((tr.post i).fg.σ T.root).bound) ((tr.post i).fg.σ T.root).J
      (sp.ts u + 6 * sp.Δ) := by
  have hp : ResetPremises tr H proposer dg g ΔF a := ⟨hrun, hsh.healthy, hsh.noColl, ha⟩
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hΔF : sp.Δ ≤ ΔF := hsh.healthy.1.deltaF
  -- `c_F ≥ 2` from `7Δ ≤ 6Δ + Δ_F ≤ 4Δ·c_F`, so `δ_t ≥ 2`
  have hδ2 : 2 ≤ sp.toParams.δt := by
    have hcF2 : (2 : Int) ≤ cF := by
      by_contra hlt
      have : (cF : Int) ≤ 1 := by omega
      nlinarith
    omega
  obtain ⟨hy, hTacc, hTh⟩ := hE
  have hTu : T.slot = u := hP.2.2.2.2.1
  rw [← tr.state_succ_of_call hTacc] at hh hhj hTh ⊢
  set σT := (tr.state y (i + 1)).fg.σ T.root with hσT
  have hTt : T ∈ (tr.state y (i + 1)).fg.tree := by
    rw [tr.state_succ_of_call hTacc, (Store.tree_grows _ _ _ _
      (Compose.fg_reachable hrun.toLocalRun hy i)).1 T _ (hrun.cutLaw y hy i _ hTacc).2.1]
    exact Set.mem_insert _ _
  -- an actual report extending `T` is at least as high, so high, below a stored high origin
  have hrep : ∀ z ∈ H, ∀ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C → Anc (tr.HonestBlocks H) T C →
      σT.h ≤ ((tr.state z r).fg.σ C.root).h ∧
      ∃ io < r, ∃ jo B, HighOrigin tr H g z io jo B ∧ Anc (tr.HonestBlocks H) C B := by
    intro z hz r ℓ C h hTC
    have hCt := report_mem hrun hz h
    have hle : σT.h ≤ ((tr.state z r).fg.σ C.root).h := by
      rw [hσT, ← σ_eq_run hp hz hy (mem_tree_of_anc hp hz hTC hCt) hTt]
      exact h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hz r)
        (anc_tree_of_anc hp hz hTC hCt)
    exact ⟨hle, high_report_origin hp hz h (hh.trans hle)⟩
  -- §2 split: a higher actual report gives the retained crossing (§5)
  rcases report_cover hp hc hP hR with hall | ⟨z, hz, r, ℓ, C, hrc, hrt, hTC, hlt⟩
  swap
  · rw [σ_eq_run hp hz hy (mem_tree_of_anc hp hz hTC (report_mem hrun hz hrc)) hTt] at hlt
    exact entryRows_iff.2 (Or.inr (crossing_of_report hp hδ2 hz hrc hrt hTu hy hTt rfl hTh hh hTC
      hlt))
  by_cases hex : ∃ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) T C ∧
      σT.h < ((tr.state z r).fg.σ C.root).h
  · obtain ⟨z, hz, r, ℓ, C, hrc, hrt, hTC, hlt⟩ := hex
    exact entryRows_iff.2 (Or.inr (crossing_of_report hp hδ2 hz hrc hrt hTu hy hTt rfl hTh hh hTC
      hlt))
  push Not at hex
  -- every honest report is at `T`'s height: one honest target row per honest node (§4)
  have hrow : ∀ z : Fin sp.n, ∃ att : FG.Att sp.n, z ∈ H → att.val = z ∧
      (∃ j, tr.SignAt att.val j att ∧ tr.time j ≤ sp.ts u + 6 * sp.Δ) ∧
      att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
      (decide σT.bound = true → att.fin = some (σT.hj, σT.J)) := by
    intro z
    by_cases hz : z ∈ H
    · obtain ⟨r, ℓ, C, hrc, hrt, hTC⟩ := hall z hz
      obtain ⟨hle, io, -, jo, B, ho, hCB⟩ := hrep z hz r ℓ C hrc hTC
      obtain ⟨j, att, hs, hj, hatt⟩ := sign_of_report hp hz hrc hy hTt rfl hTh hh hTC
        (le_antisymm (hex z hz r ℓ C hrc hrt hTC) hle) ho (hTC.trans hCB)
      obtain ⟨hv, h₂, h₃, h₄⟩ := row_of_sign hp hz hs hy hTt rfl hTh hh (fun hb => hhj hb.1 hb.2)
        ho (hTC.trans hCB) hatt
      exact ⟨att, fun _ => ⟨hv, ⟨j, by rw [hv]; exact hs, hj.trans hrt⟩, hatt, h₂, h₃,
        fun hb => h₄ (of_decide_eq_true hb)⟩⟩
    · exact ⟨⟨z, 0, 0, false, none⟩, fun h => absurd h hz⟩
  choose f hf using hrow
  classical
  refine entryRows_iff.2 (Or.inl ⟨(Finset.univ.filter (· ∈ H)).image f, ?_, fun att hatt => ?_⟩)
  · have himg : ((Finset.univ.filter (· ∈ H)).image f).image FG.Att.val =
        Finset.univ.filter (· ∈ H) := by
      rw [Finset.image_image]
      refine (Finset.image_congr fun z hz => ?_).trans Finset.image_id
      exact (hf z (Finset.mem_filter.1 (Finset.mem_coe.1 hz)).2).1
    have hcard : (Finset.univ.filter (· ∈ H)).card = H.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp
    rw [himg, hcard]
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h3 := hsh.healthy.2.2
    have hn' : sp.n = sp.toParams.n := rfl
    change (2 * sp.toParams.n + 2) / 3 ≤ _
    omega
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hatt
    have hzH := (Finset.mem_filter.1 hz).2
    obtain ⟨hv, hs, h₁, h₂, h₃, h₄⟩ := hf z hzH
    exact ⟨by rw [hv]; exact hzH, hs, h₁, h₂, h₃, h₄⟩

/-! ## The carriers -/

/-- **C0.3 at an honest proposal**: the own block of an honest proposal is accepted at its cut,
and it includes every row of the proposer's pool that is valid against its parent's state and not
on its parent's chain (`proposal_attestations`). -/
private theorem proposal_accepted (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
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
private theorem firstCutFrom_exists (hrun : GoldilocksRun proposer dg H tr)
    (hh : tr.HealthyRun H ΔF g)
    {z : Fin sp.n} (hz : z ∈ H) {t : Time} (ht : SA.gbar g ≤ t) : ∃ j, tr.FirstCutFrom j t := by
  classical
  obtain ⟨i, -, hi⟩ := hrun.awake_in_horizon z hz t (hh.2.1 z hz t ht)
  have hex : ∃ k, t ≤ tr.time k := ⟨i, hi⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩

/-- **The relay of a carrier**: a block (not genesis) that an honest node accepted by `t − Δ`,
`t ≥ ḡ + 2Δ`, which every honest node at the state at `t` holds or has above its `Σ.F`, is
accepted by every honest node before `t` (`Catch(2Δ)` or acceptance relay, `relay_held`). -/
private theorem relayed (hrun : GoldilocksRun proposer dg H tr) (hsh : HSShared tr H dg g ΔF)
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

/-- The FG projection of a Goldilocks run under the HS shared premises is an FG trace with its
contract (C0.5 (c)). -/
private theorem fg_run (hrun : GoldilocksRun proposer dg H tr) (hsh : HSShared tr H dg g ΔF) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG :=
  Compose.fg_projection _ _ dg H _ tr proposer
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
    hsh.genesisRoot hrun.toLocalRun hsh.noColl

/-- `ḡ + 8Δ < a < t_u` for the reset `a` and a slot `u` from the drain on (`c_z < a`, HR.1 (c)). -/
private theorem reset_lt (hrun : GoldilocksRun proposer dg H tr) (hsh : HSShared tr H dg g ΔF)
    (ha : IsReset tr H g a) {u : Nat} (hR : drainTime sp a ≤ sp.ts u) :
    SA.gbar g + 8 * sp.Δ < a ∧ a < sp.ts u := by
  have h1 := cutZ_lt_reset hrun hsh.healthy ha
  have h2 := lt_cutZ sp g
  have ha0 : 0 ≤ a := by linarith [gbar_nonneg g, sp.toParams.hΔ]
  have h3 : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have h4 : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts u :=
    le_trans ((SA.ts_le_iff sp).2 (by push_cast; omega)) (drainTime_eq (sp := sp) a ▸ hR)
  exact ⟨by linarith, by linarith⟩

/-- A carrier below an actual high origin is held or above the receiver's
finalized cache, using only witnesses within the given horizon. -/
theorem carrier_below_origin_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (Q : Time)
    {z : Fin sp.n} (hz : z ∈ H) {j : Nat} (hjQ : tr.time j ≤ Q)
    {x : Fin sp.n} {i s : Nat} {X O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i s O) (hiQ : tr.time i ≤ Q)
    (hXO : Anc (tr.HonestBlocks H) X O) :
    X ∈ (tr.state z j).fg.tree ∨ Anc (tr.HonestBlocks H) (tr.state z j).fg.F X := by
  have hcmp := finalized_compatible_high_origin_before hp Q hz hjQ ho hiQ
  have hFX : Compatible (tr.HonestBlocks H) (tr.state z j).fg.F X := by
    rcases hcmp with h | h
    · exact Anc.total (honest_coherent hp) h hXO
    · exact Or.inr (hXO.trans h)
  rcases hFX with h | h
  · exact Or.inr h
  · exact Or.inl (mem_tree_of_anc hp hz h
      (Store.cache_invariants _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hz j)).1)

/-- A carrier below a high origin is held or above every honest finalized cache. -/
private theorem carrier_below_origin (hrun : GoldilocksRun proposer dg H tr)
    (hsh : HSShared tr H dg g ΔF) (ha : IsReset tr H g a) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXo : ∃ xo io jo B, HighOrigin tr H g xo io jo B ∧ Anc (tr.HonestBlocks H) X B) {t : Time}
    (_hat : a ≤ t) :
    ∀ z ∈ H, ∀ j, tr.FirstCutFrom j t →
      X ∈ (tr.state z j).fg.tree ∨ Anc (tr.HonestBlocks H) (tr.state z j).fg.F X := by
  intro z hz j _hj
  obtain ⟨xo, io, jo, B, hO, hXB⟩ := hXo
  exact carrier_below_origin_before ⟨hrun, hsh.healthy, hsh.noColl, ha⟩
    (max (tr.time j) (tr.time io)) hz (le_max_left _ _) hO (le_max_right _ _) hXB

/-- **The early carrier is held or above every honest `Σ.F`** (§26 branch (ii), with the T3 paper
orb's high origin): at the state at `t_u + 7Δ` every honest node holds the retained crossing `X`
or has its `Σ.F` below `X`, so acceptance relay reaches it: `X` lies below the block of a high
origin (`carrier_below_origin`). -/
private theorem early_carrier_below (hrun : GoldilocksRun proposer dg H tr)
    (hsh : HSShared tr H dg g ΔF) (ha : IsReset tr H g a) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXo : ∃ xo io jo B, HighOrigin tr H g xo io jo B ∧ tr.time io ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) X B) :
    ∀ z ∈ H, ∀ j, tr.FirstCutFrom j (sp.ts u + 7 * sp.Δ) →
      X ∈ (tr.state z j).fg.tree ∨ Anc (tr.HonestBlocks H) (tr.state z j).fg.F X := by
  obtain ⟨xo, io, jo, B, hO, -, hXB⟩ := hXo
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hau := (reset_lt hrun hsh ha hR).2
  exact carrier_below_origin hrun hsh ha ⟨xo, io, jo, B, hO, hXB⟩ (by linarith)

/-- An honest node is joined at a time `t` of slot `m + 1` with `ḡ ≤ t_m` (no honest restart
after `ḡ`). -/
private theorem joinedAt_of_slot (hsh : HSShared tr H dg g ΔF) {y : Fin sp.n} (hy : y ∈ H)
    {t : Time} {m : Nat} (hm : sp.slot t = m + 1) (hg : SA.gbar g ≤ sp.ts m) :
    tr.JoinedAt y t := by
  intro k hk _
  change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
  rw [hm, Nat.add_sub_cancel, sp.slotTime_eq]
  exact ⟨by omega, (hsh.noRestart y hy k hk).trans hg⟩

/-- **An honest update of slot `s`** with `ḡ ≤ t_s`: the tick of an honest node at `t_s + 6Δ`
(awake under `Healthy(g)`, joined: no honest restart after `ḡ`). -/
private theorem update_exists (hrun : GoldilocksRun proposer dg H tr) (hsh : HSShared tr H dg g ΔF)
    {y : Fin sp.n} (hy : y ∈ H) {s : Nat} (hs : SA.gbar g ≤ sp.ts s) :
    ∃ k ℓ, SA.UpdateAt tr.projAC y k s ℓ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨k, x, hg⟩ := hrun.tick_of_awake y hy (sp.ts s + 6 * sp.Δ)
    (by linarith [gbar_nonneg g]) ⟨4 * (s : Int) + 6, by simp only [SA.SAParams.ts]; ring⟩
    (hsh.healthy.2.1 y hy _ (by change SA.gbar g ≤ _; linarith))
  obtain ⟨hc, ht⟩ := tick_first_cut hg
  obtain ⟨ℓ, hl, hcall⟩ : ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.label k = some (.ac ℓ) ∧ ℓ.call = .tick := ⟨_, hc.2, rfl⟩
  have hnr : ¬ tr.RestartAt y k := by
    rintro ⟨ℓ', ⟨-, hl'⟩, hr'⟩
    have h := hl'.symm.trans hl
    injection h with h
    injection h with h
    rw [h, hcall] at hr'
    cases hr'
  have hslot : sp.slot (sp.ts s + 6 * sp.Δ) = s + 1 :=
    SA.slot_of_mem sp (s + 1) (by simp only [SA.SAParams.ts]; push_cast; linarith)
      (by simp only [SA.SAParams.ts]; push_cast; linarith)
  have htk : tr.projAC.time k = sp.ts s + 6 * sp.Δ := ht
  refine ⟨k, ℓ, Compose.projAC_callAt.2 ⟨hc.1, hl⟩, hcall, htk, ?_⟩
  rw [Compose.projAC_state hrun.toLocalRun hy k, htk]
  exact ((Compose.joined_projection sp ro dg H tr proposer hrun y hy _).2.1 k ⟨_, hc⟩ hnr ht).1
    (joinedAt_of_slot hsh hy hslot hs)

/-- **A high origin below the window's carrier** (from the reset): the reset row (height
`H_z + 1`, signed at `a`) has a high source below the stored block `O` of a high origin of label
`l` with `t_l ≤ a < t_{W.slot}` (`high_row_source`); by HR.4 (R3) every honest vote of slot
`W.slot` extends `O`, and by unanimity (`ready_unanimous`) such a vote, the proposer's own (awake
and joined at `t_{W.slot} + Δ`), is `W`. -/
private theorem reset_origin_below (hp : ResetPremises tr H proposer dg g ΔF a)
    (hsh : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hWP : ReadyProposal tr H proposer w kw W.slot W)
    (hRW : drainTime sp a ≤ sp.ts W.slot) (hga : SA.gbar g + 8 * sp.Δ < a)
    (haW : a < sp.ts W.slot) (hWU : W ∈ tr.HonestBlocks H) :
    ∃ x r l O, HighOrigin tr H g x r l O ∧ Anc (tr.HonestBlocks H) O W := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨⟨y, hy, k, att, hs, hh, hk⟩, -⟩ := hp.reset
  obtain ⟨r, hrk, l, O, hO, -⟩ := high_row_source hp hy hs hh.ge
  -- the origin's label is before `W.slot`
  have hlr : sp.ts l ≤ tr.time r := by
    obtain ⟨CV, ℓw, D, hcw, hfl, -⟩ := hO.2.2.1
    rcases hfl with ⟨ℓ', C, hu, -⟩ | ⟨ℓ', A, -, hsl, -⟩
    · have h : tr.time r = sp.ts l + 6 * sp.Δ := hu.2.2.1
      linarith
    · have h : sp.slot (tr.time r) = l := hsl
      exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) l).2 (by omega)
  have hl : l < W.slot := by
    have := hp.run.time_mono hrk.le
    exact_mod_cast (SA.ts_lt_iff sp).1 (show sp.ts l < sp.ts W.slot by linarith)
  -- the proposer's slot-`W.slot` vote is `W`, and it extends `O`
  have hwH := hWP.1
  obtain ⟨m, hm⟩ : ∃ m, W.slot = m + 1 := ⟨W.slot - 1, by omega⟩
  have hmW : sp.ts W.slot = sp.ts m + 4 * sp.Δ := by
    rw [hm]; simp only [SA.SAParams.ts]; push_cast; ring
  have hslot : sp.slot (sp.ts W.slot + sp.Δ) = m + 1 := by
    rw [← hm]
    exact SA.slot_of_mem sp W.slot (by linarith)
      (by simp only [SA.SAParams.ts]; push_cast; linarith)
  obtain ⟨kv, e, hv, hes, -⟩ := Compose.vote_of_awake_joined hp.run hp.noColl hwH
    (hp.healthy.2.1 w hwH _ (by change SA.gbar g ≤ _; linarith))
    (joinedAt_of_slot hsh hwH hslot (by linarith))
  have hhead := ready_unanimous hp hc hWP hRW w hwH kv e hv hes
  obtain ⟨ℓv, hcv, hev⟩ := hv
  obtain ⟨⟨Hd, hHd, hHdr, hOHd⟩, -⟩ := (height_scoped_retention sp ro proposer dg H tr g ΔF hp.run
    hp.healthy hp.noColl a hp.reset).votes y r l O hO w hwH kv ℓv e ⟨hcv, hev⟩ (by omega)
  obtain rfl : Hd = W := (honest_coherent hp).1 hHd hWU (hHdr.trans hhead)
  exact ⟨y, r, l, O, hO, hOHd⟩

/-- **The update keeps its write or has a covering source** (phase-service §10–§11):
the ready proposal is a `viable_ancestor` candidate at its update, or an actual high origin
extends it. The raw result and unanimity suffice; the existing no-veto, fast-selection and
returned-source premises are retained for callers. -/
private theorem update_window_kept (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hWP : ReadyProposal tr H proposer w kw W.slot W)
    (hRW : drainTime sp a ≤ sp.ts W.slot) {z : Fin sp.n} (hz : z ∈ H) {kz : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC z kz W.slot ℓ)
    (hconf : SA.getConfirmation sp (tr.projAC.state z kz) ℓ.frame W.slot = some W)
    (_hnv : ¬ SA.conflictsWithLock sp (tr.projAC.state z kz).locks ℓ.frame (tr.time kz) W)
    (_hfs : SA.fastSelect sp (tr.projAC.state z kz) ℓ.frame W.slot W = some W)
    (_hsrc : ∀ k' ℓ' C, kz ≤ k' → SA.ToFGAt tr.projAC z k' ℓ' C → tr.time k' = tr.time kz →
      Anc (tr.HonestBlocks H) W C) :
    (W ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc W ℓ.frame.fcRoot) ∨
      ∃ xo io jo B, HighOrigin tr H g xo io jo B ∧ Anc (tr.HonestBlocks H) W B := by
  have hlate : cleanLabel sp a + 2 * sp.k + 1 ≤ W.slot := by
    rw [drainTime_eq] at hRW
    have := (SA.ts_le_iff sp).mp hRW
    rw [cleanLabel_eq]; omega
  rcases unanimous_result_candidate_or_high_origin hp hc hz hu hconf hlate
    (ready_unanimous hp hc hWP hRW)
    with hcand | ⟨x, r, b, B, _, ho, hWB⟩
  · exact Or.inl hcand.symm
  · exact Or.inr ⟨x, r, b, B, ho, hWB⟩

/-- A higher report above the window's proposal has a high origin at the same
reporter, strictly before the report. Retain its cut and time for bounded consumers. -/
theorem higher_report_window_origin_before (hp : ResetPremises tr H proposer dg g ΔF a)
    (hsh : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hWP : ReadyProposal tr H proposer w kw W.slot W)
    (hRW : drainTime sp a ≤ sp.ts W.slot) (hga : SA.gbar g + 8 * sp.Δ < a)
    (haW : a < sp.ts W.slot) {z : Fin sp.n} (hz : z ∈ H) {r : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ℓ C) (hWC : Anc (tr.HonestBlocks H) W C)
    (hhC : ((tr.state z r).fg.σ W.root).h < ((tr.state z r).fg.σ C.root).h) :
    ∃ io < r, ∃ jo B, HighOrigin tr H g z io jo B ∧ tr.time io ≤ tr.time r ∧
      Anc (tr.HonestBlocks H) C B ∧ Anc (tr.HonestBlocks H) W B := by
  have hCt := report_mem hp.run hz hrep
  have hWt := mem_of_honest_anc hp.run hp.noColl hz hWC hCt
  obtain ⟨x, k, l, O, hO, hOW⟩ :=
    reset_origin_below hp hsh hc hWP hRW hga haW ⟨z, hz, r, hWt⟩
  have hWh := high_of_anc hp hO hz hWt hOW
  obtain ⟨io, hio, jo, B, hB, hCB⟩ := high_report_origin hp hz hrep (by omega)
  exact ⟨io, hio, jo, B, hB, hp.run.time_mono hio.le, hCB, hWC.trans hCB⟩

/-- **A higher report above the window's proposal lies below a high origin above `W`**
(`ready_update`'s second case): `W` is high (`reset_origin_below`), so the report `C ⪰ W`, higher
than `W` in the reporter's state, is high; its stored origin (`high_report_origin`) is above `C`,
hence above `W`. -/
private theorem higher_report_window_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    (hsh : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) {w : Fin sp.n} {kw : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hWP : ReadyProposal tr H proposer w kw W.slot W)
    (hRW : drainTime sp a ≤ sp.ts W.slot) (hga : SA.gbar g + 8 * sp.Δ < a)
    (haW : a < sp.ts W.slot) {z' : Fin sp.n} (hz' : z' ∈ H) {r : Nat}
    {ℓ' : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z' r ℓ' C) (hWC : Anc (tr.HonestBlocks H) W C)
    (hhC : ((tr.state z' r).fg.σ W.root).h < ((tr.state z' r).fg.σ C.root).h) :
    ∃ xo io jo B, HighOrigin tr H g xo io jo B ∧ Anc (tr.HonestBlocks H) W B := by
  obtain ⟨io, _, jo, B, hB, _, _, hWB⟩ :=
    higher_report_window_origin_before hp hsh hc hWP hRW hga haW hz' hrep hWC hhC
  exact ⟨z', io, jo, B, hB, hWB⟩

/-- **A high origin above the window's carrier** (the T3 paper orb's route): the proposer's
update of slot `W.slot` at `t_{W.slot} + 6Δ` (`ready_update`) writes a fast lock on `W`, stored on
`W` itself (`update_window_kept`), a high origin: `W` is above the reset's origin
(`reset_origin_below`), so it is high; or a higher source or a crossing intervened, below a high
origin above `W` (`update_window_kept`, `higher_report_window_origin`). -/
private theorem window_origin (hrun : GoldilocksRun proposer dg H tr) (hsh : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (ha : IsReset tr H g a) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) {w : Fin sp.n} {kw : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hWP : ReadyProposal tr H proposer w kw W.slot W)
    (hWs : u ≤ W.slot) :
    ∃ xo io jo B, HighOrigin tr H g xo io jo B ∧ Anc (tr.HonestBlocks H) W B := by
  have hp : ResetPremises tr H proposer dg g ΔF a := ⟨hrun, hsh.healthy, hsh.noColl, ha⟩
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hga, hau⟩ := reset_lt hrun hsh ha hR
  have huW : sp.ts u ≤ sp.ts W.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast hWs)
  have hRW : drainTime sp a ≤ sp.ts W.slot := hR.trans huW
  have hwH := hWP.1
  obtain ⟨kz, ℓ, hu⟩ := update_exists hrun hsh hwH (s := W.slot) (by linarith)
  rcases ready_update hp hc hWP hRW hwH hu with ⟨hconf, hnv, hfs, hsrc⟩ |
    ⟨z', hz', r, ℓ', C, hrep, -, hWC, hhC⟩
  · rcases update_window_kept hp hc hWP hRW hwH hu hconf hnv hfs hsrc with hcand | ho
    · have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hsh.noColl).localRun
      have hWfr : W ∈ ℓ.frame.tree := (SA.deepest_mem hfs).1.1.1
      have hWt := frame_tree_subset hp hwH hu.1 hWfr
      have hfl : SA.FastLockAt tr.projAC w kz W.slot W
          (SA.fastCounted sp (tr.projAC.state w kz) ℓ.frame W.slot W) :=
        Or.inl ⟨ℓ, W, hu, hconf, hnv, hfs, rfl⟩
      obtain ⟨x, r, l, O, hO, hOW⟩ :=
        reset_origin_below hp hsh hc hWP hRW hga (by linarith) ⟨w, hwH, kz, hWt⟩
      have hWo : HighOrigin tr H g w kz W.slot W := by
        unfold HighOrigin Compose.StoredFastLockAt
        exact ⟨hwH, joinedAt_of_fastLockAt hrun hsh.noColl hwH hfl,
          ⟨_, ℓ, W, hu.1, hfl, (SA.viableAncestor_self (SA.frameIn_of_callAt hr hwH hu.1).1 hWfr
            hcand).symm⟩, high_of_anc hp hO hwH hWt hOW⟩
      exact ⟨w, kz, W.slot, W, hWo, .refl⟩
    · exact ho
  · exact higher_report_window_origin hp hsh hc hWP hRW hga (by linarith) hz' hrep hWC hhC

/-- **The window's carrier is held or above every honest `Σ.F`** (§26, "the carrier is relayed
within `Δ`", by the T3 paper orb's high-origin route): at the state at `t_{W.slot} + Δ` every
honest node holds the window's honest ready proposal `W` or has its `Σ.F` below `W`, so
acceptance relay reaches it: `W` lies below a high origin (`window_origin`), and
`carrier_below_origin` applies. -/
private theorem window_carrier_below (hrun : GoldilocksRun proposer dg H tr)
    (hsh : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (ha : IsReset tr H g a)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u) {w : Fin sp.n} {kw : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hWP : ReadyProposal tr H proposer w kw W.slot W)
    (hWs : u ≤ W.slot) :
    ∀ z ∈ H, ∀ j, tr.FirstCutFrom j (sp.ts W.slot + sp.Δ) →
      W ∈ (tr.state z j).fg.tree ∨ Anc (tr.HonestBlocks H) (tr.state z j).fg.F W := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hau := (reset_lt hrun hsh ha hR).2
  have huW : sp.ts u ≤ sp.ts W.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast hWs)
  exact carrier_below_origin hrun hsh ha (window_origin hrun hsh hc ha hR hWP hWs) (by linarith)

/-- **The outcome from the rows** (§26): with the window's honest ready proposal whose parent
extends `T`, the rows (or the retained crossing) give C1.2's conclusion: the literal good window
or the early outcome, with the carrier relayed, and at an unbound entry a justification by the
window's end. -/
theorem outcome_of_rows (hrun : GoldilocksRun proposer dg H tr) (hsh : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (_hpp : PropPlus tr H proposer g Gp)
    (hcF₁ : 4 * sp.Δ * ((cF : Time) - 1) < 6 * sp.Δ + ΔF)
    (hcF₂ : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (cF : Time)) (hδ : cF + kF ≤ sp.toParams.δt)
    (ha : IsReset tr H g a) {p y : Fin sp.n} {k i u : Nat}
    {T : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u T)
    (hE : Compose.RunEntry tr H y i T) (hR : drainTime sp a ≤ sp.ts u)
    (hW : ∃ (w : Fin sp.n) (kw : Nat) (W : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H proposer w kw W.slot W ∧ u + cF ≤ W.slot ∧ W.slot ≤ u + cF + kF ∧
      ∃ Pr, W.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) T Pr)
    (hrows : EntryRows tr H g T ((tr.post i).fg.σ T.root).h ((tr.post i).fg.σ T.root).hj
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
  have hfg := fg_run hrun hsh
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
    have := reset_lt hrun hsh ha hR
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
  rcases hrows with ⟨R, hRq, hRr⟩ | ⟨x, hx, kx, X, hXacc, hXt, hXJ, hXb, hXo⟩
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
        (early_carrier_below hrun hsh ha hR hXo z hz)
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
      (window_carrier_below hrun hsh hc ha hR hWP (by omega) z hz)
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
  intro sp ro proposer dg H tr g ΔF Gp a cF kF hrun hsh hc hpp hcF₁ hcF₂ hδ ha
    p k i T u hP hE hu hh hhj
    hW
  have hR : drainTime sp a ≤ sp.ts u := by rw [drainTime_eq]; exact hu
  exact outcome_of_rows hrun hsh hc hpp hcF₁ hcF₂ hδ ha hP hE hR hW
    (entry_rows hrun hsh hc hcF₂ hδ ha hP hE hR hh hhj)

/-- Catch before GST and acceptance relay after GST give Catch at the actual reset,
without awake or service obligations beyond the finite observation horizon. -/
theorem catch_window_at_reset_of_reset_catch_before {b t : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) (htb : t ≤ b) :
    CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t := by
  have hca := cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have hga : SA.gbar g < a := by linarith [lt_cutZ sp g, sp.toParams.hΔ]
  have hra : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ a := by
    apply le_trans _ hca.le
    rw [cutZ_eq]
    exact (SA.ts_le_iff sp).mpr (by omega)
  constructor
  intro x hx i B ha hi y hy j ell hj ht hjt hF
  change a + 2 * sp.Δ ≤ tr.time j at ht
  change tr.time j ≤ t at hjt
  by_cases hgi : tr.projAC.time i < SA.gbar g
  · obtain ⟨k, hk, hak, hkt⟩ := projection_catch_of_run hp.run hc x hx i B ha hgi
      y hy j ell hj (by change SA.gbar g + 2 * sp.Δ ≤ tr.time j; linarith) hF
    exact ⟨k, hk, hak, by linarith⟩
  · obtain ⟨i', rfl, ha', hti⟩ := fg_accept_before hp.run.toLocalRun hx ha
    change tr.time (i' + 1) < a at hi
    change ¬ tr.time (i' + 1) < SA.gbar g at hgi
    have hia : tr.time i' < a := by simpa only [hti] using hi
    have hgg : g ≤ tr.time i' := (SA.le_gbar g).trans (by
      simpa only [hti] using le_of_not_gt hgi)
    have hmax : max (tr.time i') g = tr.time i' := max_eq_left hgg
    have hdeadline : ∀ k ≤ j, tr.deadline y k (tr.time i') sp.Δ ≤ a + sp.Δ := by
      intro k hkj
      apply le_trans (Compose.deadline_le_of_restarts (a := a) (fun r hr hrest =>
        (restart_le_before hp hy hrest
          ((hp.run.time_mono (hr.trans hkj)).trans (hjt.trans htb))).trans hra) _ _)
      rw [max_eq_right hia.le]
    obtain ⟨k, hk, hak, hkt⟩ := hp.sync.relay x hx i' B ha' hgg y hy j
      ⟨_, Compose.projAC_callAt.mp hj⟩ (by
        rw [hmax]
        exact (hdeadline j le_rfl).trans (by linarith [sp.toParams.hΔ]))
      (by rwa [Compose.frame_of_projAC hp.run hy hj] at hF)
    obtain ⟨hak', htk, -⟩ := ac_block_after hp.run.toLocalRun hy hak
    have hkj : k < j := by
      rcases hk.lt_or_eq with hk | rfl
      · exact hk
      · exact absurd (hak.2.symm.trans (Compose.projAC_callAt.mp hj).2) (by simp)
    refine ⟨k + 1, hkj, hak', ?_⟩
    change tr.time (k + 1) < a + 2 * sp.Δ
    rw [htk]
    rw [hmax] at hkt
    exact lt_of_lt_of_le hkt ((hdeadline k hk).trans (by linarith [sp.toParams.hΔ]))

/-- Finite reset service supplies AC synchrony from the actual reset, retaining the
recipient deadline cutoff and strict processing deadlines. -/
theorem sync_window_at_reset_of_reset_before {b t : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (htb : t ≤ b) :
    SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC := by
  have hca := cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have hga : g ≤ a := by
    have := SA.le_gbar g
    have := lt_cutZ sp g
    linarith [sp.toParams.hΔ]
  have hs := hp.sync.syncAC (hi := b) hp.run hga
  have hsource : ∀ y j (u : Time), u ≤ tr.projAC.deadline y j u := by
    intro y j u
    unfold ACTrace.deadline
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    cases tr.projAC.lastWake y j with
    | bot => change u ≤ u + sp.Δ; linarith
    | coe w =>
      change u ≤ max u w + sp.Δ
      have := le_max_left u w
      linarith
  constructor
  · intro x hx i m hm hi y hy j ell hj ht hd
    exact hs.1 x hx i m hm hi ((hsource y j _).trans (ht.trans htb))
      y hy j ell hj hd
  · intro x hx i B hB hi y hy j ell hj ht hd hF
    exact hs.2 x hx i B hB hi ((hsource y j _).trans (ht.trans htb))
      y hy j ell hj hd hF

end Consensus.Goldilocks.Healing

end
