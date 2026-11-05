module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Phase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the facts of HS.0 (bounded settling)

HS.0 (`Settle(Δ)`, claims §"Healing: phase service") is assembled in
`Reset.lean` (`settle`) from these facts:

* **Strict-height finality at the stores** (G1.2, `finalized_anc`): with `f < 2q − n`, an honest
  `Σ.F` is an ancestor of every honest held block whose state height is at least that node's
  `Σ.h_max` (the finalized height is `< h_max`; a chain of greater height crossed it, and the
  finality and crossing quorums meet in an honest validator with an E1 pair).
* **The evidence of a phase** (`holdsEvidence_of_relay`): if every honest held block of state
  height `m` at cut `i` is held by `y` at `i'`, then `y` holds the defining evidence of the phase
  `(m, c)` at `i` there (a justifying block of `J` at `m − 1` has state height `m`, and `J` is its
  ancestor; a contest witness has height `m`).
* **Acceptance relay to the state at `w`** (`relay_held`): under `Healthy(g)`, no honest restart
  after `ḡ` and `Catch(κ)`, a block an honest node accepted at `τ` with `τ + Δ ≤ w`,
  `ḡ + κ ≤ w`, is held at the state at `w` by every honest node whose `Σ.F` there it extends
  (pre-`ḡ` acceptances by `Catch(κ)` read at `w`, `catchRun_at`; later ones by acceptance relay,
  read at the node's first call from `w`, whose `Σ.F` is the one at `w`).
* **Joined** (`joined_late`): no honest restart after `ḡ` makes every honest node joined from
  `ḡ + 8Δ` on.

G1.2 at the chain level is `FG.FGParams.finalization_meets_crossing`
(`Lemmas/FGChain/Accountable`). -/

namespace Consensus.Goldilocks.Healing

open Store
open SA (gbar)

/-! ## Stores: strict-height finality and the evidence of a phase -/

section Stores

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- A held block of an honest store has a chain whose fold is its state, each of whose roots
names a held ancestor, and each of whose attestations with an honest signer was signed before
the cut. -/
private theorem held_chain (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) :
    ∃ c : List (NodeBlock P ACP),
      P.fg.chainState (c.map Block.fgView) = some ((tr.store y i).σ B.root) ∧
      (∀ r ∈ P.fg.roots (c.map Block.fgView),
        ∃ Y ∈ (tr.store y i).tree, Y.root = r ∧ (tr.store y i).Anc Y B) ∧
      ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), a.val ∈ H → ∃ k < i, tr.SignAt a.val k a := by
  have hR := store_reachable hr hy i
  obtain ⟨c, hc, hl, hlast, hσ⟩ := chain_state_of_chain P ACP acp₀ _ hR B hB
  obtain ⟨-, -, hg, -⟩ := accepted_tree P ACP acp₀ _ hR
  have hanc := Store.anc_of_linked c _ hg hc hl B (by
    rcases hlast with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  refine ⟨c, hσ, fun r hr' => ?_, fun a ha hav => ?_⟩
  · obtain ⟨Y, hY, hYr⟩ : ∃ Y ∈ P.genesisBlock acp₀ :: c, Y.root = r := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hr'
    refine ⟨Y, ?_, hYr, hanc Y hY⟩
    rcases List.mem_cons.1 hY with rfl | h
    exacts [hg, hc _ h]
  · obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
    obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
    rcases tree_accepted hr hy (hc X hXc) with rfl | ⟨k, hk, hacc⟩
    · cases haX
    · obtain ⟨k', hk', hs⟩ := hr.unforgeable y hy k a ⟨_, hacc, haX⟩ hav
      exact ⟨k', by omega, hs⟩

/-- **G1.2 at the stores (strict height).** With `f < 2q − n`, the finalized tip of an honest
node is an ancestor of every block an honest node holds whose state height is at least the first
node's `Σ.h_max`: its finalized height `h_F` is below the height of the state that finalizes it,
so below that block's height, and a chain of greater height without it would meet its finality
quorum in an honest validator with an E1 pair (G1.2, G0.5). -/
theorem finalized_anc (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y z : Fin P.n} (hy : y ∈ H) (hz : z ∈ H) {i j : Nat} {B : NodeBlock P ACP}
    (hB : B ∈ (tr.store z j).tree) (hle : (tr.store y i).hmax ≤ ((tr.store z j).σ B.root).h) :
    (tr.store z j).Anc (tr.store y i).F B := by
  obtain ⟨hF, -, -, -, hge, -, X, hX, hXF⟩ :=
    cache_invariants P ACP acp₀ _ (store_reachable hr hy i)
  obtain ⟨c₁, h₁, -, ha₁⟩ := held_chain hr hy hX
  obtain ⟨c₂, h₂, hr₂, ha₂⟩ := held_chain hr hz hB
  obtain ⟨-, hFj, hjh, -, hF0, -⟩ := FG.chain_invariants P.fg _ _ h₁
  have hXh := hge X hX
  suffices hmem : (tr.store y i).F.root ∈ P.fg.roots (c₂.map Block.fgView) by
    obtain ⟨Y, hY, hYr, hYB⟩ := hr₂ _ hmem
    rwa [hr.coherent.1 (hr.tree_subset z hz j hY) (hr.tree_subset y hy i hF) hYr] at hYB
  rw [← hXF]
  rcases Nat.eq_zero_or_pos ((tr.store y i).σ X.root).hF with h0 | h0
  · rw [hF0 h0]
    exact List.mem_cons_self
  by_contra hnot
  obtain ⟨S, hS, hSv⟩ := P.fg.finalization_meets_crossing h₁ h₂ h0 (by omega) hnot
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H := by
    by_contra! hS'
    have := Set.ncard_le_ncard (s := (S : Set (Fin P.fg.n))) (t := Hᶜ) hS'
    rw [Set.ncard_coe_finset] at this
    have : (Hᶜ : Set (Fin P.fg.n)).ncard = (Hᶜ : Set (Fin P.n)).ncard := rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  obtain ⟨inputs, hin, hrun⟩ := signed_run hr hv (i + j)
  obtain ⟨k, hk, hka⟩ := ha₁ a ha hv
  obtain ⟨k', hk', hkb⟩ := ha₂ b hb (hab.1 ▸ hv)
  rw [← hab.1] at hkb
  exact FG.client_safety P.fg a.val inputs hin a (hrun k (by omega) a hka) b
    (hrun k' (by omega) b hkb) hab

/-- Ancestors of a held block are held. -/
theorem mem_of_anc {st : Store P ACP} {A B : NodeBlock P ACP} (h : st.Anc A B)
    (hB : B ∈ st.tree) : A ∈ st.tree := by
  induction h with
  | refl => exact hB
  | tail _ hp ih => exact ih hp.1

/-- The phase at a cut has the frontier there. -/
theorem PhaseAt.frontierAt {i m : Nat} {c : PhaseCase (NodeBlock P ACP)}
    (h : PhaseAt tr H i m c) : FrontierAt tr H i m := by
  cases c <;> exact h.1

/-- With `f < 2q − n`, the phase at a cut is unique. -/
theorem phaseAt_eq (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {i m m' : Nat} {c c' : PhaseCase (NodeBlock P ACP)} (h : PhaseAt tr H i m c)
    (h' : PhaseAt tr H i m' c') : m = m' ∧ c = c' := by
  obtain ⟨⟨y, hy, hm⟩, hle⟩ := h.frontierAt
  obtain ⟨⟨y', hy', hm'⟩, hle'⟩ := h'.frontierAt
  obtain rfl : m = m' := by
    have := hle' y hy
    have := hle y' hy'
    omega
  exact ⟨rfl, phaseAt_unique hr hH h h'⟩

/-- **The evidence of a phase**: if `y` holds at cut `i'` every block of
state height `m` that an honest node holds at cut `i`, then it holds the defining evidence of
the effective phase `(m, c)` at `i`: a block of height `m`; for a top `J` or a contest, a block
justifying `J` at `m − 1`, which has state height `m` (`h_j < h ≤ m`), and `J`, its ancestor;
for a contest, its witness, of height `m`, which does not extend `J` at `y` either. -/
theorem holdsEvidence_of_relay (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {i i' m : Nat} {c : PhaseCase (NodeBlock P ACP)} (hc : PhaseAt tr H i m c)
    (hrel : ∀ x ∈ H, ∀ B ∈ (tr.store x i).tree, ((tr.store x i).σ B.root).h = m →
      B ∈ (tr.store y i').tree) :
    HoldsEvidence (tr.store y i') m c := by
  have hf := hc.frontierAt
  have hfr : ∃ B ∈ (tr.store y i').tree, ((tr.store y i').σ B.root).h = m := by
    obtain ⟨x, hx, hxm⟩ := hf.1
    obtain ⟨-, -, -, -, -, ⟨B, hB, hBh⟩, -⟩ :=
      cache_invariants P ACP acp₀ _ (store_reachable hr hx i)
    have hBy := hrel x hx B hB (hBh.trans hxm)
    exact ⟨B, hBy, by rw [σ_eq_of_held hr hy hx hBy hB, hBh, hxm]⟩
  have hjust : ∀ J, JustifiedAt tr H i (m - 1) J → J ∈ (tr.store y i').tree ∧
      ∃ B ∈ (tr.store y i').tree, ((tr.store y i').σ B.root).hj = m - 1 ∧
        ((tr.store y i').σ B.root).J = J.root := by
    rintro J ⟨x, hx, hJ, B, hB, hBj, hBJ⟩
    have hRx := store_reachable hr hx i
    obtain ⟨c, -, -, -, hσ⟩ := chain_state_of_chain P ACP acp₀ _ hRx B hB
    obtain ⟨h1, -, hjh, -⟩ := FG.chain_invariants P.fg _ _ hσ
    have hBh : ((tr.store x i).σ B.root).h = m := by
      have := (cache_invariants P ACP acp₀ _ hRx).2.2.2.2.1 B hB
      have := hf.2 x hx
      omega
    have hBy := hrel x hx B hB hBh
    obtain ⟨-, -, X, hX, hXr, hXB⟩ := entry_state_of_source P ACP acp₀ _ hRx B hB
    obtain rfl : X = J := hr.coherent.1 (hr.tree_subset x hx i hX) (hr.tree_subset x hx i hJ)
      (hXr.trans hBJ)
    have hσ := σ_eq_of_held hr hy hx hBy hB
    exact ⟨mem_of_anc (Store.anc_transfer hr hx hy hXB hBy) hBy, B, hBy, by rw [hσ]; exact hBj,
      by rw [hσ]; exact hBJ⟩
  have hcont : ∀ J, ContestAt tr H i m J → ∃ B ∈ (tr.store y i').tree,
      ((tr.store y i').σ B.root).h = m ∧ ¬ (tr.store y i').Anc J B := by
    rintro J ⟨x, hx, B, hB, hBh, hn⟩
    have hBy := hrel x hx B hB hBh
    exact ⟨B, hBy, by rw [σ_eq_of_held hr hy hx hBy hB]; exact hBh,
      fun ha => hn (Store.anc_transfer hr hy hx ha hB)⟩
  cases c with
  | gap => exact hfr
  | top J => exact ⟨hfr, hjust J hc.2.1⟩
  | contest J =>
    obtain ⟨h1, h2⟩ := hjust J hc.2.1
    exact ⟨hfr, h1, h2, hcont J hc.2.2⟩

end Stores

/-! ## Runs: relay to the state at a time, and joining -/

section Runs

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}
  {proposer : Nat → Fin P.n}

/-- The latest wake is the time of a restart. -/
private theorem lastWake_eq {y : Fin P.n} :
    ∀ {k : Nat} {w : Time}, tr.lastWake y k = (w : WithBot Time) →
      ∃ k' ≤ k, tr.RestartAt y k' ∧ tr.time k' = w
  | 0, w, h => by
    simp only [RunTrace.lastWake] at h
    split_ifs at h with hr
    · exact ⟨0, le_rfl, hr, WithBot.coe_injective h⟩
    · simp at h
  | k + 1, w, h => by
    simp only [RunTrace.lastWake] at h
    split_ifs at h with hr
    · exact ⟨k + 1, le_rfl, hr, WithBot.coe_injective h⟩
    · obtain ⟨k', hk', h1, h2⟩ := lastWake_eq h
      exact ⟨k', by omega, h1, h2⟩

/-- With every restart of `y` at or before `t₀ ≤ τ`, the deadline of an object of time `τ` at
`y` is `τ + Δ'`. -/
private theorem deadline_eq {y : Fin P.n} {t₀ τ Δ' : Time}
    (hnr : ∀ k, tr.RestartAt y k → tr.time k ≤ t₀) (hτ : t₀ ≤ τ) (k : Nat) :
    tr.deadline y k τ Δ' = τ + Δ' := by
  simp only [RunTrace.deadline]
  rcases hw : tr.lastWake y k with _ | w
  · rfl
  · obtain ⟨k', -, hk', rfl⟩ := lastWake_eq hw
    simp [max_eq_left ((hnr k' hk').trans hτ)]

/-- The state of `y` does not change over cuts without a call of `y`. -/
private theorem state_eq_of_noCall {y : Fin P.n} {j j₂ : Nat} (hle : j ≤ j₂)
    (h : ∀ k, j ≤ k → k < j₂ → ¬ tr.IsCall y k) : tr.state y j₂ = tr.state y j := by
  induction j₂, hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [tr.state_succ_of_not fun c hc => h n hn (by omega) ⟨c, hc⟩,
      ih fun k hk hk' => h k hk (by omega)]

/-- An honest node holds a block after the cut at which it accepts it. -/
private theorem accept_mem (hrun : Node.LocalRun proposer dg H sg tr) {y : Fin P.n} (hy : y ∈ H)
    {k : Nat} {B : A.Blk} (h : tr.AcceptAt y k B) : B ∈ (tr.state y (k + 1)).fg.tree := by
  rw [tr.state_succ_of_call h,
    (Store.tree_grows P _ _ _ (Compose.fg_reachable hrun hy k)).1 B _ (hrun.cutLaw y hy k _ h).2.1]
  exact Set.mem_insert _ _

/-- A cut at or after `t` gives a first cut from `t`, at or before it. -/
theorem exists_firstCutFrom_le {t : Time} {j : Nat} (hj : t ≤ tr.time j) :
    ∃ j₁, tr.FirstCutFrom j₁ t ∧ j₁ ≤ j := by
  classical
  have hex : ∃ k, t ≤ tr.time k := ⟨j, hj⟩
  exact ⟨Nat.find hex, ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩,
    Nat.find_min' hex hj⟩

/-- **`Catch(κ)` read at a later time** `w ≥ ḡ + κ`: `Σ.F` only grows, so a block that extends
`Σ.F` at `w` extends it at `ḡ + κ`, and was accepted before then. -/
theorem catchRun_at {g κ : Time} (hc : CatchRun tr H g κ)
    (hrun : Node.LocalRun proposer dg H sg tr)
    {w : Time} (hw : gbar g + κ ≤ w) :
    ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → tr.time i < gbar g →
      ∀ y ∈ H, ∀ j, tr.FirstCutFrom j w → Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
        ∃ k < j, tr.AcceptAt y k B := by
  intro x hx i B hacc hi y hy j hj hF
  obtain ⟨j₁, hj₁, hle⟩ := exists_firstCutFrom_le (hw.trans hj.1)
  obtain ⟨k, hk, hacc'⟩ := hc x hx i B hacc hi y hy j₁ hj₁ ((run_F_mono hrun hy hle).trans hF)
  exact ⟨k, by omega, hacc'⟩

/-- **Acceptance relay to the state at `w`** (`Healthy(g)`, no honest restart after `ḡ`,
`Catch(κ)`): a block an honest `x` accepted at a time `τ` with `τ + Δ ≤ w` and `ḡ + κ ≤ w` is
held at the state at `w` of every honest `y` whose `Σ.F` there it extends. An acceptance before
`ḡ` is caught up by `ḡ + κ` (`catchRun_at`); a later one is relayed before `τ + Δ` (the deadline
`max(τ, w_y) + Δ` with `w_y ≤ ḡ ≤ τ`), read at the first call of `y` from `w` on, before which
`y`'s state, and so its `Σ.F`, is the one at `w`. -/
theorem relay_held {ΔF g κ : Time} (hrun : Node.LocalRun proposer dg H sg tr)
    (hh : tr.HealthyRun H ΔF g) (hnr : NoRestartAfter tr H (gbar g)) (hc : CatchRun tr H g κ)
    {x y : Fin P.n} (hx : x ∈ H) (hy : y ∈ H) {k₀ : Nat} {B : A.Blk} (hacc : tr.AcceptAt x k₀ B)
    {w : Time} (hκ : gbar g + κ ≤ w) (hk₀ : tr.time k₀ + P.Δ ≤ w) {j : Nat}
    (hj : tr.FirstCutFrom j w) (hF : Anc (tr.HonestBlocks H) (tr.state y j).fg.F B) :
    B ∈ (tr.state y j).fg.tree := by
  classical
  suffices ∃ k < j, tr.AcceptAt y k B by
    obtain ⟨k, hk, hak⟩ := this
    exact Compose.tree_mono hrun hy hk (accept_mem hrun hy hak)
  by_cases hτ : tr.time k₀ < gbar g
  · exact catchRun_at hc hrun hκ x hx k₀ B hacc hτ y hy j hj hF
  push Not at hτ
  have hΔ := P.hΔ
  have ht0 := hrun.time_nonneg j
  have hlt : tr.time j + 1 ≤ P.Δ * (tr.time j + 1) :=
    le_mul_of_one_le_left (by linarith) (show (1 : Int) ≤ P.Δ by
      have : (0 : Int) < P.Δ := hΔ
      omega)
  -- the first call of `y` at or after `j`
  obtain ⟨i, xx, hg⟩ := hrun.tick_of_awake y hy (P.Δ * (tr.time j + 1)) (by linarith)
    ⟨_, rfl⟩ (hh.2.1 y hy _ (by change gbar g ≤ _; linarith [hj.1]))
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 0 (List.length_pos_of_ne_nil hg.1)
  simp only [Nat.add_zero] at hn ht hl
  have hji : j ≤ i := by
    by_contra h
    have := hrun.time_mono (not_le.1 h).le
    linarith
  have hex : ∃ j₂, j ≤ j₂ ∧ tr.IsCall y j₂ := ⟨i, hji, _, hn, hl⟩
  obtain ⟨hj₂, hcall⟩ := Nat.find_spec hex
  have hst : tr.state y (Nat.find hex) = tr.state y j :=
    state_eq_of_noCall hj₂ fun k hk hk' hck => Nat.find_min hex hk' ⟨hk, hck⟩
  have hτg : max (tr.time k₀) g = tr.time k₀ := max_eq_left ((le_gbar g).trans hτ)
  have hdl : ∀ k, tr.deadline y k (tr.time k₀) P.Δ = tr.time k₀ + P.Δ :=
    deadline_eq (hnr y hy) hτ
  obtain ⟨k, -, hak, hlt⟩ := hh.1.relay x hx k₀ B hacc ((le_gbar g).trans hτ) y hy _ hcall
    (by rw [hτg, hdl]; linarith [hj.1, hrun.time_mono hj₂]) (by rw [hst]; exact hF)
  rw [hτg, hdl] at hlt
  refine ⟨k, ?_, hak⟩
  by_contra h
  have := hrun.time_mono (not_lt.1 h)
  linarith [hj.1]

end Runs

/-- **Joined late** (no honest restart after `ḡ`): from `ḡ + 8Δ` on every honest node is joined,
its restarts being at or before `ḡ < t_{slot(ḡ)+1} ≤ t_{slot(t)−1}`. -/
theorem joined_late {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {g t : Time}
    (hnr : NoRestartAfter tr H (SA.gbar g)) (ht : SA.gbar g + 8 * sp.Δ ≤ t) :
    ∀ y ∈ H, tr.JoinedAt y t := by
  intro y hy k hk _
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  have h1 := (SA.ts_le_iff_le_slot sp hg0 (sp.slot (SA.gbar g))).mpr le_rfl
  have h2 : ¬ sp.ts (sp.slot (SA.gbar g) + 1 : Int) ≤ SA.gbar g := fun h => by
    have := (SA.ts_le_iff_le_slot sp hg0 _).mp h
    omega
  have h3 : sp.ts ((sp.slot (SA.gbar g) : Int) + 2) = sp.ts (sp.slot (SA.gbar g)) + 8 * sp.Δ := by
    simp only [SA.SAParams.ts]; ring
  have hs : (sp.slot (SA.gbar g) : Int) + 2 ≤ sp.slot t :=
    (SA.ts_le_iff_le_slot sp (by linarith) _).mp (by linarith)
  change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
  rw [sp.slotTime_eq]
  refine ⟨by omega, (hnr y hy k hk).trans ?_⟩
  have : sp.ts (sp.slot (SA.gbar g) + 1 : Int) ≤ sp.ts ((sp.slot t - 1 : Nat) : Int) :=
    (SA.ts_le_iff sp).mpr (by omega)
  simp only [SA.SAParams.ts] at this h2 ⊢
  linarith [not_le.1 h2]

end Consensus.Goldilocks.Healing

end
