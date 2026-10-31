module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records

public section

/-! # Goldilocks Healing: HS.4 (b), the client subclaim

`hs234-exact-interface.md` §5 "client progress" (P1/P2 of workbench#6). At an honest
`fg_attest(C)` in the effective phase `(m, c)`, whose source `C` has state height `h ≥ ℓ`, entry
`E` and is allowed in the phase geometry, the client signs a matching row `(h, E)` (target or
timeout), or it signed one at an earlier cut (`client_progress`):

* `height_pair` does not refuse. A lock at `h` naming `X ≠ E` was written by an earlier honest
  signing whose finality pair is `(h, X)` (`record_facts`, the record's only writer is
  `record_attestation`); that pair is a justification `(h, X)` of a state held by the signer
  (`finalityPair_justified`), so the node holds a block of state height `> h`: `h ≤ m − 1`, and
  with `h ≥ ℓ` the phase is not a contest and `h = m − 1`. A gap has no justification at `m − 1`;
  in the top-`J` case `J = X` (HR.2 (a)) and the allowed `C` extends `J`, so `X` and `E` are the
  entries of `C`'s chain at `h`: `X = E`.
* If `create_attestation` refuses the pair, an earlier sent content at `h` names `E` (a timeout
  refusal) or the target record is free or `E` with no timeout at `h` (a target refusal), and the
  record tracks every sent content (`SentOK`), so the sent content names `E`; it was signed at an
  earlier cut (`record_facts`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-! ## The client record -/

namespace Client

variable {n : Nat}

/-- The record tracks the contents sent: a sent timeout's root is in the timeout set of its
height, a sent target is the target record of its height. -/
def SentOK (Λ : FG.Record) : Prop :=
  ∀ b ∈ Λ.sent, (b.2.2.1 = true → b.2.1 ∈ Λ.timeout b.1) ∧
    (b.2.2.1 = false → Λ.target b.1 = some b.2.1)

theorem sentOK_iff (Λ : FG.Record) : SentOK Λ ↔ ∀ b ∈ Λ.sent,
    (b.2.2.1 = true → b.2.1 ∈ Λ.timeout b.1) ∧ (b.2.2.1 = false → Λ.target b.1 = some b.2.1) :=
  Iff.rfl

/-- The height pair of `height_pair`: it names the entry, and a target finds no timeout and a free
or equal target at its height. -/
private theorem heightPair_some {Λ : FG.Record} {h T h' T' : Nat} {τ : Bool}
    (hp : Λ.heightPair h T = some (h', T', τ)) :
    h' = h ∧ T' = T ∧
      (τ = false → Λ.timeout h = ∅ ∧ (Λ.target h = none ∨ Λ.target h = some T)) := by
  unfold FG.Record.heightPair at hp
  split_ifs at hp with h1 h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp <;>
    obtain ⟨rfl, rfl, rfl⟩ := hp <;> simp_all

/-- `height_pair` refuses only for a lock at the height that names another block. -/
private theorem heightPair_none {Λ : FG.Record} {h T : Nat} (hp : Λ.heightPair h T = none) :
    Λ.lock h ≠ none ∧ Λ.lock h ≠ some T := by
  unfold FG.Record.heightPair at hp
  split_ifs at hp with h1
  exact h1

/-- What `create_attestation` signs. -/
theorem createAtt_some {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n} {a : FG.Att n}
    (h : Λ.createAtt v σe = some (a, Λ')) :
    Λ' = Λ.recordAtt a ∧ a.h = σe.h ∧ a.T = σe.Th ∧ a.fin = Λ.finalityPair σe ∧
      (a.timeout = false →
        Λ.timeout a.h = ∅ ∧ (Λ.target a.h = none ∨ Λ.target a.h = some a.T)) := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · cases h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl, ht⟩ := heightPair_some hp
    exact ⟨rfl, rfl, rfl, rfl, ht⟩

/-- When `create_attestation` refuses a pair that `height_pair` accepts, an earlier sent content
at its height names its entry, or (a target refusal) the target record is free or equal and no
timeout is recorded at its height. -/
theorem createAtt_none {Λ : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    (h : Λ.createAtt v σe = none) :
    (Λ.lock σe.h ≠ none ∧ Λ.lock σe.h ≠ some σe.Th) ∨
      ∃ b ∈ Λ.sent, b.1 = σe.h ∧ (b.2.1 = σe.Th ∨ (Λ.timeout σe.h = ∅ ∧
        (Λ.target σe.h = none ∨ Λ.target σe.h = some σe.Th))) := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · exact Or.inl (heightPair_none hp)
  · dsimp only at h
    split_ifs at h with hany
    obtain ⟨rfl, rfl, ht⟩ := heightPair_some hp
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.1 hany
    simp only [Bool.not_eq_true', decide_eq_true_eq] at hb'
    refine Or.inr ⟨b, hb, hb'.1, ?_⟩
    rcases hb'.2 with hτ | hT
    · exact Or.inr (ht (by simpa using hτ))
    · exact Or.inl hT

/-- Recording an attestation that `create_attestation` signs keeps the record tracking its sent
contents. -/
theorem sentOK_recordAtt {Λ : FG.Record} (hΛ : SentOK Λ) {a : FG.Att n}
    (ht : a.timeout = false → Λ.target a.h = none ∨ Λ.target a.h = some a.T) :
    SentOK (Λ.recordAtt a) := by
  intro b hb
  simp only [FG.Record.recordAtt, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · obtain ⟨h1, h2⟩ := hΛ b hb
    refine ⟨fun hτ => ?_, fun hτ => ?_⟩
    · simp only [FG.Record.recordAtt]
      split_ifs
      · rw [Function.update_apply]
        split_ifs with he
        · exact Finset.mem_insert_of_mem (by rw [← he]; exact h1 hτ)
        · exact h1 hτ
      · exact h1 hτ
    · simp only [FG.Record.recordAtt]
      split_ifs with hc
      · rw [Function.update_of_ne fun he => by rw [← he, h2 hτ] at hc; simp at hc]
        exact h2 hτ
      · exact h2 hτ
  · refine ⟨fun hτ => ?_, fun hτ => ?_⟩
    · simp only [FG.Att.content] at hτ ⊢
      simp [FG.Record.recordAtt, hτ]
    · simp only [FG.Att.content] at hτ ⊢
      rcases ht hτ with h0 | h0 <;> simp [FG.Record.recordAtt, hτ, h0]

end Client

/-! ## Justifications and finality pairs of a reachable store -/

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- Along one block, a pending pair of the new state is old or is the new state's
justification. -/
private theorem step_pending_just {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ∀ p ∈ σ'.pending, p ∈ σ.pending ∨ p = (σ'.hj, σ'.J) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, pr, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := pr, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] <;> intro q hq
  · simp only [FG.ChainState.advance] at hq ⊢
    rcases List.mem_append.1 (List.mem_of_mem_drop hq) with hq | hq
    · exact Or.inl (List.mem_filter.1 hq).1
    · exact Or.inr (List.mem_singleton.1 hq)
  · simp only [FG.ChainState.advance] at hq
    exact Or.inl (List.mem_filter.1 hq).1
  · exact Or.inl (List.mem_filter.1 hq).1

/-- **Every pending pair of a held state is the justification of a held state.** -/
theorem pending_justified (hr : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∀ p ∈ (st.σ W.root).pending, ∃ B ∈ st.tree, (st.σ B.root).hj = p.1 ∧
      (st.σ B.root).J = p.2 := by
  have hA := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]
    intro p hp
    simp [FG.ChainState.init] at hp
  | @tail Y W' _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    intro p hp
    rcases step_pending_just ht p hp with hp | rfl
    · exact ih p hp
    · exact ⟨W', hYW.2.1, rfl, rfl⟩

/-- The newest-pair fold returns its start or a member of the list. -/
private theorem foldl_newest_mem {l : List (Nat × Nat)} {acc : Option (Nat × Nat)}
    {p : Nat × Nat}
    (h : l.foldl (fun acc p => match acc with
      | none => some p
      | some r => if r.1 < p.1 then some p else some r) acc = some p) :
    acc = some p ∨ p ∈ l := by
  induction l generalizing acc with
  | nil => exact Or.inl h
  | cons q l ih =>
    rcases ih h with h' | h'
    · rcases acc with _ | r
      · simp only [Option.some.injEq] at h'
        exact Or.inr (h' ▸ List.mem_cons_self)
      · dsimp only at h'
        split_ifs at h' with hlt
        · simp only [Option.some.injEq] at h'
          exact Or.inr (h' ▸ List.mem_cons_self)
        · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h')

/-- **A finality pair of a held state is the justification of a held state** (the entry's own
justification at a bound entry, or a pending pair). -/
theorem finalityPair_justified (hr : st.Reachable acp₀) {W : NodeBlock P ACP}
    (hW : W ∈ st.tree) {Λ : FG.Record} {p : Nat × Nat}
    (hp : Λ.finalityPair (st.σ W.root) = some p) :
    ∃ B ∈ st.tree, (st.σ B.root).hj = p.1 ∧ (st.σ B.root).J = p.2 := by
  unfold FG.Record.finalityPair at hp
  split_ifs at hp
  · cases hp
    exact ⟨W, hW, rfl, rfl⟩
  · rcases foldl_newest_mem hp with h' | h'
    · cases h'
    · exact pending_justified hr hW p (List.mem_filter.1 h').1

/-- The entry state of any root is the state of a held block. -/
theorem entry_state_held (hr : st.Reachable acp₀) (r : Nat) :
    ∃ W ∈ st.tree, st.σ (st.σ r).Th = st.σ W.root := by
  rcases hs : st.blocks r with _ | X
  · have hg : (st.σ r).Th = P.genesisRoot := by rw [Store.σ_of_blocks_none hr hs]; rfl
    exact ⟨_, Store.genesis_mem hr, by rw [hg]; rfl⟩
  · have hXr : X.root = r := Goldilocks.Store.Reachable.blocks_root hr hs
    have hX : X ∈ st.tree := by change st.blocks X.root = some X; rw [hXr]; exact hs
    obtain ⟨⟨E, hE, hEr, -⟩, -⟩ := Goldilocks.Store.entry_state_of_source _ _ _ _ hr X hX
    exact ⟨E, hE, by rw [hEr, hXr]⟩

/-- State heights are at least `1`. -/
theorem one_le_h (hr : st.Reachable acp₀) {B : NodeBlock P ACP} (hB : B ∈ st.tree) :
    1 ≤ (st.σ B.root).h := by
  obtain ⟨c, -, -, -, hc⟩ := Goldilocks.Store.chain_state_of_chain P ACP acp₀ _ hr B hB
  exact (FG.chain_invariants P.fg _ _ hc).1

end Store

/-! ## The client over a run -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time}

/-- An honest node's record changes only at a cut where it signs, by `create_attestation`. -/
private theorem record_step (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) :
    (tr.state y (i + 1)).record = (tr.state y i).record ∨
      ∃ C a, tr.CallAt y i (.fg (.attest C (some a))) ∧
        (tr.state y i).fg.attest (tr.state y i).record y C =
          some (a, (tr.state y (i + 1)).record) := by
  by_cases hc : ∃ c, tr.CallAt y i c
  · obtain ⟨c, hc⟩ := hc
    have hlaw := hrun.cutLaw y hy i c hc
    rw [tr.state_succ_of_call hc]
    cases c with
    | ac ℓ => exact Or.inl hlaw.2.2.2
    | fg ℓ =>
      cases ℓ with
      | block B acc =>
        cases acc with
        | true => exact Or.inl hlaw.2.2.2
        | false => exact Or.inl (by rw [hlaw.2])
      | attestation a' => exact Or.inl hlaw.2.2
      | attest C s =>
        cases s with
        | none => exact Or.inl (by rw [hlaw.2])
        | some a' => exact Or.inr ⟨C, a', hc, hlaw.1⟩
  · exact Or.inl (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

/-- **The honest client record** (the record's only writer is `record_attestation`, durable over
restarts): it tracks its sent contents, each sent content was signed at an earlier cut, and each
lock entry `(h, r)` is the finality pair of an attestation signed at an earlier cut. -/
theorem record_facts (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) : ∀ i,
    Client.SentOK (tr.state y i).record ∧
    (∀ b ∈ (tr.state y i).record.sent, ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b) ∧
    ∀ h r, (tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r)
  | 0 => by
    rw [Trace.state, hrun.init y hy]
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun h r hx => ?_⟩
    · simp [Node.init, FG.Record.empty] at hb
    · simp [Node.init, FG.Record.empty] at hb
    · simp [Node.init, FG.Record.empty] at hx
  | i + 1 => by
    obtain ⟨ih₁, ih₂, ih₃⟩ := record_facts hrun hy i
    rcases record_step hrun hy i with he | ⟨C, a, hc, hca⟩
    · rw [he]
      exact ⟨ih₁, fun b hb => let ⟨k, hk, h'⟩ := ih₂ b hb; ⟨k, by omega, h'⟩,
        fun h r hx => let ⟨k, hk, h'⟩ := ih₃ h r hx; ⟨k, by omega, h'⟩⟩
    · obtain ⟨hrec, -, -, -, ht⟩ := Client.createAtt_some hca
      rw [hrec]
      have hs : tr.SignAt y i a := ⟨C, hc⟩
      refine ⟨Client.sentOK_recordAtt ih₁ fun hτ => (ht hτ).2, fun b hb => ?_, fun h r hx => ?_⟩
      · simp only [FG.Record.recordAtt, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · obtain ⟨k, hk, h'⟩ := ih₂ b hb
          exact ⟨k, by omega, h'⟩
        · exact ⟨i, by omega, a, hs, rfl⟩
      · simp only [FG.Record.recordAtt] at hx
        rcases hf : a.fin with _ | ⟨p₁, p₂⟩
        · rw [hf] at hx
          obtain ⟨k, hk, h'⟩ := ih₃ h r hx
          exact ⟨k, by omega, h'⟩
        · rw [hf] at hx
          dsimp only at hx
          rw [Function.update_apply] at hx
          split_ifs at hx with hh
          · cases Option.some.inj hx
            exact ⟨i, by omega, a, hs, by rw [hf, hh]⟩
          · obtain ⟨k, hk, h'⟩ := ih₃ h r hx
            exact ⟨k, by omega, h'⟩

/-- **A finality pair `(h, X)` signed by an honest node is a justification it holds**: the node
holds, from the signing on, a block whose state justifies `X` at `h`. -/
theorem signed_fin_justified (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att) {h X : Nat}
    (hfin : att.fin = some (h, X)) :
    ∃ B ∈ (tr.state y k).fg.tree, ((tr.state y k).fg.σ B.root).hj = h ∧
      ((tr.state y k).fg.σ B.root).J = X := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw y hy k _ hc).1
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨-, -, -, hfp, -⟩ := Client.createAtt_some hcl
  obtain ⟨W, hW, hWσ⟩ := Store.entry_state_held hr src.root
  rw [hWσ, hfin] at hfp
  exact Store.finalityPair_justified hr hW hfp.symm

/-- **No conflicting finality lock at an allowed source's height** (`hs234-exact-interface.md`
§5): at an honest `fg_attest(C)` in the phase `(m, c)`, with `C` allowed, of state height
`h ≥ ℓ` and entry `E`, the record's lock at `h` is free or `E`. -/
theorem lock_free_or_entry (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    {i₀ m : Nat} {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} (hk : i₀ ≤ k) (hon : PhaseOn tr.projFG H i₀ k m c)
    {C E : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat} (hE : EntryOf (tr.state y k).fg C E h)
    (hCh : ((tr.state y k).fg.σ C.root).h = h) (hfl : phaseFloor m c ≤ h)
    (hall : EffAllowed (tr.state y k).fg m c C) :
    (tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root := by
  obtain ⟨hfg, hq⟩ := fg_run_of_hs hrun hs
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  have hCTh : ((tr.state y k).fg.σ C.root).Th = E.root := by
    rw [Th_eq_of_anc hr hEC (hCh.trans hEh.symm), hETh]
  rcases hl : (tr.state y k).record.lock h with _ | X
  · exact Or.inl rfl
  refine Or.inr (congrArg some ?_)
  by_contra hne
  obtain ⟨k', hk', att, hsa, hfin⟩ := (record_facts hrun hy k).2.2 h X hl
  obtain ⟨B, hB, hBj, hBJ⟩ := signed_fin_justified hrun hy hsa hfin
  have hsub := Compose.tree_mono hrun.toLocalRun hy hk'.le
  have hσB := σ_eq_honest hrun hs.noColl hy hy (hsub hB) hB
  have hB' := hsub hB
  have h1 : 1 ≤ h := hCh ▸ Store.one_le_h hr hall.1
  obtain ⟨Z, hZ, -, hZr, hZh, hZT⟩ :=
    (chain_pairs_entry hr hB').1 (by rw [hσB, hBj]; exact h1)
  rw [hσB] at hZr hZh
  rw [hBj] at hZh
  rw [hBJ] at hZr
  -- a held block of state height above `h`: `h < m`
  have hlt : h < m := by
    have hge := (Goldilocks.Store.cache_invariants _ _ _ _ hr).2.2.2.2.1 B hB'
    have hjl := Store.hj_lt_h hr hB'
    have hmax := (hon k hk le_rfl).frontierAt.2 y hy
    rw [projFG_store_eq hrun hy] at hmax
    have hBj' : ((tr.state y k).fg.σ B.root).hj = h := by rw [hσB]; exact hBj
    omega
  have hJ : JustifiedAt tr.projFG H k h Z := ⟨y, hy, by rw [projFG_store_eq hrun hy]; exact hZ,
    B, by rw [projFG_store_eq hrun hy]; exact hB', by rw [projFG_store_eq hrun hy, hσB, hBj],
    by rw [projFG_store_eq hrun hy, hσB, hBJ, hZr]⟩
  have hph := hon k hk le_rfl
  cases c with
  | gap =>
    change m - 1 ≤ h at hfl
    obtain rfl : h = m - 1 := by omega
    exact hph.2 Z hJ
  | contest J₀ =>
    change m ≤ h at hfl
    omega
  | top J₀ =>
    change m - 1 ≤ h at hfl
    obtain rfl : h = m - 1 := by omega
    obtain rfl : J₀ = Z := justifiedAt_unique hfg hq hph.2.1 hJ
    have hZC := hall.2.2 J₀ rfl
    have := Th_eq_of_anc hr hZC (hCh.trans hZh.symm)
    rw [hCTh, hZT, hZr] at this
    exact hne this.symm

/-- **HS.4 (b), the client subclaim** (`hs234-exact-interface.md` §5, P1/P2 of workbench#6): at
an honest `fg_attest(C)` in the phase, with `C` allowed, of state height `h ≥ ℓ` and entry `E`,
the client signs a matching row for `E` at `h`, or signed one at an earlier cut. -/
theorem client_progress (hrun : GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF) {i₀ m : Nat}
    {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} :
    ∀ y ∈ H, ∀ k (C : SA.Blk sp.n (List (FG.Att sp.n))) (signed : Option (FG.Att sp.n)),
      tr.CallAt y k (.fg (.attest C signed)) → i₀ ≤ k → PhaseOn tr.projFG H i₀ k m c →
      ∀ E h, EntryOf (tr.state y k).fg C E h → ((tr.state y k).fg.σ C.root).h = h →
        phaseFloor m c ≤ h →
        EffAllowed (tr.state y k).fg m c C →
        (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
        ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root := by
  intro y hy k C signed hc hk hon E h hE hCh hfl hall
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  have hlock := lock_free_or_entry hrun hs hy hk hon hE hCh hfl hall
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  have hCTh : ((tr.state y k).fg.σ C.root).Th = E.root := by
    rw [Th_eq_of_anc hr hEC (hCh.trans hEh.symm), hETh]
  -- the entry state
  have hσe : (tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th =
      (tr.state y k).fg.σ E.root := by rw [hCTh]
  have he₁ : ((tr.state y k).fg.σ E.root).h = h := hEh
  have he₂ : ((tr.state y k).fg.σ E.root).Th = E.root := hETh
  have hlaw := hrun.cutLaw y hy k _ hc
  cases signed with
  | some a =>
    have hcl := hlaw.1
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = some (a, _) at hcl
    rw [hσe] at hcl
    obtain ⟨-, hah, haT, -⟩ := Client.createAtt_some hcl
    exact Or.inl ⟨a, rfl, hah.trans he₁, haT.trans he₂⟩
  | none =>
    have hcl := hlaw.1
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases Client.createAtt_none hcl with ⟨h1, h2⟩ | ⟨b, hb, hbh, hbT⟩
    · simp only [he₁, he₂] at h1 h2
      rcases hlock with hl | hl
      · exact absurd hl h1
      · exact absurd hl h2
    simp only [he₁, he₂] at hbh hbT
    obtain ⟨hok, hsent, -⟩ := record_facts hrun hy k
    have hbT' : b.2.1 = E.root := by
      rcases hbT with hbT | ⟨hto, htg⟩
      · exact hbT
      obtain ⟨h1, h2⟩ := hok b hb
      cases hτ : b.2.2.1
      · have := h2 hτ
        rw [hbh] at this
        rcases htg with htg | htg <;> rw [htg] at this
        · cases this
        · exact (Option.some.inj this).symm
      · have := h1 hτ
        rw [hbh, hto] at this
        simp at this
    obtain ⟨k', hk', att, hsa, rfl⟩ := hsent b hb
    exact Or.inr ⟨k', hk', att, hsa, hbh, hbT'⟩

end Consensus.Goldilocks.Healing

end
