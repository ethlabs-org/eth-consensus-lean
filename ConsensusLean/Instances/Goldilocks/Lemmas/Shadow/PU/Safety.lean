module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence

public section

/-! # Client safety for shadow P-U execution

The record induction reads only FG initialization and execution, not the tick-order fields.
It does not identify the shadow block handler with the stock handler.
-/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {ACP : Type} {st : Store P ACP}

private theorem entry_input' {acp₀ : ACP} (hr : st.Reachable' acp₀) (r : Nat) :
    1 ≤ (st.σ r).h ∧ (st.σ r).hj < (st.σ r).h ∧
      ∀ p ∈ (st.σ r).pending, p.1 < (st.σ r).h := by
  have hR := hr.reachableWith
  have hu := Store.finalitySpec_updateFinality' (P := P) (ACP := ACP)
  obtain ⟨c, hc⟩ : ∃ c, P.fg.chainState c = some (st.σ r) := by
    rcases hb : st.blocks r with _ | X
    · exact ⟨[], by rw [Store.σ_of_blocks_none_with hu hR hb]; rfl⟩
    · have hX := Store.blocks_root_with hu hR hb
      obtain ⟨c, _, _, _, hc⟩ := Store.chain_state_of_chain_with hu hR X (by
        change st.blocks X.root = some X
        rwa [hX])
      exact ⟨_, hX ▸ hc⟩
  obtain ⟨h1, _, h2, _, _, _, _, h3, _⟩ := FG.chain_invariants P.fg c _ hc
  exact ⟨h1, h2, fun p hp => (h3 p hp).2.trans_lt h2⟩

private theorem call_step' {H : Set (Fin P.n)}
    {tr : FGTrace P ACP}
    (hexec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H →
      FGLabel.Step' (tr.node i) (tr.state (tr.node i) i) ℓ (tr.post i))
    {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    (hn : tr.node i = y ∧ tr.label i ≠ none) :
    ∃ ℓ, tr.label i = some ℓ ∧ FGLabel.Step' y (tr.state y i) ℓ (tr.post i) := by
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
  refine ⟨ℓ, hℓ, ?_⟩
  rw [← hn.1]
  exact hexec i ℓ hℓ (hn.1 ▸ hy)

private theorem fg_store_reachable' {acp₀ : ACP} {H : Set (Fin P.n)}
    {tr : FGTrace P ACP}
    (hinit : ∀ y ∈ H, tr.init y = (Store.init acp₀, FG.Record.empty))
    (hexec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H →
      FGLabel.Step' (tr.node i) (tr.state (tr.node i) i) ℓ (tr.post i))
    {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    (tr.store y i).Reachable' acp₀ := by
  rw [Store.reachable'_eq]
  induction i with
  | zero =>
    change Relation.ReflTransGen Store.Step' (Store.init acp₀) (tr.init y).1
    rw [hinit y hy]
  | succ i ih =>
    rw [FGTrace.store, Trace.state]
    split_ifs with hnode
    · obtain ⟨ℓ, _, hs⟩ := call_step' hexec hy hnode
      cases ℓ with
      | block B acc =>
        rw [FGLabel.step'_block] at hs
        rcases hs with ⟨_, h, _⟩ | ⟨_, _, he⟩
        exacts [ih.tail ((Store.step'_iff _ _).2 (Or.inl ⟨B, h⟩)), he ▸ ih]
      | attestation a =>
        rw [FGLabel.step'_attestation] at hs
        rw [hs]
        exact ih.tail ((Store.step'_iff _ _).2 (Or.inr ⟨a, rfl⟩))
      | attest src signed =>
        rw [FGLabel.step'_attest] at hs
        rw [hs.1]
        exact ih
    · exact ih

private theorem record_run_append {n : Nat} (v : Fin n) (Λ : FG.Record)
    (l : List (FG.ChainState n)) (σe : FG.ChainState n) :
    FG.Record.run v Λ (l ++ [σe]) = match (FG.Record.run v Λ l).1.createAtt v σe with
      | none => FG.Record.run v Λ l
      | some (a, Λ') => (Λ', (FG.Record.run v Λ l).2 ++ [a]) := by
  induction l generalizing Λ with
  | nil =>
    rcases h : Λ.createAtt v σe with _ | ⟨a, Λ'⟩ <;> simp [FG.Record.run, h]
  | cons x l ih =>
    rcases h : Λ.createAtt v x with _ | ⟨a, Λ'⟩ <;>
      simp only [List.cons_append, FG.Record.run, h, ih]
    split <;> rfl

/-- A shadow client's signatures belong to one run over valid entry states. Only FG
execution is read; no equivalence with the stock block handler is assumed. -/
theorem signed_run' {acp₀ : ACP} {H : Set (Fin P.n)} {tr : FGTrace P ACP}
    (hinit : ∀ y ∈ H, tr.init y = (Store.init acp₀, FG.Record.empty))
    (hexec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H →
      FGLabel.Step' (tr.node i) (tr.state (tr.node i) i) ℓ (tr.post i))
    {v : Fin P.n} (hv : v ∈ H) (i : Nat) :
    ∃ inputs, FG.EntryInputs P.fg inputs ∧
      ∀ j < i, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2 := by
  suffices hrec : ∃ inputs : List (FG.ChainState P.n), FG.EntryInputs P.fg inputs ∧
      (tr.state v i).2 = (FG.Record.run v FG.Record.empty inputs).1 ∧
      ∀ j < i, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2 by
    obtain ⟨inputs, hin, _, hs⟩ := hrec
    exact ⟨inputs, hin, hs⟩
  induction i with
  | zero =>
    refine ⟨[], fun _ h => absurd h List.not_mem_nil, ?_, fun _ h => absurd h
      (Nat.not_lt_zero _)⟩
    change (tr.init v).2 = _
    rw [hinit v hv]
    rfl
  | succ i ih =>
    obtain ⟨inputs, hin, hrec, hsign⟩ := ih
    have sign_of (h₀ : ∀ a src, tr.node i = v → tr.label i ≠ some (.attest src (some a))) :
        ∀ j < i + 1, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2 :=
      fun j hj a h => (Nat.lt_succ_iff_lt_or_eq.1 hj).elim (hsign j · a h) fun e => by
        obtain ⟨src, hn, h⟩ := h
        subst e
        exact absurd h (h₀ a src hn)
    rw [Trace.state]
    split_ifs with hnode
    · obtain ⟨ℓ, hℓ, hs⟩ := call_step' hexec hv hnode
      cases ℓ with
      | block B acc =>
        rw [FGLabel.step'_block] at hs
        refine ⟨inputs, hin, ?_, sign_of fun a src _ h => by rw [hℓ] at h; cases h⟩
        rcases hs with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h, hrec]
      | attestation a =>
        rw [FGLabel.step'_attestation] at hs
        exact ⟨inputs, hin, hs ▸ hrec, sign_of fun a src _ h => by rw [hℓ] at h; cases h⟩
      | attest src signed =>
        rw [FGLabel.step'_attest] at hs
        obtain ⟨_, hs⟩ := hs
        set σe := (tr.state v i).1.σ ((tr.state v i).1.σ src.root).Th
        rw [show (tr.state v i).1.attest (tr.state v i).2 v src =
          (tr.state v i).2.createAtt v σe from rfl] at hs
        refine ⟨inputs ++ [σe], fun σ hσ => ?_, ?_⟩
        · rcases List.mem_append.1 hσ with h | h
          · exact hin σ h
          · rw [List.mem_singleton.1 h]
            exact entry_input' (fg_store_reachable' hinit hexec hv i) _
        rw [record_run_append, ← hrec]
        rcases hc : (tr.state v i).2.createAtt v σe with _ | ⟨a, Λ'⟩ <;> rw [hc] at hs
        · exact ⟨hs.2.trans hrec, sign_of fun a src' _ h => by simp [hℓ, hs.1] at h⟩
        refine ⟨hs.2, fun j hj b h => (Nat.lt_succ_iff_lt_or_eq.1 hj).elim
          (fun hj => List.mem_append_left _ (hsign j hj b h)) fun e => ?_⟩
        obtain ⟨src', _, h⟩ := h
        subst e
        obtain ⟨_, rfl⟩ : src = src' ∧ a = b := by simpa [hℓ, hs.1] using h
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact ⟨inputs, hin, hrec, sign_of fun a src hn h => hnode ⟨hn, by simp [h]⟩⟩

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace' sp}

private theorem held_att_signed' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {a : FG.Att sp.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  rcases Coherence.tree_accepted' hrun.toLocalRun' hy hX with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · obtain ⟨k', hk', hs⟩ := hrun.att_unforgeable y hy k a
      (Or.inr ⟨X, ⟨true, hacc⟩, haX⟩) hav
    exact ⟨k', hk'.trans hk, hs⟩

/-- Two honest readers' held attestations from an honest signer are not slashable in
the shadow execution. The collision premise matches the run-level safety interface. -/
theorem held_atts_safe' {ini} (hrun : GoldilocksRun' proposer dg H tr ini)
    (_hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H)
    (i j : Nat) (a b : FG.Att sp.n)
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state z j).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed' hrun hy ha hav
  obtain ⟨l, hl, hlb⟩ := held_att_signed' hrun hz hb (hab.1 ▸ hav)
  rw [← hab.1] at hlb
  obtain ⟨hinit, hexec⟩ := Compose.fg_exec' hrun.toLocalRun'
  obtain ⟨inputs, hin, hs⟩ := signed_run' hinit hexec hav (max k l + 1)
  exact FG.client_safety sp.toParams.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb.choose_spec⟩) hab

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams Payload)

variable {sp : ACParams}

private theorem held_att_signed_at' {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace' sp} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att sp.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by
    rw [Trace.upTo_state tr y hle]
    exact hX
  rcases Coherence.tree_accepted' (hrun.upTo ht).toLocalRun' hy hXt with
    rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := hrun.att_unforgeable y k a
      (hrun.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (hrun.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

/-- Client safety for two honest observations of the shadow execution. A signer remains
honest through both observations, but the two holders need not remain honest together. -/
theorem held_atts_safe_at' {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace' sp} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (_hnc : Compose.NoCollRun dg tr)
    {y x : Fin sp.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att sp.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed_at' hrun hu hytime hy ha
    (hrun.antitone hud hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed_at' hrun ht hxtime hx hb
    (hab.1 ▸ hrun.antitone htd hav)
  rw [← hab.1] at hlb
  have hka' : (tr.upTo d).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
  have hlb' : (tr.upTo d).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
  have hr := hrun.upTo (hu.trans hud)
  obtain ⟨hinit, hexec⟩ := Compose.fg_exec' hr.toLocalRun'
  obtain ⟨inputs, hin, hs⟩ := signed_run' hinit hexec hav (max k l + 1)
  exact FG.client_safety sp.toParams.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab

end Consensus.Goldilocks.Healing.Growing.Shadow

end
