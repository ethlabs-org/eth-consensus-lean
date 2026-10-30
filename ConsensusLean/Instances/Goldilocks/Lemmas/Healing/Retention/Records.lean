module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High

public section

/-! # Goldilocks Healing, HR.4: the high records (R4)

`producer-reset-continuation.md` §16. An honest client record changes only when the node signs
(`record_attestation`, the only writer; the record is durable over restarts): its target and
timeout entries at `h` name the height pair of an attestation it signed at `h`, its lock entry at
`h` the finality pair `(h, ·)` of one (`client_record_origin`). A signed height pair of height
`≥ H_z + 1` is signed at or after `a` (HR.1 (c)), so by (R1)'s rows it names the entry at its
height of a high origin's chain; a finality pair names the entry at its height of an ancestor of
the source's entry (`signed_fin_pair_entry`, `chain_pairs_entry`), which is then on a high
origin's chain too (`high_record_entry`). Two entries at one height of comparable chains are one
block (entry constancy, `entry_root_eq`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Vote Payload gbar)

/-- One accepted block keeps the height and the entry, or enters the next height by itself; it
keeps the justification, or justifies the parent's entry at the parent's height (the private
`step_fields` of `Lemmas/FGStore/Cut.lean`). -/
private theorem step_fields {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ((σ'.h = σ.h ∧ σ'.Th = σ.Th) ∨ (σ'.h = σ.h + 1 ∧ σ'.Th = B.root)) ∧
      ((σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h)) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- **Entry constancy** (G0.2 (i)): while the height stays along ancestry, the entry stays. -/
theorem Th_eq_of_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W)
    (hh : (st.σ W.root).h = (st.σ A.root).h) : (st.σ W.root).Th = (st.σ A.root).Th := by
  induction h with
  | refl => rfl
  | tail hAY hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    have h₁ := σ_h_le_of_anc hr hAY
    rcases (step_fields ht).1 with ⟨he, hT⟩ | ⟨he, -⟩
    · rw [hT]; exact ih (by omega)
    · omega

/-- `create_attestation`'s new record is the old one with the attestation recorded. -/
private theorem createAtt_record {n : Nat} {Λ Λ' : FG.Record} {v : Fin n}
    {σe : FG.ChainState n} {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    Λ' = Λ.recordAtt a := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- `create_attestation`'s finality pair is the record's `finality_pair` of the entry state. -/
private theorem createAtt_fin {n : Nat} {Λ Λ' : FG.Record} {v : Fin n}
    {σe : FG.ChainState n} {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    a.fin = Λ.finalityPair σe := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · dsimp only at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

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

/-- One accepted block: its justification is the parent's, or the parent's entry at the parent's
height; its pending pairs are the parent's or the parent's `(h, T_h)`. -/
private theorem step_pending {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ((σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h)) ∧
      ∀ p ∈ σ'.pending, p ∈ σ.pending ∨ p = (σ.h, σ.Th) := by
  refine ⟨(step_fields h).2, ?_⟩
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, pr, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := pr, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] <;> intro q hq
  · simp only [FG.ChainState.advance] at hq
    rcases List.mem_append.1 (List.mem_of_mem_drop hq) with hq | hq
    · exact Or.inl (List.mem_filter.1 hq).1
    · exact Or.inr (List.mem_singleton.1 hq)
  · simp only [FG.ChainState.advance] at hq
    exact Or.inl (List.mem_filter.1 hq).1
  · exact Or.inl (List.mem_filter.1 hq).1

/-- **The justification and the pending pairs of a held block name entries of its chain**
(G0.2 (h)): the justification at `h_j ≥ 1`, and each pending pair `(j, T)`, is the root of an
ancestor whose state has height `j` and itself as entry. -/
theorem chain_pairs_entry {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    (1 ≤ (st.σ W.root).hj → ∃ Z ∈ st.tree, st.Anc Z W ∧ Z.root = (st.σ W.root).J ∧
      (st.σ Z.root).h = (st.σ W.root).hj ∧ (st.σ Z.root).Th = Z.root) ∧
    ∀ p ∈ (st.σ W.root).pending, ∃ Z ∈ st.tree, st.Anc Z W ∧ Z.root = p.2 ∧
      (st.σ Z.root).h = p.1 ∧ (st.σ Z.root).Th = Z.root := by
  have hA := (Store.accepted_tree _ _ _ _ hr).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]
    exact ⟨fun h => absurd h (by simp [FG.ChainState.init]),
      fun p hp => by simp [FG.ChainState.init] at hp⟩
  | tail _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    obtain ⟨⟨E, hE, hEr, hEY, hEh, hET⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hr _ hYW.1
    have hET' := hET.trans hEr.symm
    obtain ⟨hJ, hpend⟩ := step_pending ht
    refine ⟨fun h1 => ?_, fun p hp => ?_⟩
    · rcases hJ with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
      · obtain ⟨Z, hZ, hZY, hZr, hZh, hZT⟩ := ih.1 (by rw [← hj]; exact h1)
        exact ⟨Z, hZ, hZY.tail hYW, hZr.trans hJ.symm, hZh.trans hj.symm, hZT⟩
      · exact ⟨E, hE, hEY.tail hYW, hEr.trans hJ.symm, hEh.trans hj.symm, hET'⟩
    · rcases hpend p hp with hp | rfl
      · obtain ⟨Z, hZ, hZY, hZr, hZh, hZT⟩ := ih.2 p hp
        exact ⟨Z, hZ, hZY.tail hYW, hZr, hZh, hZT⟩
      · exact ⟨E, hE, hEY.tail hYW, hEr, hEh, hET'⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

private theorem tree_subset_honest {y : Fin sp.n} (hy : y ∈ H) {k : Nat} :
    (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun _ hX => ⟨y, hy, k, hX⟩

/-- **The origin of a record entry** (`record_attestation` is the only writer of the record,
which only an `fg_attest` that signs changes): a target or timeout entry `r` at `h` was the height
pair `(h, r)` of an attestation the node signed earlier, a lock entry `r` at `h` its finality
pair `(h, r)`. -/
theorem client_record_origin (hp : ResetPremises tr H dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    (h r : Nat) : ∀ i,
    ((tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r) ∧
    ((tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r))
  | 0 => by
    rw [Trace.state, hp.run.init y hy]
    refine ⟨fun hx => ?_, fun hx => ?_⟩ <;>
      simp [Node.init, FG.Record.empty] at hx
  | i + 1 => by
    obtain ⟨ih₁, ih₂⟩ := client_record_origin hp hy h r i
    have old : (tr.state y (i + 1)).record = (tr.state y i).record →
        ((tr.state y (i + 1)).record.target h = some r ∨
            r ∈ (tr.state y (i + 1)).record.timeout h →
          ∃ k < i + 1, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r) ∧
        ((tr.state y (i + 1)).record.lock h = some r →
          ∃ k < i + 1, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r)) := fun he => by
      rw [he]
      exact ⟨fun hx => let ⟨k, hk, att, h'⟩ := ih₁ hx; ⟨k, by omega, att, h'⟩,
        fun hx => let ⟨k, hk, att, h'⟩ := ih₂ hx; ⟨k, by omega, att, h'⟩⟩
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := hp.run.cutLaw y hy i c hc
      have hsucc := tr.state_succ_of_call hc
      cases c with
      | ac ℓ => exact old (by rw [hsucc]; exact hlaw.2.2.2)
      | fg ℓ =>
        cases ℓ with
        | block B acc =>
          cases acc with
          | true => exact old (by rw [hsucc]; exact hlaw.2.2.2)
          | false => exact old (by rw [hsucc, hlaw.2])
        | attestation a' => exact old (by rw [hsucc]; exact hlaw.2.2)
        | attest C s =>
          cases s with
          | none => exact old (by rw [hsucc, hlaw.2])
          | some a' =>
            have hrec : (tr.state y (i + 1)).record = (tr.state y i).record.recordAtt a' :=
              hsucc ▸ createAtt_record hlaw.1
            have hs : tr.SignAt y i a' := ⟨C, hc⟩
            rw [hrec]
            refine ⟨fun hx => ?_, fun hx => ?_⟩
            · have key : (tr.state y i).record.target h = some r ∨
                  r ∈ (tr.state y i).record.timeout h ∨ (a'.h = h ∧ a'.T = r) := by
                rcases hx with hx | hx
                · simp only [FG.Record.recordAtt] at hx
                  split_ifs at hx
                  · rw [Function.update_apply] at hx
                    split_ifs at hx with hh
                    · exact Or.inr (Or.inr ⟨hh.symm, Option.some.inj hx⟩)
                    · exact Or.inl hx
                  · exact Or.inl hx
                · simp only [FG.Record.recordAtt] at hx
                  split_ifs at hx
                  · rw [Function.update_apply] at hx
                    split_ifs at hx with hh
                    · rcases Finset.mem_insert.1 hx with rfl | hx
                      · exact Or.inr (Or.inr ⟨hh.symm, rfl⟩)
                      · exact Or.inr (Or.inl (by rw [hh]; exact hx))
                    · exact Or.inr (Or.inl hx)
                  · exact Or.inr (Or.inl hx)
              rcases key with hx | hx | ⟨h₁, h₂⟩
              · obtain ⟨k, hk, att, h'⟩ := ih₁ (Or.inl hx)
                exact ⟨k, by omega, att, h'⟩
              · obtain ⟨k, hk, att, h'⟩ := ih₁ (Or.inr hx)
                exact ⟨k, by omega, att, h'⟩
              · exact ⟨i, by omega, a', hs, h₁, h₂⟩
            · simp only [FG.Record.recordAtt] at hx
              rcases hf : a'.fin with _ | ⟨p₁, p₂⟩
              · rw [hf] at hx
                dsimp only at hx
                obtain ⟨k, hk, att, h'⟩ := ih₂ hx
                exact ⟨k, by omega, att, h'⟩
              · rw [hf] at hx
                dsimp only at hx
                rw [Function.update_apply] at hx
                split_ifs at hx with hh
                · cases Option.some.inj hx
                  exact ⟨i, by omega, a', hs, by rw [hf, hh]⟩
                · obtain ⟨k, hk, att, h'⟩ := ih₂ hx
                  exact ⟨k, by omega, att, h'⟩
    · exact old (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

/-- **The finality pair of an honest attestation names an entry of its source's chain**
(§16; G0.2 (h)): the finality pair `(h, r)` that `fg_attest` signs (the justification of the entry
state at a bound entry, or one of its pending pairs) names the entry at height `h` of an
ancestor-or-self `J` of the source's entry `E` (whose root is the signed `T`). -/
theorem signed_fin_pair_entry (hp : ResetPremises tr H dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att) {h r : Nat}
    (hfin : att.fin = some (h, r)) :
    ∃ J ∈ (tr.state y k).fg.tree, ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧
      (tr.state y k).fg.Anc J E ∧ J.root = r ∧ ((tr.state y k).fg.σ J.root).h = h ∧
      ((tr.state y k).fg.σ J.root).Th = J.root := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw y hy k _ hc).1
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  have hT := (Store.createAtt_eq hcl).2
  have hfp := createAtt_fin hcl
  rw [hfin] at hfp
  rcases hs' : (tr.state y k).fg.blocks src.root with _ | X
  · have hg : ((tr.state y k).fg.σ src.root).Th = sp.genesisRoot := by
      rw [Store.σ_of_blocks_none hr hs']; rfl
    rw [hg, Store.σ_genesis hr] at hfp
    simp [FG.Record.finalityPair, FG.ChainState.bound, FG.ChainState.init] at hfp
  have hXr : X.root = src.root := Goldilocks.Store.Reachable.blocks_root hr hs'
  have hX : X ∈ (tr.state y k).fg.tree := by
    change (tr.state y k).fg.blocks X.root = some X; rw [hXr]; exact hs'
  obtain ⟨⟨E, hE, hEr, -, -, hET⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hr X hX
  rw [← hXr, ← hEr] at hfp hT
  replace hET : ((tr.state y k).fg.σ E.root).Th = E.root := hET.trans hEr.symm
  obtain ⟨hJ, hpend⟩ := chain_pairs_entry hr hE
  unfold FG.Record.finalityPair at hfp
  split_ifs at hfp with hb
  · simp only [Option.some.injEq, Prod.mk.injEq] at hfp
    obtain ⟨rfl, rfl⟩ := hfp
    obtain ⟨Z, hZ, hZE, hZr, hZh, hZT⟩ := hJ hb.1
    exact ⟨Z, hZ, E, hE, hET.symm.trans hT.symm, hZE, hZr, hZh, hZT⟩
  · rcases foldl_newest_mem hfp.symm with h' | h'
    · cases h'
    · obtain ⟨Z, hZ, hZE, hZr, hZh, hZT⟩ := hpend _ (List.mem_filter.1 h').1
      exact ⟨Z, hZ, E, hE, hET.symm.trans hT.symm, hZE, hZr, hZh, hZT⟩

/-- **A high record entry names an entry of a high origin's chain** (§16): the target, timeout
or lock entry `r` at `h ≥ H_z + 1` of an honest record is the root of a block `Z` below the
block of a high origin, the entry at height `h` of its chain. -/
theorem high_record_entry (hp : ResetPremises tr H dg g ΔF a)
    (hrows : ∀ y ∈ H, ∀ k att, tr.SignAt y k att → a ≤ tr.time k → HZ tr H g + 1 ≤ att.h →
      ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
        (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
        ((tr.state x i).fg.σ E.root).Th = E.root)
    {y : Fin sp.n} (hy : y ∈ H) {i h r : Nat} (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r) :
    ∃ x i' j B, HighOrigin tr H g x i' j B ∧ ∃ Z, Anc (tr.HonestBlocks H) Z B ∧ Z.root = r ∧
      ∃ z ∈ H, ∃ m, Z ∈ (tr.state z m).fg.tree ∧ ((tr.state z m).fg.σ Z.root).h = h ∧
        ((tr.state z m).fg.σ Z.root).Th = Z.root := by
  have hrow : ∀ {k att}, tr.SignAt y k att → HZ tr H g + 1 ≤ att.h →
      ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
        (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
        ((tr.state x i).fg.σ E.root).Th = E.root := fun hs hatt =>
    hrows y hy _ _ hs (reset_le_of_high hp.run hp.healthy hp.reset hy hs hatt) hatt
  rcases hr with hr | hr | hr
  · obtain ⟨k, -, att, hs, rfl, rfl⟩ := (client_record_origin hp hy h r i).1 (Or.inl hr)
    obtain ⟨x, i', j, B, ho, E, hE, hEB, hEr, hEh, hET⟩ := hrow hs hh
    exact ⟨x, i', j, B, ho, E, Anc.mono (tree_subset_honest ho.1) hEB, hEr, x, ho.1, i',
      hE, hEh, hET⟩
  · obtain ⟨k, -, att, hs, rfl, rfl⟩ := (client_record_origin hp hy h r i).1 (Or.inr hr)
    obtain ⟨x, i', j, B, ho, E, hE, hEB, hEr, hEh, hET⟩ := hrow hs hh
    exact ⟨x, i', j, B, ho, E, Anc.mono (tree_subset_honest ho.1) hEB, hEr, x, ho.1, i',
      hE, hEh, hET⟩
  · obtain ⟨k, -, att, hs, hfin⟩ := (client_record_origin hp hy h r i).2 hr
    obtain ⟨J, hJ, E, hE, hEr, hJE, hJr, hJh, hJT⟩ := signed_fin_pair_entry hp hy hs hfin
    obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run hy hs
    obtain rfl : E' = E :=
      (honest_coherent hp).1 ⟨y, hy, k, hE'⟩ ⟨y, hy, k, hE⟩ (hE'r.trans hEr.symm)
    have hJE' := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k) hJE
    obtain ⟨x, i', j, B, ho, E'', hE'', hE''B, hE''r, -, -⟩ := hrow hs (by omega)
    obtain rfl : E'' = E' :=
      (honest_coherent hp).1 ⟨x, ho.1, i', hE''⟩ ⟨y, hy, k, hE'⟩ (hE''r.trans hE'r.symm)
    exact ⟨x, i', j, B, ho, J, (Anc.mono (tree_subset_honest hy) hJE).trans
      (Anc.mono (tree_subset_honest ho.1) hE''B), hJr, y, hy, k, hJ, hJh, hJT⟩

/-- **Two entries at one height below one held block are one block** (entry constancy). -/
theorem entry_root_eq (hp : ResetPremises tr H dg g ΔF a) {z : Fin sp.n} (hz : z ∈ H) {m : Nat}
    {C Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state z m).fg.tree)
    (h₁ : Anc (tr.HonestBlocks H) Z₁ C) (h₂ : Anc (tr.HonestBlocks H) Z₂ C)
    (hh : ((tr.state z m).fg.σ Z₁.root).h = ((tr.state z m).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state z m).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state z m).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hz m
  rcases SA.anc_total (honest_coherent hp) h₁ h₂ with h | h
  · have := Th_eq_of_anc hr (anc_tree_of_anc hp hz h (mem_tree_of_anc hp hz h₂ hC)) hh.symm
    rw [← hT₁, ← hT₂, this]
  · have := Th_eq_of_anc hr (anc_tree_of_anc hp hz h (mem_tree_of_anc hp hz h₁ hC)) hh
    rw [← hT₁, ← hT₂, this]

end Consensus.Goldilocks.Healing

end
