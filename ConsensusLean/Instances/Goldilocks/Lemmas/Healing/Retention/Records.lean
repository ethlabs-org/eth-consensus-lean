module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable

public section

/-! # Goldilocks Healing, HR.4: the high records (R4)

An honest client record changes only when the node signs
(`record_attestation`, the only writer; the record is durable over restarts): its target and
timeout entries at `h` name the height pair of an attestation it signed at `h`, its lock entry at
`h` the finality pair `(h, ·)` of one (`client_record_origin`). A signed height pair of height
`≥ H_z + 1` is signed at or after `a` (HR.1 (c)), so by (R1)'s attestations it names the entry at
its height of a high origin's chain; a finality pair names the entry at its height of an ancestor of
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

/-- Two self-entries at the same height below one held carrier are the same block. -/
theorem self_entries_eq {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {X J Y : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hJ : J ∈ st.tree) (hXY : st.Anc X Y) (hJY : st.Anc J Y)
    (hh : (st.σ X.root).h = (st.σ J.root).h)
    (hXT : (st.σ X.root).Th = X.root) (hJT : (st.σ J.root).Th = J.root) : X = J := by
  have hcoh := (Goldilocks.Store.accepted_tree P ACP acp₀ st hr).2.1
  apply hcoh.1 hX hJ
  rcases Anc.total hcoh hXY hJY with h | h
  · exact hXT.symm.trans ((Th_eq_of_anc hr h hh.symm).symm.trans hJT)
  · exact hXT.symm.trans ((Th_eq_of_anc hr h hh).trans hJT)

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
  {proposer : Nat → Fin sp.n}

private theorem tree_subset_honest {y : Fin sp.n} (hy : y ∈ H) {k : Nat} :
    (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun _ hX => ⟨y, hy, k, hX⟩

/-- **The origin of a record entry** (`record_attestation` is the only writer of the record,
which only an `fg_attest` that signs changes): a target or timeout entry `r` at `h` was the height
pair `(h, r)` of an attestation the node signed earlier, a lock entry `r` at `h` its finality
pair `(h, r)`. -/
theorem client_record_origin_of_run (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H)
    (h r : Nat) : ∀ i,
    ((tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r) ∧
    ((tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r))
  | 0 => by
    rw [Trace.state, hrun.init y hy]
    refine ⟨fun hx => ?_, fun hx => ?_⟩ <;>
      simp [Node.init, FG.Record.empty] at hx
  | i + 1 => by
    obtain ⟨ih₁, ih₂⟩ := client_record_origin_of_run hrun hy h r i
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
      have hlaw := hrun.cutLaw y hy i c hc
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
                · dsimp only [FG.Record.recordAtt] at hx
                  split_ifs at hx
                  · rw [Function.update_apply] at hx
                    split_ifs at hx with hh
                    · exact Or.inr (Or.inr ⟨hh.symm, Option.some.inj hx⟩)
                    · exact Or.inl hx
                  · exact Or.inl hx
                · dsimp only [FG.Record.recordAtt] at hx
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
            · dsimp only [FG.Record.recordAtt] at hx
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

/-- Whole-run reset specialization of actual record provenance. -/
theorem client_record_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) (h r i : Nat) :
    ((tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r) ∧
    ((tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r)) :=
  client_record_origin_of_run hp.run hy h r i

/-- An honest record changes only when the node signs, by recording the signed attestation. -/
theorem record_step_of_run (hrun : GoldilocksRun proposer dg H tr)
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
      · exact Or.inr ⟨a', ⟨C, hc⟩, hsucc ▸ createAtt_record hlaw.1⟩
  · exact Or.inl (by rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩])

/-- The sent contents of an honest record were signed earlier. -/
theorem sent_origin (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {b : FG.Content} : ∀ i, b ∈ (tr.state y i).record.sent →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b
  | 0, hb => by
    rw [Trace.state, hrun.init y hy] at hb
    simp [Node.init, FG.Record.empty] at hb
  | i + 1, hb => by
    rcases record_step_of_run hrun hy i with he | ⟨att, hs, he⟩ <;> rw [he] at hb
    · obtain ⟨k, hk, h⟩ := sent_origin hrun hy i hb
      exact ⟨k, by omega, h⟩
    · rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨k, hk, h⟩ := sent_origin hrun hy i hb
        exact ⟨k, by omega, h⟩
      · exact ⟨i, by omega, att, hs, (List.mem_singleton.1 hb).symm⟩

/-- Honest signatures are well formed using the store at their own signing cut. -/
theorem signAt_wellFormed (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) : att.WellFormed := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw y hy k _ hc).1
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  rcases hsrc : (tr.state y k).fg.blocks src.root with _ | X
  · have hg : ((tr.state y k).fg.σ src.root).Th = sp.genesisRoot := by
      rw [Store.σ_of_blocks_none hr hsrc]; rfl
    rw [hg, Store.σ_genesis hr] at hcl
    exact Compose.createAtt_wellFormed le_rfl Nat.one_pos (by simp [FG.ChainState.init]) hcl
  · have hXr := Goldilocks.Store.Reachable.blocks_root hr hsrc
    have hX : X ∈ (tr.state y k).fg.tree := by
      change (tr.state y k).fg.blocks X.root = some X
      rw [hXr]; exact hsrc
    obtain ⟨⟨E, hE, hEr, -⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hr X hX
    obtain ⟨c, -, -, -, hcs⟩ := Store.chain_state_of_chain _ _ _ _ hr E hE
    obtain ⟨h1, -, h3, -, -, -, -, h8, -⟩ := FG.chain_invariants sp.toParams.fg _ _ hcs
    rw [hXr] at hEr
    rw [← hEr] at hcl
    exact Compose.createAtt_wellFormed h1 h3 (fun p hp => lt_of_le_of_lt (h8 p hp).2 h3) hcl

/-- With no lock at the height, `height_pair` returns that height and target. -/
private theorem heightPair_of_lock_none {Λ : FG.Record} {hc Tc : Nat} (h : Λ.lock hc = none) :
    ∃ τ, Λ.heightPair hc Tc = some (hc, Tc, τ) := by
  unfold FG.Record.heightPair
  simp only [h, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
  split_ifs <;> exact ⟨_, rfl⟩

/-- An honest high FG source forces a reset, even when its client suppresses a new signature. -/
theorem reset_of_high_source (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest C s)))
    (hh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k := by
  classical
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  have he : ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).h =
      ((tr.state y k).fg.σ C.root).h := by
    rcases hC : (tr.state y k).fg.blocks C.root with _ | X
    · rw [Store.σ_of_blocks_none hr hC]
      exact congrArg FG.ChainState.h (Store.σ_genesis hr)
    · have hXr := Goldilocks.Store.Reachable.blocks_root hr hC
      have hX : X ∈ (tr.state y k).fg.tree := by
        change (tr.state y k).fg.blocks X.root = some X
        rw [hXr]; exact hC
      obtain ⟨⟨E, -, hEr, -, hEh, -⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hr X hX
      rw [← hXr, ← hEr]
      exact hEh
  by_cases hprev : ∃ j < k, ∃ att, tr.SignAt y j att ∧ HZ tr H g + 1 ≤ att.h
  · obtain ⟨j, hj, att, hs, hh⟩ := hprev
    obtain ⟨a, ha, haj⟩ := reset_of_height_advance hrun hq hy hs hh
    exact ⟨a, ha, haj.trans (hrun.time_mono hj.le)⟩
  have hlock : (tr.state y k).record.lock ((tr.state y k).fg.σ C.root).h = none := by
    by_contra hn
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hn
    obtain ⟨j, hj, att, hs, hfin⟩ :=
      (client_record_origin_of_run hrun hy _ r k).2 hr
    have hw := (signAt_wellFormed hrun hy hs).2
      (((tr.state y k).fg.σ C.root).h, r) (by simp [hfin])
    exact hprev ⟨j, hj, att, hs, by omega⟩
  have hsent : ∀ b ∈ (tr.state y k).record.sent,
      b.1 ≠ ((tr.state y k).fg.σ C.root).h := by
    intro b hb hbh
    obtain ⟨j, hj, att, hs, hb⟩ := sent_origin hrun hy k hb
    have hah : att.h = b.1 := congrArg Prod.fst hb
    exact hprev ⟨j, hj, att, hs, by omega⟩
  have hany (τ : Bool) : (tr.state y k).record.sent.any (fun b =>
      b.1 = ((tr.state y k).fg.σ C.root).h ∧ (!τ ∨ b.2.1 =
        ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th)) = false := by
    apply List.any_eq_false.2
    intro b hb
    simp [hsent b hb]
  cases s with
  | some att =>
    have hcl := (hrun.cutLaw y hy k _ hc).1
    apply reset_of_height_advance hrun hq hy ⟨C, hc⟩
    rw [(Store.createAtt_eq hcl).1, he]
    exact hh
  | none =>
    have hcl := (hrun.cutLaw y hy k _ hc).1
    exfalso
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    obtain ⟨τ, hτ⟩ := heightPair_of_lock_none
      (Tc := ((tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th).Th) hlock
    unfold FG.Record.createAtt at hcl
    rw [he, hτ] at hcl
    dsimp only at hcl
    rw [hany τ] at hcl
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hcl

/-- **The finality pair of an honest attestation names an entry of its source's chain** (G0.2
(h)): the finality pair `(h, r)` that `fg_attest` signs (the justification of the entry state at an
entry whose previous height is justified, or one of its pending pairs) names the entry at height `h`
of an ancestor-or-self `J` of the source's entry `E` (whose root is the signed `T`). -/
theorem signed_fin_pair_entry_of_run (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att) {h r : Nat}
    (hfin : att.fin = some (h, r)) :
    ∃ J ∈ (tr.state y k).fg.tree, ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧
      (tr.state y k).fg.Anc J E ∧ J.root = r ∧ ((tr.state y k).fg.σ J.root).h = h ∧
      ((tr.state y k).fg.σ J.root).Th = J.root := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw y hy k _ hc).1
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  have hT := (Store.createAtt_eq hcl).2
  have hfp := createAtt_fin hcl
  rw [hfin] at hfp
  rcases hs' : (tr.state y k).fg.blocks src.root with _ | X
  · have hg : ((tr.state y k).fg.σ src.root).Th = sp.genesisRoot := by
      rw [Store.σ_of_blocks_none hr hs']; rfl
    rw [hg, Store.σ_genesis hr] at hfp
    simp [FG.Record.finalityPair, FG.ChainState.previousHeightJustified, FG.ChainState.init] at hfp
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

/-- Reset-premise specialization of the run-only signed finality-pair provenance. -/
theorem signed_fin_pair_entry (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att) {h r : Nat}
    (hfin : att.fin = some (h, r)) :
    ∃ J ∈ (tr.state y k).fg.tree, ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧
      (tr.state y k).fg.Anc J E ∧ J.root = r ∧ ((tr.state y k).fg.σ J.root).h = h ∧
      ((tr.state y k).fg.σ J.root).Th = J.root :=
  signed_fin_pair_entry_of_run hp.run hy hs hfin

/-- Finalizing a strict descendant is witnessed by an actual earlier honest report.
The height comparison is in the reporter's store at the report cut. -/
theorem ResetPremisesUpTo.finalized_descendant_report {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {W X P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) (hX : X ∈ (tr.state y k).fg.tree)
    (hXr : X.root = ((tr.state y k).fg.σ W.root).F)
    (hPX : Anc (tr.HonestBlocks H) P X) (hne : P ≠ X) :
    ∃ z ∈ H, ∃ r ℓ C, r < k ∧ SA.ToFGAt tr.projAC z r ℓ C ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  have hU := hp.honest_coherent
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := tree_subset_honest hy
  obtain ⟨c, hc, -, -, hcs⟩ := Store.chain_state_of_chain _ _ _ _ hr W hW
  have hpos : 1 ≤ ((tr.state y k).fg.σ W.root).hF := by
    by_contra hn
    have hg := (FG.chain_invariants _ _ _ hcs).2.2.2.2.1 (by omega)
    have he := Compose.honest_eq_genesis hp.run hU (hsub hX) (hXr.trans hg)
    rw [he] at hPX
    rcases Relation.ReflTransGen.cases_tail hPX with heq | ⟨Y, _, hY⟩
    · exact hne (heq.symm.trans he.symm)
    · exact absurd hY.2.2 (by simp [Params.genesisBlock])
  obtain ⟨Q, hQ, hrows⟩ := FG.FGParams.finalized_quorum _ hcs hpos
  change Finset (Fin sp.n) at Q
  have hex : ∃ v ∈ Q, v ∈ H := by
    by_contra hn
    have hqsub : (↑Q : Set (Fin sp.n)) ⊆ Hᶜ := fun v hv hvH => hn ⟨v, hv, hvH⟩
    have hh := Set.ncard_le_ncard hqsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hh
    have hf := hp.faults
    have hn : 0 < sp.n := sp.toParams.hn
    change (2 * sp.n + 2) / 3 ≤ Q.card at hQ
    omega
  obtain ⟨v, hvQ, hv⟩ := hex
  obtain ⟨att, hatt, hav, hfin⟩ := hrows v hvQ
  simp only [FG.FGParams.chainAtts, List.mem_flatMap] at hatt
  obtain ⟨Z', hZ', hatt⟩ := hatt
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hZ'
  have haH : att.val ∈ H := hav ▸ hv
  obtain ⟨m, hmk, _, s, hsm, hs⟩ :=
    Compose.honest_row_signed_before hp.run hp.noColl hy (hc Z hZ) hatt haH
  obtain ⟨J, hJ, E, hE, hEr, hJE, hJr, hJh, hJT⟩ :=
    signed_fin_pair_entry_of_run hp.run haH hs hfin
  have hsubs : (tr.state att.val s).fg.tree ⊆ tr.HonestBlocks H := tree_subset_honest haH
  obtain rfl : J = X := hU.1 (hsubs hJ) (hsub hX) (hJr.trans hXr.symm)
  obtain ⟨r, hsr, ht, ℓ, C, E', hto, hC, hE', hE'r, hEC, hTh, hET, hEh, _⟩ :=
    signAt_report_entry hp.run haH hs
  have hsubr : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocks H := tree_subset_honest haH
  have he : E' = E := hU.1 (hsubr hE') (hsubs hE) (hE'r.trans hEr.symm)
  subst E'
  have hXE := hJE.mono hsubs
  have hPC := hPX.trans (hXE.trans (hEC.mono hsubr))
  have hXEr := hp.anc_tree_of_anc haH hXE hE'
  have hXr' := hp.mem_tree_of_anc haH hXE hE'
  have hPXr := hp.anc_tree_of_anc haH hPX hXr'
  have hrr := Compose.fg_reachable hp.run.toLocalRun haH r
  have hPE := hPXr.trans hXEr
  have hle := σ_h_le_of_anc hrr hPE
  have hlt : ((tr.state att.val r).fg.σ P.root).h <
      ((tr.state att.val r).fg.σ E.root).h := by
    apply lt_of_le_of_ne hle
    intro heq
    have hentry := (Th_eq_of_anc hrr hPE heq.symm).symm.trans hET
    have hP := hp.mem_tree_of_anc haH hPC hC
    obtain ⟨⟨E₀, hE₀, hE₀r, hE₀P, _, _⟩, _⟩ :=
      Goldilocks.Store.entry_state_of_source _ _ _ _ hrr P hP
    obtain rfl : E₀ = E := hU.1 (hsubr hE₀) (hsubr hE') (hE₀r.trans hentry)
    exact hne (hPXr.antisymm (hU.mono hsubr) (hXEr.trans hE₀P))
  exact ⟨att.val, haH, r, ℓ, C, by omega, hto, hPC, hlt.trans_eq hEh⟩

/-- The remaining finality-loss obligation is compatibility: a comparable finality
cache either stays below `P` or already witnesses a strictly higher actual report. -/
theorem ResetPremisesUpTo.finality_below_or_higher_report {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcompat : Compatible (tr.HonestBlocks H) (tr.state y k).fg.F P) :
    Anc (tr.HonestBlocks H) (tr.state y k).fg.F P ∨
      ∃ z ∈ H, ∃ r ℓ C, r < k ∧ SA.ToFGAt tr.projAC z r ℓ C ∧
        Anc (tr.HonestBlocks H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  rcases hcompat with h | h
  · exact Or.inl h
  by_cases he : P = (tr.state y k).fg.F
  · exact Or.inl (he ▸ Relation.ReflTransGen.refl)
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  obtain ⟨hF, -, -, -, -, -, W, hW, hWF⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hr
  exact Or.inr (hp.finalized_descendant_report hy hW hF hWF.symm h he)

/-- A signed attestation naming a held entry above the target produces an actual earlier
higher report. The signing witness is retained explicitly; a covering origin alone
does not supply this fact. Heights are compared at the resulting reporter's cut. -/
theorem ResetPremisesUpTo.higher_report_of_signed_entry {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i d : Nat}
    {P E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    {att : FG.Att sp.n} (hs : tr.SignAt z d att) (hdi : d < i)
    (hT : att.T = E.root) (hPE : Anc (tr.HonestBlocks H) P E)
    (hlt : ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ E.root).h) :
    ∃ r ell C, r < i ∧ SA.ToFGAt tr.projAC z r ell C ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  obtain ⟨r, hrd, -, ell, C, E', hto, hC, hE', hEr, hEC, -, -, hEh, -⟩ :=
    signAt_report_entry hp.run hz hs
  obtain rfl : E' = E := hp.honest_coherent.1 ⟨z, hz, r, hE'⟩ ⟨y, hy, i, hE⟩
    (hEr.trans hT)
  have hPC := hPE.trans (hEC.mono (tree_subset_honest hz))
  have hPr := hp.mem_tree_of_anc hz hPC hC
  refine ⟨r, ell, C, by omega, hto, hPC, ?_⟩
  rw [← hEh, hp.σ_eq_run hz hy hPr hP, hp.σ_eq_run hz hy hE' hE]
  exact hlt

/-- Whole-run specialization of the finite finality/report alternative. -/
theorem finality_below_or_higher_report (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcompat : Compatible (tr.HonestBlocks H) (tr.state y k).fg.F P) :
    Anc (tr.HonestBlocks H) (tr.state y k).fg.F P ∨
      ∃ z ∈ H, ∃ r ℓ C, r < k ∧ SA.ToFGAt tr.projAC z r ℓ C ∧
        Anc (tr.HonestBlocks H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h :=
  (ResetPremises.toUpTo tr H hp le_rfl).finality_below_or_higher_report hy hcompat

/-- **A high record entry names an entry of a high origin's chain**: the target, timeout
or lock entry `r` at `h ≥ H_z + 1` of an honest record is the root of a block `Z` below the
block of a high origin, the entry at height `h` of its chain. -/
theorem high_record_entry (hp : ResetPremises tr H proposer dg g ΔF a)
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
theorem ResetPremisesUpTo.entry_root_eq {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H) {m : Nat}
    {C Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state z m).fg.tree)
    (h₁ : Anc (tr.HonestBlocks H) Z₁ C) (h₂ : Anc (tr.HonestBlocks H) Z₂ C)
    (hh : ((tr.state z m).fg.σ Z₁.root).h = ((tr.state z m).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state z m).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state z m).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hz m
  rcases SA.anc_total hp.honest_coherent h₁ h₂ with h | h
  · have := Th_eq_of_anc hr (hp.anc_tree_of_anc hz h (hp.mem_tree_of_anc hz h₂ hC)) hh.symm
    rw [← hT₁, ← hT₂, this]
  · have := Th_eq_of_anc hr (hp.anc_tree_of_anc hz h (hp.mem_tree_of_anc hz h₁ hC)) hh
    rw [← hT₁, ← hT₂, this]

/-- Whole-run specialization of entry constancy. -/
theorem entry_root_eq (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H) {m : Nat}
    {C Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.state z m).fg.tree)
    (h₁ : Anc (tr.HonestBlocks H) Z₁ C) (h₂ : Anc (tr.HonestBlocks H) Z₂ C)
    (hh : ((tr.state z m).fg.σ Z₁.root).h = ((tr.state z m).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state z m).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state z m).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root :=
  (hp.toUpTo tr H (le_refl a)).entry_root_eq hz hC h₁ h₂ hh hT₁ hT₂

end Consensus.Goldilocks.Healing

end
