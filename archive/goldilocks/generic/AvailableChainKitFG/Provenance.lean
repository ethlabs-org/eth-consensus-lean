module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.Certificates
public import AvailableChainKitFG.ClientSafety

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-! # `fg.provenance.v2`: honest row, entry and finality provenance (pure FG)

(1) every target, progress or finality QC has an honest row, since `q_F > a`;
(2) an honest height row names the entry `T = σ[C].T_h` of the signer's
source C, so `T ⪯ C`; (3) a finality row names the justified pair `(h_j, J)`
of the signer's head state; hence a finality QC names an already justified
entry, with an earlier target QC. -/

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

omit [DecidableEq V] [RowCodec V] in
/-- [pin fg.provenance.v2] (1) Every quorum of rows contains a row of a signer
outside a set of weight below q. -/
theorem provenance_honestRow (E : Electorate V) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (rows : Finset (Row V)) (Q : Finset V)
    (hQ : E.IsQuorum Q) (hrows : ∀ i ∈ Q, ∃ a ∈ rows, a.signer = i) :
    ∃ a ∈ rows, a.signer ∉ faulty := by
  obtain ⟨i, hiQ, hif⟩ := honest_in_quorum E faulty hQ hcap
  obtain ⟨a, ha, hai⟩ := hrows i hiQ
  exact ⟨a, ha, hai ▸ hif⟩

/-- [pin fg.provenance.v2] (2) A row made by `createRow` from source block C
names the entry of C's state at C's height, and that entry is a prefix of C. -/
theorem provenance_entry (E : Electorate V) (cfg : FGConfig) (Λ : Record) (i : V)
    (C : FGBlock V) (hd : HeadFields) :
    ∀ h T t, (createRow E cfg Λ i (some C) hd).1.height_pair = .vote h T t →
      h = (derive E cfg C).h ∧ T = (derive E cfg C).T_h.root ∧
        FGBlock.Preceq (derive E cfg C).T_h C := by
  intro h T t hp
  unfold createRow at hp
  dsimp only at hp
  have hf := height_pair_vote_fields hp
  injection hf with hf'
  injection hf' with h1 h2
  exact ⟨h1.symm, h2.symm, entry_preceq E cfg C⟩

/-- [pin fg.provenance.v2] (3) A finality row made with the head fields of a
block Hd names Hd's justified pair, above Hd's finalized height, and that pair
has a target quorum on Hd's chain. -/
theorem provenance_finalityRow (E : Electorate V) (cfg : FGConfig) (Λ : Record) (i : V)
    (src : Option (FGBlock V)) (Hd : FGBlock V) (p : FinalityPair)
    (hp : (createRow E cfg Λ i src (HeadFields.ofBlock E cfg Hd)).1.finality_pair = some p) :
    p.height = (derive E cfg Hd).h_j ∧ p.target = (derive E cfg Hd).J.root ∧
      (derive E cfg Hd).h_F < p.height ∧
      ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ j ∈ Q, ∃ carrier a,
        FGBlock.Preceq carrier Hd ∧ a ∈ carrier.rows ∧ a.signer = j ∧
        a.height_pair = .vote p.height p.target false := by
  have hp' : finality_pair Λ (HeadFields.ofBlock E cfg Hd) = some p := hp
  unfold finality_pair HeadFields.ofBlock at hp'
  dsimp only at hp'
  split at hp'
  · rename_i hg
    cases hp'
    have hnz : (derive E cfg Hd).h_j ≠ 0 := by
      have h1 := hg.1
      unfold Height at h1 ⊢
      omega
    exact ⟨rfl, rfl, hg.1, justification_certificate E cfg Hd hnz⟩
  · cases hp'

/-- [pin fg.provenance.v2] (3), QC form. A finality QC for p has an honest row.
If every honest row was made by `createRow` with the head fields of some block
(`hemit`, an emission fact of the comp layer), then p is justified with a
target quorum on the chain of such a head block. -/
theorem provenance_finalityQC (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (rows : Finset (Row V)) (Q : Finset V)
    (hQ : E.IsQuorum Q) (p : FinalityPair)
    (hrows : ∀ j ∈ Q, ∃ a ∈ rows, a.signer = j ∧ a.finality_pair = some p)
    (hemit : ∀ a ∈ rows, a.signer ∉ faulty →
      ∃ Λ src Hd, a = (createRow E cfg Λ a.signer src (HeadFields.ofBlock E cfg Hd)).1) :
    ∃ Hd : FGBlock V, p.height = (derive E cfg Hd).h_j ∧ p.target = (derive E cfg Hd).J.root ∧
      ∃ Q' : Finset V, E.IsQuorum Q' ∧ ∀ j ∈ Q', ∃ carrier a,
        FGBlock.Preceq carrier Hd ∧ a ∈ carrier.rows ∧ a.signer = j ∧
        a.height_pair = .vote p.height p.target false := by
  obtain ⟨i, hiQ, hif⟩ := honest_in_quorum E faulty hQ hcap
  obtain ⟨a, ha, hai, hafp⟩ := hrows i hiQ
  have haf : a.signer ∉ faulty := hai ▸ hif
  obtain ⟨Λ, src, Hd, heq⟩ := hemit a ha haf
  have hp : (createRow E cfg Λ a.signer src (HeadFields.ofBlock E cfg Hd)).1.finality_pair =
      some p := by rw [← heq]; exact hafp
  obtain ⟨h1, h2, -, h4⟩ := provenance_finalityRow E cfg Λ a.signer src Hd p hp
  exact ⟨Hd, h1, h2, h4⟩

/-- [helper] A finalized checkpoint on a chain was justified on that chain
before, at the same height. (Not a pin: the registry clause (3) is about
emitted finality rows and QCs, which `provenance_finalityRow` and
`provenance_finalityQC` state.) -/
theorem provenance_finality (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hnz : (derive E cfg D).h_F ≠ 0) :
    ∃ C, FGBlock.Preceq C D ∧ (derive E cfg C).J = (derive E cfg D).F ∧
      (derive E cfg C).h_j = (derive E cfg D).h_F := by
  induction D with
  | genesis => exact absurd rfl hnz
  | node p s r_s r rs ih =>
      obtain ⟨-, -, -, hJ, hhj, hF, hhF⟩ := foldRows_fields (derive E cfg p) (.node p s r_s r rs) rs
      rw [derive_node] at hnz ⊢
      rcases finality_pair_cases E cfg (foldRows (derive E cfg p) (.node p s r_s r rs) rs) with
        ⟨h1, h2⟩ | ⟨h1, h2, -⟩
      · have hnz' : (derive E cfg p).h_F ≠ 0 := by
          rw [h2, hhF] at hnz
          exact hnz
        obtain ⟨C, hCp, hCJ, hCh⟩ := ih hnz'
        exact ⟨C, preceq_node_of_preceq s r_s r rs hCp,
          hCJ.trans (h1.trans hF).symm, hCh.trans (h2.trans hhF).symm⟩
      · exact ⟨p, preceq_parent_node p s r_s r rs, (h1.trans hJ).symm, (h2.trans hhj).symm⟩

end AvailableChain.KitFG
end
