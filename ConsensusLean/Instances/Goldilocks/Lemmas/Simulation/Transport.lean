module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Evidence
public import ConsensusLean.Spec.Shape.Claims
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs

public section

/-! # R.7/R.8 engine transport

Paper references are CLAIMS `goldilocks-claims.tex` R.7, R.8, F.2/F.3 and G1.5,
and SPEC `shared/composition.tex` §Blocks/§Model, pinned in
`docs/goldilocks-mapping.md` §"AsChainShape, Simulation and Obligations". The proofs separate
structural chains, observed objects, evidence binding and validator counts.

The cited paper establishes the node-level source theorems. The docstrings below supply
separate mathematical arguments for the engine bridges, not quotations.

`NoCollTransport` targets the canonical trace. `GenesisFresh` is proved by tagged roots,
not assumed by accountability. Canonical occurrence coverage includes refused deliveries;
tagging and observed-header injectivity discharge collision transport.
The engine run and provenance suppliers the accountability closure depends on are proved;
no `sorry` remains in that closure. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Tagged node roots exclude genesis even when the raw hash equals it. -/
theorem genesisFresh : GenesisFresh S rho := by
  rw [genesisFresh_iff]
  intro x _
  exact taggedRoot_ne _ _

/-- CLAIMS R.8/F.2: a valid node output has a parent-closed chain with strictly increasing
slots and digest-correct roots. The canonical header walk transports these to `Linked` and
`PosIncreasing`; `held_in_view` supplies the signed proposal provenance. The confirmed read
uses the shape's clock, not the time of the next simulating cut. No collision escape.

Paper argument: for each honest reader choose its positive-cardinality simulation. The final
tip is held by the cache invariant; at ANY clock, `sa_tips` puts the confirmed tip in the frame
and hence the store. `validOutput_of_mem` applies to either. Induct on the tip's slot: genesis
produces the empty chain; a non-genesis tip has a held parent of smaller slot. The recursive
chain ends at that parent's header (or is empty for genesis). `RootOk` identifies its hash
with its node root, so `parentRef` gives exactly the required previous-header reference.
Append the tip; strict parent slots give increasing positions. Fuel exceeds the slot by one.
For every emitted header `mem_chainTo` supplies a held non-genesis block; `held_in_view`
supplies its signed proposer-role object. No global root injectivity is used: coherence is
local to this store. Empty V is vacuous. Status: argument complete for the current encoding;
tagged-root changes must re-establish the parent/hash conversion identities. -/
theorem engine_outputValid (hv : rho.ExecutionValid) (g : Out) : OutputValid rho g := by
  intro v hv' i hi
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hs := simTrace_simulates S rho hn hv
  have hy := honest_ownKey (S := S) hv'
  have hr := Compose.fg_reachable hs.run.toLocalRun hy (cutMap S rho hn i)
  have hhash : ∀ X ∈ ((simTrace S rho hn).state (rho.ownKey v)
      (cutMap S rho hn i)).fg.tree, X.root ≠ (S.params (pubOf E) hn).genesisRoot →
      parentRef (S.params (pubOf E) hn).genesisRoot (some X.root) =
        .digest (rho.hash (headerOf (S.params (pubOf E) hn) X)) := by
    intro X hX hg
    obtain ⟨hroot, _, _, P, _, hpar, _⟩ :=
      (Regimes.validOutput_of_mem hs.run hy hX).2 X .refl hg
    have he : X.root = taggedRoot S.genesisRoot
        (rho.hash (headerOf (S.params (pubOf E) hn) X)) := by
      simp only [Block.RootOk, digestOf_eq] at hroot
      erw [dgOf_eq] at hroot
      simpa [headerOf, hpar] using hroot
    simp only [parentRef, he, rawRoot_taggedRoot, taggedRoot_ne, ite_false]
  let blocks := ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.blocks
  have hvalid : ∀ B ∈ ((simTrace S rho hn).state (rho.ownKey v)
      (cutMap S rho hn i)).fg.tree,
      Chain.Linked rho.hash (chainTo blocks (B.slot + 1) B) ∧
      Chain.PosIncreasing (chainTo blocks (B.slot + 1) B) ∧
      Chain.Provenant (rho.ViewIdx v i) ProposalRole (chainTo blocks (B.slot + 1) B) := by
    intro B hB
    have hstruct := chainTo_append_valid hr rho.hash hhash hB (Nat.lt_succ_self _) []
      trivial trivial
    simp only [List.append_nil] at hstruct
    refine ⟨hstruct.1, hstruct.2, ?_⟩
    intro h hh
    obtain ⟨X, hX, _, hg, rfl⟩ := mem_chainTo hr hB hh
    exact ⟨X.proposer, .proposer X.slot, _, rfl, held_in_view S rho hn hv hv' hX hg⟩
  rw [read_eq_out S rho hn]
  simp only [outOf, hs.state v hv' i hi]
  cases g with
  | finalized => exact hvalid _ (Store.cache_invariants _ _ _ _ hr).1
  | confirmed =>
    have hΦ := (Store.frame_realization _ _ _ _ hr).1
    exact hvalid _ (Regimes.sa_tips hΦ (stateAt S rho hn v i).now).1.1

/-- CLAIMS R.8/C0.1: instantiate engine simulation, then transport node nesting through
`outputs_nested`. The empty-validator case has no readers. No collision escape.
Paper argument: fix a reader, obtain `n ≥ 1`, instantiate `simTrace_simulates`, and apply
`outputs_nested` at the bounded engine cut. That proved bridge uses the actual shape clock
and `chainTo_prefix`; no identification with the next cut's time is necessary.
Status: proved relative to simulation. -/
theorem engine_nested (hv : rho.ExecutionValid) :
    (chainTrace rho).Nested .finalized .confirmed := by
  intro v hv' i hi
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  exact outputs_nested (simTrace_simulates S rho hn hv) v hv' i hi

/-- CLAIMS R.8/C0.2: simulation's monotone cut map and `finalized_monotone` transport the
durable finalized chain across ticks, deliveries and restarts. No collision escape.
Paper argument: a quantified reader supplies `n ≥ 1`. Instantiate `simTrace_simulates` and
apply the proved `finalized_monotone` bridge: node monotonicity at the ordered mapped cuts,
store-growth preservation of the earlier chain, then ancestry-to-prefix. `InCuts` supplies
both read bounds. Empty V is vacuous. Status: argument complete relative to simulation. -/
theorem engine_finalMonotone (hv : rho.ExecutionValid) :
    (chainTrace rho).Monotone .finalized 0 := by
  intro v i j hi hij hj hv' hv''
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  exact finalized_monotone (simTrace_simulates S rho hn hv) v i j hi hij hj hv' hv''

/-- CLAIMS F.3/§Premises, SPEC §Blocks: each occurring block's header is observed; equal
non-genesis digests reduce to equal observed headers and the encoding is injective. Genesis
is handled separately.

Paper argument: `occurring_in_view` proves that EVERY block in the canonical trace's `Occurs`
has an observed canonical header and a nonempty parent (including REFUSED block calls,
not just held blocks).
For two such blocks, equal `dgOf` values are equal header hashes; absence of `HashCollision`
gives equal headers. Apply `parentRoot_parentRef` to the nonempty parents and decode the
equal `encodeInfo` values to recover all five fields required by `NoCollOn`. Proposer identity
is irrelevant: that conclusion does not compare proposers. For genesis versus a non-genesis
block, `GenesisFresh` excludes equal digests; two genesis entries are immediate.
`Occurs` has no honesty guard, but `simTrace_cut` identifies its engine event;
`ExecutionValid.honest_only` then proves that its node is honest. No separate non-honest
canonical call case remains in a valid run. Tick provenance uses `tick_releases` for
either acceptance flag. For deliveries, `mem_deliverRecs_exec` retains decoded-object
membership in the delivered list, including refused calls. The received object's containment
then places the canonical block object in the final engine view without acceptance or relay.
The target no longer quantifies arbitrary simulation witnesses, whose laws do not supply
this provenance.
Tagged freshness is proved by `genesisFresh`; it does not by itself prove occurrence coverage. -/
theorem noCollRun_simTrace (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTrace S rho hn) := by
  have hocc (B : Blk (S.params (pubOf E) hn)) (hB : (simTrace S rho hn).Occurs B) :
      B.parent ≠ none ∧ rho.ObservedItem (headerOf (S.params (pubOf E) hn) B) := by
    obtain ⟨hp, v, hv', hb⟩ := occurring_in_view S rho hn hv hB
    exact ⟨hp, blockObj _ B, ⟨v, hv', hb⟩, rfl⟩
  intro B hB C hC heq
  simp only [digestOf_eq] at heq
  simp only [dgOf_eq (n := Fintype.card V) rho.hash S.genesisRoot] at heq
  rcases hB with rfl | hB <;> rcases hC with rfl | hC
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hp, _⟩ := hocc C hC
    cases hc : C.parent with
    | none => exact False.elim (hp hc)
    | some p =>
      exact False.elim (taggedRoot_ne _ _
        (by simpa [hc, Params.genesisBlock] using heq.symm))
  · obtain ⟨hp, _⟩ := hocc B hB
    cases hb : B.parent with
    | none => exact False.elim (hp hb)
    | some p =>
      exact False.elim (taggedRoot_ne _ _
        (by simpa [hb, Params.genesisBlock] using heq))
  · obtain ⟨hpB, hoB⟩ := hocc B hB
    obtain ⟨hpC, hoC⟩ := hocc C hC
    obtain ⟨pb, hpb⟩ := Option.ne_none_iff_exists'.mp hpB
    obtain ⟨pc, hpc⟩ := Option.ne_none_iff_exists'.mp hpC
    have hh : rho.hash (headerOf (S.params (pubOf E) hn) B) =
        rho.hash (headerOf (S.params (pubOf E) hn) C) := by
      have h := congrArg (rawRoot S.genesisRoot) heq
      simpa [hpb, hpc, headerOf, rawRoot_taggedRoot] using h
    have he : headerOf (S.params (pubOf E) hn) B = headerOf (S.params (pubOf E) hn) C := by
      by_contra h
      exact hnc ⟨_, _, h, hoB, hoC, hh⟩
    have hpar := congrArg (fun h => parentRoot S.genesisRoot h.parent) he
    have hslot := congrArg Header.pos he
    have hin := congrArg Header.input he
    have hinfo := congrArg (fun h => decodeInfo (Fintype.card V) h.info) he
    simp only [headerOf, hpb, hpc, parentRoot_parentRef] at hpar
    simp only [headerOf, decodeInfo_encodeInfo, Option.some.injEq, Prod.mk.injEq] at hinfo
    exact ⟨by simpa [hpb, hpc] using hpar, hslot, hin, hinfo.1, hinfo.2⟩

variable (V) in
/-- Collision transport, bundled over all engine runs. -/
theorem noCollTransport : NoCollTransport V S :=
  (noCollTransport_iff V S).mpr fun _ rho hn => noCollRun_simTrace S rho hn

/-- CLAIMS R.7/G1.3–G1.5: compatibility of honest node tips gives structural compatibility
of their header chains. Parent closure and coherent honest blocks identify the ancestor walk
in either store, even when the readers hold different supersets.

Paper argument: `NoCollRun` makes the union of honest held blocks coherent. Each local tree
is parent-closed to the same genesis. For a tip shared by two trees, backward induction on
its slot identifies the parents in both trees by coherent roots, hence their entire chains
agree. If tip A is an ancestor of tip B in the honest union, follow B's local parent chain:
coherence identifies every union-path predecessor, so A and its chain occur as a prefix
there. Compare with A's reader using the shared-tip result. Handle either ancestry direction
and use `read_finalized` at the bounded cuts. Status: argument complete relative to coherent
honest blocks; the cross-store parent-walk lemma is proved. -/
theorem compatible_reads (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {u v : V} (hu : u ∈ rho.honest) (hv' : v ∈ rho.honest) {i j : Nat}
    (hi : i ≤ rho.events.length) (hj : j ≤ rho.events.length)
    (hc : Compatible ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i))
      ((simTrace S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j))) :
    Consensus.Compatible ((chainTrace rho).read .finalized u i)
      ((chainTrace rho).read .finalized v j) := by
  have hs := simTrace_simulates S rho hn hv
  have hu' := honest_ownKey (S := S) hu
  have hv'' := honest_ownKey (S := S) hv'
  have hri := Compose.fg_reachable hs.run.toLocalRun hu' (cutMap S rho hn i)
  have hrj := Compose.fg_reachable hs.run.toLocalRun hv'' (cutMap S rho hn j)
  have hU := Compose.honest_blocks_coherent hs.run.toLocalRun hnc
  have hsi : ((simTrace S rho hn).state (rho.ownKey u) (cutMap S rho hn i)).fg.tree ⊆
      (simTrace S rho hn).HonestBlocks (honestKeys S rho) := fun _ h => ⟨_, hu', _, h⟩
  have hsj : ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn j)).fg.tree ⊆
      (simTrace S rho hn).HonestBlocks (honestKeys S rho) := fun _ h => ⟨_, hv'', _, h⟩
  have hFi := (Store.cache_invariants _ _ _ _ hri).1
  have hFj := (Store.cache_invariants _ _ _ _ hrj).1
  rw [read_finalized hs hu hi, read_finalized hs hv' hj]
  rcases hc with hc | hc
  · left
    have ha := anc_in_store hrj hU hsj hc hFj
    have hm : (simTrace S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i) ∈
        ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn j)).fg.tree := by
      by_cases he : (simTrace S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i) =
          (simTrace S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j)
      · exact he ▸ hFj
      · exact (Anc.mem ha he).1
    simp only [RunTrace.finalizedAt]
    rw [chainTo_agree hri hrj hU hsi hsj hFi hm]
    exact chainTo_prefix hrj ha
  · right
    have ha := anc_in_store hri hU hsi hc hFi
    have hm : (simTrace S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j) ∈
        ((simTrace S rho hn).state (rho.ownKey u) (cutMap S rho hn i)).fg.tree := by
      by_cases he : (simTrace S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j) =
          (simTrace S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i)
      · exact he ▸ hFi
      · exact (Anc.mem ha he).1
    simp only [RunTrace.finalizedAt]
    rw [chainTo_agree hrj hri hU hsj hsi hFj hm]
    exact chainTo_prefix hri ha

omit [DecidableEq V] in
/-- CLAIMS G1.5's validator-count step:
`conflicts_iff` gives E1/E2 on the two canonical attestation objects; their signed poll keys
are transported by `rho.key`. Its injectivity preserves distinct witnesses in the count.

Paper argument: for each `k ∈ W`, take its witnesses a,b. `slashable a b` includes
`a.val = b.val`; with `a.val = k`, both canonical objects have signer `rho.key k`.
`conflicts_iff` makes their conflict test true, so `rho.Slashable A (rho.key k)` holds.
Thus the finset image of W under the equivalence `rho.key` is contained in `convicted ... A`.
Injectivity gives image cardinality `W.card`; finset cardinal monotonicity gives the bound.
No execution validity, honesty, collision freedom or nonempty-V premise is needed.
Status: proved directly from definitions. -/
theorem convicted_count {A : Set (Model.protoOf (compiled (goldilocks S)) E).Object}
    (W : Finset (Fin (Fintype.card V)))
    (hw : ∀ k ∈ W, ∃ a b : FG.Att (Fintype.card V),
      attObj a ∈ A ∧ attObj b ∈ A ∧ a.val = k ∧ FG.slashable a b) :
    W.card ≤ (convicted rho.Slashable A).card := by
  classical
  have hsub : W.image rho.key ⊆ convicted rho.Slashable A := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, b, ha, hb, hak, hab⟩ := hw k hk
    have hbk : b.val = k := hab.1.symm.trans hak
    simp only [convicted, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨attObj a, ha, attObj b, hb, ?_, ?_, ?_⟩
    · simp [Model.Run.signerOf, attObj, Model.Obj.signer?, Model.Obj.auth, hak]
    · simp [Model.Run.signerOf, attObj, Model.Obj.signer?, Model.Obj.auth, hbk]
    · exact (conflictsIff_iff.mp conflicts_iff _ _ _).mpr ⟨a, b, rfl, rfl, hab⟩
  simpa only [Finset.card_image_of_injective W rho.key.injective] using
    Finset.card_le_card hsub

/-- CLAIMS R.7/G1.5: bind every witness attestation on the TWO HELD CHAINS from
`Regimes.final_accountable` via `held_att_in_view`; `conflicts_iff` converts slashability,
and the run's key equivalence preserves the number of distinct convicted validators.

Paper argument: split on compatibility of the two finalized node tips. In the compatible
case use `compatible_reads`. Otherwise `Regimes.final_accountable` yields held X₁,X₂ and
a finset W of at least `2q−n` keys, with slashable attestation witnesses in `ChainAtts` of
those blocks. Each `ChainAtts` membership includes a held block Y containing the attestation;
`held_att_in_view` places it in the appropriate reader's view, hence in their union. Apply
`convicted_count` to W and compose the bounds. X₁,X₂ need not be finalized ancestors.
Status: argument complete relative to the named simulation/evidence/compatibility bridges. -/
theorem final_accountable_of_noColl (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {u v : V} (hu : u ∈ rho.honest) (hv' : v ∈ rho.honest) {i j : Nat}
    (hi : i ≤ rho.events.length) (hj : j ≤ rho.events.length) :
    Consensus.Compatible ((chainTrace rho).read .finalized u i)
        ((chainTrace rho).read .finalized v j) ∨
      2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V ≤
        (convicted rho.Slashable (rho.ViewIdx u i ∪ rho.ViewIdx v j)).card := by
  classical
  by_cases hc : Compatible ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i))
      ((simTrace S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j))
  · exact Or.inl (compatible_reads S rho hn hv hnc hu hv' hi hj hc)
  · right
    obtain ⟨X, _, Y, _, W, hW, hw⟩ := Regimes.final_accountable _ _ _ _ _ _
      (simTrace_goldilocksRun S rho hn hv) hnc _ (honest_ownKey (S := S) hu)
      _ (honest_ownKey (S := S) hv') _ _ hc
    have hmem : ∀ a ∈ Regimes.ChainAtts (simTrace S rho hn) (rho.ownKey u)
        (cutMap S rho hn i) X ∪ Regimes.ChainAtts (simTrace S rho hn) (rho.ownKey v)
        (cutMap S rho hn j) Y, attObj a ∈ rho.ViewIdx u i ∪ rho.ViewIdx v j := by
      intro a ha
      rcases ha with ⟨B, hB, _, ha⟩ | ⟨B, hB, _, ha⟩
      · exact Or.inl (held_att_in_view S rho hn hv hu hB ha)
      · exact Or.inr (held_att_in_view S rho hn hv hv' hB ha)
    refine hW.trans (convicted_count S rho W ?_)
    intro k hk
    obtain ⟨a, ha, b, hb, hak, hab⟩ := hw k hk
    exact ⟨a, b, hmem a ha, hmem b hb, hak, hab⟩

variable (V) in
/-- CLAIMS Refinement G1.5 (c), R.7: assemble simulation, collision transport, structural
compatibility and held-chain evidence/count transport.
Paper reduction: choose the canonical simulation, obtain its `NoCollRun` using
`noCollTransport`, then use `final_accountable_of_noColl` at the two bounded cuts.
Canonical collision transport is proved. No freshness premise remains. -/
theorem finalizedAccountable : FinalizedAccountable V S := by
  rw [finalizedAccountable_iff]
  intro E rho hn hv hnc u hu v hv' i hi j hj
  exact final_accountable_of_noColl S rho hn hv
    (noCollRun_simTrace S rho hn hv hnc)
    hu hv' hi hj

section Claims

variable (V)

/-- R.8 output validity, exact first `ShapeClaimsAt` field. Paper argument for the engine
bridge: instantiate `engine_outputValid` at every provided capability/output and valid run.
No nonempty-validator premise and no hash-collision escape. Unfold `HoldsAlways` and `Sys`:
the valid-run hypothesis is `ExecutionValid`. Apply `engine_outputValid` to the quantified g;
it covers both outputs, so the capability lookup hypothesis needs no additional reasoning.
Status: argument complete relative to `engine_outputValid`. -/
theorem shape_outputValid : (Sys (goldilocks S) V).HoldsAlways
    (fun r => ∀ c g, schema.output c = some g → OutputValid r.2 g) := by
  intro r hv c g _
  exact engine_outputValid S r.2 hv g

/-- R.8 nesting, exact second `ShapeClaimsAt` field. Paper argument for the engine bridge:
the schema aliases available/stable to confirmed and maps final to finalized; the only
strict-rank nontrivial pair is finalized-prefix-confirmed (`engine_nested`). Enumerate the
three increasing capability pairs: final/stable and final/available use `engine_nested`;
stable/available compare confirmed with itself by reflexive prefix. Lookup equalities fix
g₁,g₂, and `HoldsAlways` supplies execution validity. Status: argument complete. -/
theorem shape_nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank →
    schema.output c₁ = some g₁ → schema.output c₂ = some g₂ →
      (Sys (goldilocks S) V).HoldsAlways (fun r => (chainTrace r.2).Nested g₁ g₂) := by
  intro c₁ c₂ g₁ g₂ hr h₁ h₂ r hv
  cases c₁ <;> cases c₂ <;> simp only [Capability.rank] at hr <;> try omega
  all_goals have he₁ := Option.some.inj h₁
  all_goals have he₂ := Option.some.inj h₂
  all_goals cases he₁; cases he₂
  · intro v _ i _
    exact ⟨[], by simp⟩
  · exact engine_nested S r.2 hv
  · exact engine_nested S r.2 hv

/-- R.8 final monotonicity, exact third `ShapeClaimsAt` field. Paper argument: the lookup
equality forces g=finalized. Unfold `HoldsAlways` to obtain execution validity, then apply
`engine_finalMonotone`. No extra regime or collision premise. Status: argument complete. -/
theorem shape_finalMonotone : ∀ g, schema.output .final = some g →
    (Sys (goldilocks S) V).HoldsAlways (fun r => (chainTrace r.2).Monotone g 0) := by
  intro g hg r hv
  have hg' : g = .finalized := (Option.some.inj hg).symm
  subst g
  exact engine_finalMonotone S r.2 hv

/-- R.7/G1.1/G1.5, exact fourth `ShapeClaimsAt` field for any contract with `α ≤ 1/3`.
Paper reduction for the engine bridge: `q = ceil(2n/3)` gives `n/3 ≤ 2q−n`, and key
equivalence preserves conviction counts. Only this field permits the collision escape.
Canonical collision transport includes all-occurrences provenance.
This endpoint intentionally has no freshness premise, including for the empty validator set.
After a freshness-free collision transport is available, split on `HashCollision`; return
that excuse when present. Otherwise obtain the natural-number accountability bound for each
pair of honest reads. Write n=3m+r with r=0,1,2: `2q−n` is respectively m,m+1,m+2, so its
rational cast is at least n/3. Since n≥0 and α≤1/3, nα≤n/3, which gives the exact field.
Empty V has no honest reader and is vacuous. The assembly and arithmetic are proved. -/
theorem shape_finalAccountable (K : Contract ProgressReq) (hα : K.params.α ≤ 1 / 3) :
    ∀ g, schema.output .final = some g → (Sys (goldilocks S) V).Holds (fun _ => True)
      (fun r => (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable K.params.α g 0) := by
  intro g hg r hv _
  have hg' : g = .finalized := (Option.some.inj hg).symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  intro u hu v hv' i j hi hj
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  rcases (finalizedAccountable_iff V S).mp (finalizedAccountable V S)
      r.1 r.2 hn hv hc u hu v hv' i hi.1 j hj.1 with h | h
  · exact Or.inl h
  right
  have hq : Fintype.card V ≤
      3 * (2 * (S.params (pubOf r.1) hn).toParams.q - Fintype.card V) := by
    simp only [Params.q]
    omega
  have hq' : (Fintype.card V : ℚ) ≤
      3 * ((2 * (S.params (pubOf r.1) hn).toParams.q - Fintype.card V : Nat) : ℚ) := by
    exact_mod_cast hq
  have h' : ((2 * (S.params (pubOf r.1) hn).toParams.q - Fintype.card V : Nat) : ℚ) ≤
      (convicted r.2.Slashable (r.2.ViewIdx u i ∪ r.2.ViewIdx v j)).card := by
    exact_mod_cast h
  have hα' := mul_le_mul_of_nonneg_left hα (show (0 : ℚ) ≤ Fintype.card V by positivity)
  linarith

end Claims

end Consensus.Goldilocks.Simulation

end
