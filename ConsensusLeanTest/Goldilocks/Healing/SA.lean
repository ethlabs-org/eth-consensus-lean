module
public import ConsensusLeanTest.Goldilocks.Runs.SAHealing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # The SA live-run healing witness: `Geo`, `Inv`, H.1 and H.2 (i)

Over an AC trace of the SA with the parameters of `Goldilocks/AC/Base` (one validator `v0`, `Δ = 1`,
`t_s = 4s`, `k = c = 2`), honest set `univ`, proposer `v0` in every slot and `g = 0`, given the run
facts `RunFacts` of the concrete live run (`Goldilocks/Runs/SAHealing`): H.1's premises
(`StandaloneRun`), four cuts per integer time, the frame blocks genesis and `block s` (`s > 0`),
the own block of slot `s` accepted at cut `16s + 2`, the proposal call at cut `16s + 1`, every
frame rooted at genesis, and `block s` the honest proposal of slot `s`. From these alone:

* `geo`: `Geo(block p)` for every `p ≥ 1`. No vote of slot `p` is cast before the own block at
  `16p + 2`: a cast at `t_p < t_p + Δ` is ready (`cast_ready`), but the frame then holds no block
  of slot `p`. After it, the voter's tree is the proposer's plus `block p`.
* `inv`: `Inv(0)`. Every protected `(B, j)` has `j ≥ 1` and `B` genesis or accepted before
  `t_j + 2Δ` (P1, P2: the writer's counted head, `raw_writer_relay_source`; P3: the proposal's own
  acceptance), so `B` is in every later frame and viable at every later vote
  (`viable_of_accepted`).
* H.1 (`ac_healing_standalone`): every slot-`p` vote is `block p` for `p ≥ 8`, and `block p` is
  confirmed from `t_p + 6Δ`; at `p = 8` a vote exists (`vote8`) and the confirmation holds from
  time `38` (`confirmed38`). Its corollary with `Prop(4)` (`proposerBound`): from `t ≥ 32`,
  an honest proposal in `[t, t + 4]` is confirmed from `t + 10` (`corollary42` at `t = 32`).
* H.1 at `ḡ + (8k + 4)Δ` (`ac_healing_standalone_tight`): the same from `p ≥ 5`
  (`healing_tight_live_witness`: a vote of slot `5` and the confirmation by the tick at `26`),
  and proposal-block inclusion from `t + 10` for `t ≥ 20` (`common_confirmed_from30`).
* H.2 (i) (`ac_inclusion` with `t₀ = 0`, `inv` and `geo`): every slot-`p` vote is `block p` for
  `p ≥ 8`. -/

namespace Consensus.Goldilocks.SA.Test.SAHealing

open Consensus.Goldilocks

theorem Δ1 : sp1.Δ = 1 := rfl

theorem ts1 (a : Int) : sp1.ts a = 4 * a := by
  simp only [SAParams.ts, Δ1]; ring

theorem Θ1 : Θ sp1 = 12 := by
  unfold Θ; rw [Δ1]; norm_num

theorem gbar0 : gbar 0 = 0 := by simp [gbar]

/-- The facts of the concrete live run that the witness reads. -/
structure RunFacts (tr : SATrace sp1 Unit ro1) (U : Set (Blk sp1.n Unit))
    (block : Nat → Blk sp1.n Unit) : Prop where
  run : StandaloneRun tr Set.univ U (fun _ => v0) 0
  time : ∀ i, tr.time i = ((i / 4 : Nat) : Int)
  U_eq : U = insert Test.g {B | ∃ s : Nat, 0 < s ∧ B = block s}
  slot : ∀ s, 0 < s → (block s).slot = s
  accept : ∀ i B, tr.AcceptAt v0 i B ↔ ∃ s : Nat, 0 < s ∧ i = 16 * s + 2 ∧ B = block s
  proposal : ∀ i ℓ, tr.CallAt v0 i ℓ → (ℓ.call = .proposal ↔ ∃ s : Nat, 0 < s ∧ i = 16 * s + 1)
  F : ∀ i ℓ, tr.CallAt v0 i ℓ → ℓ.frame.F = Test.g
  honest : ∀ s, 0 < s → HonestProposal tr v0 s (block s)

namespace RunFacts

variable {tr : SATrace sp1 Unit ro1} {U : Set (Blk sp1.n Unit)} {block : Nat → Blk sp1.n Unit}

/-- The frame tree of a call at cut `j`: genesis and the blocks accepted by then. -/
theorem mem_tree (h : RunFacts tr U block) {j : Nat} {ℓ : ACLabel (goldilocksSA sp1 Unit ro1)}
    (hc : tr.CallAt v0 j ℓ) (X : Blk sp1.n Unit) :
    X ∈ ℓ.frame.tree ↔ X = Test.g ∨ ∃ s, 0 < s ∧ 16 * s + 2 ≤ j ∧ X = block s := by
  obtain ⟨-, -, -, htree⟩ := h.run.trivial v0 trivial j ℓ hc
  rw [htree, h.F j ℓ hc, Set.mem_insert_iff]
  constructor
  · rintro (rfl | ⟨k, hk, hacc⟩)
    · exact Or.inl rfl
    · obtain ⟨s, hs, rfl, rfl⟩ := (h.accept k X).1 hacc
      exact Or.inr ⟨s, hs, hk, rfl⟩
  · rintro (rfl | ⟨s, hs, hle, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨16 * s + 2, hle, (h.accept _ _).2 ⟨s, hs, rfl, rfl⟩⟩

theorem g_mem (h : RunFacts tr U block) : Test.g ∈ U := by
  rw [h.U_eq]; exact Set.mem_insert _ _

/-- A block of `U` with the genesis root is genesis. -/
theorem eq_g (h : RunFacts tr U block) {B : Blk sp1.n Unit} (hB : B ∈ U)
    (hr : B.root = sp1.genesisRoot) : B = Test.g :=
  h.run.run.localRun.coherent.1 hB h.g_mem hr

/-- Genesis has no parent: its only ancestor is itself. -/
theorem anc_g {B : Blk sp1.n Unit} (hB : Anc U B Test.g) : B = Test.g := by
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hB with he | ⟨c, -, hp⟩
  · exact he.symm
  · exact absurd hp.2.2 (by simp [Test.g])

/-- A block below a writer's counted head is genesis or accepted before the head's bound. -/
theorem of_relay (h : RunFacts tr U block) {B D : Blk sp1.n Unit} {T : Time} (hDU : D ∈ U)
    (hBD : Anc U B D)
    (hsrc : D.root = sp1.genesisRoot ∨ ∃ q, tr.AcceptAt v0 q D ∧ tr.time q < T) :
    B = Test.g ∨ ∃ k, tr.AcceptAt v0 k B ∧ tr.time k < T := by
  have hr := h.run.run.localRun
  rcases hsrc with hg | ⟨q, hq, hqt⟩
  · obtain rfl := h.eq_g hDU hg
    exact Or.inl (anc_g hBD)
  · obtain ⟨ℓq, hcq, hcall⟩ := hq
    have hD := (accept_new sp1 hr trivial ⟨ℓq, hcq, hcall⟩).1 ℓq hcq
    rcases trivial_anc_mem h.run trivial hcq hD hBD with hF | ⟨k', hk', hacc⟩
    · exact Or.inl (hF.trans (h.F _ _ hcq))
    · exact Or.inr ⟨k', hacc, lt_of_le_of_lt (hr.time_mono hk') hqt⟩

/-- **The protected blocks of `𝒫(0)`**: a label `j ≥ 1`, and the block is genesis or accepted
before `t_j + 2Δ`. -/
theorem protected_source (h : RunFacts tr U block) {B : Blk sp1.n Unit} {j : Nat}
    (hB : Protected (fun _ => v0) tr Set.univ 0 B j) :
    1 ≤ j ∧ (B = Test.g ∨ ∃ k, tr.AcceptAt v0 k B ∧ tr.time k < sp1.ts j + 2 * sp1.Δ) := by
  have hr := h.run.run.localRun
  unfold Protected at hB
  rcases hB with ⟨x, -, i, CV, -, hfl, hts⟩ | ⟨x, -, i, -, hsl, hts⟩ | ⟨-, hP, hts, -⟩
  · obtain rfl := eq_zero x
    rw [ts1, Δ1] at hts
    refine ⟨by dsimp only [Time] at *; omega, ?_⟩
    obtain ⟨-, -, D, hDU, -, hBD, hsrc⟩ :=
      Healing.raw_writer_relay_source (by decide) hr trivial
        (Or.inr hfl) Relation.ReflTransGen.refl
    exact h.of_relay hDU hBD hsrc
  · obtain rfl := eq_zero x
    rw [ts1, Δ1] at hts
    refine ⟨by dsimp only [Time] at *; omega, ?_⟩
    obtain ⟨ℓ, C, hu, hC, hdeep⟩ := hsl
    have hBp := (deepest_mem hdeep).1.1
    obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr trivial hu.1
    obtain ⟨-, -, D, hDU, -, hBD, hsrc⟩ :=
      Healing.raw_writer_relay_source (by decide) hr trivial
        (Or.inl ⟨ℓ, hu, hC, rfl⟩) (hBp.2.2.mono hΦU)
    exact h.of_relay hDU hBD hsrc
  · rw [Θ1, Δ1, ts1] at hts
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j', -, hacc, htj⟩ := hP
    refine ⟨by dsimp only [Time] at *; omega, Or.inr ⟨j', hacc, ?_⟩⟩
    rw [htj, Δ1]
    linarith

/-- **`Geo(block p)`** for every slot `p ≥ 1`. -/
theorem geo (h : RunFacts tr U block) {p : Nat} (hp : 0 < p) :
    Geo (fun _ => v0) tr Set.univ p (block p) := by
  intro k ℓP hcP hprop htk y _ i ℓ e hcast hes
  obtain rfl := eq_zero y
  have hS := h.run
  have hr := hS.run.localRun
  obtain ⟨s, hs0, rfl⟩ := (h.proposal k ℓP hcP).1 hprop
  rw [h.time, ts1] at htk
  obtain rfl : s = p := by dsimp only [Time] at *; omega
  obtain ⟨-, hsl, -, -⟩ := castAt_spec hr trivial hcast
  have hlo : sp1.ts (s : Int) ≤ tr.time i :=
    (ts_le_iff_le_slot sp1 (hr.time_nonneg i) _).2 (by rw [← hsl, hes])
  have hhi : ¬ sp1.ts ((s : Int) + 1) ≤ tr.time i := fun h' => by
    have := (ts_le_iff_le_slot sp1 (hr.time_nonneg i) _).1 h'
    rw [← hsl, hes] at this
    dsimp only [Time] at *; omega
  rw [h.time, ts1] at hlo hhi
  have hi : 16 * s ≤ i ∧ i < 16 * s + 16 := by dsimp only [Time] at *; omega
  obtain ⟨-, -, hvh, -⟩ := hS.trivial v0 trivial i ℓ hcast.1
  obtain ⟨-, -, hvhP, -⟩ := hS.trivial v0 trivial (16 * s + 1) ℓP hcP
  -- the own block is in the voter's frame: an earlier cast would be ready without it
  have hready : 16 * s + 2 ≤ i := by
    by_contra hlt
    obtain ⟨P', hP', hP's, -⟩ := cast_ready hr trivial hcast (by
      rw [hes, h.time, ts1, Δ1]; push_cast; dsimp only [Time] at *; omega)
    rw [hes] at hP's
    rcases (h.mem_tree hcast.1 P').1 hP' with rfl | ⟨s', hs', hle, rfl⟩
    · simp [Test.g] at hP's; dsimp only [Time] at *; omega
    · rw [h.slot s' hs'] at hP's; dsimp only [Time] at *; omega
  refine ⟨?_, fun X hX hXP => ?_⟩
  · rw [hvh, h.mem_tree hcast.1]
    exact Or.inr ⟨s, hs0, hready, rfl⟩
  · rw [hvh, hvhP]
    have hXt := hX.1
    refine ⟨fun _ => ?_, fun _ => hXt⟩
    rcases (h.mem_tree hcast.1 X).1 hXt with rfl | ⟨s', hs', hle, rfl⟩
    · exact (h.mem_tree hcP _).2 (Or.inl rfl)
    · have hne : s' ≠ s := fun he => hXP (by rw [he])
      exact (h.mem_tree hcP _).2 (Or.inr ⟨s', hs', by dsimp only [Time] at *; omega, rfl⟩)

/-- **`Inv(0)`**: every protected block is in every later frame and viable at every later vote. -/
theorem inv (h : RunFacts tr U block) : Inv (fun _ => v0) tr Set.univ U 0 := by
  intro B j hB y _ i ℓ hc hti
  obtain rfl := eq_zero y
  have hS := h.run
  have hr := hS.run.localRun
  obtain ⟨hj1, hsrc⟩ := h.protected_source hB
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr trivial hc
  obtain ⟨-, hfc, hvh, -⟩ := hS.trivial v0 trivial i ℓ hc
  have hti' := hti
  rw [h.time, ts1] at hti'
  push_cast at hti'
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hsrc with rfl | ⟨k, hk, hkt⟩
    · exact (h.mem_tree hc _).2 (Or.inl rfl)
    · obtain ⟨s, hs, rfl, rfl⟩ := (h.accept k B).1 hk
      rw [h.time, ts1, Δ1] at hkt
      exact (h.mem_tree hc _).2 (Or.inr ⟨s, hs, by dsimp only [Time] at *; omega, rfl⟩)
  refine ⟨Or.inr ⟨hBt, by rw [hfc]; exact hΦ.rooted.2 B hBt, B, hBt, by rw [hvh]; exact hBt,
    Relation.ReflTransGen.refl⟩, fun e he => ?_⟩
  have hcast : CastAt tr v0 i ℓ e := ⟨hc, he⟩
  obtain ⟨-, hsl, -, -⟩ := castAt_spec hr trivial hcast
  have hsj : j + 1 ≤ e.msg.slot := by
    have := (ts_le_iff_le_slot sp1 (hr.time_nonneg i) ((j + 1 : Nat) : Int)).1 hti
    rw [hsl]
    dsimp only [Time] at *; omega
  obtain ⟨σ, hσ⟩ : ∃ σ, e.msg.slot = σ + 1 := ⟨e.msg.slot - 1, by omega⟩
  have hacc : AcceptedBefore tr v0 B (sp1.ts σ + 3 * sp1.Δ) := by
    rcases hsrc with rfl | ⟨k, hk, hkt⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨k, hk, ?_⟩
      rw [ts1, Δ1] at hkt ⊢
      push_cast at hkt ⊢
      dsimp only [Time] at *; omega
  have hv := viable_of_accepted hS trivial hcast hσ
    (by rw [gbar0, Δ1, ts1]; push_cast; dsimp only [Time] at *; omega) (hΦU hBt) hacc
  rw [hσ]
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr (hv.mono hΦU)

/-- H.1's bound `ḡ + 2Θ + 8Δ ≤ t_p` holds from slot `8`. -/
theorem start_le {p : Nat} (hp : 8 ≤ p) : gbar 0 + 2 * Θ sp1 + 8 * sp1.Δ ≤ sp1.ts p := by
  rw [gbar0, Θ1, Δ1, ts1]; push_cast; dsimp only [Time] at *; omega

/-- **H.1 on the run**: for `p ≥ 8`, every slot-`p` vote is `block p`, and `block p` is below the
confirmed tip at every call from `t_p + 6Δ` (at `t_p + 6Δ` itself, from the tick there on). -/
theorem h1 (h : RunFacts tr U block) {p : Nat} (hp : 8 ≤ p) :
    (∀ x ∈ (Set.univ : Set (Fin sp1.n)), ∀ j e, VoteAt tr x j e → e.msg.slot = p →
      e.msg.head = (block p).root) ∧
    (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ j ℓ, tr.CallAt y j ℓ →
      sp1.ts p + 6 * sp1.Δ ≤ tr.time j →
      (tr.time j = sp1.ts p + 6 * sp1.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U (block p) (acConfirmed sp1 (tr.post j) ℓ.frame (tr.time j))) :=
  ac_healing_standalone sp1 Unit ro1 Set.univ U tr (fun _ => v0) 0 h.run.run h.run.driven
    h.run.trivial h.run.healthy h.run.catchUp p (block p) trivial (h.honest p (by omega))
    (start_le hp)

/-- **Slot `8`**: the validator votes in slot `8`, and every slot-`8` vote is `block 8`. -/
theorem vote8 (h : RunFacts tr U block) :
    (∃ j e, VoteAt tr v0 j e ∧ e.msg.slot = 8) ∧
    ∀ j e, VoteAt tr v0 j e → e.msg.slot = 8 → e.msg.head = (block 8).root :=
  ⟨honest_votes_in_slot h.run.toHealthyBase (m := 8) (by rw [gbar0, Δ1, ts1]; norm_num) v0
    trivial, fun j e hv hs => (h.h1 le_rfl).1 v0 trivial j e hv hs⟩

/-- **The confirmation of `block 8` from time `38`** (`t_8 + 6Δ`; at `38` itself, from the tick
there on). -/
theorem confirmed38 (h : RunFacts tr U block) :
    ∀ j ℓ, tr.CallAt v0 j ℓ → 38 ≤ tr.time j →
      (tr.time j = 38 →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt v0 k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U (block 8) (acConfirmed sp1 (tr.post j) ℓ.frame (tr.time j)) := by
  have h38 : sp1.ts ((8 : Nat) : Int) + 6 * sp1.Δ = 38 := by rw [ts1, Δ1]; norm_num
  intro j ℓ hc ht htick
  exact (h.h1 le_rfl).2 v0 trivial j ℓ hc (by rw [h38]; exact ht)
    (fun he => htick (by rw [he, h38]))

/-- **H.1's corollary on the run** (`Prop(4)`): from every `t ≥ 32 = ḡ + 2Θ + 8Δ`, an honest
proposal in `[t, t + 4]` is below the confirmed tip at every call from `t + 10`. -/
theorem corollary (h : RunFacts tr U block) {t : Time} (ht : 32 ≤ t) :
    ∃ (p : Nat) (P : Blk sp1.n Unit), t ≤ sp1.ts p ∧ sp1.ts p ≤ t + 4 ∧
      HonestProposal tr v0 p P ∧
      ∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ j ℓ, tr.CallAt y j ℓ → t + 4 + 6 * sp1.Δ ≤ tr.time j →
        (tr.time j = t + 4 + 6 * sp1.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp1 (tr.post j) ℓ.frame (tr.time j)) :=
  ac_healing_standalone_corollary sp1 Unit ro1 Set.univ U tr (fun _ => v0) 0 4 h.run.run
    h.run.driven h.run.trivial h.run.healthy h.run.catchUp proposerBound t
    (by rw [gbar0, Θ1, Δ1]; linarith)

/-- **The corollary at `t = 32`**: an honest proposal of a slot `p` with `32 ≤ t_p ≤ 36` is below
the confirmed tip at every call from time `42` (at `42` itself, from the tick there on). -/
theorem corollary42 (h : RunFacts tr U block) :
    ∃ (p : Nat) (P : Blk sp1.n Unit), 32 ≤ sp1.ts p ∧ sp1.ts p ≤ 36 ∧
      HonestProposal tr v0 p P ∧
      ∀ j ℓ, tr.CallAt v0 j ℓ → 42 ≤ tr.time j →
        (tr.time j = 42 →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt v0 k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp1 (tr.post j) ℓ.frame (tr.time j)) := by
  obtain ⟨p, P, h1, h2, hP, hc⟩ := h.corollary (t := 32) le_rfl
  have h42 : (32 : Time) + 4 + 6 * sp1.Δ = 42 := by rw [Δ1]; norm_num
  refine ⟨p, P, h1, by linarith, hP, fun j ℓ hcj ht htick => ?_⟩
  exact hc v0 trivial j ℓ hcj (by rw [h42]; exact ht) (fun he => htick (by rw [he, h42]))

/-- The bound `ḡ + (8k + 4)Δ ≤ t_p` of H.1 at `ḡ + (8k + 4)Δ` holds from slot `5`
(`(8k + 4)Δ = 20 = t_5`), three slots below H.1's slot `8`. -/
theorem start_le_tight {p : Nat} (hp : 5 ≤ p) :
    gbar 0 + (8 * (sp1.k : Time) + 4) * sp1.Δ ≤ sp1.ts p := by
  have hk : sp1.k = 2 := rfl
  rw [gbar0, Δ1, ts1, hk]; push_cast; dsimp only [Time] at *; omega

/-- **H.1 at `ḡ + (8k + 4)Δ` on the run**: for `p ≥ 5`, every slot-`p` vote is `block p`, and
`block p` is below the confirmed tip at every call from `t_p + 6Δ` (at `t_p + 6Δ` itself, from
the tick there on). -/
theorem h1_tight (h : RunFacts tr U block) {p : Nat} (hp : 5 ≤ p) :
    (∀ x ∈ (Set.univ : Set (Fin sp1.n)), ∀ j e, VoteAt tr x j e → e.msg.slot = p →
      e.msg.head = (block p).root) ∧
    (∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ j ℓ, tr.CallAt y j ℓ →
      sp1.ts p + 6 * sp1.Δ ≤ tr.time j →
      (tr.time j = sp1.ts p + 6 * sp1.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U (block p) (acConfirmed sp1 (tr.post j) ℓ.frame (tr.time j))) :=
  ac_healing_standalone_tight sp1 Unit ro1 Set.univ U tr (fun _ => v0) 0 h.run.run
    h.run.driven h.run.trivial h.run.healthy h.run.catchUp p (block p) trivial
    (h.honest p (by omega)) (start_le_tight hp)

/-- **Proposal-block inclusion on the run** (the corollary of H.1 at `ḡ + (8k + 4)Δ`, `Prop(4)`):
from every `t ≥ 20 = ḡ + (8k + 4)Δ`, an honest proposal in `[t, t + 4]` is below the confirmed
tip at every call from `t + 10`. -/
theorem corollary_tight (h : RunFacts tr U block) {t : Time} (ht : 20 ≤ t) :
    ∃ (p : Nat) (P : Blk sp1.n Unit), t ≤ sp1.ts p ∧ sp1.ts p ≤ t + 4 ∧
      HonestProposal tr v0 p P ∧
      ∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ j ℓ, tr.CallAt y j ℓ → t + 4 + 6 * sp1.Δ ≤ tr.time j →
        (tr.time j = t + 4 + 6 * sp1.Δ →
          ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
        Anc U P (acConfirmed sp1 (tr.post j) ℓ.frame (tr.time j)) :=
  ac_healing_standalone_tight_corollary sp1 Unit ro1 Set.univ U tr (fun _ => v0) 0 4 h.run.run
    h.run.driven h.run.trivial h.run.healthy h.run.catchUp proposerBound t
    (by have hk : sp1.k = 2 := rfl; rw [gbar0, Δ1, hk]; push_cast; linarith)

/-- **H.2 (i) on the run** (`t₀ = 0`, `Inv(0)`, `Geo`): for `p ≥ 8`, every slot-`p` vote is
`block p`. -/
theorem h2_votes (h : RunFacts tr U block) {p : Nat} (hp : 8 ≤ p) :
    ∀ x ∈ (Set.univ : Set (Fin sp1.n)), ∀ j e, VoteAt tr x j e → e.msg.slot = p →
      e.msg.head = (block p).root :=
  (ac_inclusion sp1 Unit ro1 Set.univ U tr (fun _ => v0) 0 0 h.run.run h.run.driven
    h.run.healthy h.run.catchUp (by rw [gbar0]) h.inv p (block p) trivial
    (h.honest p (by omega))
    (by rw [Θ1, Δ1, ts1]; push_cast; dsimp only [Time] at *; omega)).1 (h.geo (by omega))

end RunFacts

/-- Every abstract premise is discharged by the one concrete infinite execution. -/
theorem concreteRunFacts : RunFacts run blocks block where
  run := standaloneRun
  time _ := rfl
  U_eq := blocks_eq
  slot _ hs := block_slot hs
  accept := accept_iff
  proposal _ _ hc := proposal_iff hc
  F _ _ hc := by rw [(callAt_iff.1 hc).2.1]; rfl
  honest _ hs := honestProposal hs

/-- The tick at a cut's time has already occurred, even at the exact confirmation deadline. -/
theorem tick_before (i : Nat) :
    ∃ k ≤ i, ∃ ℓ, run.CallAt v0 k ℓ ∧ ℓ.call = .tick ∧ run.time k = run.time i := by
  obtain ⟨ℓ, hc, hk⟩ := call_exists
    (show call (4 * (i / 4)) = some .tick by simp [call, kind])
  exact ⟨4 * (i / 4), by omega, ℓ, hc, hk, by simp [run]⟩

/-- H.1 on the actual run, with its exact-deadline tick condition discharged. -/
theorem confirmed_from38 {i : Nat} {ℓ : ACLabel GA1}
    (hc : run.CallAt v0 i ℓ) (ht : 38 ≤ run.time i) :
    Anc blocks (block 8) (acConfirmed sp1 (run.post i) ℓ.frame (run.time i)) :=
  concreteRunFacts.confirmed38 i ℓ hc ht (fun _ => tick_before i)

/-- The time-38 tick really occurs and confirms the non-genesis slot-8 proposal. -/
theorem confirmed_tick38 : ∃ ℓ, run.CallAt v0 152 ℓ ∧ ℓ.call = .tick ∧
    Anc blocks (block 8) (acConfirmed sp1 (run.post 152) ℓ.frame (run.time 152)) := by
  obtain ⟨ℓ, hc, hk⟩ := call_exists (show call 152 = some .tick by simp [call, kind])
  exact ⟨ℓ, hc, hk, confirmed_from38 hc (by norm_num [run])⟩

/-- H.1's corollary on the actual run, including the call at the deadline `42`. -/
theorem common_confirmed_from42 :
    ∃ (p : Nat) (P : Blk sp1.n Unit), 32 ≤ sp1.ts p ∧ sp1.ts p ≤ 36 ∧
      HonestProposal run v0 p P ∧
      ∀ i ℓ, run.CallAt v0 i ℓ → 42 ≤ run.time i →
        Anc blocks P (acConfirmed sp1 (run.post i) ℓ.frame (run.time i)) := by
  obtain ⟨p, P, hlow, hhigh, hp, hconfirm⟩ := concreteRunFacts.corollary42
  exact ⟨p, P, hlow, hhigh, hp, fun i ℓ hc ht => hconfirm i ℓ hc ht (fun _ => tick_before i)⟩

/-- Kind (b) for H.1 at `ḡ + (8k + 4)Δ`, at slot `5`, below H.1's threshold slot `8`: the
non-genesis proposal of slot `5` gets an actual vote, every slot-`5` vote is it, and the tick at
time `26 = t_5 + 6Δ` (cut `104`) confirms it. -/
theorem healing_tight_live_witness :
    ∃ P : Blk sp1.n Unit, HonestProposal run v0 5 P ∧ P.root ≠ sp1.genesisRoot ∧
      (∃ i e, VoteAt run v0 i e ∧ e.msg.slot = 5 ∧ e.msg.head = P.root) ∧
      ∃ ℓ, run.CallAt v0 104 ℓ ∧ ℓ.call = .tick ∧
        Anc blocks P (acConfirmed sp1 (run.post 104) ℓ.frame (run.time 104)) := by
  obtain ⟨i, e, hv, hs⟩ := vote_each_slot (s := 5) (by omega)
  obtain ⟨ℓ, hc, hk⟩ := call_exists (show call 104 = some .tick by simp [call, kind])
  have h1 := concreteRunFacts.h1_tight (p := 5) le_rfl
  have h26 : sp1.ts ((5 : Nat) : Int) + 6 * sp1.Δ = 26 := by rw [ts1, Δ1]; norm_num
  refine ⟨block 5, honestProposal (by omega), ?_, ⟨i, e, hv, hs, h1.1 v0 trivial i e hv hs⟩,
    ℓ, hc, hk, h1.2 v0 trivial 104 ℓ hc (by rw [h26]; norm_num [run])
      (fun _ => tick_before 104)⟩
  rw [block_root (by omega)]
  decide

/-- Proposal-block inclusion on the actual run, from `ḡ + (8k + 10)Δ + G_p = 30` (`t = 20`,
`G_p = 4`), including the call at the deadline `30`. -/
theorem common_confirmed_from30 :
    ∃ (p : Nat) (P : Blk sp1.n Unit), 20 ≤ sp1.ts p ∧ sp1.ts p ≤ 24 ∧
      HonestProposal run v0 p P ∧
      ∀ i ℓ, run.CallAt v0 i ℓ → 30 ≤ run.time i →
        Anc blocks P (acConfirmed sp1 (run.post i) ℓ.frame (run.time i)) := by
  obtain ⟨p, P, hlow, hhigh, hp, hconfirm⟩ := concreteRunFacts.corollary_tight (t := 20) le_rfl
  have h30 : (20 : Time) + 4 + 6 * sp1.Δ = 30 := by rw [Δ1]; norm_num
  exact ⟨p, P, hlow, by linarith, hp, fun i ℓ hc ht => hconfirm v0 trivial i ℓ hc
    (by rw [h30]; exact ht) (fun he => tick_before i)⟩

/-- Kind (b): the premises, geometry, retention, an actual H.2(i) vote and an H.1 confirmation
all hold on the same live run and the same non-genesis proposal. -/
theorem healing_live_witness :
    StandaloneRun run Set.univ blocks (fun _ => v0) 0 ∧
    ∃ P : Blk sp1.n Unit, HonestProposal run v0 8 P ∧ P.root ≠ sp1.genesisRoot ∧
      Geo (fun _ => v0) run Set.univ 8 P ∧ Inv (fun _ => v0) run Set.univ blocks 0 ∧
      (∃ i e, VoteAt run v0 i e ∧ e.msg.slot = 8 ∧ e.msg.head = P.root) ∧
      ∃ ℓ, run.CallAt v0 152 ℓ ∧ ℓ.call = .tick ∧
        Anc blocks P (acConfirmed sp1 (run.post 152) ℓ.frame (run.time 152)) := by
  obtain ⟨i, e, hv, hs⟩ := vote_each_slot (s := 8) (by omega)
  refine ⟨standaloneRun, block 8, honestProposal (by omega), ?_,
    concreteRunFacts.geo (by omega), concreteRunFacts.inv, ⟨i, e, hv, hs, ?_⟩, confirmed_tick38⟩
  · rw [block_root (by omega)]
    decide
  · exact concreteRunFacts.h2_votes le_rfl v0 trivial i e hv hs

end Consensus.Goldilocks.SA.Test.SAHealing

end
