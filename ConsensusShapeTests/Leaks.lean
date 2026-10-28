module
public import ConsensusShape
public import Mathlib.Tactic
@[expose] public section

/-! # Leak tests for shape claims

`ShapeClaims` must not be satisfiable by protocols that do nothing, propose
without outputting, fabricate outputs, or are silenced by their own slashing
rule. The test contract `testK` serves only the available capability
(`DACore` schema), with catch-up 1, sleepy safety, and liveness index
`k : ℕ+` under `sleepy (1/2) ∧ progress ⟨Pattern.single, k⟩ 0`, latency 1.
Each refutation runs the canonical valid run of one always-awake honest
validator (`Δ = 1`, GST 0, injective hash):

* `silent`: no proposals, empty outputs: liveness fails;
* `proposeButGenesis`: proposals, but outputs stay empty: liveness fails;
* `fabricated`: an output header nobody signed: output validity fails;
* `conflictsTrue_silent`: a protocol that outputs its own proposals, but whose
  `conflicts` is always true, so engine slashing protection releases no
  signed object (stage 3); its outputs stay empty and liveness fails. -/

namespace Consensus.Shape.Tests.Leaks
open Consensus Blocks Shape
open Consensus.Model (Public Key Obj pubOf protoOf sysOf)

/-- One output identifier, serving the available capability only. -/
abbrev schema : OutputSchema := ⟨Unit, fun c => match c with
  | .available => some ()
  | _ => none⟩

theorem schema_daCore : schema.DACore := ⟨rfl, rfl⟩

/-- The available capability of the test contract. -/
def testCap : CapSpec ProgressReq ℕ+ where
  safety := { premise := Premise.sleepy (1 / 2) }
  live := { premise := fun k => .conj (Premise.sleepy (1 / 2)) (.progress ⟨Pattern.single, k⟩ .zero)
            start := fun _ => .zero
            latency := fun _ => 1 }

/-- The test contract: catch-up 1, available capability only. -/
def testK : Contract schema ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  catchUp := 1
  spec := fun c => match c with
    | .available => some testCap
    | _ => none

/-- The test skeleton: slots of one `Δ`, one proposer per slot, polling
disabled, one committee kind (every key). -/
def testSkel (n : Nat) : Skeleton n where
  grid := ⟨1, by decide⟩
  proposerSel := .sized 1
  pollSel := .fixed ∅
  Kind := Unit
  decKind := inferInstance
  kinds := [()]
  kinds_nodup := List.nodup_singleton _
  kinds_complete := fun _ => List.mem_singleton_self _
  phase := fun _ => 0
  kindSel := fun _ => .all

/-- The fabricated header. -/
def fab : Header Unit := ⟨.root, 1, 7, ()⟩

/-- Stateless test families: propose (if `proposal`), vote (if `vote`; then
`conflicts` is always true), and output nothing or (if `bad`) the fabricated
header. -/
def family (proposal vote bad : Bool) : ShapeFamily schema Unit := fun pub => {
  skel := testSkel pub.n
  State := Unit, Body := Unit, Durable := Unit
  decBody := inferInstance
  init := fun _ => (), clock := fun s _ => s
  propose := fun _ _ => if proposal then some (.root, (), []) else none
  act := fun _ _ _ => if vote then some ((), []) else none
  pollPropose := fun _ _ => none, poll := fun _ _ => none
  gossip := fun _ _ => []
  process := fun s _ _ => s, recordOwn := fun s _ _ => s
  durable := fun s => s, restore := fun _ d _ => d
  out := fun _ _ => if bad then [fab] else []
  conflicts := fun _ _ => vote }

/-- One validator, always awake, `Δ = 1`, GST 0. -/
def env : Env (Fin 1) := ⟨1, by decide, 0, fun _ _ => true⟩

/-- The identity PKI. -/
def pki : Fin (Fintype.card (Fin 1)) ≃ Fin 1 := finCongr (Fintype.card_fin 1)

/-- The selection: the only key everywhere, except the (disabled) poll role. -/
def testSel : ShapeRole Unit → Finset (Fin (Fintype.card (Fin 1)))
  | .poll => ∅
  | _ => Finset.univ

/-- An injective hash. -/
def goodHash (h : Header Unit) : Nat := Encodable.encode h

theorem goodHash_injective : Function.Injective goodHash := Encodable.encode_injective

/-- The only validator is ready at every time. -/
theorem env_ready (p : EnvPoint (Fin 1)) (hp : p.env = env) (hh : p.honest = Finset.univ)
    (c t : Time) (v : Fin 1) : p.Ready c v t := by
  refine ⟨by rw [hh]; exact Finset.mem_univ _, fun u _ _ => ?_⟩
  rw [hp]
  rfl

/-- The refutation pattern: a family with the test skeleton's selection whose
valid runs on `env` have empty outputs violates the liveness claim of `testK`. -/
theorem refuted_of_empty (F : ShapeFamily schema Unit)
    (sel : (protoOf (compiled F) env).Role → Finset (Fin (Fintype.card (Fin 1))))
    (hsel : ∀ r, ((protoOf (compiled F) env).selSpec r).Admits (sel r))
    (hprop : ∀ s, (sel (ShapeRole.proposer s)).Nonempty)
    (hout : ∀ rho : Model.Run (compiled F) env, rho.ExecutionValid →
      ∀ v i, (chainTrace rho).read () v i = []) :
    ¬ ShapeClaims F testK := by
  intro hc
  obtain ⟨relay, es, valid, sync, -⟩ := Model.canonical_run schema (compiled F) (Fin 1) env
    Finset.univ 1 (by decide) pki sel hsel (fun _ _ => []) goodHash
  let r : Model.Run (compiled F) env :=
    Model.mkRun Finset.univ 1 pki sel (fun _ _ => []) relay goodHash es
  have hready : ∀ c t v, r.point.Ready c v t := env_ready r.point rfl rfl
  have hfaulty : r.point.faulty = ∅ := by
    simp [EnvPoint.faulty, r, Model.mkRun, Model.Run.point]
  have hreadyAt : ∀ c t, r.point.readyAt c t = Finset.univ := by
    intro c t
    ext v
    simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, iff_true]
    exact ⟨Finset.mem_univ v, hready c t v⟩
  have hprem : ShapePremise testK (testCap.live.premise 1) (fun _ => 0) r := by
    refine ⟨⟨le_refl _, sync, ?_⟩, ?_⟩
    · intro t _ _
      change r.point.ReadyAbove (1 / 2) _ t
      unfold EnvPoint.ReadyAbove
      rw [hreadyAt, hfaulty]
      norm_num
    · change PatternRecurrence r.point r.key r.sel ShapeRole.proposer _ _ _ _
      apply patternRecurrence_of_all env.Δ_pos
      intro s j _
      exact ⟨hprop (s + j), fun k _ => ⟨Finset.mem_univ _, hready _ _ _⟩⟩
  have hcap := hc.caps .available () testCap rfl rfl
  rcases hcap.live (Fin 1) env r (show testK.Idx from (1 : ℕ+)) (fun _ => 0) valid hprem with
    hl | hcol
  · obtain ⟨τ, k, h, -, -, -, hin⟩ := hl 0 le_rfl
      (show (0 : Int) + ((1 : Nat) : Int) * 1 ≤ 1 by decide)
    have hmem := hin 0 (hready _ _ _)
    change h ∈ (chainTrace r).read () 0 _ at hmem
    rw [hout r valid] at hmem
    cases hmem
  · exact Model.Run.not_hashCollision_of_injective (rho := r) goodHash_injective hcol

/-- The test selection is admissible for every stateless family. -/
theorem testSel_admits (proposal vote bad : Bool) (r : ShapeRole Unit) :
    ((protoOf (compiled (family proposal vote bad)) env).selSpec r).Admits (testSel r) := by
  cases r with
  | proposer s => exact (by decide : (Finset.univ : Finset (Fin (Fintype.card (Fin 1)))).card = 1)
  | duty s k => rfl
  | poll => rfl

/-- A protocol that never proposes has no live output. -/
theorem silent : ¬ ShapeClaims (family false false false) testK :=
  refuted_of_empty _ testSel (testSel_admits _ _ _) (fun _ => Finset.univ_nonempty)
    (fun _ _ _ _ => rfl)

/-- A protocol that proposes but never outputs (genesis only) has no live
output. -/
theorem proposeButGenesis : ¬ ShapeClaims (family true false false) testK :=
  refuted_of_empty _ testSel (testSel_admits _ _ _) (fun _ => Finset.univ_nonempty)
    (fun _ _ _ _ => rfl)

/-- A protocol that outputs a header nobody signed violates output validity. -/
theorem fabricated : ¬ ShapeClaims (family false false true) testK := by
  intro hc
  obtain ⟨relay, es, valid, -, -⟩ := Model.canonical_run schema
    (compiled (family false false true)) (Fin 1) env Finset.univ 0 le_rfl pki testSel
    (testSel_admits _ _ _) (fun _ _ => []) goodHash
  let r : Model.Run (compiled (family false false true)) env :=
    Model.mkRun Finset.univ 0 pki testSel (fun _ _ => []) relay goodHash es
  have hv := hc.outputValid (Fin 1) env r valid .available () rfl 0
    (by simp [r, Model.mkRun]) 0 (Nat.zero_le _)
  obtain ⟨_, _, _, _, ⟨j, _, hj, _⟩⟩ := hv.2.2 fab (List.mem_singleton_self _)
  exact Nat.not_lt_zero _ hj

/-! ## Silenced by its own slashing rule -/

/-- A protocol that proposes and votes at every slot and outputs the headers
of its own released signed proposals, with `conflicts` always true. -/
def familyC : ShapeFamily schema Unit := fun pub => {
  skel := testSkel pub.n
  State := Chain Unit, Body := Unit, Durable := Chain Unit
  decBody := inferInstance
  init := fun _ => [], clock := fun s _ => s
  propose := fun _ _ => some (.root, (), [])
  act := fun _ _ _ => some ((), [])
  pollPropose := fun _ _ => none, poll := fun _ _ => none
  gossip := fun _ _ => []
  process := fun s _ _ => s
  recordOwn := fun s o _ => match o with
    | .mk (.signed _ _) (.item h) _ => s ++ [h]
    | _ => s
  durable := fun s => s, restore := fun _ d _ => d
  out := fun _ s => s
  conflicts := fun _ _ => true }

section C

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

omit [DecidableEq V] in
/-- With `conflicts` always true, a release round records only unsigned
objects, which leave the state unchanged. -/
theorem releaseAll_state (hash : (protoOf (compiled familyC) E).Item → Nat) (k : Key (pubOf E))
    (cs : List (protoOf (compiled familyC) E).Object)
    (nd : Model.Node (protoOf (compiled familyC) E))
    (hcs : ∀ c ∈ cs, c.signer? = none ∨ c.signer? = some k) :
    (Model.releaseAll (protoOf (compiled familyC) E) hash k nd cs).1.st = nd.st := by
  induction cs generalizing nd with
  | nil => rfl
  | cons c cs ih =>
    have hcs' : ∀ c' ∈ cs, c'.signer? = none ∨ c'.signer? = some k :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')
    unfold Model.releaseAll
    split
    · rename_i hrel
      have hp : Model.protects (protoOf (compiled familyC) E) k nd.seen c = true :=
        (Bool.and_eq_true_iff.mp hrel).2
      dsimp only
      rw [ih _ hcs']
      rcases hcs c List.mem_cons_self with hn | hk
      · obtain ⟨a, m, cs'⟩ := c
        cases a with
        | signed k' r => simp [Model.Obj.signer?, Model.Obj.auth] at hn
        | none => rfl
      · have := (Model.protects_iff.mp hp hk).1
        cases this
    · exact ih nd hcs'

/-- Every node's state (its output) stays empty along every run of `familyC`. -/
theorem familyC_state (rho : Model.Run (compiled familyC) E) (i : Nat) (v : V) :
    (rho.stateBefore i v).st.1 = [] := by
  unfold Model.Run.stateBefore
  generalize rho.events.take i = es
  suffices h : ∀ (w : V → Model.Node (protoOf (compiled familyC) E)),
      (∀ v, (w v).st.1 = []) → ∀ v, (es.foldl rho.step w v).st.1 = [] from
    h _ (fun _ => rfl) v
  induction es with
  | nil => exact fun w hw => hw
  | cons e es ih =>
    intro w hw
    apply ih
    intro u
    cases e with
    | tick x t =>
      simp only [Model.Run.step]
      by_cases hux : u = x
      · subst hux
        rw [Function.update_self]
        unfold Model.Run.tick
        split
        · rw [releaseAll_state]
          · exact hw u
          · intro c hc
            exact rho.candidates_signer _ u t hc
        · exact hw u
      · rw [Function.update_of_ne hux]
        exact hw u
    | deliver x o t =>
      simp only [Model.Run.step]
      by_cases hux : u = x
      · subst hux
        rw [Function.update_self]
        exact hw u
      · rw [Function.update_of_ne hux]
        exact hw u
    | restart x t =>
      simp only [Model.Run.step]
      by_cases hux : u = x
      · subst hux
        rw [Function.update_self]
        exact hw u
      · rw [Function.update_of_ne hux]
        exact hw u

end C

/-- Slashing protection silences a protocol whose `conflicts` is always true:
it releases no signed object, so it never records a proposal and its output
stays empty; liveness refutes it. -/
theorem conflictsTrue_silent : ¬ ShapeClaims familyC testK :=
  refuted_of_empty _ testSel (by
      intro r
      cases r with
      | proposer s =>
        exact (by decide : (Finset.univ : Finset (Fin (Fintype.card (Fin 1)))).card = 1)
      | duty s k => rfl
      | poll => rfl)
    (fun _ => Finset.univ_nonempty) (fun rho _ v i => familyC_state rho i v)

end Consensus.Shape.Tests.Leaks

end
