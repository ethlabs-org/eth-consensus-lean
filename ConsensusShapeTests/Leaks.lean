module
public import ConsensusShape
public import Mathlib.Tactic
@[expose] public section

/-! # Leak tests for shape claims

`ShapeClaims` must not be satisfiable by protocols that do nothing, propose
without outputting, fabricate outputs, or are silenced by their own slashing
rule. The test contract `testK` serves only the available capability
(`DACore` schema), with catch-up 1, sleepy safety, and liveness index
`k : ℕ+` under `sleepy (1/2) ∧ progress ⟨Pattern.single, k⟩ 0`, from time 0,
latency `k + 2`. Each refutation runs the canonical valid run of one
always-awake honest validator (`Δ = 1`, GST 0, injective hash; horizon 3,
and 0 for `fabricated`):

* `silent`: no proposals, empty outputs: liveness fails;
* `proposeButGenesis`: proposals, but outputs stay empty: liveness fails;
* `fabricated`: an output header nobody signed: output validity fails;
* `conflictsTrue_silent`: a protocol that outputs its own proposals, but whose
  `conflicts` is always true, so engine slashing protection releases no
  signed object; its outputs stay empty and liveness fails.

Positive control (`recorder_live`, `recorder_live_testK`): the same protocol with `conflicts` false
records its released proposals into its output and meets the liveness
obligation that refutes the others, on every valid run in which the validator
is honest, for every latency `D ≥ 1` and every GST (also negative:
`recorder_live_testK_negGST`). So the refutations detect the leaks, not
an unsatisfiable obligation. The control checks the liveness obligation in
isolation, not jointly with output validity (its headers do not link). -/

namespace Consensus.Shape.Tests.Leaks
open Consensus Blocks Shape
open Consensus.Model (Public Key Obj pubOf protoOf sysOf)

/-- One output identifier, serving the available capability only. -/
abbrev schema : OutputSchema := ⟨Unit, fun c => match c with
  | .available => some ()
  | _ => none⟩

theorem schema_daCore : schema.DACore := ⟨rfl, rfl⟩

/-- The available capability of the test contract. It assumes slots of one
`Δ` (the test skeleton's grid), since the progress gap counts slots and the
latency counts `Δ`. Latency `k + 2`: within `k·Δ` after `t` an honest ready
proposer releases (progress); its proposal reaches every node awake on
`[a, a + Δ)` by `a + Δ` (synchrony: `sleepy` has GST `≤ 0`); a reader ready
at `t + (k + 1)·Δ` with catch-up `Δ` was awake on such an interval, so
`k + 1` would do and the last `Δ` is slack. Liveness starts at time 0, not at
GST: `sleepy` allows a negative GST, and a start before 0 would demand
proposals that no run can have released by then. -/
def testCap : CapSpec ProgressReq ℕ+ where
  safety := { premise := Premise.sleepy (1 / 2) }
  live := { premise := fun k => .conj (Premise.sleepy (1 / 2)) (.progress ⟨Pattern.single, k⟩ .zero)
            start := fun _ => .zero
            latency := fun k => (k : Nat) + 2 }

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

/-- One validator, always awake, `Δ = 1`, GST `g`. -/
def envG (g : Int) : Env (Fin 1) := ⟨1, by decide, g, fun _ _ => true⟩

/-- The refutation environment: GST 0. -/
abbrev env : Env (Fin 1) := envG 0

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
    Finset.univ 3 (by decide) pki sel hsel (fun _ _ => []) goodHash
  let r : Model.Run (compiled F) env :=
    Model.mkRun Finset.univ 3 pki sel (fun _ _ => []) relay goodHash es
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
      (show (0 : Int) + ((testCap.live.latency 1 : Nat) : Int) * env.Δ ≤ 3 by decide)
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
of its own released signed items, with `conflicts` constantly `conf`. -/
def familyC (conf : Bool) : ShapeFamily schema Unit := fun pub => {
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
  conflicts := fun _ _ => conf }

section C

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

omit [DecidableEq V] in
/-- With `conflicts` always true, a release round records only unsigned
objects, which leave the state unchanged. -/
theorem releaseAll_state (hash : (protoOf (compiled (familyC true)) E).Item → Nat)
    (k : Key (pubOf E))
    (cs : List (protoOf (compiled (familyC true)) E).Object)
    (nd : Model.Node (protoOf (compiled (familyC true)) E))
    (hcs : ∀ c ∈ cs, c.signer? = none ∨ c.signer? = some k) :
    (Model.releaseAll (protoOf (compiled (familyC true)) E) hash k nd cs).1.st = nd.st := by
  induction cs generalizing nd with
  | nil => rfl
  | cons c cs ih =>
    have hcs' : ∀ c' ∈ cs, c'.signer? = none ∨ c'.signer? = some k :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')
    unfold Model.releaseAll
    split
    · rename_i hrel
      have hp : Model.protects (protoOf (compiled (familyC true)) E) k nd.seen c = true :=
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
theorem familyC_state (rho : Model.Run (compiled (familyC true)) E) (i : Nat) (v : V) :
    (rho.stateBefore i v).st.1 = [] := by
  unfold Model.Run.stateBefore
  generalize rho.events.take i = es
  suffices h : ∀ (w : V → Model.Node (protoOf (compiled (familyC true)) E)),
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
theorem conflictsTrue_silent : ¬ ShapeClaims (familyC true) testK :=
  refuted_of_empty _ testSel (by
      intro r
      cases r with
      | proposer s =>
        exact (by decide : (Finset.univ : Finset (Fin (Fintype.card (Fin 1)))).card = 1)
      | duty s k => rfl
      | poll => rfl)
    (fun _ => Finset.univ_nonempty) (fun rho _ v i => familyC_state rho i v)


/-! ## Positive control: recording own proposals is live -/

/-- `familyC`'s state, read as its output chain. -/
abbrev rec {conf : Bool} {pub : Public} (st : (familyC conf pub).State) : Chain Unit := st

section Control

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

omit [DecidableEq V] in
/-- A release round only adds to `familyC`'s output. -/
theorem releaseAll_mono (conf : Bool) (hash : (protoOf (compiled (familyC conf)) E).Item → Nat)
    (k : Key (pubOf E)) (cs : List (protoOf (compiled (familyC conf)) E).Object)
    (nd : Model.Node (protoOf (compiled (familyC conf)) E)) {h : Header Unit}
    (hh : h ∈ rec nd.st.1) :
    h ∈ rec ((Model.releaseAll (protoOf (compiled (familyC conf)) E) hash k nd cs).1.st.1) := by
  induction cs generalizing nd with
  | nil => exact hh
  | cons c cs ih =>
    unfold Model.releaseAll
    split
    · apply ih
      obtain ⟨a, m, cs'⟩ := c
      change h ∈ rec ((familyC conf (pubOf E)).recordOwn nd.st.1 (Obj.mk a m cs')
        (Model.digests hash (Obj.mk a m cs')))
      simp only [familyC]
      split <;> simp [hh]
    · exact ih nd hh

omit [DecidableEq V] in
/-- With `conflicts` false, a release round releases every candidate that
carries nothing, and records each such signed item in the output. -/
theorem releaseAll_record (hash : (protoOf (compiled (familyC false)) E).Item → Nat)
    (k : Key (pubOf E)) (cs : List (protoOf (compiled (familyC false)) E).Object)
    (nd : Model.Node (protoOf (compiled (familyC false)) E)) {k' r}
    {h : (protoOf (compiled (familyC false)) E).Item}
    (hc : Obj.mk (.signed k' r) (.item h) [] ∈ cs) :
    Obj.mk (.signed k' r) (.item h) [] ∈
        (Model.releaseAll (protoOf (compiled (familyC false)) E) hash k nd cs).2 ∧
      h ∈ rec ((Model.releaseAll (protoOf (compiled (familyC false)) E) hash k nd cs).1.st.1) := by
  induction cs generalizing nd with
  | nil => cases hc
  | cons c cs ih =>
    unfold Model.releaseAll
    rcases List.mem_cons.mp hc with rfl | hc'
    · split
      · refine ⟨List.mem_cons_self, releaseAll_mono false hash k cs _ ?_⟩
        exact List.mem_append_right (rec nd.st.1) (List.mem_singleton_self h)
      · rename_i hn
        have hrl : Model.releasable nd.seen
            (Obj.mk (.signed k' r) (.item h) []) = true := rfl
        have hpr : Model.protects (protoOf (compiled (familyC false)) E) k nd.seen
            (Obj.mk (.signed k' r) (.item h) []) = true := by
          unfold Model.protects
          split
          · exact List.all_eq_true.mpr fun _ _ => Bool.or_true _
          · rfl
        exact absurd (Bool.and_eq_true_iff.mpr ⟨hrl, hpr⟩) hn
    · split
      · exact ⟨List.mem_cons_of_mem _ (ih _ hc').1, (ih _ hc').2⟩
      · exact ih nd hc'

/-- `familyC`'s output only grows along a run. -/
theorem familyC_mono (conf : Bool) (rho : Model.Run (compiled (familyC conf)) E) (v : V)
    {i : Nat} {h : Header Unit} (hh : h ∈ rec ((rho.stateBefore i v).st.1)) :
    ∀ j, i ≤ j → h ∈ rec ((rho.stateBefore j v).st.1) := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => exact hh
  | succ j _ ih =>
    cases he : rho.events[j]? with
    | none =>
      have : rho.events.take (j + 1) = rho.events.take j := by
        have hl : rho.events.length ≤ j := List.getElem?_eq_none_iff.mp he
        rw [List.take_of_length_le (by omega), List.take_of_length_le hl]
      unfold Model.Run.stateBefore
      rw [this]
      exact ih
    | some e =>
      rw [rho.stateBefore_succ he]
      cases e with
      | tick x t =>
        simp only [Model.Run.step]
        by_cases hux : v = x
        · subst hux
          rw [Function.update_self]
          unfold Model.Run.tick
          split
          · exact releaseAll_mono conf _ _ _ _ ih
          · exact ih
        · rw [Function.update_of_ne hux]
          exact ih
      | deliver x o t =>
        simp only [Model.Run.step]
        by_cases hux : v = x
        · subst hux
          rw [Function.update_self]
          exact ih
        · rw [Function.update_of_ne hux]
          exact ih
      | restart x t =>
        simp only [Model.Run.step]
        by_cases hux : v = x
        · subst hux
          rw [Function.update_self]
          exact ih
        · rw [Function.update_of_ne hux]
          exact ih

end Control

/-- Positive control: on every valid run of `familyC false` with the validator
honest, the proposal of the slot right after `t` is released by the honest,
ready validator and recorded in its output at once, so `ProposalLive` holds
for every catch-up, every start `≥ 0` and every latency `D ≥ 1` (in
particular `testK`'s, `k + 2`). -/
theorem recorder_live {g : Int} (rho : Model.Run (compiled (familyC false)) (envG g))
    (hv : rho.ExecutionValid) (hh : rho.honest = Finset.univ) (c start : Time)
    (hs : 0 ≤ start) (D : Nat) (hD : 1 ≤ D) :
    ProposalLive rho c () start D := by
  intro t hst ht
  have hΔ : (envG g).Δ = 1 := rfl
  rw [hΔ, mul_one] at ht ⊢
  have hDt : (1 : Int) ≤ (D : Int) := by exact_mod_cast hD
  have ht0 : (0 : Int) ≤ t := le_trans hs hst
  obtain ⟨s, hsτ⟩ : ∃ s : Nat, (s : Int) = t + 1 := ⟨(t + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hspos : 0 < s := by omega
  have hkey : ∀ a b : Fin (Fintype.card (Fin 1)), a = b := by
    intro a b
    have h1 : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
    have ha : a.val < 1 := lt_of_lt_of_eq a.2 h1
    have hb : b.val < 1 := lt_of_lt_of_eq b.2 h1
    exact Fin.ext (by omega)
  let v : Fin 1 := rho.key 0
  have hown : rho.ownKey v = 0 := hkey _ _
  have hvh : v ∈ rho.honest := by rw [hh]; exact Finset.mem_univ _
  have htick : Model.Event.tick v (t + 1) ∈ rho.events :=
    hv.tick_total v hvh (t + 1) (by linarith)
      (by linarith) rfl
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem htick
  have hi' : rho.events[i]? = some (.tick v (t + 1)) := by rw [List.getElem?_eq_getElem hi, hie]
  let nd := rho.stateBefore i v
  let xs := Model.mempool rho.inbox v (t + 1)
  let nd₁ : Model.Node (protoOf (compiled (familyC false)) (envG g)) :=
    ⟨(protoOf (compiled (familyC false)) (envG g)).clock nd.st (t + 1) xs, nd.seen⟩
  let h : (protoOf (compiled (familyC false)) (envG g)).Item := ⟨.root, s, encodeTxs xs, ()⟩
  have hsel : rho.ownKey v ∈ rho.sel (ShapeRole.proposer s) := by
    have hc : (rho.sel (ShapeRole.proposer s)).card = 1 := hv.selValid (ShapeRole.proposer s)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    rw [ha, Finset.mem_singleton]
    exact hkey _ _
  have hcand : Obj.mk (.signed (rho.ownKey v) (ShapeRole.proposer s)) (.item h) [] ∈
      rho.candidates nd₁.st v (t + 1) := by
    unfold Model.Run.candidates
    apply List.mem_append_left
    refine List.mem_flatMap.mpr ⟨.propose s hspos, ?_, ?_⟩
    · refine ((protoOf (compiled (familyC false)) (envG g)).duties_spec _ (t + 1)).mpr ?_
      change (s : Time) * ((1 : Nat) * 1) = t + 1
      rw [hsτ]; ring
    · have hact : (protoOf (compiled (familyC false)) (envG g)).act nd₁.st (.propose s hspos) =
          some (.item h, []) := rfl
      have hrole : (protoOf (compiled (familyC false)) (envG g)).role (.propose s hspos) =
          ShapeRole.proposer s := rfl
      simp only [hact, hrole, hsel, ite_true]
      exact List.mem_singleton_self _
  have hrel := releaseAll_record rho.hash (rho.ownKey v) _ nd₁ hcand
  have hrel' : Obj.mk (.signed (rho.ownKey v) (ShapeRole.proposer s)) (.item h) [] ∈
      rho.releasesAt i ∧ h ∈ rec ((rho.stateBefore (i + 1) v).st.1) := by
    simp only [Model.Run.releasesAt, hi', rho.stateBefore_succ hi', Model.Run.step,
      Function.update_self]
    unfold Model.Run.tick
    simp only [show (envG g).awake v (t + 1) = true from rfl, ite_true]
    exact hrel
  have hk0 : rho.key 0 ∈ rho.honest := by rw [hh]; exact Finset.mem_univ _
  refine ⟨t + 1, 0, h, lt_add_one t, ⟨hk0, fun u _ _ => rfl⟩,
    ⟨hk0, ShapeRole.proposer s, [], rfl, i, hi', ?_⟩, ?_⟩
  · rw [← hown]; exact hrel'.1
  · intro w _
    have hw : w = v := Subsingleton.elim _ _
    subst hw
    have hcut : i + 1 ≤ (chainTrace rho).endCut (t + (D : Time)) := by
      apply Nat.le_findGreatest (Nat.succ_le_of_lt hi)
      change rho.cutTime (i + 1) ≤ _
      simp only [Model.Run.cutTime, hi']
      change (t : Int) + 1 ≤ t + (D : Int)
      linarith
    exact familyC_mono false rho _ hrel'.2 _ hcut

/-- The control meets exactly the obligation that `refuted_of_empty` uses:
`testK`'s liveness conclusion at every index, from its start, with its
latency and catch-up, for every GST. -/
theorem recorder_live_testK {g : Int} (rho : Model.Run (compiled (familyC false)) (envG g))
    (hv : rho.ExecutionValid) (hh : rho.honest = Finset.univ) (k : ℕ+) (σ : Nat → Time) :
    ProposalLive rho (((testK.catchUp : Nat) : Time) * (envG g).Δ) ()
      ((testCap.live.start k).eval rho.point σ) (testCap.live.latency k) :=
  recorder_live rho hv hh _ _ le_rfl _ (by simp [testCap])

/-- Regression (review-5-r2): with GST negative (allowed by `sleepy`), the
liveness obligation of `testK` stays satisfiable, because it starts at time 0,
not at GST. -/
theorem recorder_live_testK_negGST (rho : Model.Run (compiled (familyC false)) (envG (-3)))
    (hv : rho.ExecutionValid) (hh : rho.honest = Finset.univ) (k : ℕ+) (σ : Nat → Time) :
    ProposalLive rho (((testK.catchUp : Nat) : Time) * (envG (-3)).Δ) ()
      ((testCap.live.start k).eval rho.point σ) (testCap.live.latency k) :=
  recorder_live_testK rho hv hh k σ

end Consensus.Shape.Tests.Leaks

end
