module
public import ConsensusModelProofs.Canonical.Unforgeable

@[expose] public section

/-! # Provenance is an authorized signer

In every valid run, every signed object inside anything an honest node
observed is signed by a key selected for its role. Delivered objects satisfy
this by `Credentials`; the engine signs a node's own candidates only with its
own key in a role that selects it, and releases a candidate only if everything
it carries was already seen. The same induction shows that a causal network
(every delivery is an earlier release) satisfies `Credentials` by itself,
which the canonical run uses. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run
variable (rho : Run F E)

/-- Every signed object inside `o` is signed by a key selected for its role. -/
def Authorized (o : (protoOf F E).Object) : Prop :=
  ∀ d, Obj.Contains o d → ∀ k r, d.auth = .signed k r → k ∈ rho.sel r

omit [DecidableEq V] in
/-- A tick keeps `seen` authorized and releases only authorized objects. -/
theorem tick_authorized (nd : Node (protoOf F E)) (v : V) (t : Time)
    (hs : ∀ o ∈ nd.seen, rho.Authorized o) :
    (∀ o ∈ (rho.tick nd v t).1.seen, rho.Authorized o) ∧
      (∀ o ∈ (rho.tick nd v t).2, rho.Authorized o) := by
  unfold tick
  split
  · exact releaseAll_preserves rho.hash _
      (fun d => ∀ k r, d.auth = .signed k r → k ∈ rho.sel r) _ _ hs
      (fun o ho k r ha => rho.candidates_selected _ v t (releaseAll_subset _ _ _ _ o ho) ha)
  · exact ⟨hs, by simp⟩

/-- If every object delivered before event cut `i` is authorized, so is
everything every node has seen at cut `i`. -/
theorem seen_authorized (i : Nat)
    (hd : ∀ k < i, ∀ w o t, rho.events[k]? = some (.deliver w o t) → rho.Authorized o) :
    ∀ v, ∀ o ∈ (rho.stateBefore i v).seen, rho.Authorized o := by
  induction i with
  | zero => intro v o ho; simp [stateBefore, initWorld] at ho
  | succ k ih =>
    have old := ih (fun j hj => hd j (by omega))
    cases he : rho.events[k]? with
    | none =>
      have hworld : rho.stateBefore (k + 1) = rho.stateBefore k := by
        simp [stateBefore, List.take_add_one, he]
      rw [hworld]
      exact old
    | some e =>
      rw [rho.stateBefore_succ he]
      intro w o ho
      cases e with
      | tick v t =>
        by_cases hw : w = v
        · subst w; exact (rho.tick_authorized _ v t (old v)).1 o (by simpa [step] using ho)
        · exact old w o (by simpa [step, hw] using ho)
      | restart v t =>
        by_cases hw : w = v
        · subst w; exact old v o (by simpa [step] using ho)
        · exact old w o (by simpa [step, hw] using ho)
      | deliver v p t =>
        by_cases hw : w = v
        · subst w
          have hm : o ∈ (rho.stateBefore k v).seen ++ [p] := by simpa [step] using ho
          rcases List.mem_append.mp hm with hm | hm
          · exact old v o hm
          · rcases List.mem_singleton.mp hm with rfl
            exact hd k (by omega) v o t he
        · exact old w o (by simpa [step, hw] using ho)

/-- If every object delivered before event cut `i` is authorized, so is every
object released at event `i`. -/
theorem releasesAt_authorized (i : Nat)
    (hd : ∀ k < i, ∀ w o t, rho.events[k]? = some (.deliver w o t) → rho.Authorized o) :
    ∀ o ∈ rho.releasesAt i, rho.Authorized o := by
  cases he : rho.events[i]? with
  | none => simp [releasesAt, he]
  | some e =>
    cases e with
    | tick v t =>
      simp only [releasesAt, he]
      exact (rho.tick_authorized _ v t (rho.seen_authorized i hd v)).2
    | deliver v p t => simp [releasesAt, he]
    | restart v t => simp [releasesAt, he]

/-- Every signed object inside anything an honest node observed is signed by
a key selected for its role ("provenance = authorized signer"). -/
theorem selected_of_observed (hv : rho.ExecutionValid) {o : (protoOf F E).Object}
    (ho : o ∈ rho.Observed) {o' : (protoOf F E).Object} (hc : Obj.Contains o o')
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} (ha : o'.auth = .signed k r) :
    k ∈ rho.sel r := by
  have hd : ∀ i, ∀ j < i, ∀ w o t, rho.events[j]? = some (Event.deliver w o t) →
      rho.Authorized o :=
    fun _ j _ w o t he => hv.credentials j w o t he
  obtain ⟨v, _, j, o₀, _, hr, hc₀⟩ := ho
  rcases hr with ⟨t, _, hr⟩ | ⟨t, he⟩
  · exact rho.releasesAt_authorized j (hd j) o₀ hr o' (hc₀.trans hc) k r ha
  · exact hv.credentials j v o₀ t he o' (hc₀.trans hc) k r ha

/-- A causal network (every delivery is an earlier release) delivers only
authorized objects: `Credentials` holds. -/
theorem credentials_of_causal (hc : rho.Causal) : rho.Credentials := by
  have D : ∀ i : Nat, ∀ k < i, ∀ w o t, rho.events[k]? = some (Event.deliver w o t) →
      rho.Authorized o := by
    intro i
    induction i with
    | zero => intro k hk; omega
    | succ i ih =>
      intro k hk w o t he
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ih k hk w o t he
      · obtain ⟨j, _, _, hj, _, hjo⟩ := hc k w o t he
        exact rho.releasesAt_authorized j (fun m hm => ih m (by omega)) o hjo
  intro i w o t he
  exact D (i + 1) i (by omega) w o t he

end Run
end Consensus.Model
end
