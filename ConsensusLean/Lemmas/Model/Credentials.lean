module
public import ConsensusLean.Lemmas.Model.Canonical.Unforgeable
public import ConsensusLean.Lemmas.Model.View

public section

/-! # Provenance is an authorized signer

In every valid run, every signed object inside anything an honest node
observed, other than a delegated vote body (`Protocol.voteBody`, authenticated by
evidence instead), is signed by a key selected for its role. Delivered objects
satisfy this by `OtherCredentials`; the engine signs a node's own candidates only
with its own key in a role that selects it, and releases a candidate only if
everything it carries was already seen. The same induction shows that a causal
network (every delivery is an earlier release) satisfies `OtherCredentials` by
itself, which the canonical run uses; with `VoteVerification`, `Credentials`. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run
variable (rho : Run F E)

/-- Every signed object inside `o` other than a delegated vote body is signed by a key selected
for its role. -/
def Authorized (o : (protoOf F E).Object) : Prop :=
  ∀ d, Obj.Contains o d → ∀ k r, d.auth = .signed k r →
    (∀ b, d.msg = .data b → (protoOf F E).voteBody b = false) → k ∈ rho.sel r

omit [DecidableEq V] in
/-- A tick keeps `seen` authorized and releases only authorized objects. -/
theorem tick_authorized (nd : Node (protoOf F E)) (v : V) (t : Time)
    (hs : ∀ o ∈ nd.seen, rho.Authorized o) :
    (∀ o ∈ (rho.tick nd v t).1.seen, rho.Authorized o) ∧
      (∀ o ∈ (rho.tick nd v t).2, rho.Authorized o) := by
  have hr : ∀ o ∈ (rho.tick nd v t).2, ∀ k r, o.auth = .signed k r →
      (∀ b, o.msg = .data b → (protoOf F E).voteBody b = false) → k ∈ rho.sel r :=
    fun o ho k r ha _ => rho.tick_selected nd v t ho ha
  obtain ⟨cs, -, h2, h1⟩ := rho.tick_flat nd v t
  rw [h2] at hr ⊢
  rw [h1]
  exact releaseAll_preserves rho.hash _
    (fun d => ∀ k r, d.auth = .signed k r →
      (∀ b, d.msg = .data b → (protoOf F E).voteBody b = false) → k ∈ rho.sel r) _ _ hs hr

omit [DecidableEq V] in
/-- A delivery of an authorized object keeps `seen` authorized and releases
only authorized objects. -/
theorem deliver_authorized (nd : Node (protoOf F E)) (v : V) (p : (protoOf F E).Object)
    (t : Time) (hs : ∀ o ∈ nd.seen, rho.Authorized o) (hp : rho.Authorized p) :
    (∀ o ∈ (rho.deliver nd v p t).1.seen, rho.Authorized o) ∧
      (∀ o ∈ (rho.deliver nd v p t).2, rho.Authorized o) := by
  have hr : ∀ o ∈ (rho.deliver nd v p t).2, ∀ k r, o.auth = .signed k r →
      (∀ b, o.msg = .data b → (protoOf F E).voteBody b = false) → k ∈ rho.sel r :=
    fun o ho k r ha _ => rho.deliver_selected nd v p t ho ha
  have hs' : ∀ o ∈ nd.seen ++ [p], rho.Authorized o := by
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hs o ho
    · rw [List.mem_singleton.mp ho]; exact hp
  obtain ⟨cs, -, h2, h1⟩ := rho.deliver_flat nd v p t
  rw [h2] at hr ⊢
  rw [h1]
  exact releaseAll_preserves rho.hash _
    (fun d => ∀ k r, d.auth = .signed k r →
      (∀ b, d.msg = .data b → (protoOf F E).voteBody b = false) → k ∈ rho.sel r) _ _ hs' hr

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
          exact (rho.deliver_authorized _ v p t (old v) (hd k (by omega) v p t he)).1 o
            (by simpa [step] using ho)
        · exact old w o (by simpa [step, hw] using ho)

/-- If every object delivered at an event `k ≤ i` is authorized, so is every
object released at event `i` (a delivery at `i` releases from its object). -/
theorem releasesAt_authorized (i : Nat)
    (hd : ∀ k ≤ i, ∀ w o t, rho.events[k]? = some (.deliver w o t) → rho.Authorized o) :
    ∀ o ∈ rho.releasesAt i, rho.Authorized o := by
  cases he : rho.events[i]? with
  | none => simp [releasesAt, he]
  | some e =>
    cases e with
    | tick v t =>
      simp only [releasesAt, he]
      exact (rho.tick_authorized _ v t
        (rho.seen_authorized i (fun k hk => hd k hk.le) v)).2
    | deliver v p t =>
      simp only [releasesAt, he]
      exact (rho.deliver_authorized _ v p t
        (rho.seen_authorized i (fun k hk => hd k hk.le) v) (hd i le_rfl v p t he)).2
    | restart v t => simp [releasesAt, he]

/-- Every signed object inside anything an honest node observed, other than a delegated vote
body, is signed by a key selected for its role ("provenance = authorized signer"). A delegated
vote body's signer is a member through its verified evidence instead. -/
theorem selected_of_observed (hv : rho.ExecutionValid) {o : (protoOf F E).Object}
    (ho : o ∈ rho.Observed) {o' : (protoOf F E).Object} (hc : Obj.Contains o o')
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} (ha : o'.auth = .signed k r)
    (hb : ∀ b, o'.msg = .data b → (protoOf F E).voteBody b = false) :
    k ∈ rho.sel r := by
  have hd : ∀ i, ∀ j ≤ i, ∀ w o t, rho.events[j]? = some (Event.deliver w o t) →
      rho.Authorized o :=
    fun _ j _ w o t he => hv.credentials.2 j w o t he
  obtain ⟨v, i, _, _, hov⟩ := ho
  obtain ⟨j, o₀, _, hr, hc₀⟩ := rho.mem_viewIdx_iff.mp hov
  rcases hr with ⟨t, _, hr⟩ | ⟨t, he⟩
  · exact rho.releasesAt_authorized j (hd j) o₀ hr o' (hc₀.trans hc) k r ha hb
  · exact hv.credentials.2 j v o₀ t he o' (hc₀.trans hc) k r ha hb

/-- A causal network (every delivery is an earlier release) delivers only
authorized objects: `OtherCredentials` holds, and with `VoteVerification`, `Credentials`. -/
theorem credentials_of_causal (hvv : rho.VoteVerification) (hc : rho.Causal) :
    rho.Credentials := by
  have D : ∀ i : Nat, ∀ k < i, ∀ w o t, rho.events[k]? = some (Event.deliver w o t) →
      rho.Authorized o := by
    intro i
    induction i with
    | zero => intro k hk; omega
    | succ i ih =>
      intro k hk w o t he
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ih k hk w o t he
      · obtain ⟨j, _, _, hj, _, hjo⟩ := causal_iff.mp hc k w o t he
        exact rho.releasesAt_authorized j (fun m hm => ih m (by omega)) o hjo
  exact ⟨hvv, fun i w o t he => D (i + 1) i (by omega) w o t he⟩

omit [DecidableEq V] in
/-- **The own issuer gate.** A node's own issuer gives evidence for data `d` in role `r` exactly
when a role that selects its own key, and then the run's issued evidence for its own claim. -/
theorem voteIO_own_eq_some_iff (v : V) (r : (protoOf F E).Role) (d : (protoOf F E).VoteData)
    (z : (protoOf F E).Token) :
    (rho.voteIO v).own r d = some z ↔
      rho.ownKey v ∈ rho.sel r ∧ z = rho.issue (rho.ownKey v, r, d) := by
  simp only [voteIO]
  split_ifs with h <;> simp [h, eq_comm]

omit [DecidableEq V] in
/-- A selected node's own issuer gives evidence. -/
theorem voteIO_own_isSome {v : V} {r : (protoOf F E).Role} (h : rho.ownKey v ∈ rho.sel r)
    (d : (protoOf F E).VoteData) :
    (rho.voteIO v).own r d = some (rho.issue (rho.ownKey v, r, d)) :=
  (rho.voteIO_own_eq_some_iff v r d _).2 ⟨h, rfl⟩

omit [DecidableEq V] in
/-- **Own evidence verifies.** Under `VoteVerification`, evidence the own issuer gives for a
canonical own claim (the data claims the node's own key in that role) passes every node's
check. -/
theorem voteIO_own_check (hvv : rho.VoteVerification) {v : V} {r : (protoOf F E).Role}
    {d : (protoOf F E).VoteData} {z : (protoOf F E).Token}
    (hz : (rho.voteIO v).own r d = some z)
    (hc : (protoOf F E).claim d = some (rho.ownKey v, r)) (w : V) :
    (rho.voteIO w).check (rho.ownKey v) r d z = true := by
  obtain ⟨hs, rfl⟩ := (rho.voteIO_own_eq_some_iff v r d z).1 hz
  exact (hvv.2 _ _ _ _).2 ⟨hc, hs, rfl⟩

end Run
end Consensus.Model
end
