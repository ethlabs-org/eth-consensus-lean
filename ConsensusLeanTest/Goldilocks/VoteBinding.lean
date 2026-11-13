module
public import ConsensusLean.Instances.Goldilocks.AsChainShape

public section

/-! # Stock vote-binding regression

The legacy constructors below retain the population instance's bodies, with only the
permission arguments forced by the model interface. No production module imports them.
-/

namespace Consensus.Goldilocks.AsChainShape.Regression
open Blocks Shape
open Consensus.Model (Public)
open SA (SAParams ReplayOrder)

def legacySkeleton (pub : Public) : Skeleton pub.n where
  grid := ⟨4 * pub.ΔAC, mul_pos (by decide) pub.ΔAC_pos⟩
  proposerSel := fun _ => .sized 1
  pollSel := .fixed Finset.univ
  Kind := Empty
  decKind := inferInstance
  kinds := []
  phase := fun k => k.elim
  kindSel := fun k => k.elim
  order := [.poll, .poll, .pollPropose, .propose, .poll, .poll]
  deliverOrder := [.poll]

noncomputable def legacyShape (sp : SAParams)
    (ro : ReplayOrder sp (List (FG.Att sp.n))) : ChainShape sp.pub Out Info where
  skel := { legacySkeleton sp.pub with grid := ⟨4 * sp.Δ, mul_pos (by decide) sp.toParams.hΔ⟩ }
  State := State sp ro (binding := stock)
  Body := Body
  Durable := State sp ro (binding := stock)
  decBody := inferInstance
  init k _ := ⟨k, Node.init (goldilocksNode sp ro), 0, [], [], false, fun _ => none, [], []⟩
  clock st t := { st with now := t }
  propose := propose
  act := fun _ _ k => k.elim
  pollPropose st _ := (nodeTick st, none)
  poll := poll
  pollBatch := pollBatch
  gossip st _ :=
    match st.relayBuf with
    | [] => []
    | cs => [(.data .relay, cs)]
  process := process
  dependencies := dependencies sp.n (binding := stock)
  recordOwn := recordOwn
  durable := id
  restore := restore
  out g st := outOf st.node st.now g
  conflicts := conflicts (binding := stock)
  isFGAtt := isFGAtt (binding := stock)

noncomputable def legacyGoldilocks (S : Setup) : ChainShapeFamily schema Info := fun pub =>
  let G := fun hn : 1 ≤ pub.n => legacyShape (S.params pub hn) (S.ro _)
  { skel := legacySkeleton pub
    State := PubState S pub (binding := stock)
    Body := Body
    Durable := PubState S pub (binding := stock)
    decBody := inferInstance
    init := fun k p hn => (G hn).init k p
    clock := fun st t hn => (G hn).clock (st hn) t
    propose := fun st s =>
      if hn : 1 ≤ pub.n then (fun _ => ((G hn).propose (st hn) s).1, ((G hn).propose (st hn) s).2)
      else (st, none)
    act := fun _ _ k => k.elim
    pollPropose := fun st t =>
      if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollPropose (st hn) t).1, ((G hn).pollPropose (st hn) t).2)
      else (st, none)
    poll := fun st t =>
      if hn : 1 ≤ pub.n then (fun _ => ((G hn).poll (st hn) t).1, ((G hn).poll (st hn) t).2)
      else (st, none)
    pollBatch := fun st t =>
      if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollBatch (st hn) t).1, ((G hn).pollBatch (st hn) t).2)
      else (st, [])
    gossip := fun st t => if hn : 1 ≤ pub.n then (G hn).gossip (st hn) t else []
    process := fun st o hs hn => (G hn).process (st hn) o hs
    dependencies := dependencies pub.n (binding := stock)
    recordOwn := fun st o hs hn => (G hn).recordOwn (st hn) o hs
    durable := id
    restore := fun k d t hn => (G hn).restore k (d hn) t
    out := fun g st => if hn : 1 ≤ pub.n then (G hn).out g (st hn) else []
    conflicts := conflicts (binding := stock)
    isFGAtt := isFGAtt (binding := stock) }

/-- The public stock subject reduces to the stock binding without a transport. -/
theorem goldilocks_stock (S : Setup) : goldilocks S = goldilocksWith ⟨S, stock⟩ := by rfl

/-- The generic stock instance equals the legacy population shape. -/
theorem stock_legacy (S : Setup) : goldilocksWith ⟨S, stock⟩ = legacyGoldilocks S := by
  funext pub
  let X := goldilocksWith ⟨S, stock⟩ pub
  have hphase : (fun _ => 0 : X.skel.Kind → Nat) = fun k => Empty.elim k :=
    funext fun k => nomatch k
  have hact : (fun st _ _ => (st, none) : X.State → Slot → X.skel.Kind →
      X.State × Option (X.Body × List (ShapeObj pub.n X.skel.Kind Info X.Body))) =
      fun _ _ k => Empty.elim k :=
    funext fun _ => funext fun _ => funext fun k => nomatch k
  calc
    X = { X with
      skel := { X.skel with phase := fun _ => 0 }
      act := fun st _ _ => (st, none) } := rfl
    _ = { X with
      skel := { X.skel with phase := fun k => Empty.elim k }
      act := fun _ _ k => Empty.elim k } :=
      congrArg₂ (fun p a => { X with skel := { X.skel with phase := p }, act := a }) hphase hact
    _ = legacyGoldilocks S pub := by
      dsimp only [X, goldilocksWith, legacyGoldilocks]
      congr 1
      funext st t
      by_cases hn : 1 ≤ pub.n
      · simp only [hn, ↓reduceDIte, goldilocksShape, legacyShape]
        cases (st hn).relayBuf <;> rfl
      · simp only [hn, ↓reduceDIte]
        rfl

end Consensus.Goldilocks.AsChainShape.Regression
