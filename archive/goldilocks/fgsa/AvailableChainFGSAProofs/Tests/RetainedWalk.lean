module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedWalk

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.RetainedWalk

open AvailableChain.SimplexFG
open Gen.Pure

/-- Blueprint 21:787–806; spec 1063–1107. Class (iii).
DC: INTENTIONAL; finite FG-SA fixture for the retained prefix. -/
private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

/-- Blueprint 21:787–806; spec 1063–1107. Class (iii).
DC: INTENTIONAL; the first retained child. -/
private def pfg : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
/-- Blueprint 21:787–806; spec 1063–1107. Class (iii).
DC: INTENTIONAL; the supported retained child. -/
private def qfg : FGBlock (Fin 1) := .node pfg 2 ⟨2⟩ 0 []
/-- Blueprint 21:787–806; spec 1063–1107. Class (iii).
DC: INTENTIONAL; an eligible rival of the supported child. -/
private def rfg : FGBlock (Fin 1) := .node pfg 3 ⟨3⟩ 1 []
/-- Blueprint 21:812–814; spec 1276–1302. Class (iii).
DC: INTENTIONAL; the proposal after the retained parent. -/
private def bfg : FGBlock (Fin 1) := .node qfg 3 ⟨4⟩ 0 []
/-- Blueprint 21:787–814; spec 1025–1037. Class (iii).
DC: INTENTIONAL; the finite target duty store. -/
private def fixture : State 1 :=
  { initial 1 with
    base := { (initial 1).base with
      now := 12
      blocks := [.genesis, eraseFG pfg, eraseFG qfg, eraseFG rfg]
      votes := [⟨.seat 2 0, .head (eraseFG qfg).root⟩]
      voteStamp := [(⟨.seat 2 0, .head (eraseFG qfg).root⟩, 0)]
      blockStamp := [(.genesis, 0), (eraseFG pfg, 0), (eraseFG qfg, 0), (eraseFG rfg, 0)] }
    fg := { TF := {.genesis, pfg, qfg, rfg}, F := .genesis, J := .genesis, h_j := 0, h_max := 1 } }

/-- Blueprint 21:787–806; spec 1086–1098. Class (iii).
DC: INTENTIONAL; expose strict ancestry only inside this finite test. -/
private theorem strict_order (A B : Block) (h : Block.Prec A B) :
    A ≠ B ∧ Block.Preceq A B := by
  simpa only [Block.Prec, Block.Preceq, Block.prec, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] using h

/-- Blueprint 21:787–806, 2822–2845; spec 1063–1107. Class (iii).
DC: INTENTIONAL; S2 has two actual edges, including a rival with score zero. -/
private theorem trunk_and_support :
    BestAncestry (RetainedWalk.ay params fixture) (eraseFG qfg)
      (RetainedWalk.T params fixture 3) (RetainedWalk.ts params fixture 3)
      (RetainedWalk.et params fixture 3) := by
  apply fgsa_retained_prefix_of_trunk_or_support
  intro X _ hX
  obtain ⟨hne, hle⟩ := strict_order _ _ hX
  change (decide (X = eraseFG qfg) ||
    (decide (X = eraseFG pfg) || decide (X = .genesis))) = true at hle
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hle
  rcases hle with hq | hp | hg
  · exact (hne hq).elim
  · subst X
    refine ⟨eraseFG qfg, rfl, by decide +kernel, by decide +kernel,
      by decide +kernel, Or.inr ⟨1, 0, by decide, by decide +kernel, ?_⟩⟩
    decide +kernel
  · subst X
    refine ⟨eraseFG pfg, rfl, by decide +kernel, by decide +kernel,
      by decide +kernel, Or.inl ?_⟩
    decide +kernel

/-- Blueprint 21:787–806; spec 1063–1107. Class (iii).
DC: INTENTIONAL; the supported branch has an eligible stored rival. -/
private theorem prefix_nonvacuous :
    Block.Prec .genesis (eraseFG pfg) ∧ Block.Prec (eraseFG pfg) (eraseFG qfg) ∧
    eraseFG rfg ∈ RetainedWalk.T params fixture 3 ∧
    RetainedWalk.et params fixture 3 (eraseFG rfg) = true ∧
    RetainedWalk.ts params fixture 3 (eraseFG qfg) = 1 ∧
    RetainedWalk.ts params fixture 3 (eraseFG rfg) = 0 := by decide +kernel

/-- Blueprint 21:798–809; spec 1025–1037, 1219–1226. Class (iii).
DC: INTENTIONAL; S3 uses a different descendant in a proper duty subset. -/
private theorem internal_witness :
    eraseFG pfg ∈ erasedList fixture (domainR params fixture {pfg, qfg}) := by
  apply fgsa_walk_domain_of_witness params fixture {pfg, qfg} pfg qfg
  all_goals decide +kernel

/-- Blueprint 21:783–814; spec 1063–1114. Class (iii).
DC: INTENTIONAL; concrete geometry with a nonempty target prefix. -/
private theorem walk_geometry :
    RetainedWalkRunGeometry params fixture fixture 3 .genesis (eraseFG bfg) (eraseFG qfg) := by
  refine ⟨by decide +kernel, fgsa_Z_preceq_liveRoot params fixture, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, trunk_and_support, ?_, ?_, ?_⟩
  · intro X _ hX
    change Block.Prec X .genesis at hX
    have h := strict_order _ _ hX
    exact (h.1 (of_decide_eq_true h.2)).elim
  all_goals
    intro X C hle hlt
    have h := strict_order _ _ hlt
    exact (h.1 (block_preceq_antisymm h.2 hle)).elim

/-- Blueprint 21:812–814; spec 1276–1302. Class (iii).
DC: INTENTIONAL; a concrete store with one current proposal. -/
private def endpointFixture : State 1 :=
  { fixture with
    base := { fixture.base with blocks := [.genesis, eraseFG pfg, eraseFG qfg, eraseFG bfg] }
    fg := { fixture.fg with TF := {.genesis, pfg, qfg, bfg} } }

/-- Blueprint 21:812–814, 2865–2872; spec 1276–1302. Class (iii).
DC: INTENTIONAL; all eight endpoint fields have concrete witnesses. -/
private theorem endpoint_geometry :
    RetainedEndpointGeometry params fixture endpointFixture 3 (eraseFG bfg) := by
  constructor <;> decide +kernel

/-- Blueprint 21:787–806; spec 1086–1098. Class (iii).
DC: INTENTIONAL; the same start adapter applies to both reads. -/
private theorem actual_starts :
    Block.Preceq (RetainedWalk.z params fixture) (RetainedWalk.ap params fixture) ∧
    Block.Preceq (RetainedWalk.z params endpointFixture) (RetainedWalk.ay params endpointFixture) :=
  ⟨fgsa_Z_preceq_liveRoot params fixture, fgsa_Z_preceq_liveRoot params endpointFixture⟩

end AvailableChain.FGSA.Run.Tests.RetainedWalk
