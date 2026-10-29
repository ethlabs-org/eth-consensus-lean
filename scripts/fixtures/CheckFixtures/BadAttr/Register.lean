module
public meta import Lean

@[expose] public section

meta initialize fixtureTag : Lean.TagAttribute ← Lean.registerTagAttribute `fixture_tag "fixture attribute"
