module
public import CheckFixtures.RootAxiom.A

@[expose] public section

axiom CheckFixtures.RootAxiom.ax : False

theorem CheckFixtures.RootAxiom.u : False := CheckFixtures.RootAxiom.ax
