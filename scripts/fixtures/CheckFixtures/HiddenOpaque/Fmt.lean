module
public import CheckFixtures.HiddenOpaqueDep

@[expose] public section

/-! A formatting definition (a `ToString` instance): check-decls does not check it for reaches-opaque. -/

namespace CheckFixtures.HiddenOpaque.Fmt

instance fmt : ToString Unit := ⟨fun _ => toString CheckFixtures.HiddenOpaqueDep.secret⟩

end CheckFixtures.HiddenOpaque.Fmt
