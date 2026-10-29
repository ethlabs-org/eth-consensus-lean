module

@[expose] public section

namespace CheckFixtures.BadNative

theorem n : 2 + 2 = 4 := by native_decide

end CheckFixtures.BadNative
