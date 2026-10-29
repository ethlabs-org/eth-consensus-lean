Header-only fixtures for `review_imports` (step 6 of scripts/check.sh; never built): the tests root must
import the review-pins module (`Fx.ReviewAxioms` here) directly. `Direct.lean` passes; `Indirect.lean`
(only through `Fx.Helper`, see `Helper.lean`) and `Missing.lean` fail with FAIL[review].
