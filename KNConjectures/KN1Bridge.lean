-- SPDX-License-Identifier: Apache-2.0
-- Produced by Claude Fable 5.1 (max); released under the Apache License 2.0 (matching the development it is a corollary of).
import KNConjectures.KN1Statement
import KNConjectures.KozmaNitzanConjecture1

/-! The Mathlib-only statement `KN1Statement.MultiplicativeGluing` is, by definitional unfolding, the theorem
`KN1Corollary.kozmaNitzan_conjecture1` declared in `KozmaNitzanConjecture1.lean`, which is proved there
solely from theorems of the development. -/

theorem KN1Statement.multiplicativeGluing_holds : KN1Statement.MultiplicativeGluing :=
  fun n w A hA o b => KN1Corollary.kozmaNitzan_conjecture1 n w A hA o b

#print axioms KN1Statement.multiplicativeGluing_holds
