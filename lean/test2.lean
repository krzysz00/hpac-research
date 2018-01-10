structure S := (m : ℕ) (n: ℕ)

constant M (shape : S) : Type

namespace M

constant arb (shape : S) : M shape
constant zero (shape : S) : M shape
constant one (shape : S) : M shape

constant neg {shape : S} (x : M shape) : M shape
constant add {shape : S} (x y : M shape) : M shape
constant mul {m k n : ℕ} (x : M (S.mk m k)) (y : M (S.mk k n)) : M (S.mk m n)
constant trans {m n : ℕ} (x : M (S.mk m n)) : M (S.mk n m)

@[inline, priority 10000] instance (shape : S) : has_zero (M shape) := ⟨M.zero shape⟩
@[inline, priority 10000] instance (shape : S) : has_one (M shape) := ⟨M.one shape⟩
@[inline, priority 10000] instance (shape : S) : has_neg (M shape) := ⟨M.neg⟩
@[inline, priority 10000] instance (shape : S) : has_add (M shape) := ⟨M.add⟩
@[inline, priority 10000] instance (shape : S) : has_mul (M shape) := ⟨M.mul⟩
end M
