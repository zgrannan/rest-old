open nat

mutual def f,g
with f : ℕ → ℕ
| (succ x) := have 1 < 1, from sorry, g (succ x)
| zero     := zero
with g : ℕ → ℕ
| (succ x) := have x < succ x, from lt_succ_self x, f x
| zero     := zero

theorem diverge (x : ℕ): f x = g (succ (succ x)) := sorry

theorem proof (x : ℕ) : g x = f x := begin
    simp [diverge]
end
