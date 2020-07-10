open nat

def sumSeries : ℕ → ℕ
| zero       := zero
| (succ n)   := succ n + sumSeries n

def sumSeries' : ℕ → ℕ
| n := (n * (succ n)) / 2

theorem isOpt : ∀ (n : ℕ) , sumSeries n = sumSeries' n := sorry

theorem proof (n : ℕ) (f : ℕ -> ℕ → ℕ) : f (sumSeries n) = f (sumSeries' n) := by simp [isOpt]
