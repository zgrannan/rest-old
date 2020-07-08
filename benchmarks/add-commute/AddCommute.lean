inductive N : Type
| z : N
| s : N → N


def add : N → N → N
| m N.z     := m
| m (N.s n) := N.s (add m n)


theorem comm : ∀ (p q : N), add p q = add q p := sorry

theorem assoc : ∀ (p q r : N), add (add p q) r = add p (add q r) := sorry

theorem simple (p q r : N) : add (add p q) r = add (add r q) p := by simp [comm,assoc]
