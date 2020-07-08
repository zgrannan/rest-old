theory AddCommute
  imports Main 
begin

datatype N = S N | Z

primrec add :: "N \<Rightarrow> N \<Rightarrow> N" where
  "add m Z = m"
| "add m (S n) = S (add m n)"

theorem comm [simp] : "add p q = add q p" sorry

theorem assoc [simp] : "add (add p q) r = add p (add q r)" sorry

theorem ac : "add p (add q r) = add q (add r p)"
  apply(auto)
done
end
