theory Optimize
  imports Main
begin

datatype N = S N | Z

primrec plus :: "N \<Rightarrow> N \<Rightarrow> N" where
  "plus m Z = m"
| "plus m (S n) = S (plus m n)"

primrec times :: "N \<Rightarrow> N \<Rightarrow> N" where
  "times m Z = Z"
| "times m (S n) = plus m (times m n)"

fun half :: "N \<Rightarrow> N" where
  "half Z = Z"
| "half (S Z) = Z"
| "half (S (S n)) = S (half n)"

primrec sumSeries :: "N \<Rightarrow> N" where
  "sumSeries Z = Z"
| "sumSeries (S n) = plus (S n) (sumSeries n)"

fun sumSeries2 :: "N \<Rightarrow> N" where
  "sumSeries2 n = half (times n (S n))"

theorem eq [simp] : "sumSeries n = sumSeries2 n" sorry

theorem eq2 : "f (sumSeries n) = f (sumSeries2 n)"
  apply(auto)
done
end

