theory Diverge
  imports Main
begin

datatype N = S N | Z

fun g :: "N \<Rightarrow> N" and f :: "N \<Rightarrow> N"
  where
    "g (S x) = f x"
  | "g Z = Z"
  | "f (S x) = g (S x)"
  | "f Z = Z"

theorem diverge [simp] : "f x = g (S (S x))"
  apply(auto)
  done

theorem eq : "g x = f x"
  apply(simp)
done
end
