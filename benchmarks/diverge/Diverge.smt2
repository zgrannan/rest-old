(set-logic ALL)
(declare-datatype Nat ( (z) (s (p Nat)) ))
(define-funs-rec ((f ((x Nat)) Nat) (g ((y Nat)) Nat)) (

(f (match x (
  (z z)
  ((s a) (g (s a)))
)))
(g (match y (
  (z z)
  ((s b) (f b))
)))
))

(assert (not
  (=>
    (forall ((y Nat)) (= (f y) (g (s (s y)))))
    (forall ((x Nat)) (= (f x) (g x)))
  ))
)

; (assert (not (forall ((x Nat)) (= (f x) (g x)))))
(check-sat)
