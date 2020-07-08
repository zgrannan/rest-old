(set-logic ALL)
(declare-datatype Nat ( (z) (s (p Nat)) ))
(define-fun-rec plus ((m Nat) (n Nat)) Nat (
  match n (
    (z m)
    ((s nn) (s (plus m nn)))
  )
))

(assert
  (not
  (forall ((p Nat) (q Nat) (r Nat))
    (=>
        (and
            (forall ((a Nat) (b Nat)) (= (plus a b) (plus b a)))
            (forall ((x Nat) (y Nat) (z Nat)) (= (plus (plus x y) z) (plus x (plus y z))))
        )
        (= (plus (plus p q) r) (plus r q) p)
    )
  ))
)

(check-sat)
