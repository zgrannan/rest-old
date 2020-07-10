(set-logic ALL)
(declare-datatype Nat ( (z) (s (p Nat)) ))

(define-fun-rec plus ((m Nat) (n Nat)) Nat (
  match n (
    (z m)
    ((s nn) (s (plus m nn)))
  )
))

(define-fun-rec times ((m Nat) (n Nat)) Nat (
  match n (
    (z z)
    ((s nn) (plus m (times m nn)))
  )
))

(define-fun-rec half ((n Nat)) Nat (
  match n (
    (z z)
    ((s nn) (match nn ((z z) ((s m) (s (half m))))))
  )
))

(define-fun-rec sumSeries ((n Nat)) Nat (
  match n (
    (z z)
    ((s nn) (plus n (sumSeries nn)))
  )
))

(define-fun-rec sumSeries2 ((n Nat)) Nat
  (half (times n (s n))
))

(assert
 (not
   (forall ((n Nat) (f (Array Nat Nat)))
     (=>
       (forall
         ((m Nat))
         (= (sumSeries m) (sumSeries2 m)))

       (= (select f (sumSeries n)) (select f (sumSeries2 n)))
     )
)))

(check-sat)
