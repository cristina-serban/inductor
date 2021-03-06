; An acyclic list segment is a list segment

(set-logic SEPLOGLIA)

(declare-heap (Int Int))

(define-fun-rec ls ((x Int) (y Int)) Bool
        (or (sep (= x y) (_ emp Int Int))
            (exists ((z Int))
                (sep (pto x z) (ls z y)))
        )
)

(define-fun-rec lsa ((x Int) (y Int)) Bool
        (or (sep (= x y) (_ emp Int Int))
            (exists ((z Int))
                (sep (distinct x y) (pto x z) (lsa z y)))
        )
)

(declare-const x Int)
(declare-const y Int)

(assert (ls x y))
(assert (not (lsa x y)))

(check-sat)