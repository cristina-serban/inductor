; An acyclic list segment of lists is a list segment of lists

(set-logic SEPLOGLIA)

(declare-datatypes ((Node 0)) (((node (left Int) (right Int)))))

(define-fun-rec list ((x Int)) Bool
        (or (emp)
            (exists ((y Int))
                (sep (pto x (node y 0)) (list y)))
        )
)

(define-fun-rec lls ((x Int) (y Int)) Bool
        (or (sep (= x y) emp)
            (exists ((z Int) (u Int))
                (sep (pto x (node u z)) (list u) (lls z y)))
        )
)

(define-fun-rec llsa ((x Int) (y Int)) Bool
        (or (sep (= x y) emp)
            (exists ((z Int) (u Int))
                (sep (distinct x y) (pto x (node u z)) (list u) (llsa z y)))
        )
)

(declare-const x Int)
(declare-const y Int)

(assert ((=> (llsa x y) (lls x y))))