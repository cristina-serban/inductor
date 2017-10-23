; A list is a list of even length or a list of odd length

(set-logic SEPLOGLIA)

(define-fun-rec list ((x Int)) Bool
        (or (emp)
            (exists ((y Int))
                (sep (pto x y) (list y)))
        )
)

(define-funs-rec ((liste ((x Int)) Bool) (listo ((x Int)) Bool))
        ((or (emp)
            (exists ((y Int))
                (sep (pto x y) (listo y)))
        )

        (or (exists ((y Int)) (pto x y))
            (exists ((y Int))
                (sep (pto x y) (liste y)))
        ))
)

(define-fun-rec listeo ((x Int)) Bool
        (or (liste x)
            (listo x)
        )
)

(declare-const x Int)

(assert ((=> (list x) (listo x))))