; A list segment is a list segment of even length or a list segment of odd length

(set-logic SEPLOGLIA)

(define-fun-rec ls ((x Int) (y Int)) Bool
        (or (and ( = x y) emp)
            (exists ((z Int))
                (sep (pto x z) (ls z y)))
        )
)

(define-funs-rec ((lse ((x Int) (y Int)) Bool) (lso ((x Int) (y Int)) Bool))
        ((or (and ( = x y) emp)
            (exists ((z Int))
                (sep (pto x z) (lso z y)))
        )

        (or (pto x y)
            (exists ((z Int))
                (sep (pto x z) (lse z y)))
        ))
)

(define-fun-rec lseo ((x Int) (y Int)) Bool
        (or (lse x y)
            (lso x y)
        )
)

(declare-const x Int)
(declare-const y Int)

(assert ((=> (ls x y) (lseo x y))))