; A tree with at least one element is a tree

(set-logic SEPLOGLIA)

(declare-datatypes ((Node 0)) (((node (left Int) (right Int)))))

(define-fun-rec tree ((x Int)) Bool
        (or (and (= x (as nil Int)) emp)
            (exists ((l Int) (r Int)) (sep (pto x (node l r)) (tree l) (tree r)))
        )
)

(define-fun-rec treep1 ((x Int)) Bool
        (or (pto x (node (as nil Int) (as nil Int)))
            (exists ((l Int) (r Int)) (sep (pto x (node l r)) (treep1 l) (tree r)))
            (exists ((l Int) (r Int)) (sep (pto x (node l r)) (tree l) (treep1 r)))
        )
)

(define-fun-rec treep2 ((x Int)) Bool
        (or (pto x (node (as nil Int) (as nil Int)))
            (exists ((l Int) (r Int)) (sep (pto x (node l r)) (treep2 l) (treep2 r)))
        )
)

(declare-const x Int)

(assert ((=> (tree x) (treep2 x))))