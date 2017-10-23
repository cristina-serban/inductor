; A tree with at least one element is a tree

(set-logic SEPLOGLIA)

(declare-datatypes ((Node 0)) (((node (left Int) (right Int)))))

(define-fun-rec tree ((x Int)) Bool
        (or (emp)
            (exists ((l Int) (r Int)) (sep (pto x (node l r)) (tree l) (tree r)))
        )
)

(define-fun-rec treep ((x Int)) Bool
        (or (exists ((l Int) (r Int)) (pto x (node l r)))
            (exists ((l Int) (r Int)) (sep (pto x (node l r)) (treep l) (tree r)))
            (exists ((l Int) (r Int)) (sep (pto x (node l r)) (tree l) (treep r)))
        )
)

(declare-const x Int)

(assert ((=> (tree x) (treep x))))