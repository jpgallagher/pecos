(set-logic HORN)
(set-info :status sat)
(declare-fun itp (Int Int ) Bool)

(assert (forall ((x1 Int) (x3 Int)) (=> (and (= x1 0) (= x3 0)) (itp x1 x3))))
(assert (forall ((x1 Int) (x3 Int) (x2 Int) (x4 Int))
  (=> (and (itp x1 x3) (= x2 (+ x1 1)) (= x4 (- x3 1))) (itp x2 x4))))
(assert (forall ((x1 Int) (x3 Int))
  (let ((a!1 (and (itp x1 x3) (not (and (>= x1 0) (<= x3 0))))))
    (=> a!1 false))))
(check-sat)

