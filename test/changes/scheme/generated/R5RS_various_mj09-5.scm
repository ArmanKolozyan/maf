; Changes:
; * removed: 0
; * added: 1
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((h (lambda (b)
              (letrec ((g (lambda (z)
                            z))
                       (f (lambda (k)
                            (<change>
                               ()
                               (k 1))
                            (if b (k 1) (k 2))))
                       (y (f (lambda (x) x))))
                 (g y))))
         (x (h #t))
         (y (h #f)))
   y)