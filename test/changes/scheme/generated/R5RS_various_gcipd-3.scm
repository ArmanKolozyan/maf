; Changes:
; * removed: 0
; * added: 0
; * swaps: 0
; * negated predicates: 1
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((id (lambda (x)
               x))
         (f (lambda (n)
              (if (<change> (<= n 1) (not (<= n 1)))
                 1
                 (* n (f (- n 1))))))
         (g (lambda (n)
              (if (<= n 1) 1 (+ (* n n) (g (- n 1)))))))
   (+ ((id f) 3) ((id g) 4)))