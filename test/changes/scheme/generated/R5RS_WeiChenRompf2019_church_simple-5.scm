; Changes:
; * removed: 0
; * added: 3
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((pred (lambda (n)
                 (<change>
                    ()
                    g)
                 (lambda (rf)
                    (lambda (rx)
                       (((n (lambda (g) (lambda (h) (h (g rf))))) (lambda (ignored) rx))
                          (lambda (id)
                             (<change>
                                ()
                                (display id))
                             id))))))
         (church0 (lambda (f0)
                    (lambda (x0)
                       x0)))
         (church1 (lambda (f1)
                    (lambda (x1)
                       (f1 x1))))
         (church0? (lambda (z)
                     (<change>
                        ()
                        zx)
                     ((z (lambda (zx) #f)) #t)))
         (ff (lambda (e)
               (if (church0? e) e (ff ((church1 pred) e))))))
   (ff church1))