; Changes:
; * removed: 1
; * added: 0
; * swaps: 0
; * negated predicates: 2
; * swapped branches: 0
; * calls to id fun: 2
(letrec ((result ())
         (output (lambda (i)
                   (set! result (cons i result))))
         (count1 (lambda (x)
                   (<change>
                      (if (= 0 x)
                         (display x)
                         (begin
                            (display x)
                            (count1 (- x 1))))
                      ((lambda (x) x)
                         (if (<change> (= 0 x) (not (= 0 x)))
                            (display x)
                            (begin
                               (<change>
                                  (display x)
                                  ())
                               (count1 (- x 1))))))))
         (count2 (lambda (x)
                   (if (<change> (= 0 x) (not (= 0 x)))
                      (display x)
                      (begin
                         (count2 (- x 1))
                         (display x))))))
   (count1 4)
   (count2 4)
   (<change>
      (equal?
         result
         (__toplevel_cons
            4
            (__toplevel_cons
               3
               (__toplevel_cons
                  2
                  (__toplevel_cons
                     1
                     (__toplevel_cons
                        0
                        (__toplevel_cons
                           0
                           (__toplevel_cons 1 (__toplevel_cons 2 (__toplevel_cons 3 (__toplevel_cons 4 ())))))))))))
      ((lambda (x) x)
         (equal?
            result
            (__toplevel_cons
               4
               (__toplevel_cons
                  3
                  (__toplevel_cons
                     2
                     (__toplevel_cons
                        1
                        (__toplevel_cons
                           0
                           (__toplevel_cons
                              0
                              (__toplevel_cons 1 (__toplevel_cons 2 (__toplevel_cons 3 (__toplevel_cons 4 ()))))))))))))))