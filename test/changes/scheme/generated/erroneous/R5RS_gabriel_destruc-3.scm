; Changes:
; * removed: 1
; * added: 1
; * swaps: 4
; * negated predicates: 0
; * swapped branches: 2
; * calls to id fun: 2
(letrec ((append-to-tail! (lambda (x y)
                            (<change>
                               @sensitivity:FA
                               (if (null? x)
                                  y
                                  ((letrec ((loop (lambda (a b)
                                                   @sensitivity:FA
                                                   (if (null? b)
                                                      (begin
                                                         (set-cdr! a y)
                                                         x)
                                                      (loop b (cdr b))))))
                                     loop)
                                     x
                                     (cdr x))))
                            (<change>
                               (if (null? x)
                                  y
                                  ((letrec ((loop (lambda (a b)
                                                   @sensitivity:FA
                                                   (if (null? b)
                                                      (begin
                                                         (set-cdr! a y)
                                                         x)
                                                      (loop b (cdr b))))))
                                     loop)
                                     x
                                     (cdr x)))
                               @sensitivity:FA)))
         (destructive (lambda (n m)
                        @sensitivity:FA
                        (let ((l (letrec ((__do_loop (lambda (i a)
                                                      (<change>
                                                         @sensitivity:FA
                                                         ())
                                                      (if (= i 0) a (__do_loop (- i 1) (cons () a))))))
                                   (__do_loop 10 ()))))
                           (letrec ((__do_loop (lambda (i)
                                                 @sensitivity:No
                                                 (if (= i 0)
                                                    l
                                                    (begin
                                                       (<change>
                                                          (if (null? (car l))
                                                             (letrec ((__do_loop (lambda (l)
                                                                                   @sensitivity:FA
                                                                                   (if (null? l)
                                                                                      #f
                                                                                      (begin
                                                                                         (if (null? (car l)) (set-car! l (cons () ())) #f)
                                                                                         (append-to-tail!
                                                                                            (car l)
                                                                                            (letrec ((__do_loop (lambda (j a)
                                                                                                                  @sensitivity:No
                                                                                                                  (if (= j 0) a (__do_loop (- j 1) (cons () a))))))
                                                                                               (__do_loop m ())))
                                                                                         (__do_loop (cdr l)))))))
                                                                (__do_loop l))
                                                             (letrec ((__do_loop (lambda (l1 l2)
                                                                                   @sensitivity:FA
                                                                                   (if (null? l2)
                                                                                      #f
                                                                                      (begin
                                                                                         (set-cdr!
                                                                                            (letrec ((__do_loop (lambda (j a)
                                                                                                                  @sensitivity:FA
                                                                                                                  (if (zero? j)
                                                                                                                     a
                                                                                                                     (begin
                                                                                                                        (set-car! a i)
                                                                                                                        (__do_loop (- j 1) (cdr a)))))))
                                                                                               (__do_loop (quotient (length (car l2)) 2) (car l2)))
                                                                                            (let ((n (quotient (length (car l1)) 2)))
                                                                                               (if (= n 0)
                                                                                                  (begin
                                                                                                     (set-car! l1 ())
                                                                                                     (car l1))
                                                                                                  (letrec ((__do_loop (lambda (j a)
                                                                                                                        @sensitivity:FA
                                                                                                                        (if (= j 1)
                                                                                                                           (let ((x (cdr a)))
                                                                                                                              (set-cdr! a ())
                                                                                                                              x)
                                                                                                                           (begin
                                                                                                                              (set-car! a i)
                                                                                                                              (__do_loop (- j 1) (cdr a)))))))
                                                                                                     (__do_loop n (car l1))))))
                                                                                         (__do_loop (cdr l1) (cdr l2)))))))
                                                                (__do_loop l (cdr l))))
                                                          (__do_loop (- i 1)))
                                                       (<change>
                                                          (__do_loop (- i 1))
                                                          (if (null? (car l))
                                                             (letrec ((__do_loop (lambda (l1 l2)
                                                                                   @sensitivity:FA
                                                                                   (if (null? l2)
                                                                                      #f
                                                                                      (begin
                                                                                         (set-cdr!
                                                                                            (letrec ((__do_loop (lambda (j a)
                                                                                                                  @sensitivity:FA
                                                                                                                  (if (zero? j)
                                                                                                                     a
                                                                                                                     (begin
                                                                                                                        (__do_loop (- j 1) (cdr a))
                                                                                                                        (set-car! a i))))))
                                                                                               (__do_loop (quotient (length (car l2)) 2) (car l2)))
                                                                                            (let ((n (quotient (length (car l1)) 2)))
                                                                                               (if (= n 0)
                                                                                                  (begin
                                                                                                     (set-car! l1 ())
                                                                                                     (car l1))
                                                                                                  (letrec ((__do_loop (lambda (j a)
                                                                                                                        @sensitivity:FA
                                                                                                                        (if (= j 1)
                                                                                                                           (let ((x (cdr a)))
                                                                                                                              (set-cdr! a ())
                                                                                                                              x)
                                                                                                                           (begin
                                                                                                                              (set-car! a i)
                                                                                                                              (__do_loop (- j 1) (cdr a)))))))
                                                                                                     (__do_loop n (car l1))))))
                                                                                         (__do_loop (cdr l1) (cdr l2)))))))
                                                                (__do_loop l (cdr l)))
                                                             (letrec ((__do_loop (lambda (l)
                                                                                   @sensitivity:FA
                                                                                   (if (null? l)
                                                                                      (begin
                                                                                         (if (null? (car l)) (set-car! l (cons () ())) #f)
                                                                                         (append-to-tail!
                                                                                            (car l)
                                                                                            (letrec ((__do_loop (lambda (j a)
                                                                                                                  @sensitivity:No
                                                                                                                  (if (= j 0) a (__do_loop (- j 1) (cons () a))))))
                                                                                               (__do_loop m ())))
                                                                                         (letrec ((__do_loop (lambda (j a)
                                                                                                               (if (= j 0) a (__do_loop (- j 1) (cons () a)))
                                                                                                               @sensitivity:No)))
                                                                                            (__do_loop m ()))
                                                                                         ((lambda (x) x) (__do_loop (cdr l))))
                                                                                      #f))))
                                                                (__do_loop l)))))))))
                              (__do_loop n))))))
   (<change>
      (equal?
         (destructive 600 50)
         (__toplevel_cons
            (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))
            (__toplevel_cons
               (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 ())))
               (__toplevel_cons
                  (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ()))))
                  (__toplevel_cons
                     (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 ()))))
                     (__toplevel_cons
                        (__toplevel_cons
                           1
                           (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                        (__toplevel_cons
                           (__toplevel_cons
                              1
                              (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                           (__toplevel_cons
                              (__toplevel_cons
                                 1
                                 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                              (__toplevel_cons
                                 (__toplevel_cons
                                    1
                                    (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                                 (__toplevel_cons
                                    (__toplevel_cons
                                       1
                                       (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                                    (__toplevel_cons
                                       (__toplevel_cons
                                          1
                                          (__toplevel_cons
                                             1
                                             (__toplevel_cons
                                                1
                                                (__toplevel_cons
                                                   1
                                                   (__toplevel_cons
                                                      1
                                                      (__toplevel_cons
                                                         1
                                                         (__toplevel_cons
                                                            1
                                                            (__toplevel_cons
                                                               1
                                                               (__toplevel_cons
                                                                  1
                                                                  (__toplevel_cons
                                                                     1
                                                                     (__toplevel_cons
                                                                        1
                                                                        (__toplevel_cons
                                                                           1
                                                                           (__toplevel_cons
                                                                              1
                                                                              (__toplevel_cons
                                                                                 1
                                                                                 (__toplevel_cons
                                                                                    1
                                                                                    (__toplevel_cons
                                                                                       2
                                                                                       (__toplevel_cons
                                                                                          2
                                                                                          (__toplevel_cons 2 (__toplevel_cons 2 (__toplevel_cons 2 (__toplevel_cons 3 ())))))))))))))))))))))
                                       ())))))))))))
      ((lambda (x) x)
         (equal?
            (destructive 600 50)
            (__toplevel_cons
               (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))
               (__toplevel_cons
                  (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 ())))
                  (__toplevel_cons
                     (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ()))))
                     (__toplevel_cons
                        (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 ()))))
                        (__toplevel_cons
                           (__toplevel_cons
                              1
                              (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                           (__toplevel_cons
                              (__toplevel_cons
                                 1
                                 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                              (__toplevel_cons
                                 (__toplevel_cons
                                    1
                                    (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                                 (__toplevel_cons
                                    (__toplevel_cons
                                       1
                                       (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                                    (__toplevel_cons
                                       (__toplevel_cons
                                          1
                                          (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 1 (__toplevel_cons 2 ())))))
                                       (__toplevel_cons
                                          (__toplevel_cons
                                             1
                                             (__toplevel_cons
                                                1
                                                (__toplevel_cons
                                                   1
                                                   (__toplevel_cons
                                                      1
                                                      (__toplevel_cons
                                                         1
                                                         (__toplevel_cons
                                                            1
                                                            (__toplevel_cons
                                                               1
                                                               (__toplevel_cons
                                                                  1
                                                                  (__toplevel_cons
                                                                     1
                                                                     (__toplevel_cons
                                                                        1
                                                                        (__toplevel_cons
                                                                           1
                                                                           (__toplevel_cons
                                                                              1
                                                                              (__toplevel_cons
                                                                                 1
                                                                                 (__toplevel_cons
                                                                                    1
                                                                                    (__toplevel_cons
                                                                                       1
                                                                                       (__toplevel_cons
                                                                                          2
                                                                                          (__toplevel_cons
                                                                                             2
                                                                                             (__toplevel_cons 2 (__toplevel_cons 2 (__toplevel_cons 2 (__toplevel_cons 3 ())))))))))))))))))))))
                                          ()))))))))))))))