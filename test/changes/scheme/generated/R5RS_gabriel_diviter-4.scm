; Changes:
; * removed: 1
; * added: 0
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 2
(letrec ((create-n (lambda (n)
                     (<change>
                        @sensitivity:FA
                        ())
                     (letrec ((__do_loop (lambda (n a)
                                           @sensitivity:FA
                                           (if (= n 0) a (__do_loop (- n 1) (cons () a))))))
                        (__do_loop n ()))))
         (*ll* (create-n 200))
         (iterative-div2 (lambda (l)
                           (<change>
                              @sensitivity:FA
                              ((lambda (x) x) @sensitivity:FA))
                           (letrec ((__do_loop (lambda (l a)
                                                 @sensitivity:FA
                                                 (if (null? l)
                                                    a
                                                    (__do_loop (cddr l) (cons (car l) a))))))
                              (<change>
                                 (__do_loop l ())
                                 ((lambda (x) x) (__do_loop l ())))))))
   (equal?
      (iterative-div2 *ll*)
      (__toplevel_cons
         ()
         (__toplevel_cons
            ()
            (__toplevel_cons
               ()
               (__toplevel_cons
                  ()
                  (__toplevel_cons
                     ()
                     (__toplevel_cons
                        ()
                        (__toplevel_cons
                           ()
                           (__toplevel_cons
                              ()
                              (__toplevel_cons
                                 ()
                                 (__toplevel_cons
                                    ()
                                    (__toplevel_cons
                                       ()
                                       (__toplevel_cons
                                          ()
                                          (__toplevel_cons
                                             ()
                                             (__toplevel_cons
                                                ()
                                                (__toplevel_cons
                                                   ()
                                                   (__toplevel_cons
                                                      ()
                                                      (__toplevel_cons
                                                         ()
                                                         (__toplevel_cons
                                                            ()
                                                            (__toplevel_cons
                                                               ()
                                                               (__toplevel_cons
                                                                  ()
                                                                  (__toplevel_cons
                                                                     ()
                                                                     (__toplevel_cons
                                                                        ()
                                                                        (__toplevel_cons
                                                                           ()
                                                                           (__toplevel_cons
                                                                              ()
                                                                              (__toplevel_cons
                                                                                 ()
                                                                                 (__toplevel_cons
                                                                                    ()
                                                                                    (__toplevel_cons
                                                                                       ()
                                                                                       (__toplevel_cons
                                                                                          ()
                                                                                          (__toplevel_cons
                                                                                             ()
                                                                                             (__toplevel_cons
                                                                                                ()
                                                                                                (__toplevel_cons
                                                                                                   ()
                                                                                                   (__toplevel_cons
                                                                                                      ()
                                                                                                      (__toplevel_cons
                                                                                                         ()
                                                                                                         (__toplevel_cons
                                                                                                            ()
                                                                                                            (__toplevel_cons
                                                                                                               ()
                                                                                                               (__toplevel_cons
                                                                                                                  ()
                                                                                                                  (__toplevel_cons
                                                                                                                     ()
                                                                                                                     (__toplevel_cons
                                                                                                                        ()
                                                                                                                        (__toplevel_cons
                                                                                                                           ()
                                                                                                                           (__toplevel_cons
                                                                                                                              ()
                                                                                                                              (__toplevel_cons
                                                                                                                                 ()
                                                                                                                                 (__toplevel_cons
                                                                                                                                    ()
                                                                                                                                    (__toplevel_cons
                                                                                                                                       ()
                                                                                                                                       (__toplevel_cons
                                                                                                                                          ()
                                                                                                                                          (__toplevel_cons
                                                                                                                                             ()
                                                                                                                                             (__toplevel_cons
                                                                                                                                                ()
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   ()
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      ()
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         ()
                                                                                                                                                         (__toplevel_cons
                                                                                                                                                            ()
                                                                                                                                                            (__toplevel_cons
                                                                                                                                                               ()
                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                  ()
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     ()
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        ()
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           ()
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              ()
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 ()
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    ()
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       ()
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          ()
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             ()
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                ()
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   ()
                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                      ()
                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                         ()
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            ()
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               ()
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  ()
                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                     ()
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        ()
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           ()
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              ()
                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                 ()
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    ()
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       ()
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          ()
                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                             ()
                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                ()
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   ()
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      ()
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         ()
                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                            ()
                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                               ()
                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                  ()
                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                     ()
                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                        ()
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           ()
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              ()
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 ()
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    ()
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       ()
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          ()
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             ()
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                ()
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   ()
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      ()
                                                                                                                                                                                                                                                                                                      (__toplevel_cons () (__toplevel_cons () (__toplevel_cons () (__toplevel_cons () ()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))