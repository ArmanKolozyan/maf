; Changes:
; * removed: 0
; * added: 1
; * swaps: 1
; * negated predicates: 1
; * swapped branches: 1
; * calls to id fun: 1
(letrec ((inport #f)
         (nl #f)
         (nw #f)
         (nc #f)
         (inword #f)
         (wcport (lambda (port)
                   (<change>
                      ()
                      x)
                   (let ((x (read-char port)))
                      (if (<change> (eof-object? x) (not (eof-object? x)))
                         (begin
                            (list nl nw nc))
                         (begin
                            (<change>
                               (set! nc (+ nc 1))
                               ((lambda (x) x) (set! nc (+ nc 1))))
                            (if (char=? x #\
) (set! nl (+ nl 1)) #f)
                            (if (let ((__or_res (char=? x #\ ))) (if __or_res (<change> __or_res (char=? x #\
)) (<change> (char=? x #\
) __or_res)))
                               (set! inword #f)
                               (if (not inword)
                                  (begin
                                     (set! nw (+ nw 1))
                                     (set! inword #t))
                                  #f))
                            (wcport port))))))
         (go (lambda ()
               (set! inport (open-input-file "input.txt"))
               (<change>
                  (set! nl 0)
                  (set! nw 0))
               (<change>
                  (set! nw 0)
                  (set! nl 0))
               (set! nc 0)
               (set! inword #f)
               (let ((result (wcport inport)))
                  (close-input-port inport)
                  result))))
   (equal? (go) (__toplevel_cons 31102 (__toplevel_cons 851820 (__toplevel_cons 4460056 ())))))