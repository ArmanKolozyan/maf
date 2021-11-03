; Changes:
; * removed: 1
; * added: 0
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((inport #f)
         (outport #f)
         (catport (lambda (port)
                    (let ((x (read-char port)))
                       (if (eof-object? x)
                          (close-output-port outport)
                          (begin
                             (write-char x outport)
                             (catport port))))))
         (go (lambda ()
               (set! inport (open-input-file "input.txt"))
               (<change>
                  (set! outport (open-output-file "output.txt"))
                  ())
               (catport inport)
               (close-input-port inport))))
   (go))