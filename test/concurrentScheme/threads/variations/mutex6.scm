(letrec ((lock #f)
         (acq (lambda ()
                (if (cas lock #f #t)
                    #t
                    (acq))))
         (rel (lambda ()
                (set! lock #f)))
         (counter 0)
         (inc (lambda ()
                (acq)
                (set! counter (+ counter 1))
                (rel)))
         (t1 (fork (inc)))
         (t2 (fork (inc)))
         (t3 (fork (inc)))
         (t4 (fork (inc)))
         (t5 (fork (inc)))
         (t6 (fork (inc))))
  (join t1)
  (join t2)
  (join t3)
  (join t4)
  (join t5)
  (join t6)
  #t)