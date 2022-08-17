(define Capacity (int-top))
(define Haircuts (int-top))

(define waiting-room
  (actor "waiting-room" (waiting-customers barber-asleep)
           (enter (customer)
                  (if (= (length waiting-customers) Capacity)
                      (begin
                        (send customer full)
                        (become waiting-room waiting-customers barber-asleep))
                      (begin
                        (if barber-asleep
                            (begin
                              (send a/self next)
                              (become waiting-room (cons customer waiting-customers) #t))
                            (begin
                              (send customer wait)
                              (become waiting-room (cons customer waiting-customers) #f))))))
           (next ()
                 (if (pair? waiting-customers)
                     (let ((c (car waiting-customers)))
                       (send barber-actor enter c a/self)
                       (become waiting-room (cdr waiting-customers) barber-asleep))
                     (begin
                       (send barber-actor wait)
                       (become waiting-room waiting-customers #t))))
           (exit ()
                 (send barber-actor exit)
                 (terminate))))
(define barber
  (actor "barber" ()
           (enter (customer room)
                  (send customer start)
                  (send customer done)
                  (send room next)
                  (become barber))
           (wait ()
                 (become barber))
           (exit ()
                 (terminate))))
(define customer-factory
  (actor "customer-factory" (hairs-cut-so-far id-gen)
           (start ()
                  (letrec ((loop (lambda (i)
                                   (if (= i Haircuts)
                                       #f
                                       (let ((c (create customer (+ i id-gen))))
                                         (send waiting-room-actor enter c)
                                         (loop (+ i 1)))))))
                    (loop 0)
                    (become customer-factory hairs-cut-so-far (+ id-gen Haircuts))))
           (returned (customer)
                     (send waiting-room-actor enter customer)
                     (become customer-factory hairs-cut-so-far (+ id-gen 1)))
           (done ()
                 (if (= (+ hairs-cut-so-far 1) Haircuts)
                     (begin
                       (send waiting-room-actor exit)
                       (terminate))
                     (become customer-factory (+ 1 hairs-cut-so-far) id-gen)))))
(define customer
  (actor "customer" (id)
           (full ()
                 (send factory-actor returned a/self)
                 (become customer id))
           (wait ()
                 (become customer id))
           (start ()
                  (become customer id))
           (done ()
                 (send factory-actor done)
                 (terminate))))

(define barber-actor (create barber))
(define waiting-room-actor (create waiting-room '() #t))
(define factory-actor (create customer-factory 0 0))
(send factory-actor start)