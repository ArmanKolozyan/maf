; Changes:
; * removed: 4
; * added: 9
; * swaps: 9
; * negated predicates: 5
; * swapped branches: 2
; * calls to id fun: 6
(letrec ((create-redblack-tree (lambda options
                                 (letrec ((make-null-tree (lambda ()
                                                            (<change>
                                                               ()
                                                               ())
                                                            (list (cons () 'black) () () ()))))
                                    (let* ((content (make-null-tree))
                                           (same? (if (null? options) equal? (car options)))
                                           (less? (if (null? options) < (cadr options))))
                                       (letrec ((make-node (lambda (item left right parent)
                                                             (list (cons item 'red) left right parent)))
                                                (node-item (lambda (node)
                                                             (car (car node))))
                                                (node-color (lambda (node)
                                                              (cdr (car node))))
                                                (node-left (lambda (node)
                                                             (cadr node)))
                                                (node-right (lambda (node)
                                                              (caddr node)))
                                                (node-parent (lambda (node)
                                                               (cadddr node)))
                                                (node-set-item! (lambda (node item)
                                                                  (set-car! (car node) item)))
                                                (node-set-color! (lambda (node color)
                                                                   (set-cdr! (car node) color)))
                                                (node-set-color-red! (lambda (node)
                                                                       (set-cdr! (car node) 'red)))
                                                (node-set-color-black! (lambda (node)
                                                                         (set-cdr! (car node) 'black)))
                                                (node-set-left! (lambda (node son)
                                                                  (set-car! (cdr node) son)))
                                                (node-set-right! (lambda (node son)
                                                                   (set-car! (cddr node) son)))
                                                (node-set-parent! (lambda (node parent)
                                                                    (set-car! (cdddr node) parent)))
                                                (null-tree? (lambda (tree)
                                                              (null? (node-item tree))))
                                                (is-leaf? (lambda (node)
                                                            (if (null-tree? (node-left node))
                                                               (null-tree? (node-right node))
                                                               #f)))
                                                (traverse (lambda (tree order action)
                                                            (<change>
                                                               (letrec ((traverse-preorder (lambda (tree)
                                                                                             (if (null-tree? tree)
                                                                                                #t
                                                                                                (begin
                                                                                                   (action (node-item tree) (node-color tree))
                                                                                                   (traverse-preorder (node-left tree))
                                                                                                   (traverse-preorder (node-right tree))))))
                                                                        (traverse-inorder (lambda (tree)
                                                                                            (if (null-tree? tree)
                                                                                               #t
                                                                                               (begin
                                                                                                  (traverse-inorder (node-left tree))
                                                                                                  (action (node-item tree) (node-color tree))
                                                                                                  (traverse-inorder (node-right tree))))))
                                                                        (traverse-postorder (lambda (tree)
                                                                                              (if (null-tree? tree)
                                                                                                 #t
                                                                                                 (begin
                                                                                                    (traverse-postorder (node-left tree))
                                                                                                    (traverse-postorder (node-right tree))
                                                                                                    (action (node-item tree) (node-color tree)))))))
                                                                  (if (eq? order 'preorder)
                                                                     (traverse-preorder tree)
                                                                     (if (eq? order 'inorder)
                                                                        (traverse-inorder tree)
                                                                        (if (eq? order 'postorder)
                                                                           (traverse-postorder tree)
                                                                           (error "Unknown tree traversal order")))))
                                                               ((lambda (x) x)
                                                                  (letrec ((traverse-preorder (lambda (tree)
                                                                                                (if (<change> (null-tree? tree) (not (null-tree? tree)))
                                                                                                   #t
                                                                                                   (begin
                                                                                                      (action (node-item tree) (node-color tree))
                                                                                                      (traverse-preorder (node-left tree))
                                                                                                      (traverse-preorder (node-right tree))))))
                                                                           (traverse-inorder (lambda (tree)
                                                                                               (if (null-tree? tree)
                                                                                                  (<change>
                                                                                                     #t
                                                                                                     (begin
                                                                                                        (traverse-inorder (node-left tree))
                                                                                                        (action (node-item tree) (node-color tree))
                                                                                                        (traverse-inorder (node-right tree))))
                                                                                                  (<change>
                                                                                                     (begin
                                                                                                        (traverse-inorder (node-left tree))
                                                                                                        (action (node-item tree) (node-color tree))
                                                                                                        (traverse-inorder (node-right tree)))
                                                                                                     #t))))
                                                                           (traverse-postorder (lambda (tree)
                                                                                                 (if (null-tree? tree)
                                                                                                    #t
                                                                                                    (begin
                                                                                                       (traverse-postorder (node-left tree))
                                                                                                       (traverse-postorder (node-right tree))
                                                                                                       (action (node-item tree) (node-color tree)))))))
                                                                     (if (eq? order 'preorder)
                                                                        (traverse-preorder tree)
                                                                        (if (eq? order 'inorder)
                                                                           (traverse-inorder tree)
                                                                           (if (eq? order 'postorder)
                                                                              (traverse-postorder tree)
                                                                              (error "Unknown tree traversal order")))))))))
                                                (left-rotate (lambda (node-x)
                                                               (<change>
                                                                  ()
                                                                  node-parent)
                                                               (let ((node-y (node-right node-x)))
                                                                  (<change>
                                                                     (node-set-right! node-x (node-left node-y))
                                                                     (node-set-parent! (node-left node-y) node-x))
                                                                  (<change>
                                                                     (node-set-parent! (node-left node-y) node-x)
                                                                     (node-set-right! node-x (node-left node-y)))
                                                                  (node-set-parent! node-y (node-parent node-x))
                                                                  (<change>
                                                                     (if (not (null-tree? (node-parent node-x)))
                                                                        (if (same? (node-item node-x) (node-item (node-left (node-parent node-x))))
                                                                           (node-set-left! (node-parent node-x) node-y)
                                                                           (node-set-right! (node-parent node-x) node-y))
                                                                        (set! content node-y))
                                                                     ((lambda (x) x)
                                                                        (if (not (null-tree? (node-parent node-x)))
                                                                           (if (same? (node-item node-x) (node-item (node-left (node-parent node-x))))
                                                                              (<change>
                                                                                 (node-set-left! (node-parent node-x) node-y)
                                                                                 (node-set-right! (node-parent node-x) node-y))
                                                                              (<change>
                                                                                 (node-set-right! (node-parent node-x) node-y)
                                                                                 (node-set-left! (node-parent node-x) node-y)))
                                                                           (set! content node-y))))
                                                                  (node-set-left! node-y node-x)
                                                                  (node-set-parent! node-x node-y))))
                                                (right-rotate (lambda (node-y)
                                                                (<change>
                                                                   ()
                                                                   node-set-right!)
                                                                (let ((node-x (node-left node-y)))
                                                                   (<change>
                                                                      ()
                                                                      node-y)
                                                                   (node-set-left! node-y (node-right node-x))
                                                                   (node-set-parent! (node-right node-x) node-y)
                                                                   (node-set-parent! node-x (node-parent node-y))
                                                                   (<change>
                                                                      (if (not (null-tree? (node-parent node-y)))
                                                                         (if (same? (node-item node-y) (node-item (node-left (node-parent node-y))))
                                                                            (node-set-left! (node-parent node-y) node-x)
                                                                            (node-set-right! (node-parent node-y) node-x))
                                                                         (set! content node-x))
                                                                      (node-set-right! node-x node-y))
                                                                   (<change>
                                                                      (node-set-right! node-x node-y)
                                                                      (if (not (null-tree? (node-parent node-y)))
                                                                         (if (same? (node-item node-y) (node-item (node-left (node-parent node-y))))
                                                                            (node-set-left! (node-parent node-y) node-x)
                                                                            (node-set-right! (node-parent node-y) node-x))
                                                                         (set! content node-x)))
                                                                   (node-set-parent! node-y node-x))))
                                                (parent-is-in (lambda (node-x node-branch then-rotate other-rotate)
                                                                (let ((node-y (node-branch (node-parent (node-parent node-x)))))
                                                                   (if (equal? 'red (node-color node-y))
                                                                      (begin
                                                                         (node-set-color-black! (node-parent node-x))
                                                                         (node-set-color-black! node-y)
                                                                         (<change>
                                                                            (node-set-color-red! (node-parent (node-parent node-x)))
                                                                            (evaluate-redblack-conditions (node-parent (node-parent node-x))))
                                                                         (<change>
                                                                            (evaluate-redblack-conditions (node-parent (node-parent node-x)))
                                                                            (node-set-color-red! (node-parent (node-parent node-x)))))
                                                                      (begin
                                                                         (if (if (not (null-tree? (node-branch (node-parent node-x)))) (same? (node-item node-x) (node-item (node-branch (node-parent node-x)))) #f)
                                                                            (begin
                                                                               (set! node-x (node-parent node-x))
                                                                               (<change>
                                                                                  (then-rotate node-x)
                                                                                  ((lambda (x) x) (then-rotate node-x))))
                                                                            #f)
                                                                         (node-set-color-black! (node-parent node-x))
                                                                         (<change>
                                                                            (node-set-color-red! (node-parent (node-parent node-x)))
                                                                            ())
                                                                         (<change>
                                                                            (other-rotate (node-parent (node-parent node-x)))
                                                                            ())
                                                                         (evaluate-redblack-conditions node-x))))))
                                                (evaluate-redblack-conditions (lambda (node-x)
                                                                                (if (if (<change> (not (same? (node-item node-x) (node-item content))) (not (not (same? (node-item node-x) (node-item content))))) (if (equal? 'red (node-color (node-parent node-x))) (not (null-tree? (node-parent (node-parent node-x)))) #f) #f)
                                                                                   (if (if (not (null-tree? (node-left (node-parent (node-parent node-x))))) (same? (node-item (node-parent node-x)) (node-item (node-left (node-parent (node-parent node-x))))) #f)
                                                                                      (parent-is-in node-x node-right left-rotate right-rotate)
                                                                                      (parent-is-in node-x node-left right-rotate left-rotate))
                                                                                   #f)))
                                                (child-is-in (lambda (node-x main-branch other-branch main-rotate other-rotate)
                                                               (let ((node-w (main-branch (node-parent node-x))))
                                                                  (<change>
                                                                     (if (equal? 'red (node-color node-w))
                                                                        (begin
                                                                           (node-set-color-red! (node-parent node-x))
                                                                           (node-set-color-black! node-w)
                                                                           (main-rotate (node-parent node-x))
                                                                           (set! node-w (main-branch (node-parent node-x))))
                                                                        #f)
                                                                     ((lambda (x) x)
                                                                        (if (equal? 'red (node-color node-w))
                                                                           (begin
                                                                              (<change>
                                                                                 ()
                                                                                 node-x)
                                                                              (<change>
                                                                                 (node-set-color-red! (node-parent node-x))
                                                                                 ())
                                                                              (node-set-color-black! node-w)
                                                                              (main-rotate (node-parent node-x))
                                                                              (set! node-w (main-branch (node-parent node-x))))
                                                                           #f)))
                                                                  (if (if (eq? 'black (node-color (node-left node-w))) (eq? 'black (node-color (node-right node-w))) #f)
                                                                     (begin
                                                                        (<change>
                                                                           ()
                                                                           (node-set-color-red! node-w))
                                                                        (<change>
                                                                           ()
                                                                           (node-set-color-red! node-w))
                                                                        (node-set-color-red! node-w)
                                                                        (fixup-redblack-conditions (node-parent node-x)))
                                                                     (begin
                                                                        (<change>
                                                                           (if (eq? 'black (node-color (main-branch node-w)))
                                                                              (begin
                                                                                 (node-set-color-black! (other-branch node-w))
                                                                                 (node-set-color-red! node-w)
                                                                                 (other-rotate node-w)
                                                                                 (set! node-w (main-branch (node-parent node-w))))
                                                                              #f)
                                                                           ())
                                                                        (node-set-color! node-w (node-color (node-parent node-x)))
                                                                        (<change>
                                                                           (node-set-color-black! (node-parent node-x))
                                                                           (node-set-color-black! (main-branch node-w)))
                                                                        (<change>
                                                                           (node-set-color-black! (main-branch node-w))
                                                                           (node-set-color-black! (node-parent node-x)))
                                                                        (main-rotate (node-parent node-x))
                                                                        (fixup-redblack-conditions content))))))
                                                (fixup-redblack-conditions (lambda (node-x)
                                                                             (if (if (not (same? (node-item node-x) (node-item content))) (equal? 'black (node-color node-x)) #f)
                                                                                (if (same? (node-item node-x) (node-item (node-left (node-parent node-x))))
                                                                                   (child-is-in node-x node-right node-left left-rotate right-rotate)
                                                                                   (child-is-in node-x node-left node-right right-rotate left-rotate))
                                                                                (node-set-color-black! node-x))))
                                                (tree-empty? (lambda ()
                                                               (null-tree? content)))
                                                (lookup (lambda (element)
                                                          (letrec ((lookup-aux (lambda (node)
                                                                                 (if (<change> (null-tree? node) (not (null-tree? node)))
                                                                                    #f
                                                                                    (if (same? element (node-item node))
                                                                                       (node-item node)
                                                                                       (if (less? element (node-item node))
                                                                                          (lookup-aux (node-left node))
                                                                                          (lookup-aux (node-right node))))))))
                                                             (lookup-aux content))))
                                                (insert (lambda (element)
                                                          (letrec ((insert-aux (lambda (node parent)
                                                                                 (if (null-tree? node)
                                                                                    (let ((new-node (make-node element (make-null-tree) (make-null-tree) (make-null-tree))))
                                                                                       (node-set-parent! (node-left new-node) new-node)
                                                                                       (node-set-parent! (node-right new-node) new-node)
                                                                                       (if (not (null-tree? parent))
                                                                                          (begin
                                                                                             (node-set-parent! new-node parent)
                                                                                             (if (less? element (node-item parent))
                                                                                                (node-set-left! parent new-node)
                                                                                                (node-set-right! parent new-node))
                                                                                             (evaluate-redblack-conditions new-node))
                                                                                          (begin
                                                                                             (set! content new-node)))
                                                                                       (node-set-color-black! content)
                                                                                       #t)
                                                                                    (if (same? element (node-item node))
                                                                                       (begin
                                                                                          (node-set-item! node element)
                                                                                          #t)
                                                                                       (if (less? element (node-item node))
                                                                                          (insert-aux (node-left node) node)
                                                                                          (insert-aux (node-right node) node)))))))
                                                             (insert-aux content (make-null-tree)))))
                                                (delete (lambda (element)
                                                          (letrec ((left-most-node (lambda (node parent)
                                                                                     (if (null-tree? (node-left node))
                                                                                        node
                                                                                        (left-most-node (node-left node) node))))
                                                                   (delete-aux (lambda (node)
                                                                                 (if (null-tree? node)
                                                                                    #f
                                                                                    (if (same? element (node-item node))
                                                                                       (let* ((node-y (if (let ((__or_res (null-tree? (node-left node)))) (if __or_res __or_res (null-tree? (node-right node))))
                                                                                                        node
                                                                                                        (left-most-node (node-right node) #f)))
                                                                                              (node-x (if (null-tree? (node-left node-y))
                                                                                                        (node-right node-y)
                                                                                                        (node-left node-y))))
                                                                                          (node-set-parent! node-x (node-parent node-y))
                                                                                          (if (null-tree? (node-parent node-y))
                                                                                             (set! content node-x)
                                                                                             (if (if (not (null-tree? (node-left (node-parent node-y)))) (same? (node-item node-y) (node-item (node-left (node-parent node-y)))) #f)
                                                                                                (node-set-left! (node-parent node-y) node-x)
                                                                                                (node-set-right! (node-parent node-y) node-x)))
                                                                                          (if (not (same? (node-item node-y) (node-item node)))
                                                                                             (begin
                                                                                                (node-set-item! node (node-item node-y)))
                                                                                             #f)
                                                                                          (if (eq? 'black (node-color node-y))
                                                                                             (fixup-redblack-conditions node-x)
                                                                                             #f)
                                                                                          #t)
                                                                                       (if (less? element (node-item node))
                                                                                          (delete-aux (node-left node))
                                                                                          (delete-aux (node-right node))))))))
                                                             (delete-aux content))))
                                                (dispatch (lambda (msg . args)
                                                            (if (eq? msg 'empty)
                                                               (tree-empty?)
                                                               (if (eq? msg 'insert)
                                                                  (insert (car args))
                                                                  (if (eq? msg 'delete)
                                                                     (delete (car args))
                                                                     (if (<change> (eq? msg 'lookup) (not (eq? msg 'lookup)))
                                                                        (lookup (car args))
                                                                        (if (<change> (eq? msg 'display) (not (eq? msg 'display)))
                                                                           (traverse
                                                                              content
                                                                              'preorder
                                                                              (lambda (x c)
                                                                                 (<change>
                                                                                    ()
                                                                                    (display (cons x c)))
                                                                                 (display (cons x c))
                                                                                 (newline)))
                                                                           (error "unknown request -- create-BST")))))))))
                                          dispatch)))))
         (tree (create-redblack-tree)))
   (tree 'insert 1)
   (tree 'display)
   (tree 'insert 2)
   (<change>
      (tree 'display)
      (tree 'insert 5))
   (<change>
      (tree 'insert 5)
      (tree 'display))
   (tree 'display)
   (tree 'insert 7)
   (tree 'display)
   (<change>
      (tree 'insert 8)
      (tree 'display))
   (<change>
      (tree 'display)
      (tree 'insert 8))
   (tree 'insert 11)
   (tree 'display)
   (tree 'insert 14)
   (<change>
      (tree 'display)
      (tree 'insert 15))
   (<change>
      (tree 'insert 15)
      (tree 'display))
   (tree 'display)
   (<change>
      (tree 'insert 4)
      ((lambda (x) x) (tree 'insert 4)))
   (<change>
      ()
      tree)
   (tree 'display)
   (tree 'insert 3)
   (tree 'display)
   (<change>
      (tree 'delete 1)
      (tree 'display))
   (<change>
      (tree 'display)
      (tree 'delete 1))
   (tree 'delete 2)
   (<change>
      (tree 'display)
      ((lambda (x) x) (tree 'display)))
   (<change>
      (tree 'delete 11)
      (tree 'display))
   (<change>
      (tree 'display)
      (tree 'delete 11)))