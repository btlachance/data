#lang typed/racket/base
(require racket/vector
         racket/match
         racket/bool)

(define MIN-SIZE 4)
(struct empty ())
(struct (a) heap ([vec : (Vectorof (U empty a))]
                  [count : Integer]
                  [<=? : (-> a a Boolean)])
  #:mutable)
;; length(vec)/4 <= size <= length(vec), except size >= MIN-SIZE
;; size = next available index

;; A VT is a binary tree represented as a vector.

;; VT Index functions

(define (vt-root) 0)

(define (vt-parent [n : Integer]) (quotient (sub1 n) 2))
(define (vt-leftchild [n : Integer]) (+ (* n 2) 1))
(define (vt-rightchild [n : Integer]) (+ (* n 2) 2))

(define (vt-root? [n : Integer]) (zero? n))
(define (vt-leftchild? [n : Integer]) (odd? n))
(define (vt-rightchild? [n : Integer]) (even? n))


;; Operations
(: heapify-up  (All (a) (-> (-> a a Boolean) (Vectorof (U empty a)) Integer Void)))
(define (heapify-up <=? vec n)
  (unless (vt-root? n)
    (let* ([parent (vt-parent n)]
           [n-key (vector-ref vec n)]
           [parent-key (vector-ref vec parent)])
      (unless (or (empty? n-key) (empty? parent-key) (<=? parent-key n-key))
        (vector-set! vec parent n-key)
        (vector-set! vec n parent-key)
        (heapify-up <=? vec parent)))))

(: heapify-down (All (a) (case-> (-> (-> a a Boolean) (Vectorof (U empty a)) Integer Integer Void)
                                 (-> (-> a a Boolean) (Vectorof a) Integer Integer Void))))
(define (heapify-down <=? vec n size)
  (let ([left (vt-leftchild n)]
        [right (vt-rightchild n)]
        [n-key (vector-ref vec n)])
    (when (< left size)
      (define left-key (vector-ref vec left))
      (unless (empty? left-key)
        (let-values ([(child child-key)
                      (if (< right size)
                          (let ([right-key (vector-ref vec right)])
                            (if (and (not (empty? right-key))
                                     (<=? left-key right-key))
                                (values left left-key)
                                (values right right-key)))
                          (values left left-key))])
          (unless (or (empty? n-key) (empty? child-key) (<=? n-key child-key))
            (vector-set! vec n child-key)
            (vector-set! vec child n-key)
            (heapify-down <=? vec child size)))))))

(: grow-vector (All (a) (-> (Vectorof (U empty a)) Integer (Vectorof (U empty a)))))
(define (grow-vector v1 new-size-min)
  (let ([new-size (let loop : Integer ([size (vector-length v1)])
                    (if (>= size new-size-min)
                        size
                        (loop (* size 2))))])
    (let ([v2 (ann (make-vector new-size (empty)) (Vectorof (U empty a)))])
      (vector-copy! v2 0 v1 0)
      v2)))

(: shrink-vector (All (a) (-> (Vectorof (U empty a)) (Vectorof (U empty a)))))
(define (shrink-vector v1)
  (let ([v2 (ann (make-vector (quotient (vector-length v1) 2) (empty)) (Vectorof (U empty a)))])
    (vector-copy! v2 0 v1 0 (vector-length v2))
    v2))

;; Heaps
(: make-heap (All (a) (-> (-> a a Boolean) (heap a))))
(define (make-heap <=?)
  (heap (ann (make-vector MIN-SIZE (empty)) (Vectorof (U empty a))) 0 <=?))

(: list->heap (All (a) (-> (-> a a Boolean) (List a) (heap a))))
(define (list->heap <=? lst)
  (vector->heap <=? (list->vector lst)))

(: vector->heap (All (a) (->* ((-> a a Boolean) (Vectorof a)) (Integer Integer) (heap a))))
(define (vector->heap <=? vec0 [start 0] [end (vector-length vec0)])
  (define size (- end start))
  (define len (let loop : Integer ([len MIN-SIZE]) (if (<= size len) len (loop (* 2 len)))))
  (define vec (ann (make-vector len (empty)) (Vectorof (U empty a))))
  ;; size <= length(vec)
  (vector-copy! vec 0
                (for/vector : (Vectorof (U empty a)) ([i vec0]) i)
                start end)
  (for ([n (in-range (sub1 size) -1 -1)])
    (heapify-down <=? vec n size))
  (heap vec size <=?))

(: heap-copy (All (a) (-> (heap a) (heap a))))
(define (heap-copy h)
  (match h
    [(heap vec count <=?)
     (heap (vector-copy vec) count <=?)]))

(: heap-add! (All (a) (-> (heap a) a * Void)))
(define (heap-add! h . keys)
  (heap-add-all! h (list->vector keys)))

(: heap-add-all! (All (a) (-> (heap a) (U (Vectorof a) (Listof a) (heap a)) Void)))
(define (heap-add-all! h keys)
  (let-values ([(keys keys-size)
                (cond [(list? keys)
                       (let ([keys-v (list->vector keys)])
                         (values keys-v (vector-length keys-v)))]
                      [(vector? keys)
                       (values keys (vector-length keys))]
                      [(heap? keys)
                       (values (heap-vec keys) (heap-count keys))])])
    (match h
      [(heap vec size <=?)
       (let* ([new-size (+ size keys-size)]
              [vec (if (> new-size (vector-length vec))
                       (let ([vec (grow-vector vec new-size)])
                         (set-heap-vec! h vec)
                         vec)
                       vec)])
         (vector-copy! vec size
                       (for/vector : (Vectorof (U empty a)) ([i keys]) i)
                       0 keys-size)
         (for ([n (in-range size new-size)])
           (heapify-up <=? vec n))
         (set-heap-count! h new-size))])))

(: heap-min (All (a) (-> (heap a) a)))
(define (heap-min h)
  (match h
    [(heap vec size <=?)
     (define val (vector-ref vec 0))
     (when (or (zero? size) (empty? val))
       (error 'heap-min "empty heap"))
     val]))

(: heap-remove-min! (All (a) (-> (heap a) Void)))
(define (heap-remove-min! h)
  (match h
    [(heap vec size <=?)
     (when (zero? size)
       (error 'heap-remove-min! "empty heap"))
     (heap-remove-index! h 0)]))

(: heap-remove-index! (All (a) (-> (heap a) Integer Void)))
(define (heap-remove-index! h index)
  (match h
    [(heap vec size <=?)
     (unless (< index size)
       (if (zero? size)
           (error 'heap-remove-index!
                  "empty heap: ~s" index)
           (error 'heap-remove-index!
                  "index out of bounds [0,~s]: ~s" (sub1 size) index)))
     (define sub1-size (sub1 size))
     (vector-set! vec index (vector-ref vec sub1-size))
     (vector-set! vec sub1-size (empty))
     (cond
       [(= sub1-size index)
        ;; easy to remove the right-most leaf
        (void)]
       [(= index 0)
        ;; can only go down when at the root
        (heapify-down <=? vec index sub1-size)]
       [else
        (define index-key (vector-ref vec index))
        (define parent-key (vector-ref vec (vt-parent index)))
        (when (and (not (empty? index-key)) (not (empty? parent-key)))
          (cond
            ;; if we are in the right relationship with our parent,
            ;; try to heapify down
            [(<=? parent-key index-key)
             (heapify-down <=? vec index sub1-size)]
            [else
             ;; otherwise we need to heapify up
             (heapify-up <=? vec index)]))])
     (when (< MIN-SIZE size (quotient (vector-length vec) 4))
       (set-heap-vec! h (shrink-vector vec)))
     (set-heap-count! h sub1-size)]))

(: heap-get-index (All (a) (-> (heap a) a (-> a a Boolean) (U False Integer))))
(define (heap-get-index h v same?)
  (match h
    [(heap vec size <=?)
     (and (not (eq? 0 size))
          (let search ([n 0] [n-key (vector-ref vec 0)])
            (cond
             [(and (not (empty? n-key)) (same? n-key v)) n]
             ;; The heap property ensures n-key <= all its children
             [else
              (define (search-right)
                (define right (vt-rightchild n))
                (and (< right size)
                     (let ([right-key (vector-ref vec right)])
                       (and (not (empty? right-key))
                            (<=? right-key v)
                            (search right right-key)))))
              ;; Try going left if the left child is <= v
              (define left (vt-leftchild n))
              (and (< left size) ;; if no left, there can't be a right.
                   (let ([left-key (vector-ref vec left)])
                     (and (not (empty? left-key))
                          ;; If left <= v, try left side.
                          (if (<=? left-key v)
                              (or (search left left-key) (search-right))
                              (search-right)))))])))]))

(: heap-remove! (All (a) (->* ((heap a) a) (#:same? (-> a a Boolean)) Void)))
(define (heap-remove! h v #:same? [same? equal?])
  (define index/#f (heap-get-index h v same?))
  (cond
    [(false? index/#f) (void)]
    [else (heap-remove-index! h index/#f)]))

(: in-heap (All (a) (-> (heap a) (Sequenceof a))))
(define (in-heap h)
  (in-heap/consume! (heap-copy h)))

(: in-heap/consume! (All (a) (-> (heap a) (Sequenceof a))))
(define (in-heap/consume! h)
  (make-do-sequence
   (lambda ()
     (values (lambda (_) (heap-min h))
             (lambda (_) (heap-remove-min! h) #t)
             #t
             (lambda (_) (> (heap-count h) 0))
             (lambda _ #t)
             (lambda _ #t)))))

;; --------

;; preferred order is (heap-sort vec <=?), but allow old order too
(: heap-sort! (All (a) (-> (U (-> a a Boolean) (Vectorof a))
                           (U (-> a a Boolean) (Vectorof a)) Void)))
(define (heap-sort! x y)
  (cond [(and (vector? x) (procedure? y))
         (heap-sort!* x y)]
        [(and (vector? y) (procedure? x))
         (heap-sort!* y x)]
        [else
         (unless (vector? x)
           (raise-argument-error 'heap-sort! "vector?" x))
         (raise-argument-error 'heap-sort! "procedure?" y)]))

(: heap-sort!* (All (a) (-> (Vectorof a) (-> a a Boolean) Void)))
(define (heap-sort!* v <=?)
  ;; to get ascending order, need max-heap, so reverse comparison
  (define (>=? [x : a] [y : a]) (<=? y x))
  (define size (vector-length v))
  (for ([n (in-range (sub1 size) -1 -1)])
    (heapify-down >=? v n size))
  (for ([last (in-range (sub1 size) 0 -1)])
    (let ([tmp (vector-ref v 0)])
      (vector-set! v 0 (vector-ref v last))
      (vector-set! v last tmp))
    (heapify-down >=? v 0 last)))

(: heap->vector (All (a) (-> (heap a) (Vectorof a))))
(define (heap->vector h)
  (match h
    [(heap vec size <=?)
     (let ([v (for/vector : (Vectorof a) ([i (vector-copy vec 0 size)] #:when (not (empty? i))) i)])
       (heap-sort!* v <=?)
       v)]))

;; --------

(provide
 make-heap
 heap?
 heap-count
 heap-add!
 heap-add-all!
 heap-min
 heap-remove-min!
 heap-remove!

 vector->heap
 heap->vector
 heap-copy

 in-heap
 in-heap/consume!)

(provide heap-sort!)

(module+ test-util
  (provide valid-heap?)
  (: valid-heap? (-> (heap Flonum) Boolean))
  (define (valid-heap? a-heap)
    (match a-heap
      [(heap vec size <=?)
       (let loop : Boolean ([i 0]
                            [parent -inf.0])
         (cond
           [(< i size)
            (define this (vector-ref vec i))
            (and (not (empty? this))
                 (<=? parent this)
                 (loop (vt-leftchild i) this)
                 (loop (vt-rightchild i) this))]
           [else #t]))])))
